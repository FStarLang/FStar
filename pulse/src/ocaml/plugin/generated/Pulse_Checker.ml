open Prims
let (terms_to_string :
  Pulse_Syntax_Base.term Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Tactics_Util.map Pulse_Syntax_Printer.term_to_string t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (55))
               (Prims.of_int (23)) (Prims.of_int (55)) (Prims.of_int (68)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (55))
               (Prims.of_int (4)) (Prims.of_int (55)) (Prims.of_int (68)))))
      (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_String.concat "\n" uu___1))
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
                             let uu___1 =
                               Obj.magic
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       match Pulse_Syntax_Pure.inspect_term w
                                       with
                                       | Pulse_Syntax_Pure.Tm_Unknown ->
                                           ((FStar_Pervasives_Native.Some
                                               (Pulse_Typing_Env.fresh g)),
                                             (Pulse_Syntax_Pure.tm_var
                                                {
                                                  Pulse_Syntax_Base.nm_index
                                                    =
                                                    (Pulse_Typing_Env.fresh g);
                                                  Pulse_Syntax_Base.nm_ppname
                                                    =
                                                    (b.Pulse_Syntax_Base.binder_ppname)
                                                }),
                                             (Pulse_Typing_Env.push_binding g
                                                (Pulse_Typing_Env.fresh g)
                                                b.Pulse_Syntax_Base.binder_ppname
                                                b.Pulse_Syntax_Base.binder_ty))
                                       | uu___3 ->
                                           (FStar_Pervasives_Native.None, w,
                                             g))) in
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
                               (Obj.magic uu___1)
                               (fun uu___2 ->
                                  (fun uu___2 ->
                                     match uu___2 with
                                     | (xopt, w1, g1) ->
                                         let uu___3 =
                                           Obj.magic
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___4 ->
                                                   Pulse_Syntax_Naming.open_term'
                                                     body w1 Prims.int_zero)) in
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
                                              (Obj.magic uu___3)
                                              (fun uu___4 ->
                                                 (fun t1 ->
                                                    let uu___4 =
                                                      gen_names_for_unknowns
                                                        g1 t1 ws1 in
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
                                                         (Obj.magic uu___4)
                                                         (fun uu___5 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___6 ->
                                                                 match uu___5
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
                                                   uu___4))) uu___2)
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
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> t.Pulse_Syntax_Base.term1)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (89))
                 (Prims.of_int (43)) (Prims.of_int (89)) (Prims.of_int (49)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (87))
                 (Prims.of_int (28)) (Prims.of_int (113)) (Prims.of_int (10)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | Pulse_Syntax_Base.Tm_IntroExists
                  { Pulse_Syntax_Base.p5 = p;
                    Pulse_Syntax_Base.witnesses = ws;_}
                  ->
                  let uu___2 = gen_names_for_unknowns g p ws in
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
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 ->
                               match uu___3 with
                               | (new_names, opened_p, new_ws) ->
                                   (match new_names with
                                    | [] -> FStar_Pervasives_Native.None
                                    | uu___5 ->
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
                                                                   Prims.int_zero).Pulse_Syntax_Base.effect_tag);
                                                             Pulse_Syntax_Base.source
                                                               =
                                                               ((Pulse_Syntax_Naming.close_st_term'
                                                                   e x
                                                                   Prims.int_zero).Pulse_Syntax_Base.source)
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
                                                            (t.Pulse_Syntax_Base.effect_tag);
                                                          Pulse_Syntax_Base.source
                                                            =
                                                            (t.Pulse_Syntax_Base.source)
                                                        }
                                                    });
                                               Pulse_Syntax_Base.range1 =
                                                 (t.Pulse_Syntax_Base.range1);
                                               Pulse_Syntax_Base.effect_tag =
                                                 (Pulse_Syntax_Base.as_effect_hint
                                                    Pulse_Syntax_Base.STT_Ghost);
                                               Pulse_Syntax_Base.source =
                                                 (FStar_Sealed.seal false)
                                             })))))) uu___1)
let rec (transform_to_unary_intro_exists :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term Prims.list ->
        (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun ws ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> Pulse_RuntimeUtils.range_of_term t)) in
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
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun t_rng ->
                match ws with
                | [] ->
                    Obj.magic
                      (Pulse_Typing_Env.fail g
                         (FStar_Pervasives_Native.Some t_rng)
                         "intro exists with empty witnesses")
                | w::[] ->
                    let uu___1 =
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___2 -> Pulse_Syntax_Pure.inspect_term t)) in
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
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            (fun tv ->
                               if Pulse_Syntax_Pure.uu___is_Tm_ExistsSL tv
                               then
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
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
                              uu___2))
                | w::ws1 ->
                    (match Pulse_Syntax_Pure.inspect_term t with
                     | Pulse_Syntax_Pure.Tm_ExistsSL (u, b, body) ->
                         let uu___1 =
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   Pulse_Syntax_Naming.subst_term body
                                     [FStar_Reflection_Typing.DT
                                        (Prims.int_zero, w)])) in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (129))
                                       (Prims.of_int (17))
                                       (Prims.of_int (129))
                                       (Prims.of_int (46)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (129))
                                       (Prims.of_int (49))
                                       (Prims.of_int (136))
                                       (Prims.of_int (34)))))
                              (Obj.magic uu___1)
                              (fun uu___2 ->
                                 (fun body1 ->
                                    let uu___2 =
                                      transform_to_unary_intro_exists g body1
                                        ws1 in
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
                                         (Obj.magic uu___2)
                                         (fun st ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___3 ->
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
                                                      }))))) uu___2))
                     | uu___1 ->
                         Obj.magic
                           (Pulse_Typing_Env.fail g
                              (FStar_Pervasives_Native.Some t_rng)
                              "intro exists with non-existential"))) uu___1)
let (trace :
  Pulse_Syntax_Base.st_term ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.range -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun g ->
      fun pre ->
        fun rng ->
          let uu___ =
            FStar_Tactics_V2_Builtins.norm_well_typed_term
              (Pulse_Typing.elab_env g)
              [FStar_Pervasives.unascribe;
              FStar_Pervasives.primops;
              FStar_Pervasives.iota] pre in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (145)) (Prims.of_int (12))
                     (Prims.of_int (145)) (Prims.of_int (89)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (145)) (Prims.of_int (92))
                     (Prims.of_int (159)) (Prims.of_int (27)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun pre1 ->
                  let uu___1 =
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            Pulse_Syntax_Pure.canon_slprop_print pre1 in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Pulse.Checker.fst"
                                     (Prims.of_int (148)) (Prims.of_int (20))
                                     (Prims.of_int (148)) (Prims.of_int (42)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Pulse.Checker.fst"
                                     (Prims.of_int (148)) (Prims.of_int (13))
                                     (Prims.of_int (148)) (Prims.of_int (43)))))
                            (Obj.magic uu___5)
                            (fun uu___6 ->
                               (fun uu___6 ->
                                  Obj.magic
                                    (Pulse_PP.pp Pulse_PP.printable_term
                                       uu___6)) uu___6) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Checker.fst"
                                   (Prims.of_int (148)) (Prims.of_int (13))
                                   (Prims.of_int (148)) (Prims.of_int (43)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Checker.fst"
                                   (Prims.of_int (148)) (Prims.of_int (6))
                                   (Prims.of_int (148)) (Prims.of_int (43)))))
                          (Obj.magic uu___4)
                          (fun uu___5 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___6 -> Pulse_PP.indent uu___5)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.fst"
                                 (Prims.of_int (148)) (Prims.of_int (6))
                                 (Prims.of_int (148)) (Prims.of_int (43)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.fst"
                                 (Prims.of_int (147)) (Prims.of_int (4))
                                 (Prims.of_int (148)) (Prims.of_int (43)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___5 ->
                                FStar_Pprint.op_Hat_Hat
                                  (Pulse_PP.text "TRACE. Current context:")
                                  uu___4)) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.fst"
                               (Prims.of_int (147)) (Prims.of_int (4))
                               (Prims.of_int (148)) (Prims.of_int (43)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.fst"
                               (Prims.of_int (146)) (Prims.of_int (12))
                               (Prims.of_int (153)) (Prims.of_int (3)))))
                      (Obj.magic uu___2)
                      (fun uu___3 ->
                         (fun uu___3 ->
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  let uu___7 =
                                    Pulse_Typing_Env.env_to_doc' true g in
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (150))
                                             (Prims.of_int (13))
                                             (Prims.of_int (150))
                                             (Prims.of_int (33)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (150))
                                             (Prims.of_int (6))
                                             (Prims.of_int (150))
                                             (Prims.of_int (33)))))
                                    (Obj.magic uu___7)
                                    (fun uu___8 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___9 ->
                                            Pulse_PP.indent uu___8)) in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (150))
                                           (Prims.of_int (6))
                                           (Prims.of_int (150))
                                           (Prims.of_int (33)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (149))
                                           (Prims.of_int (4))
                                           (Prims.of_int (150))
                                           (Prims.of_int (33)))))
                                  (Obj.magic uu___6)
                                  (fun uu___7 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___8 ->
                                          FStar_Pprint.op_Hat_Hat
                                            (Pulse_PP.text
                                               "Typing environment (units elided): ")
                                            uu___7)) in
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (149))
                                         (Prims.of_int (4))
                                         (Prims.of_int (150))
                                         (Prims.of_int (33)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (146))
                                         (Prims.of_int (12))
                                         (Prims.of_int (153))
                                         (Prims.of_int (3)))))
                                (Obj.magic uu___5)
                                (fun uu___6 ->
                                   (fun uu___6 ->
                                      let uu___7 =
                                        let uu___8 =
                                          let uu___9 =
                                            Pulse_PP.pp
                                              Pulse_PP.printable_st_term t in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (152))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (152))
                                                     (Prims.of_int (12)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (151))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (152))
                                                     (Prims.of_int (12)))))
                                            (Obj.magic uu___9)
                                            (fun uu___10 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___11 ->
                                                    FStar_Pprint.prefix
                                                      (Prims.of_int (2))
                                                      Prims.int_one
                                                      (Pulse_PP.text
                                                         "Just before checking:")
                                                      uu___10)) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.fst"
                                                   (Prims.of_int (151))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (152))
                                                   (Prims.of_int (12)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.fst"
                                                   (Prims.of_int (146))
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (153))
                                                   (Prims.of_int (3)))))
                                          (Obj.magic uu___8)
                                          (fun uu___9 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___10 -> [uu___9])) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.fst"
                                                    (Prims.of_int (146))
                                                    (Prims.of_int (12))
                                                    (Prims.of_int (153))
                                                    (Prims.of_int (3)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.fst"
                                                    (Prims.of_int (146))
                                                    (Prims.of_int (12))
                                                    (Prims.of_int (153))
                                                    (Prims.of_int (3)))))
                                           (Obj.magic uu___7)
                                           (fun uu___8 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___9 -> uu___6 ::
                                                   uu___8)))) uu___6) in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.fst"
                                          (Prims.of_int (146))
                                          (Prims.of_int (12))
                                          (Prims.of_int (153))
                                          (Prims.of_int (3)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.fst"
                                          (Prims.of_int (146))
                                          (Prims.of_int (12))
                                          (Prims.of_int (153))
                                          (Prims.of_int (3)))))
                                 (Obj.magic uu___4)
                                 (fun uu___5 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___6 -> uu___3 :: uu___5))))
                           uu___3) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (146)) (Prims.of_int (12))
                                (Prims.of_int (153)) (Prims.of_int (3)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (153)) (Prims.of_int (6))
                                (Prims.of_int (159)) (Prims.of_int (27)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun msg ->
                             let uu___2 =
                               let uu___3 =
                                 let uu___4 = FStar_Tactics_Unseal.unseal rng in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.fst"
                                            (Prims.of_int (156))
                                            (Prims.of_int (50))
                                            (Prims.of_int (156))
                                            (Prims.of_int (64)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.fst"
                                            (Prims.of_int (156))
                                            (Prims.of_int (30))
                                            (Prims.of_int (156))
                                            (Prims.of_int (64)))))
                                   (Obj.magic uu___4)
                                   (fun uu___5 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___6 ->
                                           FStar_Range.explode uu___5)) in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.fst"
                                          (Prims.of_int (156))
                                          (Prims.of_int (30))
                                          (Prims.of_int (156))
                                          (Prims.of_int (64)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.fst"
                                          (Prims.of_int (155))
                                          (Prims.of_int (11))
                                          (Prims.of_int (157))
                                          (Prims.of_int (36)))))
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___5 ->
                                         match uu___4 with
                                         | (f, l1, c1, l2, c2) ->
                                             FStar_Range.mk_range f l1
                                               Prims.int_zero l1
                                               (Prims.of_int (2)))) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (155))
                                           (Prims.of_int (11))
                                           (Prims.of_int (157))
                                           (Prims.of_int (36)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (159))
                                           (Prims.of_int (2))
                                           (Prims.of_int (159))
                                           (Prims.of_int (27)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     (fun rng1 ->
                                        Obj.magic
                                          (Pulse_Typing_Env.info_doc g
                                             (FStar_Pervasives_Native.Some
                                                rng1) msg)) uu___3))) uu___2)))
                 uu___1)
let (maybe_trace :
  Pulse_Syntax_Base.st_term ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.range -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun g ->
      fun pre ->
        fun rng ->
          let uu___ =
            let uu___1 = FStar_Tactics_V2_Builtins.ext_getv "pulse:trace" in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.fst"
                       (Prims.of_int (165)) (Prims.of_int (18))
                       (Prims.of_int (165)) (Prims.of_int (42)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.fst"
                       (Prims.of_int (165)) (Prims.of_int (18))
                       (Prims.of_int (165)) (Prims.of_int (48)))))
              (Obj.magic uu___1)
              (fun uu___2 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___3 -> uu___2 = "1")) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (165)) (Prims.of_int (18))
                     (Prims.of_int (165)) (Prims.of_int (48)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (165)) (Prims.of_int (51))
                     (Prims.of_int (171)) (Prims.of_int (21)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun trace_opt ->
                  let uu___1 =
                    let uu___2 =
                      FStar_Tactics_V2_Builtins.ext_getv "pulse:trace_full" in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.fst"
                               (Prims.of_int (166)) (Prims.of_int (23))
                               (Prims.of_int (166)) (Prims.of_int (52)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.fst"
                               (Prims.of_int (166)) (Prims.of_int (23))
                               (Prims.of_int (166)) (Prims.of_int (58)))))
                      (Obj.magic uu___2)
                      (fun uu___3 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___4 -> uu___3 = "1")) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (166)) (Prims.of_int (23))
                                (Prims.of_int (166)) (Prims.of_int (58)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (166)) (Prims.of_int (61))
                                (Prims.of_int (171)) (Prims.of_int (21)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun trace_full_opt ->
                             let uu___2 =
                               FStar_Tactics_Unseal.unseal
                                 t.Pulse_Syntax_Base.source in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (167))
                                           (Prims.of_int (18))
                                           (Prims.of_int (167))
                                           (Prims.of_int (35)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (168))
                                           (Prims.of_int (2))
                                           (Prims.of_int (171))
                                           (Prims.of_int (21)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     (fun is_source ->
                                        if
                                          ((trace_opt && is_source) &&
                                             (Prims.op_Negation
                                                ((Pulse_Syntax_Base.uu___is_Tm_Bind
                                                    t.Pulse_Syntax_Base.term1)
                                                   ||
                                                   (Pulse_Syntax_Base.uu___is_Tm_TotBind
                                                      t.Pulse_Syntax_Base.term1))))
                                            || trace_full_opt
                                        then
                                          Obj.magic
                                            (Obj.repr (trace t g pre rng))
                                        else
                                          Obj.magic
                                            (Obj.repr
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___4 -> ()))))
                                       uu___3))) uu___2))) uu___1)
let rec (check : Pulse_Checker_Base.check_t) =
  fun g0 ->
    fun pre0 ->
      fun pre0_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun t ->
              Pulse_RuntimeUtils.with_error_bound t.Pulse_Syntax_Base.range1
                (fun uu___ ->
                   if
                     Pulse_Checker_AssertWithBinders.handle_head_immediately
                       t
                   then
                     Pulse_Checker_AssertWithBinders.check g0 pre0 ()
                       post_hint res_ppname t check
                   else
                     (let uu___2 =
                        Pulse_Checker_Prover.elim_exists_and_pure g0 pre0 () in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.fst"
                                 (Prims.of_int (187)) (Prims.of_int (6))
                                 (Prims.of_int (187)) (Prims.of_int (59)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.fst"
                                 (Prims.of_int (185)) (Prims.of_int (7))
                                 (Prims.of_int (326)) (Prims.of_int (3)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun uu___3 ->
                              match uu___3 with
                              | FStar_Pervasives.Mkdtuple4
                                  (g, pre, pre_typing, k_elim_pure) ->
                                  let uu___4 =
                                    maybe_trace t g pre
                                      t.Pulse_Syntax_Base.range1 in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.fst"
                                                (Prims.of_int (190))
                                                (Prims.of_int (4))
                                                (Prims.of_int (190))
                                                (Prims.of_int (31)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.fst"
                                                (Prims.of_int (192))
                                                (Prims.of_int (4))
                                                (Prims.of_int (325))
                                                (Prims.of_int (52)))))
                                       (Obj.magic uu___4)
                                       (fun uu___5 ->
                                          (fun uu___5 ->
                                             let uu___6 =
                                               if
                                                 Pulse_RuntimeUtils.debug_at_level
                                                   (Pulse_Typing_Env.fstar_env
                                                      g) "pulse.checker"
                                               then
                                                 Obj.magic
                                                   (Obj.repr
                                                      (let uu___7 =
                                                         let uu___8 =
                                                           Pulse_Syntax_Printer.st_term_to_string
                                                             t in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (58)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (59)))))
                                                           (Obj.magic uu___8)
                                                           (fun uu___9 ->
                                                              (fun uu___9 ->
                                                                 let uu___10
                                                                   =
                                                                   let uu___11
                                                                    =
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    pre in
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (59)))))
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
                                                                    Pulse_Typing_Env.env_to_string
                                                                    g in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    Pulse_RuntimeUtils.print_context
                                                                    (Pulse_Typing_Env.get_context
                                                                    g) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (59)))))
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
                                                                    FStar_Tactics_V2_Builtins.range_to_string
                                                                    t.Pulse_Syntax_Base.range1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (194))
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
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
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
                                                                    uu___21
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
                                                                    x3 "}}\n"))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (59)))))
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
                                                                    uu___18) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    uu___17
                                                                    uu___15))))
                                                                    uu___15) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    uu___14
                                                                    uu___12))))
                                                                    uu___12) in
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    uu___11
                                                                    uu___9))))
                                                                uu___9) in
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (193))
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (198))
                                                                  (Prims.of_int (59)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (193))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (198))
                                                                  (Prims.of_int (59)))))
                                                         (Obj.magic uu___7)
                                                         (fun uu___8 ->
                                                            (fun uu___8 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_V2_Builtins.print
                                                                    uu___8))
                                                              uu___8)))
                                               else
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___8 -> ()))) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (192))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (198))
                                                           (Prims.of_int (59)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (198))
                                                           (Prims.of_int (60))
                                                           (Prims.of_int (325))
                                                           (Prims.of_int (52)))))
                                                  (Obj.magic uu___6)
                                                  (fun uu___7 ->
                                                     (fun uu___7 ->
                                                        let uu___8 =
                                                          let uu___9 =
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___10
                                                                    ->
                                                                    Pulse_Checker_Pure.push_context
                                                                    (Pulse_Syntax_Printer.tag_of_st_term
                                                                    t)
                                                                    t.Pulse_Syntax_Base.range1
                                                                    g)) in
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (57)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (50)))))
                                                            (Obj.magic uu___9)
                                                            (fun uu___10 ->
                                                               (fun g1 ->
                                                                  match 
                                                                    t.Pulse_Syntax_Base.term1
                                                                  with
                                                                  | Pulse_Syntax_Base.Tm_Return
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Checker_Return.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t check))
                                                                  | Pulse_Syntax_Base.Tm_Abs
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Tm_Abs check should not have been called in the checker"))
                                                                  | Pulse_Syntax_Base.Tm_STApp
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Checker_STApp.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t))
                                                                  | Pulse_Syntax_Base.Tm_ElimExists
                                                                    uu___10
                                                                    ->
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
                                                                    =
                                                                    witnesses;_}
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___10
                                                                    =
                                                                    instantiate_unknown_witnesses
                                                                    g1 t in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (58)))))
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
                                                                    uu___12::[]
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Exists.check_intro_exists
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    uu___12
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    transform_to_unary_intro_exists
                                                                    g1 p
                                                                    witnesses in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun t1
                                                                    ->
                                                                    Obj.magic
                                                                    (check g1
                                                                    pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t1))
                                                                    uu___14))))
                                                                    uu___11)))
                                                                  | Pulse_Syntax_Base.Tm_Bind
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Checker_Bind.check_bind
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t check))
                                                                  | Pulse_Syntax_Base.Tm_TotBind
                                                                    uu___10
                                                                    ->
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
                                                                    (let uu___10
                                                                    =
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
                                                                    uu___11
                                                                    -> p)))
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
                                                                    (let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    p in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    q.Pulse_Typing.post in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (253))
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
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Multiple annotated postconditions---remove one of them.\nThe context expects the postcondition "
                                                                    (Prims.strcat
                                                                    uu___16
                                                                    ",\nbut this conditional was annotated with postcondition "))
                                                                    (Prims.strcat
                                                                    x ""))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    uu___15
                                                                    uu___13))))
                                                                    uu___13) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    uu___12))
                                                                    uu___12)))
                                                                    | 
                                                                    (uu___11,
                                                                    uu___12)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    "Pulse cannot yet infer a postcondition for a non-tail conditional statement;\nEither annotate this `if` with `returns` clause; or rewrite your code to use a tail conditional")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun post
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Pulse_Checker_If.check
                                                                    g1 pre ()
                                                                    post
                                                                    res_ppname
                                                                    b e1 e2
                                                                    check in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___11)
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
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, t1,
                                                                    pre',
                                                                    g11, k)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, t1,
                                                                    pre',
                                                                    g11, k)))))
                                                                    uu___11)))
                                                                  | Pulse_Syntax_Base.Tm_While
                                                                    uu___10
                                                                    ->
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
                                                                    =
                                                                    post_match;
                                                                    Pulse_Syntax_Base.brs
                                                                    = brs;_}
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___10
                                                                    =
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
                                                                    uu___11
                                                                    -> p)))
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
                                                                    (let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    p in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    q.Pulse_Typing.post in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (282))
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
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Multiple annotated postconditions---remove one of them.\nThe context expects the postcondition "
                                                                    (Prims.strcat
                                                                    uu___16
                                                                    ",\nbut this conditional was annotated with postcondition "))
                                                                    (Prims.strcat
                                                                    x ""))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    uu___15
                                                                    uu___13))))
                                                                    uu___13) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    uu___12))
                                                                    uu___12)))
                                                                    | 
                                                                    (uu___11,
                                                                    uu___12)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    "Pulse cannot yet infer a postcondition for a non-tail conditional statement;\nEither annotate this `if` with `returns` clause; or rewrite your code to use a tail conditional")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun post
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Pulse_Checker_Match.check
                                                                    g1 pre ()
                                                                    post
                                                                    res_ppname
                                                                    sc brs
                                                                    check in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    uu___11)
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
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, ty,
                                                                    pre',
                                                                    g11, k)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, ty,
                                                                    pre',
                                                                    g11, k)))))
                                                                    uu___11)))
                                                                  | Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Checker_AssertWithBinders.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t check))
                                                                  | Pulse_Syntax_Base.Tm_WithLocal
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Checker_WithLocal.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t check))
                                                                  | Pulse_Syntax_Base.Tm_WithLocalArray
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Checker_WithLocalArray.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t check))
                                                                  | Pulse_Syntax_Base.Tm_Par
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Checker_Par.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t check))
                                                                  | Pulse_Syntax_Base.Tm_IntroPure
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Checker_IntroPure.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t))
                                                                  | Pulse_Syntax_Base.Tm_Admit
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Checker_Admit.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t))
                                                                  | Pulse_Syntax_Base.Tm_Unreachable
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Checker_Unreachable.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t))
                                                                  | Pulse_Syntax_Base.Tm_Rewrite
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Checker_Rewrite.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t))
                                                                  | Pulse_Syntax_Base.Tm_WithInv
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Checker_WithInv.check
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t check))
                                                                  | uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Checker form not implemented")))
                                                                 uu___10) in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (50)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (52)))))
                                                             (Obj.magic
                                                                uu___8)
                                                             (fun r ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___9
                                                                    ->
                                                                    match r
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, g1,
                                                                    t1, pre',
                                                                    k) ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, g1,
                                                                    t1, pre',
                                                                    (Pulse_Checker_Base.k_elab_trans
                                                                    g0 g g1
                                                                    pre0 pre
                                                                    (FStar_Pervasives.dfst
                                                                    pre')
                                                                    k_elim_pure
                                                                    k))))))
                                                       uu___7))) uu___5)))
                             uu___3)))