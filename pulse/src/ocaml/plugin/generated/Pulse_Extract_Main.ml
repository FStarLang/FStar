open Prims
type name = (Pulse_Syntax_Base.ppname * Prims.nat)
let (debug :
  Pulse_Typing_Env.env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun f ->
           if
             Pulse_RuntimeUtils.debug_at_level (Pulse_Typing_Env.fstar_env g)
               "pulse_extraction"
           then
             Obj.magic
               (Obj.repr
                  (let uu___ = f () in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (44)) (Prims.of_int (17))
                              (Prims.of_int (44)) (Prims.of_int (22)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (44)) (Prims.of_int (9))
                              (Prims.of_int (44)) (Prims.of_int (22)))))
                     (Obj.magic uu___)
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStarC_Tactics_V2_Builtins.print uu___1))
                          uu___1)))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
        uu___1 uu___
let (extend_env' :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.ppname ->
      Pulse_Syntax_Base.typ ->
        ((Pulse_Typing_Env.env * Pulse_Syntax_Base.nvar), unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun ppname ->
             fun ty ->
               Obj.magic
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       let x = Pulse_Typing_Env.fresh g in
                       ((Pulse_Typing_Env.push_binding g x ppname ty),
                         (ppname, x))))) uu___2 uu___1 uu___
let (extend_env'_binder :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.binder ->
      ((Pulse_Typing_Env.env * Pulse_Syntax_Base.nvar), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun b ->
      extend_env' g b.Pulse_Syntax_Base.binder_ppname
        b.Pulse_Syntax_Base.binder_ty
let rec (extend_env'_pattern :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.pattern ->
      ((Pulse_Typing_Env.env * Pulse_Typing_Env.binding Prims.list), 
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun p ->
           match p with
           | Pulse_Syntax_Base.Pat_Cons (fv, pats) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       extend_env'_patterns g
                         (FStar_List_Tot_Base.map FStar_Pervasives_Native.fst
                            pats) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (61)) (Prims.of_int (16))
                                (Prims.of_int (61)) (Prims.of_int (62)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (60)) (Prims.of_int (23))
                                (Prims.of_int (62)) (Prims.of_int (9)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               match uu___1 with | (g1, bs) -> (g1, bs)))))
           | Pulse_Syntax_Base.Pat_Constant c ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> (g, []))))
           | Pulse_Syntax_Base.Pat_Var (ppname, sort) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = FStarC_Tactics_Unseal.unseal sort in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (66)) (Prims.of_int (13))
                                (Prims.of_int (66)) (Prims.of_int (26)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (66)) (Prims.of_int (29))
                                (Prims.of_int (68)) (Prims.of_int (14)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun ty ->
                             let uu___1 =
                               extend_env' g
                                 (Pulse_Syntax_Base.mk_ppname ppname
                                    FStar_Range.range_0) ty in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (67))
                                           (Prims.of_int (20))
                                           (Prims.of_int (67))
                                           (Prims.of_int (69)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (66))
                                           (Prims.of_int (29))
                                           (Prims.of_int (68))
                                           (Prims.of_int (14)))))
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___3 ->
                                          match uu___2 with
                                          | (g1, (uu___4, x)) ->
                                              (g1, [(x, ty)]))))) uu___1)))
           | Pulse_Syntax_Base.Pat_Dot_Term t ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> (g, [])))))
        uu___1 uu___
and (extend_env'_patterns :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.pattern Prims.list ->
      ((Pulse_Typing_Env.env * Pulse_Typing_Env.binding Prims.list), 
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun ps ->
           match ps with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> (g, []))))
           | p::ps1 ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = extend_env'_pattern g p in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (76)) (Prims.of_int (16))
                                (Prims.of_int (76)) (Prims.of_int (39)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (75)) (Prims.of_int (12))
                                (Prims.of_int (78)) (Prims.of_int (13)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             match uu___1 with
                             | (g1, bs) ->
                                 let uu___2 = extend_env'_patterns g1 ps1 in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (77))
                                               (Prims.of_int (17))
                                               (Prims.of_int (77))
                                               (Prims.of_int (42)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (76))
                                               (Prims.of_int (42))
                                               (Prims.of_int (78))
                                               (Prims.of_int (13)))))
                                      (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 ->
                                              match uu___3 with
                                              | (g2, bs') ->
                                                  (g2,
                                                    (FStar_List_Tot_Base.op_At
                                                       bs bs')))))) uu___1))))
        uu___1 uu___
let (is_erasable :
  Pulse_Syntax_Base.st_term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun p ->
    let uu___ = FStarC_Tactics_Unseal.unseal p.Pulse_Syntax_Base.effect_tag in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (81)) (Prims.of_int (12)) (Prims.of_int (81))
               (Prims.of_int (33)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (82)) (Prims.of_int (2)) (Prims.of_int (84))
               (Prims.of_int (14))))) (Obj.magic uu___)
      (fun tag ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              match tag with
              | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.STT_Ghost) ->
                  true
              | uu___2 -> false))
let (head_and_args :
  Pulse_Syntax_Base.term ->
    (FStarC_Reflection_Types.term * FStarC_Reflection_V2_Data.argv
      Prims.list) FStar_Pervasives_Native.option)
  =
  fun t ->
    FStar_Pervasives_Native.Some
      (FStar_Reflection_V2_Collect.collect_app_ln t)
let (term_eq_string :
  Prims.string -> FStarC_Reflection_Types.term -> Prims.bool) =
  fun s ->
    fun t ->
      match FStarC_Reflection_V2_Builtins.inspect_ln t with
      | FStarC_Reflection_V2_Data.Tv_Const
          (FStarC_Reflection_V2_Data.C_String s') -> s = s'
      | uu___ -> false
let (push_binding :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.var -> Pulse_Syntax_Base.binder -> Pulse_Typing_Env.env)
  =
  fun g ->
    fun x ->
      fun b ->
        Pulse_Typing_Env.push_binding g x b.Pulse_Syntax_Base.binder_ppname
          b.Pulse_Syntax_Base.binder_ty
let (with_open :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.binder ->
      Pulse_Syntax_Base.st_term ->
        (Pulse_Typing_Env.env ->
           Pulse_Syntax_Base.st_term ->
             (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
          -> (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun b ->
      fun e ->
        fun f ->
          let uu___ =
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 -> Pulse_Typing_Env.fresh g)) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                     (Prims.of_int (101)) (Prims.of_int (10))
                     (Prims.of_int (101)) (Prims.of_int (17)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                     (Prims.of_int (101)) (Prims.of_int (20))
                     (Prims.of_int (104)) (Prims.of_int (22)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun x ->
                  let uu___1 =
                    Obj.magic
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___2 ->
                            Pulse_Syntax_Naming.open_st_term' e
                              (Pulse_Syntax_Pure.tm_var
                                 {
                                   Pulse_Syntax_Base.nm_index = x;
                                   Pulse_Syntax_Base.nm_ppname =
                                     (b.Pulse_Syntax_Base.binder_ppname)
                                 }) Prims.int_zero)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (102)) (Prims.of_int (10))
                                (Prims.of_int (102)) (Prims.of_int (82)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (102)) (Prims.of_int (85))
                                (Prims.of_int (104)) (Prims.of_int (22)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun e1 ->
                             let uu___2 = f (push_binding g x b) e1 in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (103))
                                           (Prims.of_int (10))
                                           (Prims.of_int (103))
                                           (Prims.of_int (34)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (104))
                                           (Prims.of_int (2))
                                           (Prims.of_int (104))
                                           (Prims.of_int (22)))))
                                  (Obj.magic uu___2)
                                  (fun e2 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___3 ->
                                          Pulse_Syntax_Naming.close_st_term'
                                            e2 x Prims.int_zero)))) uu___2)))
                 uu___1)
let (is_internal_binder :
  Pulse_Syntax_Base.binder ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    let uu___ =
      FStarC_Tactics_Unseal.unseal
        (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (107)) (Prims.of_int (10)) (Prims.of_int (107))
               (Prims.of_int (39)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (108)) (Prims.of_int (2)) (Prims.of_int (113))
               (Prims.of_int (11))))) (Obj.magic uu___)
      (fun s ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              (((((s = "_fret") || (s = "_bind_c")) || (s = "_while_c")) ||
                  (s = "_tbind_c"))
                 || (s = "_if_br"))
                || (s = "_br")))
let (is_return :
  Pulse_Syntax_Base.st_term ->
    Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun e ->
    match e.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_Return
        { Pulse_Syntax_Base.expected_type = uu___;
          Pulse_Syntax_Base.insert_eq = uu___1;
          Pulse_Syntax_Base.term = term;_}
        -> FStar_Pervasives_Native.Some term
    | uu___ -> FStar_Pervasives_Native.None
let (is_return_bv0 : Pulse_Syntax_Base.st_term -> Prims.bool) =
  fun e ->
    match is_return e with
    | FStar_Pervasives_Native.Some term ->
        (Pulse_Syntax_Pure.is_bvar term) =
          (FStar_Pervasives_Native.Some Prims.int_zero)
    | uu___ -> false
let (simplify_nested_let :
  Pulse_Syntax_Base.st_term ->
    Pulse_Syntax_Base.binder ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.st_term FStar_Pervasives_Native.option)
  =
  fun e ->
    fun b_x ->
      fun head ->
        fun e3 ->
          let mk t =
            {
              Pulse_Syntax_Base.term1 = t;
              Pulse_Syntax_Base.range1 = (e.Pulse_Syntax_Base.range1);
              Pulse_Syntax_Base.effect_tag =
                Pulse_Syntax_Base.default_effect_hint;
              Pulse_Syntax_Base.source = (FStar_Sealed.seal false)
            } in
          let body e2 =
            mk
              (Pulse_Syntax_Base.Tm_Bind
                 {
                   Pulse_Syntax_Base.binder = b_x;
                   Pulse_Syntax_Base.head1 = e2;
                   Pulse_Syntax_Base.body1 = e3
                 }) in
          match head.Pulse_Syntax_Base.term1 with
          | Pulse_Syntax_Base.Tm_TotBind
              { Pulse_Syntax_Base.binder1 = b_y;
                Pulse_Syntax_Base.head2 = e1; Pulse_Syntax_Base.body2 = e2;_}
              ->
              FStar_Pervasives_Native.Some
                (mk
                   (Pulse_Syntax_Base.Tm_TotBind
                      {
                        Pulse_Syntax_Base.binder1 = b_y;
                        Pulse_Syntax_Base.head2 = e1;
                        Pulse_Syntax_Base.body2 = (body e2)
                      }))
          | Pulse_Syntax_Base.Tm_Bind
              { Pulse_Syntax_Base.binder = b_y; Pulse_Syntax_Base.head1 = e1;
                Pulse_Syntax_Base.body1 = e2;_}
              ->
              FStar_Pervasives_Native.Some
                (mk
                   (Pulse_Syntax_Base.Tm_Bind
                      {
                        Pulse_Syntax_Base.binder = b_y;
                        Pulse_Syntax_Base.head1 = e1;
                        Pulse_Syntax_Base.body1 = (body e2)
                      }))
          | Pulse_Syntax_Base.Tm_WithLocal
              { Pulse_Syntax_Base.binder2 = b_y;
                Pulse_Syntax_Base.initializer1 = e1;
                Pulse_Syntax_Base.body4 = e2;_}
              ->
              FStar_Pervasives_Native.Some
                (mk
                   (Pulse_Syntax_Base.Tm_WithLocal
                      {
                        Pulse_Syntax_Base.binder2 = b_y;
                        Pulse_Syntax_Base.initializer1 = e1;
                        Pulse_Syntax_Base.body4 = (body e2)
                      }))
          | Pulse_Syntax_Base.Tm_WithLocalArray
              { Pulse_Syntax_Base.binder3 = b_y;
                Pulse_Syntax_Base.initializer2 = e1;
                Pulse_Syntax_Base.length = length;
                Pulse_Syntax_Base.body5 = e2;_}
              ->
              FStar_Pervasives_Native.Some
                (mk
                   (Pulse_Syntax_Base.Tm_WithLocalArray
                      {
                        Pulse_Syntax_Base.binder3 = b_y;
                        Pulse_Syntax_Base.initializer2 = e1;
                        Pulse_Syntax_Base.length = length;
                        Pulse_Syntax_Base.body5 = (body e2)
                      }))
          | uu___ -> FStar_Pervasives_Native.None
let rec (simplify_st_term :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                fun t ->
                  {
                    Pulse_Syntax_Base.term1 = t;
                    Pulse_Syntax_Base.range1 = (e.Pulse_Syntax_Base.range1);
                    Pulse_Syntax_Base.effect_tag =
                      (e.Pulse_Syntax_Base.effect_tag);
                    Pulse_Syntax_Base.source = (e.Pulse_Syntax_Base.source)
                  })) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (155)) (Prims.of_int (16))
                 (Prims.of_int (155)) (Prims.of_int (31)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (155)) (Prims.of_int (36))
                 (Prims.of_int (217)) (Prims.of_int (25)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun ret ->
              let uu___1 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        fun b -> fun e1 -> with_open g b e1 simplify_st_term)) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (156)) (Prims.of_int (22))
                            (Prims.of_int (156)) (Prims.of_int (54)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (158)) (Prims.of_int (2))
                            (Prims.of_int (217)) (Prims.of_int (25)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun with_open1 ->
                         match e.Pulse_Syntax_Base.term1 with
                         | Pulse_Syntax_Base.Tm_Return uu___2 ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> e)))
                         | Pulse_Syntax_Base.Tm_IntroPure uu___2 ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> e)))
                         | Pulse_Syntax_Base.Tm_ElimExists uu___2 ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> e)))
                         | Pulse_Syntax_Base.Tm_IntroExists uu___2 ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> e)))
                         | Pulse_Syntax_Base.Tm_STApp uu___2 ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> e)))
                         | Pulse_Syntax_Base.Tm_Rewrite uu___2 ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> e)))
                         | Pulse_Syntax_Base.Tm_Admit uu___2 ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> e)))
                         | Pulse_Syntax_Base.Tm_ProofHintWithBinders uu___2
                             ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> e)))
                         | Pulse_Syntax_Base.Tm_Abs
                             { Pulse_Syntax_Base.b = b;
                               Pulse_Syntax_Base.q = q;
                               Pulse_Syntax_Base.ascription = ascription;
                               Pulse_Syntax_Base.body = body;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (let uu___2 =
                                     let uu___3 =
                                       let uu___4 = with_open1 b body in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (169))
                                                  (Prims.of_int (43))
                                                  (Prims.of_int (169))
                                                  (Prims.of_int (59)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (169))
                                                  (Prims.of_int (18))
                                                  (Prims.of_int (169))
                                                  (Prims.of_int (59)))))
                                         (Obj.magic uu___4)
                                         (fun uu___5 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___6 ->
                                                 {
                                                   Pulse_Syntax_Base.b = b;
                                                   Pulse_Syntax_Base.q = q;
                                                   Pulse_Syntax_Base.ascription
                                                     = ascription;
                                                   Pulse_Syntax_Base.body =
                                                     uu___5
                                                 })) in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (169))
                                                (Prims.of_int (18))
                                                (Prims.of_int (169))
                                                (Prims.of_int (59)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (169))
                                                (Prims.of_int (8))
                                                (Prims.of_int (169))
                                                (Prims.of_int (62)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___5 ->
                                               Pulse_Syntax_Base.Tm_Abs
                                                 uu___4)) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (169))
                                              (Prims.of_int (8))
                                              (Prims.of_int (169))
                                              (Prims.of_int (62)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (169))
                                              (Prims.of_int (4))
                                              (Prims.of_int (169))
                                              (Prims.of_int (62)))))
                                     (Obj.magic uu___2)
                                     (fun uu___3 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___4 -> ret uu___3))))
                         | Pulse_Syntax_Base.Tm_Bind
                             { Pulse_Syntax_Base.binder = binder;
                               Pulse_Syntax_Base.head1 = head;
                               Pulse_Syntax_Base.body1 = body;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (let uu___2 = is_internal_binder binder in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (172))
                                              (Prims.of_int (29))
                                              (Prims.of_int (172))
                                              (Prims.of_int (54)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (173))
                                              (Prims.of_int (4))
                                              (Prims.of_int (187))
                                              (Prims.of_int (7)))))
                                     (Obj.magic uu___2)
                                     (fun uu___3 ->
                                        (fun is_internal_binder1 ->
                                           if
                                             is_internal_binder1 &&
                                               (is_return_bv0 body)
                                           then
                                             Obj.magic
                                               (simplify_st_term g head)
                                           else
                                             if
                                               is_internal_binder1 &&
                                                 (FStar_Pervasives_Native.uu___is_Some
                                                    (is_return head))
                                             then
                                               (let uu___4 =
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___5 ->
                                                          is_return head)) in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (178))
                                                              (Prims.of_int (25))
                                                              (Prims.of_int (178))
                                                              (Prims.of_int (39)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (178))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (179))
                                                              (Prims.of_int (66)))))
                                                     (Obj.magic uu___4)
                                                     (fun uu___5 ->
                                                        (fun uu___5 ->
                                                           match uu___5 with
                                                           | FStar_Pervasives_Native.Some
                                                               head1 ->
                                                               Obj.magic
                                                                 (simplify_st_term
                                                                    g
                                                                    (
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    [
                                                                    FStar_Reflection_Typing.DT
                                                                    (Prims.int_zero,
                                                                    head1)])))
                                                          uu___5)))
                                             else
                                               (match simplify_nested_let e
                                                        binder head body
                                                with
                                                | FStar_Pervasives_Native.Some
                                                    e1 ->
                                                    Obj.magic
                                                      (simplify_st_term g e1)
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    let uu___5 =
                                                      simplify_st_term g head in
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (184))
                                                                  (Prims.of_int (19))
                                                                  (Prims.of_int (184))
                                                                  (Prims.of_int (42)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (184))
                                                                  (Prims.of_int (45))
                                                                  (Prims.of_int (186))
                                                                  (Prims.of_int (44)))))
                                                         (Obj.magic uu___5)
                                                         (fun uu___6 ->
                                                            (fun head1 ->
                                                               let uu___6 =
                                                                 with_open1
                                                                   binder
                                                                   body in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (40)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (44)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___6)
                                                                    (
                                                                    fun body1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = binder;
                                                                    Pulse_Syntax_Base.head1
                                                                    = head1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = body1
                                                                    })))))
                                                              uu___6))))
                                          uu___3)))
                         | Pulse_Syntax_Base.Tm_TotBind
                             { Pulse_Syntax_Base.binder1 = binder;
                               Pulse_Syntax_Base.head2 = head;
                               Pulse_Syntax_Base.body2 = body;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (let uu___2 =
                                     let uu___3 =
                                       let uu___4 = with_open1 binder body in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (190))
                                                  (Prims.of_int (43))
                                                  (Prims.of_int (190))
                                                  (Prims.of_int (64)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (190))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (190))
                                                  (Prims.of_int (64)))))
                                         (Obj.magic uu___4)
                                         (fun uu___5 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___6 ->
                                                 {
                                                   Pulse_Syntax_Base.binder1
                                                     = binder;
                                                   Pulse_Syntax_Base.head2 =
                                                     head;
                                                   Pulse_Syntax_Base.body2 =
                                                     uu___5
                                                 })) in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (190))
                                                (Prims.of_int (22))
                                                (Prims.of_int (190))
                                                (Prims.of_int (64)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (190))
                                                (Prims.of_int (8))
                                                (Prims.of_int (190))
                                                (Prims.of_int (67)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___5 ->
                                               Pulse_Syntax_Base.Tm_TotBind
                                                 uu___4)) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (190))
                                              (Prims.of_int (8))
                                              (Prims.of_int (190))
                                              (Prims.of_int (67)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (190))
                                              (Prims.of_int (4))
                                              (Prims.of_int (190))
                                              (Prims.of_int (67)))))
                                     (Obj.magic uu___2)
                                     (fun uu___3 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___4 -> ret uu___3))))
                         | Pulse_Syntax_Base.Tm_If
                             { Pulse_Syntax_Base.b1 = b;
                               Pulse_Syntax_Base.then_ = then_;
                               Pulse_Syntax_Base.else_ = else_;
                               Pulse_Syntax_Base.post1 = post;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (let uu___2 =
                                     let uu___3 =
                                       let uu___4 = simplify_st_term g then_ in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (193))
                                                  (Prims.of_int (28))
                                                  (Prims.of_int (193))
                                                  (Prims.of_int (52)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (193))
                                                  (Prims.of_int (17))
                                                  (Prims.of_int (193))
                                                  (Prims.of_int (92)))))
                                         (Obj.magic uu___4)
                                         (fun uu___5 ->
                                            (fun uu___5 ->
                                               let uu___6 =
                                                 simplify_st_term g else_ in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (193))
                                                             (Prims.of_int (62))
                                                             (Prims.of_int (193))
                                                             (Prims.of_int (86)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (193))
                                                             (Prims.of_int (17))
                                                             (Prims.of_int (193))
                                                             (Prims.of_int (92)))))
                                                    (Obj.magic uu___6)
                                                    (fun uu___7 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___8 ->
                                                            {
                                                              Pulse_Syntax_Base.b1
                                                                = b;
                                                              Pulse_Syntax_Base.then_
                                                                = uu___5;
                                                              Pulse_Syntax_Base.else_
                                                                = uu___7;
                                                              Pulse_Syntax_Base.post1
                                                                = post
                                                            })))) uu___5) in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (193))
                                                (Prims.of_int (17))
                                                (Prims.of_int (193))
                                                (Prims.of_int (92)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (193))
                                                (Prims.of_int (8))
                                                (Prims.of_int (193))
                                                (Prims.of_int (95)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___5 ->
                                               Pulse_Syntax_Base.Tm_If uu___4)) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (193))
                                              (Prims.of_int (8))
                                              (Prims.of_int (193))
                                              (Prims.of_int (95)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (193))
                                              (Prims.of_int (4))
                                              (Prims.of_int (193))
                                              (Prims.of_int (95)))))
                                     (Obj.magic uu___2)
                                     (fun uu___3 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___4 -> ret uu___3))))
                         | Pulse_Syntax_Base.Tm_Match
                             { Pulse_Syntax_Base.sc = sc;
                               Pulse_Syntax_Base.returns_ = returns_;
                               Pulse_Syntax_Base.brs = brs;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (let uu___2 =
                                     let uu___3 =
                                       let uu___4 =
                                         FStar_Tactics_Util.map
                                           (simplify_branch g) brs in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (196))
                                                  (Prims.of_int (40))
                                                  (Prims.of_int (196))
                                                  (Prims.of_int (69)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (196))
                                                  (Prims.of_int (20))
                                                  (Prims.of_int (196))
                                                  (Prims.of_int (69)))))
                                         (Obj.magic uu___4)
                                         (fun uu___5 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___6 ->
                                                 {
                                                   Pulse_Syntax_Base.sc = sc;
                                                   Pulse_Syntax_Base.returns_
                                                     = returns_;
                                                   Pulse_Syntax_Base.brs =
                                                     uu___5
                                                 })) in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (196))
                                                (Prims.of_int (20))
                                                (Prims.of_int (196))
                                                (Prims.of_int (69)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (196))
                                                (Prims.of_int (8))
                                                (Prims.of_int (196))
                                                (Prims.of_int (72)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___5 ->
                                               Pulse_Syntax_Base.Tm_Match
                                                 uu___4)) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (196))
                                              (Prims.of_int (8))
                                              (Prims.of_int (196))
                                              (Prims.of_int (72)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (196))
                                              (Prims.of_int (4))
                                              (Prims.of_int (196))
                                              (Prims.of_int (72)))))
                                     (Obj.magic uu___2)
                                     (fun uu___3 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___4 -> ret uu___3))))
                         | Pulse_Syntax_Base.Tm_While
                             { Pulse_Syntax_Base.invariant = invariant;
                               Pulse_Syntax_Base.condition = condition;
                               Pulse_Syntax_Base.condition_var =
                                 condition_var;
                               Pulse_Syntax_Base.body3 = body;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (let uu___2 = simplify_st_term g condition in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (199))
                                              (Prims.of_int (20))
                                              (Prims.of_int (199))
                                              (Prims.of_int (48)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (199))
                                              (Prims.of_int (51))
                                              (Prims.of_int (201))
                                              (Prims.of_int (76)))))
                                     (Obj.magic uu___2)
                                     (fun uu___3 ->
                                        (fun condition1 ->
                                           let uu___3 =
                                             simplify_st_term g body in
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (200))
                                                         (Prims.of_int (15))
                                                         (Prims.of_int (200))
                                                         (Prims.of_int (38)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (201))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (201))
                                                         (Prims.of_int (74)))))
                                                (Obj.magic uu___3)
                                                (fun body1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        {
                                                          Pulse_Syntax_Base.term1
                                                            =
                                                            (Pulse_Syntax_Base.Tm_While
                                                               {
                                                                 Pulse_Syntax_Base.invariant
                                                                   =
                                                                   invariant;
                                                                 Pulse_Syntax_Base.condition
                                                                   =
                                                                   condition1;
                                                                 Pulse_Syntax_Base.condition_var
                                                                   =
                                                                   condition_var;
                                                                 Pulse_Syntax_Base.body3
                                                                   = body1
                                                               });
                                                          Pulse_Syntax_Base.range1
                                                            =
                                                            (e.Pulse_Syntax_Base.range1);
                                                          Pulse_Syntax_Base.effect_tag
                                                            =
                                                            (e.Pulse_Syntax_Base.effect_tag);
                                                          Pulse_Syntax_Base.source
                                                            =
                                                            (e.Pulse_Syntax_Base.source)
                                                        })))) uu___3)))
                         | Pulse_Syntax_Base.Tm_Par
                             { Pulse_Syntax_Base.pre1 = pre1;
                               Pulse_Syntax_Base.body11 = body1;
                               Pulse_Syntax_Base.post11 = post1;
                               Pulse_Syntax_Base.pre2 = pre2;
                               Pulse_Syntax_Base.body21 = body2;
                               Pulse_Syntax_Base.post2 = post2;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (let uu___2 = simplify_st_term g body1 in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (204))
                                              (Prims.of_int (16))
                                              (Prims.of_int (204))
                                              (Prims.of_int (40)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (204))
                                              (Prims.of_int (43))
                                              (Prims.of_int (206))
                                              (Prims.of_int (71)))))
                                     (Obj.magic uu___2)
                                     (fun uu___3 ->
                                        (fun body11 ->
                                           let uu___3 =
                                             simplify_st_term g body2 in
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (205))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (205))
                                                         (Prims.of_int (40)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (206))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (206))
                                                         (Prims.of_int (69)))))
                                                (Obj.magic uu___3)
                                                (fun body21 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        {
                                                          Pulse_Syntax_Base.term1
                                                            =
                                                            (Pulse_Syntax_Base.Tm_Par
                                                               {
                                                                 Pulse_Syntax_Base.pre1
                                                                   = pre1;
                                                                 Pulse_Syntax_Base.body11
                                                                   = body11;
                                                                 Pulse_Syntax_Base.post11
                                                                   = post1;
                                                                 Pulse_Syntax_Base.pre2
                                                                   = pre2;
                                                                 Pulse_Syntax_Base.body21
                                                                   = body21;
                                                                 Pulse_Syntax_Base.post2
                                                                   = post2
                                                               });
                                                          Pulse_Syntax_Base.range1
                                                            =
                                                            (e.Pulse_Syntax_Base.range1);
                                                          Pulse_Syntax_Base.effect_tag
                                                            =
                                                            (e.Pulse_Syntax_Base.effect_tag);
                                                          Pulse_Syntax_Base.source
                                                            =
                                                            (e.Pulse_Syntax_Base.source)
                                                        })))) uu___3)))
                         | Pulse_Syntax_Base.Tm_WithLocal
                             { Pulse_Syntax_Base.binder2 = binder;
                               Pulse_Syntax_Base.initializer1 = initializer1;
                               Pulse_Syntax_Base.body4 = body;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (let uu___2 =
                                     let uu___3 =
                                       let uu___4 = with_open1 binder body in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (209))
                                                  (Prims.of_int (52))
                                                  (Prims.of_int (209))
                                                  (Prims.of_int (73)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (209))
                                                  (Prims.of_int (24))
                                                  (Prims.of_int (209))
                                                  (Prims.of_int (73)))))
                                         (Obj.magic uu___4)
                                         (fun uu___5 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___6 ->
                                                 {
                                                   Pulse_Syntax_Base.binder2
                                                     = binder;
                                                   Pulse_Syntax_Base.initializer1
                                                     = initializer1;
                                                   Pulse_Syntax_Base.body4 =
                                                     uu___5
                                                 })) in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (209))
                                                (Prims.of_int (24))
                                                (Prims.of_int (209))
                                                (Prims.of_int (73)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (209))
                                                (Prims.of_int (8))
                                                (Prims.of_int (209))
                                                (Prims.of_int (76)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___5 ->
                                               Pulse_Syntax_Base.Tm_WithLocal
                                                 uu___4)) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (209))
                                              (Prims.of_int (8))
                                              (Prims.of_int (209))
                                              (Prims.of_int (76)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (209))
                                              (Prims.of_int (4))
                                              (Prims.of_int (209))
                                              (Prims.of_int (76)))))
                                     (Obj.magic uu___2)
                                     (fun uu___3 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___4 -> ret uu___3))))
                         | Pulse_Syntax_Base.Tm_WithLocalArray
                             { Pulse_Syntax_Base.binder3 = binder;
                               Pulse_Syntax_Base.initializer2 = initializer1;
                               Pulse_Syntax_Base.length = length;
                               Pulse_Syntax_Base.body5 = body;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (let uu___2 =
                                     let uu___3 =
                                       let uu___4 = with_open1 binder body in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (212))
                                                  (Prims.of_int (65))
                                                  (Prims.of_int (212))
                                                  (Prims.of_int (86)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (212))
                                                  (Prims.of_int (29))
                                                  (Prims.of_int (212))
                                                  (Prims.of_int (86)))))
                                         (Obj.magic uu___4)
                                         (fun uu___5 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___6 ->
                                                 {
                                                   Pulse_Syntax_Base.binder3
                                                     = binder;
                                                   Pulse_Syntax_Base.initializer2
                                                     = initializer1;
                                                   Pulse_Syntax_Base.length =
                                                     length;
                                                   Pulse_Syntax_Base.body5 =
                                                     uu___5
                                                 })) in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (212))
                                                (Prims.of_int (29))
                                                (Prims.of_int (212))
                                                (Prims.of_int (86)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (212))
                                                (Prims.of_int (8))
                                                (Prims.of_int (212))
                                                (Prims.of_int (89)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___5 ->
                                               Pulse_Syntax_Base.Tm_WithLocalArray
                                                 uu___4)) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (212))
                                              (Prims.of_int (8))
                                              (Prims.of_int (212))
                                              (Prims.of_int (89)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (212))
                                              (Prims.of_int (4))
                                              (Prims.of_int (212))
                                              (Prims.of_int (89)))))
                                     (Obj.magic uu___2)
                                     (fun uu___3 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___4 -> ret uu___3))))
                         | Pulse_Syntax_Base.Tm_WithInv
                             { Pulse_Syntax_Base.name1 = uu___2;
                               Pulse_Syntax_Base.body6 = body;
                               Pulse_Syntax_Base.returns_inv = uu___3;_}
                             ->
                             Obj.magic (Obj.repr (simplify_st_term g body))
                         | Pulse_Syntax_Base.Tm_Unreachable uu___2 ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> e)))) uu___2))) uu___1)
and (simplify_branch :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.branch ->
      (Pulse_Syntax_Base.branch, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun b ->
      let uu___ =
        Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> b)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (220)) (Prims.of_int (18))
                 (Prims.of_int (220)) (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (219)) (Prims.of_int (55))
                 (Prims.of_int (224)) (Prims.of_int (62)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | (pat, body) ->
                  let uu___2 = extend_env'_pattern g pat in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (221)) (Prims.of_int (14))
                                (Prims.of_int (221)) (Prims.of_int (39)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (220)) (Prims.of_int (22))
                                (Prims.of_int (224)) (Prims.of_int (62)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          (fun uu___3 ->
                             match uu___3 with
                             | (g1, bs) ->
                                 let uu___4 =
                                   Obj.magic
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___5 ->
                                           Pulse_Checker_Match.open_st_term_bs
                                             body bs)) in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (222))
                                               (Prims.of_int (13))
                                               (Prims.of_int (222))
                                               (Prims.of_int (56)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (222))
                                               (Prims.of_int (59))
                                               (Prims.of_int (224))
                                               (Prims.of_int (62)))))
                                      (Obj.magic uu___4)
                                      (fun uu___5 ->
                                         (fun body1 ->
                                            let uu___5 =
                                              simplify_st_term g1 body1 in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (223))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (223))
                                                          (Prims.of_int (36)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (224))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (224))
                                                          (Prims.of_int (62)))))
                                                 (Obj.magic uu___5)
                                                 (fun body2 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___6 ->
                                                         (pat,
                                                           (Pulse_Syntax_Naming.close_st_term_n
                                                              body2
                                                              (FStar_List_Tot_Base.map
                                                                 FStar_Pervasives_Native.fst
                                                                 bs)))))))
                                           uu___5))) uu___3))) uu___1)
let (erase_type_for_extraction :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun t ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   Pulse_RuntimeUtils.must_erase_for_extraction
                     (Pulse_Typing_Env.fstar_env g) t))) uu___1 uu___
let rec (erase_ghost_subterms :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                fun g1 ->
                  fun x ->
                    fun b ->
                      Pulse_Typing_Env.push_binding g1 x
                        b.Pulse_Syntax_Base.binder_ppname
                        b.Pulse_Syntax_Base.binder_ty)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (233)) (Prims.of_int (4)) (Prims.of_int (233))
                 (Prims.of_int (50)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (233)) (Prims.of_int (53))
                 (Prims.of_int (314)) (Prims.of_int (5))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun push_binding1 ->
              let uu___1 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        fun g1 ->
                          fun b ->
                            fun e ->
                              let uu___3 =
                                Obj.magic
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___4 -> Pulse_Typing_Env.fresh g1)) in
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Extract.Main.fst"
                                         (Prims.of_int (236))
                                         (Prims.of_int (12))
                                         (Prims.of_int (236))
                                         (Prims.of_int (19)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Extract.Main.fst"
                                         (Prims.of_int (236))
                                         (Prims.of_int (22))
                                         (Prims.of_int (239))
                                         (Prims.of_int (24)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   (fun x ->
                                      let uu___4 =
                                        Obj.magic
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___5 ->
                                                Pulse_Syntax_Naming.open_st_term'
                                                  e
                                                  (Pulse_Syntax_Pure.tm_var
                                                     {
                                                       Pulse_Syntax_Base.nm_index
                                                         = x;
                                                       Pulse_Syntax_Base.nm_ppname
                                                         =
                                                         (b.Pulse_Syntax_Base.binder_ppname)
                                                     }) Prims.int_zero)) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (237))
                                                    (Prims.of_int (12))
                                                    (Prims.of_int (237))
                                                    (Prims.of_int (84)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (237))
                                                    (Prims.of_int (87))
                                                    (Prims.of_int (239))
                                                    (Prims.of_int (24)))))
                                           (Obj.magic uu___4)
                                           (fun uu___5 ->
                                              (fun e1 ->
                                                 let uu___5 =
                                                   erase_ghost_subterms
                                                     (push_binding1 g1 x b)
                                                     e1 in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (238))
                                                               (Prims.of_int (12))
                                                               (Prims.of_int (238))
                                                               (Prims.of_int (55)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (239))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (239))
                                                               (Prims.of_int (24)))))
                                                      (Obj.magic uu___5)
                                                      (fun e2 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___6 ->
                                                              Pulse_Syntax_Naming.close_st_term'
                                                                e2 x
                                                                Prims.int_zero))))
                                                uu___5))) uu___4))) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (235)) (Prims.of_int (71))
                            (Prims.of_int (239)) (Prims.of_int (24)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (239)) (Prims.of_int (27))
                            (Prims.of_int (314)) (Prims.of_int (5)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun open_erase_close ->
                         let uu___2 =
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___3 ->
                                   {
                                     Pulse_Syntax_Base.term1 =
                                       (Pulse_Syntax_Base.Tm_Return
                                          {
                                            Pulse_Syntax_Base.expected_type =
                                              Pulse_Syntax_Pure.tm_unknown;
                                            Pulse_Syntax_Base.insert_eq =
                                              false;
                                            Pulse_Syntax_Base.term =
                                              Pulse_Extract_CompilerLib.unit_tm
                                          });
                                     Pulse_Syntax_Base.range1 =
                                       (p.Pulse_Syntax_Base.range1);
                                     Pulse_Syntax_Base.effect_tag =
                                       (p.Pulse_Syntax_Base.effect_tag);
                                     Pulse_Syntax_Base.source =
                                       (p.Pulse_Syntax_Base.source)
                                   })) in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (242))
                                       (Prims.of_int (6))
                                       (Prims.of_int (242))
                                       (Prims.of_int (97)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (243))
                                       (Prims.of_int (4))
                                       (Prims.of_int (314))
                                       (Prims.of_int (5)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 (fun unit_tm ->
                                    let uu___3 =
                                      Obj.magic
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 ->
                                              fun t ->
                                                {
                                                  Pulse_Syntax_Base.term1 = t;
                                                  Pulse_Syntax_Base.range1 =
                                                    (p.Pulse_Syntax_Base.range1);
                                                  Pulse_Syntax_Base.effect_tag
                                                    =
                                                    (p.Pulse_Syntax_Base.effect_tag);
                                                  Pulse_Syntax_Base.source =
                                                    (p.Pulse_Syntax_Base.source)
                                                })) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (244))
                                                  (Prims.of_int (27))
                                                  (Prims.of_int (244))
                                                  (Prims.of_int (42)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (245))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (314))
                                                  (Prims.of_int (5)))))
                                         (Obj.magic uu___3)
                                         (fun uu___4 ->
                                            (fun ret ->
                                               let uu___4 = is_erasable p in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (245))
                                                             (Prims.of_int (5))
                                                             (Prims.of_int (245))
                                                             (Prims.of_int (18)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (245))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (314))
                                                             (Prims.of_int (5)))))
                                                    (Obj.magic uu___4)
                                                    (fun uu___5 ->
                                                       (fun uu___5 ->
                                                          if uu___5
                                                          then
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___6 ->
                                                                    unit_tm)))
                                                          else
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (match 
                                                                    p.Pulse_Syntax_Base.term1
                                                                  with
                                                                  | Pulse_Syntax_Base.Tm_IntroPure
                                                                    uu___7 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    unit_tm))
                                                                  | Pulse_Syntax_Base.Tm_ElimExists
                                                                    uu___7 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    unit_tm))
                                                                  | Pulse_Syntax_Base.Tm_IntroExists
                                                                    uu___7 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    unit_tm))
                                                                  | Pulse_Syntax_Base.Tm_Rewrite
                                                                    uu___7 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    unit_tm))
                                                                  | Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    = b;
                                                                    Pulse_Syntax_Base.q
                                                                    = q;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    ascription;
                                                                    Pulse_Syntax_Base.body
                                                                    = body;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    open_erase_close
                                                                    g b body in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ret
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
                                                                    = body1
                                                                    }))))
                                                                  | Pulse_Syntax_Base.Tm_Return
                                                                    uu___7 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    p))
                                                                  | Pulse_Syntax_Base.Tm_STApp
                                                                    uu___7 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    p))
                                                                  | Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = binder;
                                                                    Pulse_Syntax_Base.head1
                                                                    = head;
                                                                    Pulse_Syntax_Base.body1
                                                                    = body;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    is_erasable
                                                                    head in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    if uu___8
                                                                    then
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    [
                                                                    FStar_Reflection_Typing.DT
                                                                    (Prims.int_zero,
                                                                    Pulse_Extract_CompilerLib.unit_tm)])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g body1))
                                                                    uu___10))
                                                                    else
                                                                    (let uu___10
                                                                    =
                                                                    erase_ghost_subterms
                                                                    g head in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    head1 ->
                                                                    let uu___11
                                                                    =
                                                                    open_erase_close
                                                                    g binder
                                                                    body in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = binder;
                                                                    Pulse_Syntax_Base.head1
                                                                    = head1;
                                                                    Pulse_Syntax_Base.body1
                                                                    = body1
                                                                    })))))
                                                                    uu___11))))
                                                                    uu___8))
                                                                  | Pulse_Syntax_Base.Tm_TotBind
                                                                    {
                                                                    Pulse_Syntax_Base.binder1
                                                                    = binder;
                                                                    Pulse_Syntax_Base.head2
                                                                    = head;
                                                                    Pulse_Syntax_Base.body2
                                                                    = body;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    erase_type_for_extraction
                                                                    g
                                                                    binder.Pulse_Syntax_Base.binder_ty in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    if uu___8
                                                                    then
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    [
                                                                    FStar_Reflection_Typing.DT
                                                                    (Prims.int_zero,
                                                                    Pulse_Extract_CompilerLib.unit_tm)])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g body1))
                                                                    uu___10))
                                                                    else
                                                                    (let uu___10
                                                                    =
                                                                    open_erase_close
                                                                    g binder
                                                                    body in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_TotBind
                                                                    {
                                                                    Pulse_Syntax_Base.binder1
                                                                    = binder;
                                                                    Pulse_Syntax_Base.head2
                                                                    = head;
                                                                    Pulse_Syntax_Base.body2
                                                                    = body1
                                                                    }))))))
                                                                    uu___8))
                                                                  | Pulse_Syntax_Base.Tm_If
                                                                    {
                                                                    Pulse_Syntax_Base.b1
                                                                    = b;
                                                                    Pulse_Syntax_Base.then_
                                                                    = then_;
                                                                    Pulse_Syntax_Base.else_
                                                                    = else_;
                                                                    Pulse_Syntax_Base.post1
                                                                    = post;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    erase_ghost_subterms
                                                                    g then_ in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    then_1 ->
                                                                    let uu___8
                                                                    =
                                                                    erase_ghost_subterms
                                                                    g else_ in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    else_1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_If
                                                                    {
                                                                    Pulse_Syntax_Base.b1
                                                                    = b;
                                                                    Pulse_Syntax_Base.then_
                                                                    = then_1;
                                                                    Pulse_Syntax_Base.else_
                                                                    = else_1;
                                                                    Pulse_Syntax_Base.post1
                                                                    = post
                                                                    })))))
                                                                    uu___8))
                                                                  | Pulse_Syntax_Base.Tm_Match
                                                                    {
                                                                    Pulse_Syntax_Base.sc
                                                                    = sc;
                                                                    Pulse_Syntax_Base.returns_
                                                                    =
                                                                    returns_;
                                                                    Pulse_Syntax_Base.brs
                                                                    = brs;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    FStar_Tactics_Util.map
                                                                    (erase_ghost_subterms_branch
                                                                    g) brs in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun brs1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_Match
                                                                    {
                                                                    Pulse_Syntax_Base.sc
                                                                    = sc;
                                                                    Pulse_Syntax_Base.returns_
                                                                    =
                                                                    returns_;
                                                                    Pulse_Syntax_Base.brs
                                                                    = brs1
                                                                    }))))
                                                                  | Pulse_Syntax_Base.Tm_While
                                                                    {
                                                                    Pulse_Syntax_Base.invariant
                                                                    =
                                                                    invariant;
                                                                    Pulse_Syntax_Base.condition
                                                                    =
                                                                    condition;
                                                                    Pulse_Syntax_Base.condition_var
                                                                    =
                                                                    condition_var;
                                                                    Pulse_Syntax_Base.body3
                                                                    = body;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    erase_ghost_subterms
                                                                    g
                                                                    condition in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    condition1
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    erase_ghost_subterms
                                                                    g body in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_While
                                                                    {
                                                                    Pulse_Syntax_Base.invariant
                                                                    =
                                                                    invariant;
                                                                    Pulse_Syntax_Base.condition
                                                                    =
                                                                    condition1;
                                                                    Pulse_Syntax_Base.condition_var
                                                                    =
                                                                    condition_var;
                                                                    Pulse_Syntax_Base.body3
                                                                    = body1
                                                                    })))))
                                                                    uu___8))
                                                                  | Pulse_Syntax_Base.Tm_Par
                                                                    {
                                                                    Pulse_Syntax_Base.pre1
                                                                    = pre1;
                                                                    Pulse_Syntax_Base.body11
                                                                    = body1;
                                                                    Pulse_Syntax_Base.post11
                                                                    = post1;
                                                                    Pulse_Syntax_Base.pre2
                                                                    = pre2;
                                                                    Pulse_Syntax_Base.body21
                                                                    = body2;
                                                                    Pulse_Syntax_Base.post2
                                                                    = post2;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    erase_ghost_subterms
                                                                    g body1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    body11 ->
                                                                    let uu___8
                                                                    =
                                                                    erase_ghost_subterms
                                                                    g body2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    body21 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_Par
                                                                    {
                                                                    Pulse_Syntax_Base.pre1
                                                                    = pre1;
                                                                    Pulse_Syntax_Base.body11
                                                                    = body11;
                                                                    Pulse_Syntax_Base.post11
                                                                    = post1;
                                                                    Pulse_Syntax_Base.pre2
                                                                    = pre2;
                                                                    Pulse_Syntax_Base.body21
                                                                    = body21;
                                                                    Pulse_Syntax_Base.post2
                                                                    = post2
                                                                    })))))
                                                                    uu___8))
                                                                  | Pulse_Syntax_Base.Tm_WithLocal
                                                                    {
                                                                    Pulse_Syntax_Base.binder2
                                                                    = binder;
                                                                    Pulse_Syntax_Base.initializer1
                                                                    =
                                                                    initializer1;
                                                                    Pulse_Syntax_Base.body4
                                                                    = body;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    open_erase_close
                                                                    g binder
                                                                    body in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_WithLocal
                                                                    {
                                                                    Pulse_Syntax_Base.binder2
                                                                    = binder;
                                                                    Pulse_Syntax_Base.initializer1
                                                                    =
                                                                    initializer1;
                                                                    Pulse_Syntax_Base.body4
                                                                    = body1
                                                                    }))))
                                                                  | Pulse_Syntax_Base.Tm_WithLocalArray
                                                                    {
                                                                    Pulse_Syntax_Base.binder3
                                                                    = binder;
                                                                    Pulse_Syntax_Base.initializer2
                                                                    =
                                                                    initializer1;
                                                                    Pulse_Syntax_Base.length
                                                                    = length;
                                                                    Pulse_Syntax_Base.body5
                                                                    = body;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    open_erase_close
                                                                    g binder
                                                                    body in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_WithLocalArray
                                                                    {
                                                                    Pulse_Syntax_Base.binder3
                                                                    = binder;
                                                                    Pulse_Syntax_Base.initializer2
                                                                    =
                                                                    initializer1;
                                                                    Pulse_Syntax_Base.length
                                                                    = length;
                                                                    Pulse_Syntax_Base.body5
                                                                    = body1
                                                                    }))))
                                                                  | Pulse_Syntax_Base.Tm_Unreachable
                                                                    uu___7 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    p))
                                                                  | Pulse_Syntax_Base.Tm_Admit
                                                                    uu___7 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    p))
                                                                  | Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                                    uu___7 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "erase_ghost_subterms: Unexpected constructor: ProofHintWithBinders should have been desugared away")
                                                                  | Pulse_Syntax_Base.Tm_WithInv
                                                                    {
                                                                    Pulse_Syntax_Base.name1
                                                                    = name1;
                                                                    Pulse_Syntax_Base.body6
                                                                    = body;
                                                                    Pulse_Syntax_Base.returns_inv
                                                                    =
                                                                    returns_inv;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    erase_ghost_subterms
                                                                    g body in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (77)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    {
                                                                    Pulse_Syntax_Base.name1
                                                                    = name1;
                                                                    Pulse_Syntax_Base.body6
                                                                    = uu___10;
                                                                    Pulse_Syntax_Base.returns_inv
                                                                    =
                                                                    returns_inv
                                                                    })) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (80)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Syntax_Base.Tm_WithInv
                                                                    uu___9)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (80)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ret
                                                                    uu___8))))))
                                                         uu___5))) uu___4)))
                                   uu___3))) uu___2))) uu___1)
and (erase_ghost_subterms_branch :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.branch ->
      (Pulse_Syntax_Base.branch, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun b ->
      let uu___ =
        Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> b)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (317)) (Prims.of_int (18))
                 (Prims.of_int (317)) (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (316)) (Prims.of_int (67))
                 (Prims.of_int (321)) (Prims.of_int (62)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | (pat, body) ->
                  let uu___2 = extend_env'_pattern g pat in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (318)) (Prims.of_int (14))
                                (Prims.of_int (318)) (Prims.of_int (39)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (317)) (Prims.of_int (22))
                                (Prims.of_int (321)) (Prims.of_int (62)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          (fun uu___3 ->
                             match uu___3 with
                             | (g1, bs) ->
                                 let uu___4 =
                                   Obj.magic
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___5 ->
                                           Pulse_Checker_Match.open_st_term_bs
                                             body bs)) in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (319))
                                               (Prims.of_int (13))
                                               (Prims.of_int (319))
                                               (Prims.of_int (56)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (319))
                                               (Prims.of_int (59))
                                               (Prims.of_int (321))
                                               (Prims.of_int (62)))))
                                      (Obj.magic uu___4)
                                      (fun uu___5 ->
                                         (fun body1 ->
                                            let uu___5 =
                                              erase_ghost_subterms g1 body1 in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (320))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (320))
                                                          (Prims.of_int (40)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (321))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (321))
                                                          (Prims.of_int (62)))))
                                                 (Obj.magic uu___5)
                                                 (fun body2 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___6 ->
                                                         (pat,
                                                           (Pulse_Syntax_Naming.close_st_term_n
                                                              body2
                                                              (FStar_List_Tot_Base.map
                                                                 FStar_Pervasives_Native.fst
                                                                 bs)))))))
                                           uu___5))) uu___3))) uu___1)
let (extract_dv_binder :
  Pulse_Syntax_Base.binder ->
    Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option ->
      (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun q ->
      let uu___ =
        let uu___1 =
          FStarC_Tactics_Unseal.unseal b.Pulse_Syntax_Base.binder_attrs in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (328)) (Prims.of_int (12))
                   (Prims.of_int (328)) (Prims.of_int (35)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (326)) (Prims.of_int (4))
                   (Prims.of_int (332)) (Prims.of_int (30)))))
          (Obj.magic uu___1)
          (fun uu___2 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___3 ->
                  {
                    FStarC_Reflection_V2_Data.sort2 =
                      (b.Pulse_Syntax_Base.binder_ty);
                    FStarC_Reflection_V2_Data.qual =
                      (match q with
                       | FStar_Pervasives_Native.Some
                           (Pulse_Syntax_Base.Implicit) ->
                           FStarC_Reflection_V2_Data.Q_Implicit
                       | FStar_Pervasives_Native.Some
                           (Pulse_Syntax_Base.TcArg) ->
                           FStarC_Reflection_V2_Data.Q_Explicit
                       | FStar_Pervasives_Native.None ->
                           FStarC_Reflection_V2_Data.Q_Explicit);
                    FStarC_Reflection_V2_Data.attrs = uu___2;
                    FStarC_Reflection_V2_Data.ppname2 =
                      ((b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name)
                  })) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (326)) (Prims.of_int (4)) (Prims.of_int (332))
                 (Prims.of_int (30)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (325)) (Prims.of_int (2)) (Prims.of_int (333))
                 (Prims.of_int (3))))) (Obj.magic uu___)
        (fun uu___1 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___2 -> FStarC_Reflection_V2_Builtins.pack_binder uu___1))
let rec (extract_dv_pattern :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.pattern ->
      ((Pulse_Typing_Env.env * FStarC_Reflection_V2_Data.pattern *
         Pulse_Typing_Env.binding Prims.list),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun p ->
           match p with
           | Pulse_Syntax_Base.Pat_Cons (fv, pats) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       Obj.magic
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStarC_Reflection_V2_Builtins.pack_fv
                                 fv.Pulse_Syntax_Base.fv_name)) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (339)) (Prims.of_int (13))
                                (Prims.of_int (339)) (Prims.of_int (33)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (339)) (Prims.of_int (36))
                                (Prims.of_int (341)) (Prims.of_int (64)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun fv1 ->
                             let uu___1 =
                               extract_dv_patterns g
                                 (FStar_List_Tot_Base.map
                                    FStar_Pervasives_Native.fst pats) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (340))
                                           (Prims.of_int (22))
                                           (Prims.of_int (340))
                                           (Prims.of_int (67)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (339))
                                           (Prims.of_int (36))
                                           (Prims.of_int (341))
                                           (Prims.of_int (64)))))
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___3 ->
                                          match uu___2 with
                                          | (g1, pats1, bs) ->
                                              (g1,
                                                (FStarC_Reflection_V2_Data.Pat_Cons
                                                   (fv1,
                                                     FStar_Pervasives_Native.None,
                                                     (FStar_List_Tot_Base.map
                                                        (fun p1 ->
                                                           (p1, false)) pats1))),
                                                bs))))) uu___1)))
           | Pulse_Syntax_Base.Pat_Constant c ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          (g, (FStarC_Reflection_V2_Data.Pat_Constant c), []))))
           | Pulse_Syntax_Base.Pat_Var (ppname, sort) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = FStarC_Tactics_Unseal.unseal sort in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (345)) (Prims.of_int (13))
                                (Prims.of_int (345)) (Prims.of_int (26)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (345)) (Prims.of_int (29))
                                (Prims.of_int (347)) (Prims.of_int (37)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun ty ->
                             let uu___1 =
                               extend_env' g
                                 (Pulse_Syntax_Base.mk_ppname ppname
                                    FStar_Range.range_0) ty in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (346))
                                           (Prims.of_int (20))
                                           (Prims.of_int (346))
                                           (Prims.of_int (69)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (345))
                                           (Prims.of_int (29))
                                           (Prims.of_int (347))
                                           (Prims.of_int (37)))))
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___3 ->
                                          match uu___2 with
                                          | (g1, (uu___4, x)) ->
                                              (g1,
                                                (FStarC_Reflection_V2_Data.Pat_Var
                                                   (sort, ppname)),
                                                [(x, ty)]))))) uu___1)))
           | Pulse_Syntax_Base.Pat_Dot_Term t ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          (g, (FStarC_Reflection_V2_Data.Pat_Dot_Term t), [])))))
        uu___1 uu___
and (extract_dv_patterns :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.pattern Prims.list ->
      ((Pulse_Typing_Env.env * FStarC_Reflection_V2_Data.pattern Prims.list *
         Pulse_Typing_Env.binding Prims.list),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun ps ->
           match ps with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> (g, [], []))))
           | p::ps1 ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = extract_dv_pattern g p in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (355)) (Prims.of_int (19))
                                (Prims.of_int (355)) (Prims.of_int (41)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (354)) (Prims.of_int (12))
                                (Prims.of_int (357)) (Prims.of_int (20)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             match uu___1 with
                             | (g1, p1, bs) ->
                                 let uu___2 = extract_dv_patterns g1 ps1 in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (356))
                                               (Prims.of_int (21))
                                               (Prims.of_int (356))
                                               (Prims.of_int (45)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (355))
                                               (Prims.of_int (44))
                                               (Prims.of_int (357))
                                               (Prims.of_int (20)))))
                                      (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 ->
                                              match uu___3 with
                                              | (g2, ps2, bs') ->
                                                  (g2, (p1 :: ps2),
                                                    (FStar_List_Tot_Base.op_At
                                                       bs bs')))))) uu___1))))
        uu___1 uu___
let (get_type_of_ref :
  Pulse_Syntax_Base.term ->
    (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun p ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              fun uu___2 ->
                let uu___3 =
                  let uu___4 = Pulse_Syntax_Printer.term_to_string p in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                             (Prims.of_int (360)) (Prims.of_int (93))
                             (Prims.of_int (360)) (Prims.of_int (111)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Prims.fst"
                             (Prims.of_int (611)) (Prims.of_int (19))
                             (Prims.of_int (611)) (Prims.of_int (31)))))
                    (Obj.magic uu___4)
                    (fun uu___5 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___6 ->
                            Prims.strcat
                              "expected term (Pulse.Lib.Reference.ref ...), got "
                              (Prims.strcat uu___5 ""))) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                           (Prims.of_int (360)) (Prims.of_int (23))
                           (Prims.of_int (360)) (Prims.of_int (112)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                           (Prims.of_int (360)) (Prims.of_int (16))
                           (Prims.of_int (360)) (Prims.of_int (112)))))
                  (Obj.magic uu___3)
                  (fun uu___4 -> FStar_Tactics_V2_Derived.fail uu___4))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (360)) (Prims.of_int (16)) (Prims.of_int (360))
               (Prims.of_int (112)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (361)) (Prims.of_int (2)) (Prims.of_int (365))
               (Prims.of_int (16))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun fail ->
            match FStarC_Reflection_V2_Builtins.inspect_ln p with
            | FStarC_Reflection_V2_Data.Tv_App (hd, (arg, uu___1)) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> arg)))
            | uu___1 -> Obj.magic (Obj.repr (fail ()))) uu___1)
let (get_type_of_array :
  Pulse_Syntax_Base.term ->
    (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun p ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              fun uu___2 ->
                let uu___3 =
                  let uu___4 = Pulse_Syntax_Printer.term_to_string p in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                             (Prims.of_int (368)) (Prims.of_int (96))
                             (Prims.of_int (368)) (Prims.of_int (114)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Prims.fst"
                             (Prims.of_int (611)) (Prims.of_int (19))
                             (Prims.of_int (611)) (Prims.of_int (31)))))
                    (Obj.magic uu___4)
                    (fun uu___5 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___6 ->
                            Prims.strcat
                              "expected term (Pulse.Lib.Array.Core.array ...), got "
                              (Prims.strcat uu___5 ""))) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                           (Prims.of_int (368)) (Prims.of_int (23))
                           (Prims.of_int (368)) (Prims.of_int (115)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                           (Prims.of_int (368)) (Prims.of_int (16))
                           (Prims.of_int (368)) (Prims.of_int (115)))))
                  (Obj.magic uu___3)
                  (fun uu___4 -> FStar_Tactics_V2_Derived.fail uu___4))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (368)) (Prims.of_int (16)) (Prims.of_int (368))
               (Prims.of_int (115)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (369)) (Prims.of_int (2)) (Prims.of_int (373))
               (Prims.of_int (16))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun fail ->
            match FStarC_Reflection_V2_Builtins.inspect_ln p with
            | FStarC_Reflection_V2_Data.Tv_App (hd, (arg, uu___1)) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> arg)))
            | uu___1 -> Obj.magic (Obj.repr (fail ()))) uu___1)
let (mk_abs :
  FStarC_Reflection_Types.binder ->
    FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  =
  fun b ->
    fun e ->
      FStarC_Reflection_V2_Builtins.pack_ln
        (FStarC_Reflection_V2_Data.Tv_Abs (b, e))
let (unit_binder : Prims.string -> FStarC_Reflection_Types.binder) =
  fun ppname ->
    FStarC_Reflection_V2_Builtins.pack_binder
      {
        FStarC_Reflection_V2_Data.sort2 = Pulse_Extract_CompilerLib.unit_ty;
        FStarC_Reflection_V2_Data.qual = FStarC_Reflection_V2_Data.Q_Explicit;
        FStarC_Reflection_V2_Data.attrs = [];
        FStarC_Reflection_V2_Data.ppname2 = (FStar_Sealed.seal ppname)
      }
let rec (extract_dv :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      let uu___ = is_erasable p in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (387)) (Prims.of_int (5)) (Prims.of_int (387))
                 (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (387)) (Prims.of_int (2)) (Prims.of_int (475))
                 (Prims.of_int (5))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              if uu___1
              then
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Pulse_Extract_CompilerLib.mk_return
                             Pulse_Extract_CompilerLib.unit_tm)))
              else
                Obj.magic
                  (Obj.repr
                     (match p.Pulse_Syntax_Base.term1 with
                      | Pulse_Syntax_Base.Tm_IntroPure uu___3 ->
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___4 ->
                                  Pulse_Extract_CompilerLib.mk_return
                                    Pulse_Extract_CompilerLib.unit_tm))
                      | Pulse_Syntax_Base.Tm_ElimExists uu___3 ->
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___4 ->
                                  Pulse_Extract_CompilerLib.mk_return
                                    Pulse_Extract_CompilerLib.unit_tm))
                      | Pulse_Syntax_Base.Tm_IntroExists uu___3 ->
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___4 ->
                                  Pulse_Extract_CompilerLib.mk_return
                                    Pulse_Extract_CompilerLib.unit_tm))
                      | Pulse_Syntax_Base.Tm_Rewrite uu___3 ->
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___4 ->
                                  Pulse_Extract_CompilerLib.mk_return
                                    Pulse_Extract_CompilerLib.unit_tm))
                      | Pulse_Syntax_Base.Tm_ProofHintWithBinders uu___3 ->
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___4 ->
                                  Pulse_Extract_CompilerLib.mk_return
                                    Pulse_Extract_CompilerLib.unit_tm))
                      | Pulse_Syntax_Base.Tm_Abs
                          { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = q;
                            Pulse_Syntax_Base.ascription = uu___3;
                            Pulse_Syntax_Base.body = body;_}
                          ->
                          Obj.repr
                            (let uu___4 = extract_dv_binder b q in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (397))
                                        (Prims.of_int (15))
                                        (Prims.of_int (397))
                                        (Prims.of_int (36)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (397))
                                        (Prims.of_int (39))
                                        (Prims.of_int (400))
                                        (Prims.of_int (38)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  (fun b' ->
                                     let uu___5 = extend_env'_binder g b in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (398))
                                                   (Prims.of_int (17))
                                                   (Prims.of_int (398))
                                                   (Prims.of_int (39)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (397))
                                                   (Prims.of_int (39))
                                                   (Prims.of_int (400))
                                                   (Prims.of_int (38)))))
                                          (Obj.magic uu___5)
                                          (fun uu___6 ->
                                             (fun uu___6 ->
                                                match uu___6 with
                                                | (g1, x) ->
                                                    let uu___7 =
                                                      extract_dv g1
                                                        (Pulse_Syntax_Naming.open_st_term_nv
                                                           body x) in
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (399))
                                                                  (Prims.of_int (17))
                                                                  (Prims.of_int (399))
                                                                  (Prims.of_int (54)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (400))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (400))
                                                                  (Prims.of_int (38)))))
                                                         (Obj.magic uu___7)
                                                         (fun body1 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___8 ->
                                                                 mk_abs b'
                                                                   (Pulse_Syntax_Naming.close_term
                                                                    body1
                                                                    (FStar_Pervasives_Native.__proj__Mktuple2__item___2
                                                                    x))))))
                                               uu___6))) uu___5))
                      | Pulse_Syntax_Base.Tm_Return
                          { Pulse_Syntax_Base.expected_type = uu___3;
                            Pulse_Syntax_Base.insert_eq = uu___4;
                            Pulse_Syntax_Base.term = term;_}
                          ->
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___5 ->
                                  Pulse_Extract_CompilerLib.mk_return term))
                      | Pulse_Syntax_Base.Tm_STApp
                          { Pulse_Syntax_Base.head = head;
                            Pulse_Syntax_Base.arg_qual = arg_qual;
                            Pulse_Syntax_Base.arg = arg;_}
                          ->
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 ->
                                  Pulse_Extract_CompilerLib.mk_meta_monadic
                                    (FStar_Reflection_V2_Derived.mk_app head
                                       [(arg,
                                          (Pulse_Elaborate_Pure.elab_qual
                                             arg_qual))])))
                      | Pulse_Syntax_Base.Tm_Bind
                          { Pulse_Syntax_Base.binder = binder;
                            Pulse_Syntax_Base.head1 = head;
                            Pulse_Syntax_Base.body1 = body;_}
                          ->
                          Obj.repr
                            (let uu___3 =
                               extract_dv_binder binder
                                 FStar_Pervasives_Native.None in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (408))
                                        (Prims.of_int (15))
                                        (Prims.of_int (408))
                                        (Prims.of_int (44)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (408))
                                        (Prims.of_int (47))
                                        (Prims.of_int (412))
                                        (Prims.of_int (45)))))
                               (Obj.magic uu___3)
                               (fun uu___4 ->
                                  (fun b' ->
                                     let uu___4 = extract_dv g head in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (409))
                                                   (Prims.of_int (15))
                                                   (Prims.of_int (409))
                                                   (Prims.of_int (32)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (409))
                                                   (Prims.of_int (35))
                                                   (Prims.of_int (412))
                                                   (Prims.of_int (45)))))
                                          (Obj.magic uu___4)
                                          (fun uu___5 ->
                                             (fun e1 ->
                                                let uu___5 =
                                                  extend_env'_binder g binder in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (410))
                                                              (Prims.of_int (17))
                                                              (Prims.of_int (410))
                                                              (Prims.of_int (44)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (409))
                                                              (Prims.of_int (35))
                                                              (Prims.of_int (412))
                                                              (Prims.of_int (45)))))
                                                     (Obj.magic uu___5)
                                                     (fun uu___6 ->
                                                        (fun uu___6 ->
                                                           match uu___6 with
                                                           | (g1, x) ->
                                                               let uu___7 =
                                                                 extract_dv
                                                                   g1
                                                                   (Pulse_Syntax_Naming.open_st_term_nv
                                                                    body x) in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (54)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (45)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___7)
                                                                    (
                                                                    fun body1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Extract_CompilerLib.mk_let
                                                                    b' e1
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    body1
                                                                    (FStar_Pervasives_Native.__proj__Mktuple2__item___2
                                                                    x))))))
                                                          uu___6))) uu___5)))
                                    uu___4))
                      | Pulse_Syntax_Base.Tm_TotBind
                          { Pulse_Syntax_Base.binder1 = binder;
                            Pulse_Syntax_Base.head2 = head;
                            Pulse_Syntax_Base.body2 = body;_}
                          ->
                          Obj.repr
                            (let uu___3 =
                               extract_dv_binder binder
                                 FStar_Pervasives_Native.None in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (415))
                                        (Prims.of_int (15))
                                        (Prims.of_int (415))
                                        (Prims.of_int (44)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (415))
                                        (Prims.of_int (47))
                                        (Prims.of_int (419))
                                        (Prims.of_int (43)))))
                               (Obj.magic uu___3)
                               (fun uu___4 ->
                                  (fun b' ->
                                     let uu___4 =
                                       Obj.magic
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___5 ->
                                               Pulse_Extract_CompilerLib.mk_return
                                                 head)) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (416))
                                                   (Prims.of_int (15))
                                                   (Prims.of_int (416))
                                                   (Prims.of_int (33)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (416))
                                                   (Prims.of_int (36))
                                                   (Prims.of_int (419))
                                                   (Prims.of_int (43)))))
                                          (Obj.magic uu___4)
                                          (fun uu___5 ->
                                             (fun e1 ->
                                                let uu___5 =
                                                  extend_env'_binder g binder in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (417))
                                                              (Prims.of_int (17))
                                                              (Prims.of_int (417))
                                                              (Prims.of_int (44)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (416))
                                                              (Prims.of_int (36))
                                                              (Prims.of_int (419))
                                                              (Prims.of_int (43)))))
                                                     (Obj.magic uu___5)
                                                     (fun uu___6 ->
                                                        (fun uu___6 ->
                                                           match uu___6 with
                                                           | (g1, x) ->
                                                               let uu___7 =
                                                                 extract_dv
                                                                   g1
                                                                   (Pulse_Syntax_Naming.open_st_term_nv
                                                                    body x) in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (418))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (418))
                                                                    (Prims.of_int (52)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (43)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___7)
                                                                    (
                                                                    fun e2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Extract_CompilerLib.mk_let
                                                                    b' e1
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    e2
                                                                    (FStar_Pervasives_Native.__proj__Mktuple2__item___2
                                                                    x))))))
                                                          uu___6))) uu___5)))
                                    uu___4))
                      | Pulse_Syntax_Base.Tm_If
                          { Pulse_Syntax_Base.b1 = b;
                            Pulse_Syntax_Base.then_ = then_;
                            Pulse_Syntax_Base.else_ = else_;
                            Pulse_Syntax_Base.post1 = uu___3;_}
                          ->
                          Obj.repr
                            (let uu___4 = extract_dv g then_ in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (422))
                                        (Prims.of_int (18))
                                        (Prims.of_int (422))
                                        (Prims.of_int (36)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (422))
                                        (Prims.of_int (39))
                                        (Prims.of_int (424))
                                        (Prims.of_int (29)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  (fun then_1 ->
                                     let uu___5 = extract_dv g else_ in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (423))
                                                   (Prims.of_int (18))
                                                   (Prims.of_int (423))
                                                   (Prims.of_int (36)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (424))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (424))
                                                   (Prims.of_int (29)))))
                                          (Obj.magic uu___5)
                                          (fun else_1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___6 ->
                                                  Pulse_Extract_CompilerLib.mk_if
                                                    b then_1 else_1))))
                                    uu___5))
                      | Pulse_Syntax_Base.Tm_Match
                          { Pulse_Syntax_Base.sc = sc;
                            Pulse_Syntax_Base.returns_ = uu___3;
                            Pulse_Syntax_Base.brs = brs;_}
                          ->
                          Obj.repr
                            (let uu___4 =
                               let uu___5 =
                                 FStar_Tactics_Util.map (extract_dv_branch g)
                                   brs in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Extract.Main.fst"
                                          (Prims.of_int (427))
                                          (Prims.of_int (36))
                                          (Prims.of_int (427))
                                          (Prims.of_int (69)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Extract.Main.fst"
                                          (Prims.of_int (427))
                                          (Prims.of_int (16))
                                          (Prims.of_int (427))
                                          (Prims.of_int (70)))))
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___7 ->
                                         FStarC_Reflection_V2_Data.Tv_Match
                                           (sc, FStar_Pervasives_Native.None,
                                             uu___6))) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (427))
                                        (Prims.of_int (16))
                                        (Prims.of_int (427))
                                        (Prims.of_int (70)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (427))
                                        (Prims.of_int (6))
                                        (Prims.of_int (427))
                                        (Prims.of_int (70)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 ->
                                       FStarC_Reflection_V2_Builtins.pack_ln
                                         uu___5)))
                      | Pulse_Syntax_Base.Tm_While
                          { Pulse_Syntax_Base.invariant = uu___3;
                            Pulse_Syntax_Base.condition = condition;
                            Pulse_Syntax_Base.condition_var = uu___4;
                            Pulse_Syntax_Base.body3 = body;_}
                          ->
                          Obj.repr
                            (let uu___5 = extract_dv g condition in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (430))
                                        (Prims.of_int (22))
                                        (Prims.of_int (430))
                                        (Prims.of_int (44)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (430))
                                        (Prims.of_int (47))
                                        (Prims.of_int (435))
                                        (Prims.of_int (65)))))
                               (Obj.magic uu___5)
                               (fun uu___6 ->
                                  (fun condition1 ->
                                     let uu___6 = extract_dv g body in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (431))
                                                   (Prims.of_int (17))
                                                   (Prims.of_int (431))
                                                   (Prims.of_int (34)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (432))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (435))
                                                   (Prims.of_int (65)))))
                                          (Obj.magic uu___6)
                                          (fun body1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___7 ->
                                                  Pulse_Extract_CompilerLib.mk_meta_monadic
                                                    (FStar_Reflection_V2_Derived.mk_app
                                                       (FStarC_Reflection_V2_Builtins.pack_ln
                                                          (FStarC_Reflection_V2_Data.Tv_FVar
                                                             (FStarC_Reflection_V2_Builtins.pack_fv
                                                                ["Pulse";
                                                                "Lib";
                                                                "Dv";
                                                                "while_"])))
                                                       [((mk_abs
                                                            (unit_binder
                                                               "while_cond")
                                                            condition1),
                                                          FStarC_Reflection_V2_Data.Q_Explicit);
                                                       ((mk_abs
                                                           (unit_binder
                                                              "while_body")
                                                           body1),
                                                         FStarC_Reflection_V2_Data.Q_Explicit)])))))
                                    uu___6))
                      | Pulse_Syntax_Base.Tm_Par
                          { Pulse_Syntax_Base.pre1 = uu___3;
                            Pulse_Syntax_Base.body11 = body1;
                            Pulse_Syntax_Base.post11 = uu___4;
                            Pulse_Syntax_Base.pre2 = uu___5;
                            Pulse_Syntax_Base.body21 = body2;
                            Pulse_Syntax_Base.post2 = uu___6;_}
                          ->
                          Obj.repr
                            (let uu___7 = extract_dv g body1 in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (438))
                                        (Prims.of_int (18))
                                        (Prims.of_int (438))
                                        (Prims.of_int (36)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (438))
                                        (Prims.of_int (39))
                                        (Prims.of_int (443))
                                        (Prims.of_int (62)))))
                               (Obj.magic uu___7)
                               (fun uu___8 ->
                                  (fun body11 ->
                                     let uu___8 = extract_dv g body2 in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (439))
                                                   (Prims.of_int (18))
                                                   (Prims.of_int (439))
                                                   (Prims.of_int (36)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (440))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (443))
                                                   (Prims.of_int (62)))))
                                          (Obj.magic uu___8)
                                          (fun body21 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___9 ->
                                                  Pulse_Extract_CompilerLib.mk_meta_monadic
                                                    (FStar_Reflection_V2_Derived.mk_app
                                                       (FStarC_Reflection_V2_Builtins.pack_ln
                                                          (FStarC_Reflection_V2_Data.Tv_FVar
                                                             (FStarC_Reflection_V2_Builtins.pack_fv
                                                                ["Pulse";
                                                                "Lib";
                                                                "Dv";
                                                                "par"])))
                                                       [((mk_abs
                                                            (unit_binder
                                                               "par_b1")
                                                            body11),
                                                          FStarC_Reflection_V2_Data.Q_Explicit);
                                                       ((mk_abs
                                                           (unit_binder
                                                              "par_b2")
                                                           body21),
                                                         FStarC_Reflection_V2_Data.Q_Explicit)])))))
                                    uu___8))
                      | Pulse_Syntax_Base.Tm_WithLocal
                          { Pulse_Syntax_Base.binder2 = binder;
                            Pulse_Syntax_Base.initializer1 = initializer1;
                            Pulse_Syntax_Base.body4 = body;_}
                          ->
                          Obj.repr
                            (let uu___3 =
                               extract_dv_binder binder
                                 FStar_Pervasives_Native.None in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (446))
                                        (Prims.of_int (15))
                                        (Prims.of_int (446))
                                        (Prims.of_int (44)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (446))
                                        (Prims.of_int (47))
                                        (Prims.of_int (451))
                                        (Prims.of_int (52)))))
                               (Obj.magic uu___3)
                               (fun uu___4 ->
                                  (fun b' ->
                                     let uu___4 =
                                       let uu___5 =
                                         let uu___6 =
                                           let uu___7 =
                                             get_type_of_ref
                                               binder.Pulse_Syntax_Base.binder_ty in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Extract.Main.fst"
                                                      (Prims.of_int (448))
                                                      (Prims.of_int (9))
                                                      (Prims.of_int (448))
                                                      (Prims.of_int (41)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Extract.Main.fst"
                                                      (Prims.of_int (448))
                                                      (Prims.of_int (9))
                                                      (Prims.of_int (448))
                                                      (Prims.of_int (55)))))
                                             (Obj.magic uu___7)
                                             (fun uu___8 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___9 ->
                                                     (uu___8,
                                                       FStarC_Reflection_V2_Data.Q_Implicit))) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (448))
                                                    (Prims.of_int (9))
                                                    (Prims.of_int (448))
                                                    (Prims.of_int (55)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (448))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (448))
                                                    (Prims.of_int (83)))))
                                           (Obj.magic uu___6)
                                           (fun uu___7 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___8 ->
                                                   [uu___7;
                                                   (initializer1,
                                                     FStarC_Reflection_V2_Data.Q_Explicit)])) in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (448))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (448))
                                                  (Prims.of_int (83)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (447))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (448))
                                                  (Prims.of_int (83)))))
                                         (Obj.magic uu___5)
                                         (fun uu___6 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___7 ->
                                                 FStar_Reflection_V2_Derived.mk_app
                                                   (FStarC_Reflection_V2_Builtins.pack_ln
                                                      (FStarC_Reflection_V2_Data.Tv_FVar
                                                         (FStarC_Reflection_V2_Builtins.pack_fv
                                                            ["Pulse";
                                                            "Lib";
                                                            "Reference";
                                                            "alloc"])))
                                                   uu___6)) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (447))
                                                   (Prims.of_int (22))
                                                   (Prims.of_int (448))
                                                   (Prims.of_int (83)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (448))
                                                   (Prims.of_int (86))
                                                   (Prims.of_int (451))
                                                   (Prims.of_int (52)))))
                                          (Obj.magic uu___4)
                                          (fun uu___5 ->
                                             (fun allocator ->
                                                let uu___5 =
                                                  extend_env'_binder g binder in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (449))
                                                              (Prims.of_int (17))
                                                              (Prims.of_int (449))
                                                              (Prims.of_int (44)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (448))
                                                              (Prims.of_int (86))
                                                              (Prims.of_int (451))
                                                              (Prims.of_int (52)))))
                                                     (Obj.magic uu___5)
                                                     (fun uu___6 ->
                                                        (fun uu___6 ->
                                                           match uu___6 with
                                                           | (g1, x) ->
                                                               let uu___7 =
                                                                 extract_dv
                                                                   g1
                                                                   (Pulse_Syntax_Naming.open_st_term_nv
                                                                    body x) in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (54)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (52)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___7)
                                                                    (
                                                                    fun body1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Extract_CompilerLib.mk_let
                                                                    b'
                                                                    allocator
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    body1
                                                                    (FStar_Pervasives_Native.__proj__Mktuple2__item___2
                                                                    x))))))
                                                          uu___6))) uu___5)))
                                    uu___4))
                      | Pulse_Syntax_Base.Tm_WithLocalArray
                          { Pulse_Syntax_Base.binder3 = binder;
                            Pulse_Syntax_Base.initializer2 = initializer1;
                            Pulse_Syntax_Base.length = length;
                            Pulse_Syntax_Base.body5 = body;_}
                          ->
                          Obj.repr
                            (let uu___3 =
                               extract_dv_binder binder
                                 FStar_Pervasives_Native.None in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (454))
                                        (Prims.of_int (15))
                                        (Prims.of_int (454))
                                        (Prims.of_int (44)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (454))
                                        (Prims.of_int (47))
                                        (Prims.of_int (464))
                                        (Prims.of_int (52)))))
                               (Obj.magic uu___3)
                               (fun uu___4 ->
                                  (fun b' ->
                                     let uu___4 =
                                       let uu___5 =
                                         let uu___6 =
                                           let uu___7 =
                                             get_type_of_array
                                               binder.Pulse_Syntax_Base.binder_ty in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Extract.Main.fst"
                                                      (Prims.of_int (461))
                                                      (Prims.of_int (9))
                                                      (Prims.of_int (461))
                                                      (Prims.of_int (43)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Extract.Main.fst"
                                                      (Prims.of_int (461))
                                                      (Prims.of_int (9))
                                                      (Prims.of_int (461))
                                                      (Prims.of_int (57)))))
                                             (Obj.magic uu___7)
                                             (fun uu___8 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___9 ->
                                                     (uu___8,
                                                       FStarC_Reflection_V2_Data.Q_Implicit))) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (461))
                                                    (Prims.of_int (9))
                                                    (Prims.of_int (461))
                                                    (Prims.of_int (57)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (461))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (461))
                                                    (Prims.of_int (107)))))
                                           (Obj.magic uu___6)
                                           (fun uu___7 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___8 ->
                                                   [uu___7;
                                                   (initializer1,
                                                     FStarC_Reflection_V2_Data.Q_Explicit);
                                                   (length,
                                                     FStarC_Reflection_V2_Data.Q_Explicit)])) in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (461))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (461))
                                                  (Prims.of_int (107)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (460))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (461))
                                                  (Prims.of_int (107)))))
                                         (Obj.magic uu___5)
                                         (fun uu___6 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___7 ->
                                                 FStar_Reflection_V2_Derived.mk_app
                                                   (FStarC_Reflection_V2_Builtins.pack_ln
                                                      (FStarC_Reflection_V2_Data.Tv_FVar
                                                         (FStarC_Reflection_V2_Builtins.pack_fv
                                                            ["Pulse";
                                                            "Lib";
                                                            "Array";
                                                            "Core";
                                                            "alloc"])))
                                                   uu___6)) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (460))
                                                   (Prims.of_int (22))
                                                   (Prims.of_int (461))
                                                   (Prims.of_int (107)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (461))
                                                   (Prims.of_int (110))
                                                   (Prims.of_int (464))
                                                   (Prims.of_int (52)))))
                                          (Obj.magic uu___4)
                                          (fun uu___5 ->
                                             (fun allocator ->
                                                let uu___5 =
                                                  extend_env'_binder g binder in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (462))
                                                              (Prims.of_int (17))
                                                              (Prims.of_int (462))
                                                              (Prims.of_int (44)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (461))
                                                              (Prims.of_int (110))
                                                              (Prims.of_int (464))
                                                              (Prims.of_int (52)))))
                                                     (Obj.magic uu___5)
                                                     (fun uu___6 ->
                                                        (fun uu___6 ->
                                                           match uu___6 with
                                                           | (g1, x) ->
                                                               let uu___7 =
                                                                 extract_dv
                                                                   g1
                                                                   (Pulse_Syntax_Naming.open_st_term_nv
                                                                    body x) in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (54)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (52)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___7)
                                                                    (
                                                                    fun body1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Extract_CompilerLib.mk_let
                                                                    b'
                                                                    allocator
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    body1
                                                                    (FStar_Pervasives_Native.__proj__Mktuple2__item___2
                                                                    x))))))
                                                          uu___6))) uu___5)))
                                    uu___4))
                      | Pulse_Syntax_Base.Tm_Admit uu___3 ->
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___4 ->
                                  Pulse_Extract_CompilerLib.mk_return
                                    Pulse_Extract_CompilerLib.unit_tm))
                      | Pulse_Syntax_Base.Tm_Unreachable
                          { Pulse_Syntax_Base.c = c;_} ->
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 ->
                                  Pulse_Extract_CompilerLib.mk_meta_monadic
                                    (FStar_Reflection_V2_Derived.mk_app
                                       (FStarC_Reflection_V2_Builtins.pack_ln
                                          (FStarC_Reflection_V2_Data.Tv_FVar
                                             (FStarC_Reflection_V2_Builtins.pack_fv
                                                ["Pulse";
                                                "Lib";
                                                "Dv";
                                                "unreachable"])))
                                       [((Pulse_Syntax_Base.comp_res c),
                                          FStarC_Reflection_V2_Data.Q_Explicit);
                                       (Pulse_Reflection_Util.unit_tm,
                                         FStarC_Reflection_V2_Data.Q_Explicit)])))
                      | Pulse_Syntax_Base.Tm_WithInv
                          { Pulse_Syntax_Base.name1 = uu___3;
                            Pulse_Syntax_Base.body6 = body;
                            Pulse_Syntax_Base.returns_inv = uu___4;_}
                          -> Obj.repr (extract_dv g body)))) uu___1)
and (extract_dv_branch :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.branch ->
      (FStarC_Reflection_V2_Data.branch, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun b ->
      let uu___ =
        Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> b)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (478)) (Prims.of_int (18))
                 (Prims.of_int (478)) (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (477)) (Prims.of_int (71))
                 (Prims.of_int (482)) (Prims.of_int (18)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | (pat, body) ->
                  let uu___2 = extract_dv_pattern g pat in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (479)) (Prims.of_int (19))
                                (Prims.of_int (479)) (Prims.of_int (43)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (478)) (Prims.of_int (22))
                                (Prims.of_int (482)) (Prims.of_int (18)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          (fun uu___3 ->
                             match uu___3 with
                             | (g1, pat1, bs) ->
                                 let uu___4 =
                                   let uu___5 =
                                     extract_dv g1
                                       (Pulse_Checker_Match.open_st_term_bs
                                          body bs) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (481))
                                              (Prims.of_int (4))
                                              (Prims.of_int (481))
                                              (Prims.of_int (64)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (480))
                                              (Prims.of_int (7))
                                              (Prims.of_int (482))
                                              (Prims.of_int (18)))))
                                     (Obj.magic uu___5)
                                     (fun uu___6 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___7 ->
                                             Pulse_Syntax_Naming.close_term_n
                                               uu___6
                                               (FStar_List_Tot_Base.map
                                                  FStar_Pervasives_Native.fst
                                                  bs))) in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (480))
                                               (Prims.of_int (7))
                                               (Prims.of_int (482))
                                               (Prims.of_int (18)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (480))
                                               (Prims.of_int (2))
                                               (Prims.of_int (482))
                                               (Prims.of_int (18)))))
                                      (Obj.magic uu___4)
                                      (fun uu___5 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___6 -> (pat1, uu___5)))))
                            uu___3))) uu___1)
let (extract_pulse_dv :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      let uu___ = erase_ghost_subterms g p in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (485)) (Prims.of_int (10))
                 (Prims.of_int (485)) (Prims.of_int (34)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (485)) (Prims.of_int (37))
                 (Prims.of_int (487)) (Prims.of_int (16)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun p1 ->
              let uu___1 = simplify_st_term g p1 in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (486)) (Prims.of_int (10))
                            (Prims.of_int (486)) (Prims.of_int (30)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (487)) (Prims.of_int (2))
                            (Prims.of_int (487)) (Prims.of_int (16)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun p2 -> Obj.magic (extract_dv g p2)) uu___2)))
             uu___1)
let rec (extract_dv_recursive :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      FStarC_Reflection_Types.fv ->
        (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun p ->
             fun rec_name ->
               match p.Pulse_Syntax_Base.term1 with
               | Pulse_Syntax_Base.Tm_Abs
                   { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = q;
                     Pulse_Syntax_Base.ascription = uu___;
                     Pulse_Syntax_Base.body = body;_}
                   ->
                   Obj.magic
                     (Obj.repr
                        (match body.Pulse_Syntax_Base.term1 with
                         | Pulse_Syntax_Base.Tm_Abs uu___1 ->
                             let uu___2 = extend_env'_binder g b in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (495))
                                        (Prims.of_int (19))
                                        (Prims.of_int (495))
                                        (Prims.of_int (41)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (494))
                                        (Prims.of_int (19))
                                        (Prims.of_int (498))
                                        (Prims.of_int (61)))))
                               (Obj.magic uu___2)
                               (fun uu___3 ->
                                  (fun uu___3 ->
                                     match uu___3 with
                                     | (g1, x) ->
                                         let uu___4 =
                                           Obj.magic
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___5 ->
                                                   Pulse_Syntax_Naming.open_st_term_nv
                                                     body x)) in
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Extract.Main.fst"
                                                       (Prims.of_int (496))
                                                       (Prims.of_int (19))
                                                       (Prims.of_int (496))
                                                       (Prims.of_int (41)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Extract.Main.fst"
                                                       (Prims.of_int (496))
                                                       (Prims.of_int (44))
                                                       (Prims.of_int (498))
                                                       (Prims.of_int (61)))))
                                              (Obj.magic uu___4)
                                              (fun uu___5 ->
                                                 (fun body1 ->
                                                    let uu___5 =
                                                      extract_dv_recursive g1
                                                        body1 rec_name in
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (497))
                                                                  (Prims.of_int (19))
                                                                  (Prims.of_int (497))
                                                                  (Prims.of_int (55)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (498))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (498))
                                                                  (Prims.of_int (61)))))
                                                         (Obj.magic uu___5)
                                                         (fun uu___6 ->
                                                            (fun body2 ->
                                                               let uu___6 =
                                                                 extract_dv_binder
                                                                   b q in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (38)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (61)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___6)
                                                                    (
                                                                    fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    mk_abs
                                                                    uu___7
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    body2
                                                                    (FStar_Pervasives_Native.__proj__Mktuple2__item___2
                                                                    x))))))
                                                              uu___6)))
                                                   uu___5))) uu___3)
                         | uu___1 ->
                             let uu___2 =
                               Obj.magic
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___3 ->
                                       Pulse_Syntax_Naming.subst_st_term body
                                         [FStar_Reflection_Typing.DT
                                            (Prims.int_zero,
                                              (Pulse_Syntax_Pure.wr
                                                 (FStarC_Reflection_V2_Builtins.pack_ln
                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                       rec_name))
                                                 FStar_Range.range_0))])) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (500))
                                        (Prims.of_int (19))
                                        (Prims.of_int (500))
                                        (Prims.of_int (100)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (501))
                                        (Prims.of_int (8))
                                        (Prims.of_int (501))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___2)
                               (fun uu___3 ->
                                  (fun body1 ->
                                     Obj.magic (extract_pulse_dv g body1))
                                    uu___3)))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_V2_Derived.fail
                           "Unexpected recursive definition of non-function")))
          uu___2 uu___1 uu___