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
let (add_intro_pure :
  Pulse_Syntax_Base.range ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term -> Pulse_Syntax_Base.st_term)
  =
  fun rng ->
    fun continuation ->
      fun p ->
        let wr t =
          { Pulse_Syntax_Base.term1 = t; Pulse_Syntax_Base.range2 = rng } in
        let intro_pure_tm =
          wr
            (Pulse_Syntax_Base.Tm_Protect
               {
                 Pulse_Syntax_Base.t3 =
                   (wr
                      (Pulse_Syntax_Base.Tm_IntroPure
                         {
                           Pulse_Syntax_Base.p = p;
                           Pulse_Syntax_Base.should_check =
                             Pulse_Syntax_Base.should_check_false
                         }))
               }) in
        wr
          (Pulse_Syntax_Base.Tm_Protect
             {
               Pulse_Syntax_Base.t3 =
                 (wr
                    (Pulse_Syntax_Base.Tm_Bind
                       {
                         Pulse_Syntax_Base.binder = default_binder_annot;
                         Pulse_Syntax_Base.head1 = intro_pure_tm;
                         Pulse_Syntax_Base.body1 = continuation
                       }))
             })
type uvar_tys =
  (Pulse_Checker_Inference.uvar * Pulse_Syntax_Base.term) Prims.list
let rec (prepare_instantiations :
  Pulse_Typing_Env.env ->
    (Pulse_Syntax_Base.vprop * (Pulse_Syntax_Base.term,
      Pulse_Syntax_Base.term) FStar_Pervasives.either) Prims.list ->
      uvar_tys ->
        Pulse_Syntax_Base.vprop ->
          Pulse_Syntax_Base.term Prims.list ->
            ((Pulse_Syntax_Base.vprop * (Pulse_Syntax_Base.vprop *
               (Pulse_Syntax_Base.term, Pulse_Syntax_Base.term)
               FStar_Pervasives.either) Prims.list * uvar_tys),
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun g ->
               fun out ->
                 fun out_uvars ->
                   fun goal_vprop ->
                     fun witnesses ->
                       match (witnesses, (goal_vprop.Pulse_Syntax_Base.t))
                       with
                       | ([], Pulse_Syntax_Base.Tm_ExistsSL (u, b, p)) ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.fst"
                                            (Prims.of_int (73))
                                            (Prims.of_int (37))
                                            (Prims.of_int (75))
                                            (Prims.of_int (37)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.fst"
                                            (Prims.of_int (72))
                                            (Prims.of_int (30))
                                            (Prims.of_int (77))
                                            (Prims.of_int (105)))))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.fst"
                                                  (Prims.of_int (74))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (74))
                                                  (Prims.of_int (70)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.fst"
                                                  (Prims.of_int (73))
                                                  (Prims.of_int (37))
                                                  (Prims.of_int (75))
                                                  (Prims.of_int (37)))))
                                         (Obj.magic
                                            (Pulse_Checker_Inference.gen_uvar
                                               b.Pulse_Syntax_Base.binder_ppname))
                                         (fun uu___ ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___1 ->
                                                 match uu___ with
                                                 | (uv, t) ->
                                                     ((Pulse_Syntax_Naming.open_term'
                                                         p t Prims.int_zero),
                                                       (FStar_Pervasives.Inr
                                                          t), uv)))))
                                   (fun uu___ ->
                                      (fun uu___ ->
                                         match uu___ with
                                         | (next_goal_vprop, inst, uv) ->
                                             Obj.magic
                                               (prepare_instantiations g
                                                  ((goal_vprop, inst) :: out)
                                                  ((uv,
                                                     (b.Pulse_Syntax_Base.binder_ty))
                                                  :: out_uvars)
                                                  next_goal_vprop [])) uu___)))
                       | ([], uu___) ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 ->
                                      (goal_vprop, out, out_uvars))))
                       | (t::witnesses1, Pulse_Syntax_Base.Tm_ExistsSL
                          (u, b, p)) ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.fst"
                                            (Prims.of_int (84))
                                            (Prims.of_int (10))
                                            (Prims.of_int (89))
                                            (Prims.of_int (39)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.fst"
                                            (Prims.of_int (82))
                                            (Prims.of_int (42))
                                            (Prims.of_int (91))
                                            (Prims.of_int (98)))))
                                   (match t.Pulse_Syntax_Base.t with
                                    | Pulse_Syntax_Base.Tm_Unknown ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.fst"
                                                         (Prims.of_int (86))
                                                         (Prims.of_int (24))
                                                         (Prims.of_int (86))
                                                         (Prims.of_int (72)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.fst"
                                                         (Prims.of_int (85))
                                                         (Prims.of_int (25))
                                                         (Prims.of_int (87))
                                                         (Prims.of_int (55)))))
                                                (Obj.magic
                                                   (Pulse_Checker_Inference.gen_uvar
                                                      b.Pulse_Syntax_Base.binder_ppname))
                                                (fun uu___ ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___1 ->
                                                        match uu___ with
                                                        | (uv, t1) ->
                                                            ((Pulse_Syntax_Naming.open_term'
                                                                p t1
                                                                Prims.int_zero),
                                                              (FStar_Pervasives.Inr
                                                                 t1),
                                                              [(uv,
                                                                 (b.Pulse_Syntax_Base.binder_ty))])))))
                                    | uu___ ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   ((Pulse_Syntax_Naming.open_term'
                                                       p t Prims.int_zero),
                                                     (FStar_Pervasives.Inl t),
                                                     [])))))
                                   (fun uu___ ->
                                      (fun uu___ ->
                                         match uu___ with
                                         | (next_goal_vprop, inst, uvs) ->
                                             Obj.magic
                                               (prepare_instantiations g
                                                  ((goal_vprop, inst) :: out)
                                                  (FStar_List_Tot_Base.op_At
                                                     uvs out_uvars)
                                                  next_goal_vprop witnesses1))
                                        uu___)))
                       | uu___ ->
                           Obj.magic
                             (Obj.repr
                                (Pulse_Typing_Env.fail g
                                   FStar_Pervasives_Native.None
                                   "Unexpected number of instantiations in intro")))
              uu___4 uu___3 uu___2 uu___1 uu___
let rec (build_instantiations :
  Pulse_Checker_Inference.solution ->
    (Pulse_Syntax_Base.term * (Pulse_Syntax_Base.term,
      Pulse_Syntax_Base.term) FStar_Pervasives.either) Prims.list ->
      (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun solutions ->
    fun insts ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (98))
                 (Prims.of_int (29)) (Prims.of_int (110))
                 (Prims.of_int (102)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (112))
                 (Prims.of_int (8)) (Prims.of_int (119)) (Prims.of_int (92)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              fun uu___1 ->
                match uu___1 with
                | (v, i) ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.fst"
                               (Prims.of_int (99)) (Prims.of_int (18))
                               (Prims.of_int (99)) (Prims.of_int (68)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.fst"
                               (Prims.of_int (100)) (Prims.of_int (10))
                               (Prims.of_int (110)) (Prims.of_int (102)))))
                      (Obj.magic
                         (Pulse_Checker_Inference.apply_solution solutions v))
                      (fun uu___2 ->
                         (fun v1 ->
                            match i with
                            | FStar_Pervasives.Inl user_provided ->
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 ->
                                           Pulse_Typing.wr
                                             (Pulse_Syntax_Base.Tm_IntroExists
                                                {
                                                  Pulse_Syntax_Base.erased =
                                                    false;
                                                  Pulse_Syntax_Base.p2 = v1;
                                                  Pulse_Syntax_Base.witnesses
                                                    = [user_provided];
                                                  Pulse_Syntax_Base.should_check1
                                                    =
                                                    Pulse_Syntax_Base.should_check_true
                                                }))))
                            | FStar_Pervasives.Inr inferred ->
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.fst"
                                                 (Prims.of_int (105))
                                                 (Prims.of_int (22))
                                                 (Prims.of_int (105))
                                                 (Prims.of_int (79)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.fst"
                                                 (Prims.of_int (106))
                                                 (Prims.of_int (12))
                                                 (Prims.of_int (110))
                                                 (Prims.of_int (102)))))
                                        (Obj.magic
                                           (Pulse_Checker_Inference.apply_solution
                                              solutions inferred))
                                        (fun sol ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                match Pulse_Syntax_Pure.unreveal
                                                        sol
                                                with
                                                | FStar_Pervasives_Native.Some
                                                    sol1 ->
                                                    Pulse_Typing.wr
                                                      (Pulse_Syntax_Base.Tm_IntroExists
                                                         {
                                                           Pulse_Syntax_Base.erased
                                                             = true;
                                                           Pulse_Syntax_Base.p2
                                                             = v1;
                                                           Pulse_Syntax_Base.witnesses
                                                             = [sol1];
                                                           Pulse_Syntax_Base.should_check1
                                                             =
                                                             Pulse_Syntax_Base.should_check_false
                                                         })
                                                | uu___3 ->
                                                    Pulse_Typing.wr
                                                      (Pulse_Syntax_Base.Tm_IntroExists
                                                         {
                                                           Pulse_Syntax_Base.erased
                                                             = true;
                                                           Pulse_Syntax_Base.p2
                                                             = v1;
                                                           Pulse_Syntax_Base.witnesses
                                                             = [sol];
                                                           Pulse_Syntax_Base.should_check1
                                                             =
                                                             Pulse_Syntax_Base.should_check_false
                                                         })))))) uu___2)))
        (fun uu___ ->
           (fun one_inst ->
              match insts with
              | [] ->
                  Obj.magic
                    (Obj.repr (FStar_Tactics_V2_Derived.fail "Impossible"))
              | hd::[] ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Checker.fst"
                                   (Prims.of_int (114)) (Prims.of_int (21))
                                   (Prims.of_int (114)) (Prims.of_int (53)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Checker.fst"
                                   (Prims.of_int (114)) (Prims.of_int (18))
                                   (Prims.of_int (114)) (Prims.of_int (53)))))
                          (Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (114))
                                         (Prims.of_int (35))
                                         (Prims.of_int (114))
                                         (Prims.of_int (50)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (114))
                                         (Prims.of_int (21))
                                         (Prims.of_int (114))
                                         (Prims.of_int (53)))))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (114))
                                               (Prims.of_int (39))
                                               (Prims.of_int (114))
                                               (Prims.of_int (50)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (114))
                                               (Prims.of_int (35))
                                               (Prims.of_int (114))
                                               (Prims.of_int (50)))))
                                      (Obj.magic (one_inst hd))
                                      (fun uu___ ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              { Pulse_Syntax_Base.t3 = uu___
                                              }))))
                                (fun uu___ ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 ->
                                        Pulse_Syntax_Base.Tm_Protect uu___))))
                          (fun uu___ ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> Pulse_Typing.wr uu___))))
              | hd::tl ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Checker.fst"
                                   (Prims.of_int (116)) (Prims.of_int (23))
                                   (Prims.of_int (119)) (Prims.of_int (92)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Checker.fst"
                                   (Prims.of_int (116)) (Prims.of_int (20))
                                   (Prims.of_int (119)) (Prims.of_int (92)))))
                          (Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (117))
                                         (Prims.of_int (28))
                                         (Prims.of_int (119))
                                         (Prims.of_int (89)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (116))
                                         (Prims.of_int (23))
                                         (Prims.of_int (119))
                                         (Prims.of_int (92)))))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (117))
                                               (Prims.of_int (32))
                                               (Prims.of_int (119))
                                               (Prims.of_int (89)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (117))
                                               (Prims.of_int (28))
                                               (Prims.of_int (119))
                                               (Prims.of_int (89)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (117))
                                                     (Prims.of_int (35))
                                                     (Prims.of_int (119))
                                                     (Prims.of_int (89)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (117))
                                                     (Prims.of_int (32))
                                                     (Prims.of_int (119))
                                                     (Prims.of_int (89)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (117))
                                                           (Prims.of_int (46))
                                                           (Prims.of_int (119))
                                                           (Prims.of_int (86)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.fst"
                                                           (Prims.of_int (117))
                                                           (Prims.of_int (35))
                                                           (Prims.of_int (119))
                                                           (Prims.of_int (89)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.fst"
                                                                 (Prims.of_int (118))
                                                                 (Prims.of_int (53))
                                                                 (Prims.of_int (118))
                                                                 (Prims.of_int (88)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.fst"
                                                                 (Prims.of_int (117))
                                                                 (Prims.of_int (46))
                                                                 (Prims.of_int (119))
                                                                 (Prims.of_int (86)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (88)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (88)))))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (85)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (88)))))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (85)))))
                                                                    (Obj.magic
                                                                    (one_inst
                                                                    hd))
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    {
                                                                    Pulse_Syntax_Base.t3
                                                                    = uu___
                                                                    }))))
                                                                    (
                                                                    fun uu___
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Syntax_Base.Tm_Protect
                                                                    uu___))))
                                                              (fun uu___ ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___1 ->
                                                                    Pulse_Typing.wr
                                                                    uu___))))
                                                        (fun uu___ ->
                                                           (fun uu___ ->
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (86)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (86)))))
                                                                   (Obj.magic
                                                                    (build_instantiations
                                                                    solutions
                                                                    tl))
                                                                   (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    =
                                                                    default_binder_annot;
                                                                    Pulse_Syntax_Base.head1
                                                                    = uu___;
                                                                    Pulse_Syntax_Base.body1
                                                                    = uu___1
                                                                    }))))
                                                             uu___)))
                                                  (fun uu___ ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___1 ->
                                                          Pulse_Syntax_Base.Tm_Bind
                                                            uu___))))
                                            (fun uu___ ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___1 ->
                                                    Pulse_Typing.wr uu___))))
                                      (fun uu___ ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              { Pulse_Syntax_Base.t3 = uu___
                                              }))))
                                (fun uu___ ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 ->
                                        Pulse_Syntax_Base.Tm_Protect uu___))))
                          (fun uu___ ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> Pulse_Typing.wr uu___)))))
             uu___)
let (maybe_infer_intro_exists :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun st ->
      fun pre ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (126)) (Prims.of_int (33))
                   (Prims.of_int (138)) (Prims.of_int (18)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (143)) (Prims.of_int (4))
                   (Prims.of_int (222)) (Prims.of_int (10)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                fun t ->
                  match FStar_List_Tot_Base.partition
                          (fun uu___1 ->
                             match uu___1 with
                             | {
                                 Pulse_Syntax_Base.t =
                                   Pulse_Syntax_Base.Tm_Pure uu___2;
                                 Pulse_Syntax_Base.range1 = uu___3;_} ->
                                 false
                             | {
                                 Pulse_Syntax_Base.t =
                                   Pulse_Syntax_Base.Tm_Emp;
                                 Pulse_Syntax_Base.range1 = uu___2;_} ->
                                 false
                             | uu___2 -> true)
                          (Pulse_Typing_Combinators.vprop_as_list t)
                  with
                  | (rest, pure) ->
                      (((match Pulse_Typing_Combinators.list_as_vprop rest
                         with
                         | {
                             Pulse_Syntax_Base.t = Pulse_Syntax_Base.Tm_Star
                               (t1,
                                {
                                  Pulse_Syntax_Base.t =
                                    Pulse_Syntax_Base.Tm_Emp;
                                  Pulse_Syntax_Base.range1 = uu___1;_});
                             Pulse_Syntax_Base.range1 = uu___2;_} -> t1
                         | {
                             Pulse_Syntax_Base.t = Pulse_Syntax_Base.Tm_Star
                               ({
                                  Pulse_Syntax_Base.t =
                                    Pulse_Syntax_Base.Tm_Emp;
                                  Pulse_Syntax_Base.range1 = uu___1;_},
                                t1);
                             Pulse_Syntax_Base.range1 = uu___2;_} -> t1
                         | t1 -> t1)), pure)))
          (fun uu___ ->
             (fun remove_pure_conjuncts ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (143)) (Prims.of_int (4))
                              (Prims.of_int (148)) (Prims.of_int (5)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (148)) (Prims.of_int (6))
                              (Prims.of_int (222)) (Prims.of_int (10)))))
                     (if
                        Pulse_RuntimeUtils.debug_at_level
                          (Pulse_Typing_Env.fstar_env g) "inference"
                      then
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (145))
                                         (Prims.of_int (14))
                                         (Prims.of_int (147))
                                         (Prims.of_int (43)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (144))
                                         (Prims.of_int (9))
                                         (Prims.of_int (148))
                                         (Prims.of_int (5)))))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (147))
                                               (Prims.of_int (18))
                                               (Prims.of_int (147))
                                               (Prims.of_int (42)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (145))
                                               (Prims.of_int (14))
                                               (Prims.of_int (147))
                                               (Prims.of_int (43)))))
                                      (Obj.magic
                                         (Pulse_Syntax_Printer.st_term_to_string
                                            st))
                                      (fun uu___ ->
                                         (fun uu___ ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (145))
                                                          (Prims.of_int (14))
                                                          (Prims.of_int (147))
                                                          (Prims.of_int (43)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (145))
                                                          (Prims.of_int (14))
                                                          (Prims.of_int (147))
                                                          (Prims.of_int (43)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (146))
                                                                (Prims.of_int (18))
                                                                (Prims.of_int (146))
                                                                (Prims.of_int (46)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Printf.fst"
                                                                (Prims.of_int (121))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (123))
                                                                (Prims.of_int (44)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_V2_Builtins.range_to_string
                                                             st.Pulse_Syntax_Base.range2))
                                                       (fun uu___1 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___2 ->
                                                               fun x ->
                                                                 Prims.strcat
                                                                   (Prims.strcat
                                                                    "At "
                                                                    (Prims.strcat
                                                                    uu___1
                                                                    ": infer_intro_exists for "))
                                                                   (Prims.strcat
                                                                    x "\n")))))
                                                 (fun uu___1 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         uu___1 uu___))))
                                           uu___)))
                                (fun uu___ ->
                                   (fun uu___ ->
                                      Obj.magic
                                        (FStar_Tactics_V2_Builtins.print
                                           uu___)) uu___)))
                      else
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 -> ()))))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (149))
                                         (Prims.of_int (50))
                                         (Prims.of_int (149))
                                         (Prims.of_int (57)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (148))
                                         (Prims.of_int (6))
                                         (Prims.of_int (222))
                                         (Prims.of_int (10)))))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 -> st.Pulse_Syntax_Base.term1))
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      match uu___1 with
                                      | Pulse_Syntax_Base.Tm_IntroExists
                                          {
                                            Pulse_Syntax_Base.erased = erased;
                                            Pulse_Syntax_Base.p2 = t;
                                            Pulse_Syntax_Base.witnesses =
                                              witnesses;
                                            Pulse_Syntax_Base.should_check1 =
                                              uu___2;_}
                                          ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.fst"
                                                        (Prims.of_int (150))
                                                        (Prims.of_int (15))
                                                        (Prims.of_int (150))
                                                        (Prims.of_int (64)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.fst"
                                                        (Prims.of_int (149))
                                                        (Prims.of_int (60))
                                                        (Prims.of_int (222))
                                                        (Prims.of_int (10)))))
                                               (Obj.magic
                                                  (Pulse_Checker_Pure.instantiate_term_implicits
                                                     g t))
                                               (fun uu___3 ->
                                                  (fun uu___3 ->
                                                     match uu___3 with
                                                     | (t1, uu___4) ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (75)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (10)))))
                                                              (Obj.magic
                                                                 (prepare_instantiations
                                                                    g [] []
                                                                    t1
                                                                    witnesses))
                                                              (fun uu___5 ->
                                                                 (fun uu___5
                                                                    ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (goal_vprop,
                                                                    insts,
                                                                    uvs) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    remove_pure_conjuncts
                                                                    goal_vprop))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (goal_vprop1,
                                                                    pure_conjuncts)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.try_inst_uvs_in_goal
                                                                    g pre
                                                                    goal_vprop1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    solutions
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    fun
                                                                    solutions1
                                                                    ->
                                                                    fun p ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions1
                                                                    p))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun p1
                                                                    ->
                                                                    match 
                                                                    p1.Pulse_Syntax_Base.t
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Pure
                                                                    p2 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.try_solve_pure_equalities
                                                                    g p2))
                                                                    (fun sols
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    sols
                                                                    solutions1))))
                                                                    | 
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    solutions1))))
                                                                    uu___8)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    maybe_solve_pure
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.fold_left
                                                                    maybe_solve_pure
                                                                    solutions
                                                                    pure_conjuncts))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    solutions1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (10)))))
                                                                    (if
                                                                    Pulse_RuntimeUtils.debug_at_level
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g)
                                                                    "inference"
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (68)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.solutions_to_string
                                                                    solutions1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (68)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (61)))))
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
                                                                    (Pulse_Typing_Combinators.list_as_vprop
                                                                    pure_conjuncts)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "maybe_infer_intro_exists: solutions after solving pure conjuncts ("
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    "): "))
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
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___7))
                                                                    uu___7)))
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
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    fun
                                                                    ty_opt ->
                                                                    fun e ->
                                                                    match ty_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Pulse_Syntax_Pure.tm_pureapp
                                                                    (Pulse_Syntax_Pure.tm_fvar
                                                                    (Pulse_Syntax_Base.as_fv
                                                                    Pulse_Reflection_Util.hide_lid))
                                                                    FStar_Pervasives_Native.None
                                                                    e
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ty ->
                                                                    Pulse_Syntax_Pure.tm_pureapp
                                                                    (Pulse_Syntax_Pure.tm_pureapp
                                                                    (Pulse_Syntax_Pure.tm_fvar
                                                                    (Pulse_Syntax_Base.as_fv
                                                                    Pulse_Reflection_Util.hide_lid))
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.Implicit)
                                                                    ty)
                                                                    FStar_Pervasives_Native.None
                                                                    e))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    mk_hide
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    fun uv ->
                                                                    match 
                                                                    FStar_List_Tot_Base.tryFind
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (u,
                                                                    uu___10)
                                                                    ->
                                                                    Pulse_Checker_Inference.uvar_eq
                                                                    u uv) uvs
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (uu___9,
                                                                    ty) ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ty))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    type_of_uvar
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (u, v) ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions1
                                                                    v))
                                                                    (fun sol
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    match 
                                                                    Pulse_Syntax_Pure.unreveal
                                                                    sol
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___10
                                                                    ->
                                                                    (u, sol)
                                                                    | 
                                                                    uu___10
                                                                    ->
                                                                    (u,
                                                                    (mk_hide
                                                                    (type_of_uvar
                                                                    u) sol)))))
                                                                    solutions1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    solutions2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (10)))))
                                                                    (match 
                                                                    Pulse_Checker_Inference.unsolved
                                                                    solutions2
                                                                    uvs
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    uvs1 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (126)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (126)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (125)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (124)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (125)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (u,
                                                                    uu___9)
                                                                    ->
                                                                    Pulse_Checker_Inference.uvar_to_string
                                                                    u) uvs1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_String.concat
                                                                    ", "
                                                                    uu___8))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "Could not instantiate existential variables "
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    "\n")))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (st.Pulse_Syntax_Base.range2))
                                                                    uu___8))
                                                                    uu___8)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    fun t2 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    = t2;
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range2)
                                                                    }))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun wr
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (build_instantiations
                                                                    solutions2
                                                                    insts))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    intro_exists_chain
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (fun vp
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions2
                                                                    vp))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    uu___9.Pulse_Syntax_Base.t))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Pure
                                                                    p -> 
                                                                    [p]
                                                                    | 
                                                                    p -> [])))
                                                                    pure_conjuncts))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    pure_conjuncts1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_List_Tot_Base.flatten
                                                                    pure_conjuncts1))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    pure_conjuncts2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (111)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_List_Tot_Base.fold_left
                                                                    (add_intro_pure
                                                                    intro_exists_chain.Pulse_Syntax_Base.range2)
                                                                    intro_exists_chain
                                                                    pure_conjuncts2))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    result ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (14)))))
                                                                    (if
                                                                    Pulse_RuntimeUtils.debug_at_level
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g)
                                                                    "inference"
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (220))
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
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    result))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Prims.strcat
                                                                    "Inferred pure and exists:{\n\t "
                                                                    (Prims.strcat
                                                                    uu___9
                                                                    "\n\t}")))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___9))
                                                                    uu___9)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> ()))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> result))))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                   uu___5)))
                                                    uu___3))) uu___1))) uu___)))
               uu___)
let rec (check' : Prims.bool -> Pulse_Checker_Common.check_t) =
  fun allow_inst ->
    fun g ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            fun t ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.fst"
                         (Prims.of_int (338)) (Prims.of_int (12))
                         (Prims.of_int (338)) (Prims.of_int (55)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.fst"
                         (Prims.of_int (340)) (Prims.of_int (6))
                         (Prims.of_int (355)) (Prims.of_int (50)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Pulse_Checker_Pure.push_context
                        (Pulse_Syntax_Printer.tag_of_st_term t)
                        t.Pulse_Syntax_Base.range2 g))
                (fun uu___ ->
                   (fun g1 ->
                      match t.Pulse_Syntax_Base.term1 with
                      | Pulse_Syntax_Base.Tm_Protect uu___ ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_V2_Derived.fail
                                  "Protect should have been removed"))
                      | Pulse_Syntax_Base.Tm_Abs uu___ ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_V2_Derived.fail
                                  "Tm_Abs check should not have been called in the checker"))
                      | Pulse_Syntax_Base.Tm_STApp uu___ ->
                          Obj.magic
                            (Obj.repr
                               (Pulse_Checker_STApp.check_stapp g1 t pre ()
                                  post_hint))
                      | Pulse_Syntax_Base.Tm_Bind uu___ ->
                          Obj.magic
                            (Obj.repr
                               (Pulse_Checker_Bind.check_bind g1 t pre ()
                                  post_hint (check' true)))
                      | uu___ ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_V2_Derived.fail
                                  "Checker form not implemented"))) uu___)
let (check : Pulse_Checker_Common.check_t) = check' true