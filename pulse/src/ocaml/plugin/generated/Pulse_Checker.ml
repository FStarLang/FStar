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
                         (Prims.of_int (342)) (Prims.of_int (4))
                         (Prims.of_int (342)) (Prims.of_int (47)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.fst"
                         (Prims.of_int (320)) (Prims.of_int (20))
                         (Prims.of_int (421)) (Prims.of_int (50)))))
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
                                        (Prims.of_int (344))
                                        (Prims.of_int (44))
                                        (Prims.of_int (417))
                                        (Prims.of_int (48)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (418))
                                        (Prims.of_int (4))
                                        (Prims.of_int (421))
                                        (Prims.of_int (50)))))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.fst"
                                              (Prims.of_int (345))
                                              (Prims.of_int (12))
                                              (Prims.of_int (345))
                                              (Prims.of_int (55)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.fst"
                                              (Prims.of_int (347))
                                              (Prims.of_int (4))
                                              (Prims.of_int (417))
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
                                                 Pulse_Syntax_Base.p2 =
                                                   uu___2;
                                                 Pulse_Syntax_Base.witnesses
                                                   = witnesses;
                                                 Pulse_Syntax_Base.should_check1
                                                   = uu___3;_}
                                               ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (363))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (369))
                                                                (Prims.of_int (19)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (371))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (379))
                                                                (Prims.of_int (77)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___4 ->
                                                             match witnesses
                                                             with
                                                             | w::[] ->
                                                                 (match 
                                                                    w.Pulse_Syntax_Base.t
                                                                  with
                                                                  | Pulse_Syntax_Base.Tm_Unknown
                                                                    -> true
                                                                  | uu___5 ->
                                                                    false)
                                                             | uu___5 -> true))
                                                       (fun uu___4 ->
                                                          (fun
                                                             should_infer_witnesses
                                                             ->
                                                             if
                                                               should_infer_witnesses
                                                             then
                                                               Obj.magic
                                                                 (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    "Pulse cannot yet infer witnesses for existential quantifiers; annotate them explicitly")
                                                             else
                                                               Obj.magic
                                                                 (Pulse_Checker_Exists.check_intro_exists_either
                                                                    g1 t
                                                                    FStar_Pervasives_Native.None
                                                                    pre ()
                                                                    post_hint))
                                                            uu___4)))
                                           | Pulse_Syntax_Base.Tm_Bind uu___1
                                               ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (Pulse_Checker_Bind.check_bind
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
                                                                (Prims.of_int (391))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (407))
                                                                (Prims.of_int (97)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (408))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (411))
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
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (37)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (37)))))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (402))
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
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (401))
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
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (63)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (408))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (411))
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