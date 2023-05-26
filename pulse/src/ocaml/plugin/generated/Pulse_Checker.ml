open Prims
let (terms_to_string :
  Pulse_Syntax_Base.term Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (32))
         (Prims.of_int (23)) (Prims.of_int (32)) (Prims.of_int (68)))
      (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (32))
         (Prims.of_int (4)) (Prims.of_int (32)) (Prims.of_int (68)))
      (Obj.magic
         (FStar_Tactics_Util.map Pulse_Syntax_Printer.term_to_string t))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_String.concat "\n" uu___))
let (has_pure_vprops : Pulse_Syntax_Base.term -> Prims.bool) =
  fun pre ->
    FStar_List_Tot_Base.existsb Pulse_Syntax_Base.uu___is_Tm_Pure
      (Pulse_Checker_Framing.vprop_as_list pre)
let (elim_pure_explicit_lid : Prims.string Prims.list) =
  Pulse_Reflection_Util.mk_steel_wrapper_lid "elim_pure_explicit"
let (default_binder_annot : Pulse_Syntax_Base.binder) =
  {
    Pulse_Syntax_Base.binder_ty = Pulse_Syntax_Base.Tm_Unknown;
    Pulse_Syntax_Base.binder_ppname = FStar_Reflection_Typing.pp_name_default
  }
let (maybe_add_elim_pure :
  Pulse_Syntax_Base.term Prims.list ->
    Pulse_Syntax_Base.st_term ->
      ((Prims.bool * Pulse_Syntax_Base.st_term), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun pre ->
         fun t ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   if
                     (FStar_List_Tot_Base.length
                        (FStar_List_Tot_Base.flatten
                           (FStar_List_Tot_Base.map
                              (fun t1 ->
                                 match t1 with
                                 | Pulse_Syntax_Base.Tm_Pure p -> [p]
                                 | uu___1 -> []) pre)))
                       = Prims.int_zero
                   then (false, t)
                   else
                     (true,
                       (FStar_List_Tot_Base.fold_left
                          (fun t1 ->
                             fun p ->
                               Pulse_Typing.wr
                                 (Pulse_Syntax_Base.Tm_Bind
                                    {
                                      Pulse_Syntax_Base.binder =
                                        default_binder_annot;
                                      Pulse_Syntax_Base.head1 =
                                        (Pulse_Typing.wr
                                           (Pulse_Syntax_Base.Tm_Protect
                                              {
                                                Pulse_Syntax_Base.t =
                                                  (Pulse_Typing.wr
                                                     (Pulse_Syntax_Base.Tm_STApp
                                                        {
                                                          Pulse_Syntax_Base.head
                                                            =
                                                            (Pulse_Syntax_Pure.tm_fvar
                                                               (Pulse_Syntax_Base.as_fv
                                                                  elim_pure_explicit_lid));
                                                          Pulse_Syntax_Base.arg_qual
                                                            =
                                                            FStar_Pervasives_Native.None;
                                                          Pulse_Syntax_Base.arg
                                                            = p
                                                        }))
                                              }));
                                      Pulse_Syntax_Base.body1 = t1
                                    })) t
                          (FStar_List_Tot_Base.flatten
                             (FStar_List_Tot_Base.map
                                (fun t1 ->
                                   match t1 with
                                   | Pulse_Syntax_Base.Tm_Pure p -> [p]
                                   | uu___2 -> []) pre))))))) uu___1 uu___
let rec (prepare_instantiations :
  (Pulse_Syntax_Base.vprop * (Pulse_Syntax_Base.term, Pulse_Syntax_Base.term)
    FStar_Pervasives.either) Prims.list ->
    Pulse_Checker_Inference.uvar_id Prims.list ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term Prims.list ->
          ((Pulse_Syntax_Base.vprop * (Pulse_Syntax_Base.vprop *
             (Pulse_Syntax_Base.term, Pulse_Syntax_Base.term)
             FStar_Pervasives.either) Prims.list *
             Pulse_Checker_Inference.uvar_id Prims.list),
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun out ->
             fun out_uvars ->
               fun goal_vprop ->
                 fun witnesses ->
                   match (witnesses, goal_vprop) with
                   | ([], Pulse_Syntax_Base.Tm_ExistsSL (u, ty, p, uu___)) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (81)) (Prims.of_int (37))
                                  (Prims.of_int (83)) (Prims.of_int (37)))
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (80)) (Prims.of_int (33))
                                  (Prims.of_int (85)) (Prims.of_int (89)))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (82))
                                        (Prims.of_int (22))
                                        (Prims.of_int (82))
                                        (Prims.of_int (57)))
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.fst"
                                        (Prims.of_int (81))
                                        (Prims.of_int (37))
                                        (Prims.of_int (83))
                                        (Prims.of_int (37)))
                                     (Obj.magic
                                        (Pulse_Checker_Inference.gen_uvar ()))
                                     (fun uu___1 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___2 ->
                                             match uu___1 with
                                             | (uv, t) ->
                                                 ((Pulse_Syntax_Naming.open_term'
                                                     p t Prims.int_zero),
                                                   (FStar_Pervasives.Inr t),
                                                   uv)))))
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     match uu___1 with
                                     | (next_goal_vprop, inst, uv) ->
                                         Obj.magic
                                           (prepare_instantiations
                                              ((goal_vprop, inst) :: out) (uv
                                              :: out_uvars) next_goal_vprop
                                              [])) uu___1)))
                   | ([], uu___) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> (goal_vprop, out, out_uvars))))
                   | (t::witnesses1, Pulse_Syntax_Base.Tm_ExistsSL
                      (u, ty, p, uu___)) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (92)) (Prims.of_int (10))
                                  (Prims.of_int (97)) (Prims.of_int (39)))
                               (FStar_Range.mk_range "Pulse.Checker.fst"
                                  (Prims.of_int (90)) (Prims.of_int (45))
                                  (Prims.of_int (99)) (Prims.of_int (96)))
                               (match t with
                                | Pulse_Syntax_Base.Tm_Unknown ->
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (94))
                                               (Prims.of_int (24))
                                               (Prims.of_int (94))
                                               (Prims.of_int (59)))
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (93))
                                               (Prims.of_int (25))
                                               (Prims.of_int (95))
                                               (Prims.of_int (41)))
                                            (Obj.magic
                                               (Pulse_Checker_Inference.gen_uvar
                                                  ()))
                                            (fun uu___1 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 ->
                                                    match uu___1 with
                                                    | (uv, t1) ->
                                                        ((Pulse_Syntax_Naming.open_term'
                                                            p t1
                                                            Prims.int_zero),
                                                          (FStar_Pervasives.Inr
                                                             t1), [uv])))))
                                | uu___1 ->
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 ->
                                               ((Pulse_Syntax_Naming.open_term'
                                                   p t Prims.int_zero),
                                                 (FStar_Pervasives.Inl t),
                                                 [])))))
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     match uu___1 with
                                     | (next_goal_vprop, inst, uvs) ->
                                         Obj.magic
                                           (prepare_instantiations
                                              ((goal_vprop, inst) :: out)
                                              (FStar_List_Tot_Base.op_At uvs
                                                 out_uvars) next_goal_vprop
                                              witnesses1)) uu___1)))
                   | uu___ ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Derived.fail
                               "Unexpected number of instantiations in intro")))
            uu___3 uu___2 uu___1 uu___
let (maybe_infer_intro_exists :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun st ->
      fun pre ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (110))
             (Prims.of_int (33)) (Prims.of_int (122)) (Prims.of_int (18)))
          (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (123))
             (Prims.of_int (6)) (Prims.of_int (232)) (Prims.of_int (40)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                fun t ->
                  match FStar_List_Tot_Base.partition
                          (fun uu___1 ->
                             match uu___1 with
                             | Pulse_Syntax_Base.Tm_Pure uu___2 -> false
                             | Pulse_Syntax_Base.Tm_Emp -> false
                             | uu___2 -> true)
                          (Pulse_Checker_Framing.vprop_as_list t)
                  with
                  | (rest, pure) ->
                      (((match Pulse_Checker_Framing.list_as_vprop rest with
                         | Pulse_Syntax_Base.Tm_Star
                             (t1, Pulse_Syntax_Base.Tm_Emp) -> t1
                         | Pulse_Syntax_Base.Tm_Star
                             (Pulse_Syntax_Base.Tm_Emp, t1) -> t1
                         | t1 -> t1)), pure)))
          (fun uu___ ->
             (fun remove_pure_conjuncts ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Checker.fst"
                        (Prims.of_int (143)) (Prims.of_int (50))
                        (Prims.of_int (143)) (Prims.of_int (57)))
                     (FStar_Range.mk_range "Pulse.Checker.fst"
                        (Prims.of_int (123)) (Prims.of_int (6))
                        (Prims.of_int (232)) (Prims.of_int (40)))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ -> st.Pulse_Syntax_Base.term1))
                     (fun uu___ ->
                        (fun uu___ ->
                           match uu___ with
                           | Pulse_Syntax_Base.Tm_IntroExists
                               { Pulse_Syntax_Base.erased = erased;
                                 Pulse_Syntax_Base.p1 = t;
                                 Pulse_Syntax_Base.witnesses = witnesses;_}
                               ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (144))
                                       (Prims.of_int (28))
                                       (Prims.of_int (144))
                                       (Prims.of_int (43)))
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (143))
                                       (Prims.of_int (60))
                                       (Prims.of_int (232))
                                       (Prims.of_int (40)))
                                    (Obj.magic
                                       (Pulse_Checker_Pure.check_vprop g t))
                                    (fun uu___1 ->
                                       (fun uu___1 ->
                                          match uu___1 with
                                          | Prims.Mkdtuple2 (t1, t_typing) ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.fst"
                                                      (Prims.of_int (145))
                                                      (Prims.of_int (33))
                                                      (Prims.of_int (145))
                                                      (Prims.of_int (73)))
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.fst"
                                                      (Prims.of_int (144))
                                                      (Prims.of_int (46))
                                                      (Prims.of_int (232))
                                                      (Prims.of_int (40)))
                                                   (Obj.magic
                                                      (prepare_instantiations
                                                         [] [] t1 witnesses))
                                                   (fun uu___2 ->
                                                      (fun uu___2 ->
                                                         match uu___2 with
                                                         | (goal_vprop,
                                                            insts, uvs) ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (69)))
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (40)))
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    remove_pure_conjuncts
                                                                    goal_vprop))
                                                                  (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (goal_vprop1,
                                                                    pure_conjuncts)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (79)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (40)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.try_inst_uvs_in_goal
                                                                    pre
                                                                    goal_vprop1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    solutions
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (22)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun
                                                                    solutions1
                                                                    ->
                                                                    fun p ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (64)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (22)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Checker_Inference.apply_solution
                                                                    solutions1
                                                                    p))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun p1
                                                                    ->
                                                                    match p1
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Pure
                                                                    p2 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    Pulse_Syntax_Pure.is_eq2
                                                                    p2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (l, r) ->
                                                                    Obj.repr
                                                                    (if
                                                                    (Pulse_Checker_Inference.contains_uvar
                                                                    l) ||
                                                                    (Pulse_Checker_Inference.contains_uvar
                                                                    r)
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (38)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (28)))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Inference.try_unify
                                                                    l r))
                                                                    (fun sols
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    sols
                                                                    solutions1)))
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    solutions1)))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    solutions1))))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    solutions1))))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    maybe_solve_pure
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (73)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (40)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.fold_left
                                                                    maybe_solve_pure
                                                                    solutions
                                                                    pure_conjuncts))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    solutions1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (28)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun e ->
                                                                    Pulse_Syntax_Pure.tm_pureapp
                                                                    (Pulse_Syntax_Pure.tm_fvar
                                                                    (Pulse_Syntax_Base.as_fv
                                                                    Pulse_Reflection_Util.hide_lid))
                                                                    FStar_Pervasives_Native.None
                                                                    e))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    mk_hide
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (17)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_List_Tot_Base.map
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (u, v) ->
                                                                    (match 
                                                                    Pulse_Syntax_Pure.unreveal
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions1
                                                                    v)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___6 ->
                                                                    (u,
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions1
                                                                    v))
                                                                    | 
                                                                    uu___6 ->
                                                                    (u,
                                                                    (mk_hide
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions1
                                                                    v)))))
                                                                    solutions1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    solutions2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (18)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (40)))
                                                                    (match 
                                                                    FStar_List_Tot_Base.tryFind
                                                                    (fun u ->
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    (FStar_List_Tot_Base.tryFind
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (u',
                                                                    uu___5)
                                                                    -> 
                                                                    u = u')
                                                                    solutions2))
                                                                    uvs
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    u ->
                                                                    FStar_Tactics_Derived.fail
                                                                    (Prims.strcat
                                                                    "maybe_infer_intro_exists: unification failed for uvar "
                                                                    (Prims.strcat
                                                                    (Pulse_Checker_Inference.uvar_id_to_string
                                                                    u) "\n"))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (43)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun t2 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    = t2;
                                                                    Pulse_Syntax_Base.range
                                                                    =
                                                                    (st.Pulse_Syntax_Base.range)
                                                                    }))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun wr
                                                                    ->
                                                                    let rec build_instantiations
                                                                    solutions3
                                                                    insts1 =
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (v, i) ->
                                                                    (match i
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Inl
                                                                    user_provided
                                                                    ->
                                                                    wr
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.erased
                                                                    = false;
                                                                    Pulse_Syntax_Base.p1
                                                                    =
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions3
                                                                    v);
                                                                    Pulse_Syntax_Base.witnesses
                                                                    =
                                                                    [user_provided]
                                                                    })
                                                                    | 
                                                                    FStar_Pervasives.Inr
                                                                    inferred
                                                                    ->
                                                                    (match 
                                                                    Pulse_Syntax_Pure.unreveal
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions3
                                                                    inferred)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    sol ->
                                                                    wr
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.erased
                                                                    = true;
                                                                    Pulse_Syntax_Base.p1
                                                                    =
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions3
                                                                    v);
                                                                    Pulse_Syntax_Base.witnesses
                                                                    = [sol]
                                                                    })
                                                                    | 
                                                                    uu___7 ->
                                                                    wr
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.erased
                                                                    = true;
                                                                    Pulse_Syntax_Base.p1
                                                                    =
                                                                    (Pulse_Checker_Inference.apply_solution
                                                                    solutions3
                                                                    v);
                                                                    Pulse_Syntax_Base.witnesses
                                                                    =
                                                                    [
                                                                    Pulse_Checker_Inference.apply_solution
                                                                    solutions3
                                                                    inferred]
                                                                    })))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    one_inst
                                                                    ->
                                                                    match insts1
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Impossible"))
                                                                    | 
                                                                    hd::[] ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    wr
                                                                    (Pulse_Syntax_Base.Tm_Protect
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    =
                                                                    (one_inst
                                                                    hd)
                                                                    }))))
                                                                    | 
                                                                    hd::tl ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (92)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (92)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (89)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (92)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (89)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (89)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (89)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (89)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (86)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (89)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (86)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (86)))
                                                                    (Obj.magic
                                                                    (build_instantiations
                                                                    solutions3
                                                                    tl))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    =
                                                                    default_binder_annot;
                                                                    Pulse_Syntax_Base.head1
                                                                    =
                                                                    (wr
                                                                    (Pulse_Syntax_Base.Tm_Protect
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    =
                                                                    (one_inst
                                                                    hd)
                                                                    }));
                                                                    Pulse_Syntax_Base.body1
                                                                    = uu___5
                                                                    }))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Base.Tm_Bind
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    wr uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    = uu___5
                                                                    }))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Base.Tm_Protect
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    wr uu___5)))))
                                                                    uu___5) in
                                                                    Obj.magic
                                                                    (build_instantiations
                                                                    solutions2
                                                                    insts))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                        uu___2))) uu___1)))
                          uu___))) uu___)
let (range_of_head :
  Pulse_Syntax_Base.st_term ->
    (Pulse_Syntax_Base.term * Pulse_Syntax_Base.range)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    match t.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_STApp
        { Pulse_Syntax_Base.head = head; Pulse_Syntax_Base.arg_qual = uu___;
          Pulse_Syntax_Base.arg = uu___1;_}
        ->
        let rec aux t1 =
          match t1 with
          | Pulse_Syntax_Base.Tm_FStar (uu___2, r) -> (t1, r)
          | uu___2 -> (t1, FStar_Range.range_0) in
        FStar_Pervasives_Native.Some (aux head)
    | uu___ -> FStar_Pervasives_Native.None
let (tag_of_term : Pulse_Syntax_Base.term -> Prims.string) =
  fun t ->
    match t with
    | Pulse_Syntax_Base.Tm_Emp -> "Tm_Emp"
    | Pulse_Syntax_Base.Tm_Pure uu___ -> "Tm_Pure"
    | Pulse_Syntax_Base.Tm_Star (uu___, uu___1) -> "Tm_Star"
    | Pulse_Syntax_Base.Tm_ExistsSL (uu___, uu___1, uu___2, uu___3) ->
        "Tm_ExistsSL"
    | Pulse_Syntax_Base.Tm_ForallSL (uu___, uu___1, uu___2) -> "Tm_ForallSL"
    | Pulse_Syntax_Base.Tm_VProp -> "Tm_VProp"
    | Pulse_Syntax_Base.Tm_Inames -> "Tm_Inames"
    | Pulse_Syntax_Base.Tm_EmpInames -> "Tm_EmpInames"
    | Pulse_Syntax_Base.Tm_Unknown -> "Tm_Unknown"
    | Pulse_Syntax_Base.Tm_FStar (uu___, uu___1) -> "Tm_FStar"
let (tag_of_st_term : Pulse_Syntax_Base.st_term -> Prims.string) =
  fun t ->
    match t.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_Return uu___ -> "Tm_Return"
    | Pulse_Syntax_Base.Tm_Abs uu___ -> "Tm_Abs"
    | Pulse_Syntax_Base.Tm_STApp uu___ -> "Tm_STApp"
    | Pulse_Syntax_Base.Tm_Bind uu___ -> "Tm_Bind"
    | Pulse_Syntax_Base.Tm_TotBind uu___ -> "Tm_TotBind"
    | Pulse_Syntax_Base.Tm_If uu___ -> "Tm_If"
    | Pulse_Syntax_Base.Tm_ElimExists uu___ -> "Tm_ElimExists"
    | Pulse_Syntax_Base.Tm_IntroExists uu___ -> "Tm_IntroExists"
    | Pulse_Syntax_Base.Tm_While uu___ -> "Tm_While"
    | Pulse_Syntax_Base.Tm_Par uu___ -> "Tm_Par"
    | Pulse_Syntax_Base.Tm_WithLocal uu___ -> "Tm_WithLocal"
    | Pulse_Syntax_Base.Tm_Rewrite uu___ -> "Tm_Rewrite"
    | Pulse_Syntax_Base.Tm_Admit uu___ -> "Tm_Admit"
    | Pulse_Syntax_Base.Tm_Protect uu___ -> "Tm_Protect"
let (maybe_log :
  Pulse_Syntax_Base.st_term -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (278))
         (Prims.of_int (4)) (Prims.of_int (284)) (Prims.of_int (16)))
      (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (286))
         (Prims.of_int (2)) (Prims.of_int (308)) (Prims.of_int (11)))
      (match range_of_head t with
       | FStar_Pervasives_Native.Some (head, range) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Checker.fst"
                      (Prims.of_int (280)) (Prims.of_int (14))
                      (Prims.of_int (283)) (Prims.of_int (49)))
                   (FStar_Range.mk_range "Pulse.Checker.fst"
                      (Prims.of_int (280)) (Prims.of_int (6))
                      (Prims.of_int (283)) (Prims.of_int (49)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range "Pulse.Checker.fst"
                            (Prims.of_int (283)) (Prims.of_int (25))
                            (Prims.of_int (283)) (Prims.of_int (48)))
                         (FStar_Range.mk_range "Pulse.Checker.fst"
                            (Prims.of_int (280)) (Prims.of_int (14))
                            (Prims.of_int (283)) (Prims.of_int (49)))
                         (Obj.magic
                            (Pulse_Syntax_Printer.term_to_string head))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (280))
                                       (Prims.of_int (14))
                                       (Prims.of_int (283))
                                       (Prims.of_int (49)))
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (280))
                                       (Prims.of_int (14))
                                       (Prims.of_int (283))
                                       (Prims.of_int (49)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (280))
                                             (Prims.of_int (14))
                                             (Prims.of_int (283))
                                             (Prims.of_int (49)))
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (280))
                                             (Prims.of_int (14))
                                             (Prims.of_int (283))
                                             (Prims.of_int (49)))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.fst"
                                                   (Prims.of_int (281))
                                                   (Prims.of_int (25))
                                                   (Prims.of_int (281))
                                                   (Prims.of_int (50)))
                                                (FStar_Range.mk_range
                                                   "FStar.Printf.fst"
                                                   (Prims.of_int (121))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (123))
                                                   (Prims.of_int (44)))
                                                (Obj.magic
                                                   (FStar_Tactics_Builtins.range_to_string
                                                      range))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        fun x ->
                                                          fun x1 ->
                                                            Prims.strcat
                                                              (Prims.strcat
                                                                 (Prims.strcat
                                                                    "At location "
                                                                    (
                                                                    Prims.strcat
                                                                    uu___1
                                                                    ": Checking app with head ("))
                                                                 (Prims.strcat
                                                                    x ") = "))
                                                              (Prims.strcat
                                                                 x1 "")))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  uu___1 (tag_of_term head)))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 -> uu___1 uu___))))
                              uu___)))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic (FStar_Tactics_Builtins.print uu___))
                        uu___)))
       | FStar_Pervasives_Native.None ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ()))))
      (fun uu___ ->
         (fun uu___ ->
            match t.Pulse_Syntax_Base.term1 with
            | Pulse_Syntax_Base.Tm_STApp
                { Pulse_Syntax_Base.head = head;
                  Pulse_Syntax_Base.arg_qual = FStar_Pervasives_Native.None;
                  Pulse_Syntax_Base.arg = p;_}
                ->
                Obj.magic
                  (Obj.repr
                     (match Pulse_Syntax_Pure.is_fvar head with
                      | FStar_Pervasives_Native.Some (l, uu___1) ->
                          Obj.repr
                            (if l = elim_pure_explicit_lid
                             then
                               Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (291))
                                       (Prims.of_int (25))
                                       (Prims.of_int (292))
                                       (Prims.of_int (46)))
                                    (FStar_Range.mk_range "Pulse.Checker.fst"
                                       (Prims.of_int (291))
                                       (Prims.of_int (17))
                                       (Prims.of_int (292))
                                       (Prims.of_int (46)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.fst"
                                             (Prims.of_int (292))
                                             (Prims.of_int (25))
                                             (Prims.of_int (292))
                                             (Prims.of_int (45)))
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (Pulse_Syntax_Printer.term_to_string
                                                p))
                                          (fun uu___2 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___3 ->
                                                  Prims.strcat
                                                    "LOG ELIM PURE: "
                                                    (Prims.strcat uu___2 "\n")))))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          Obj.magic
                                            (FStar_Tactics_Builtins.print
                                               uu___2)) uu___2))
                             else
                               Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___3 -> ())))
                      | uu___1 ->
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 -> ()))))
            | Pulse_Syntax_Base.Tm_STApp
                { Pulse_Syntax_Base.head = head;
                  Pulse_Syntax_Base.arg_qual = FStar_Pervasives_Native.None;
                  Pulse_Syntax_Base.arg = uu___1;_}
                ->
                Obj.magic
                  (Obj.repr
                     (match Pulse_Syntax_Pure.is_pure_app head with
                      | FStar_Pervasives_Native.Some
                          (head1, FStar_Pervasives_Native.None, p) ->
                          Obj.repr
                            (match Pulse_Syntax_Pure.is_fvar head1 with
                             | FStar_Pervasives_Native.Some (l, uu___2) ->
                                 Obj.repr
                                   (if
                                      l =
                                        (Pulse_Reflection_Util.mk_steel_wrapper_lid
                                           "intro_pure")
                                    then
                                      Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.fst"
                                              (Prims.of_int (302))
                                              (Prims.of_int (33))
                                              (Prims.of_int (303))
                                              (Prims.of_int (54)))
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.fst"
                                              (Prims.of_int (302))
                                              (Prims.of_int (25))
                                              (Prims.of_int (303))
                                              (Prims.of_int (54)))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.fst"
                                                    (Prims.of_int (303))
                                                    (Prims.of_int (33))
                                                    (Prims.of_int (303))
                                                    (Prims.of_int (53)))
                                                 (FStar_Range.mk_range
                                                    "prims.fst"
                                                    (Prims.of_int (590))
                                                    (Prims.of_int (19))
                                                    (Prims.of_int (590))
                                                    (Prims.of_int (31)))
                                                 (Obj.magic
                                                    (Pulse_Syntax_Printer.term_to_string
                                                       p))
                                                 (fun uu___3 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___4 ->
                                                         Prims.strcat
                                                           "LOG INTRO PURE: "
                                                           (Prims.strcat
                                                              uu___3 "\n")))))
                                           (fun uu___3 ->
                                              (fun uu___3 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Builtins.print
                                                      uu___3)) uu___3))
                                    else
                                      Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 -> ())))
                             | uu___2 ->
                                 Obj.repr
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___3 -> ())))
                      | uu___2 ->
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 -> ()))))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))))
           uu___)
let (handle_framing_failure :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Checker_Common.post_hint_opt ->
            Pulse_Checker_Framing.framing_failure ->
              Pulse_Checker_Common.check_t ->
                ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
                   (unit, unit, unit) Pulse_Typing.st_typing)
                   FStar_Pervasives.dtuple3,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t0 ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            fun failure ->
              fun check ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (321)) (Prims.of_int (17))
                     (Prims.of_int (321)) (Prims.of_int (43)))
                  (FStar_Range.mk_range "Pulse.Checker.fst"
                     (Prims.of_int (321)) (Prims.of_int (48))
                     (Prims.of_int (388)) (Prims.of_int (30)))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        fun t ->
                          {
                            Pulse_Syntax_Base.term1 = t;
                            Pulse_Syntax_Base.range =
                              (t0.Pulse_Syntax_Base.range)
                          }))
                  (fun uu___ ->
                     (fun wr ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (322)) (Prims.of_int (28))
                                (Prims.of_int (339)) (Prims.of_int (7)))
                             (FStar_Range.mk_range "Pulse.Checker.fst"
                                (Prims.of_int (340)) (Prims.of_int (6))
                                (Prims.of_int (388)) (Prims.of_int (30)))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ ->
                                   fun p ->
                                     fun t ->
                                       wr
                                         (Pulse_Syntax_Base.Tm_Protect
                                            {
                                              Pulse_Syntax_Base.t =
                                                (wr
                                                   (Pulse_Syntax_Base.Tm_Bind
                                                      {
                                                        Pulse_Syntax_Base.binder
                                                          =
                                                          default_binder_annot;
                                                        Pulse_Syntax_Base.head1
                                                          =
                                                          (wr
                                                             (Pulse_Syntax_Base.Tm_Protect
                                                                {
                                                                  Pulse_Syntax_Base.t
                                                                    =
                                                                    (
                                                                    wr
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    =
                                                                    (Pulse_Syntax_Pure.tm_pureapp
                                                                    (Pulse_Syntax_Pure.tm_fvar
                                                                    (Pulse_Syntax_Base.as_fv
                                                                    (Pulse_Reflection_Util.mk_steel_wrapper_lid
                                                                    "intro_pure")))
                                                                    FStar_Pervasives_Native.None
                                                                    p);
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    Pulse_Syntax_Base.arg
                                                                    =
                                                                    (Pulse_Syntax_Pure.tm_constant
                                                                    FStar_Reflection_Data.C_Unit)
                                                                    }))
                                                                }));
                                                        Pulse_Syntax_Base.body1
                                                          = t
                                                      }))
                                            })))
                             (fun uu___ ->
                                (fun add_intro_pure ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (348))
                                           (Prims.of_int (6))
                                           (Prims.of_int (348))
                                           (Prims.of_int (91)))
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.fst"
                                           (Prims.of_int (340))
                                           (Prims.of_int (6))
                                           (Prims.of_int (388))
                                           (Prims.of_int (30)))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___ ->
                                              FStar_List_Tot_Base.partition
                                                (fun uu___1 ->
                                                   match uu___1 with
                                                   | Pulse_Syntax_Base.Tm_Pure
                                                       uu___2 -> true
                                                   | uu___2 -> false)
                                                failure.Pulse_Checker_Framing.unmatched_preconditions))
                                        (fun uu___ ->
                                           (fun uu___ ->
                                              match uu___ with
                                              | (pures, rest) ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (351))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (357))
                                                          (Prims.of_int (13)))
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (358))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (388))
                                                          (Prims.of_int (30)))
                                                       (Obj.magic
                                                          (FStar_Tactics_Util.fold_left
                                                             (fun uu___2 ->
                                                                fun uu___1 ->
                                                                  (fun t ->
                                                                    fun p ->
                                                                    match p
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Pure
                                                                    p1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    add_intro_pure
                                                                    p1 t))
                                                                    | 
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Impossible"))
                                                                    uu___2
                                                                    uu___1)
                                                             (wr
                                                                (Pulse_Syntax_Base.Tm_Protect
                                                                   {
                                                                    Pulse_Syntax_Base.t
                                                                    = t0
                                                                   })) pures))
                                                       (fun uu___1 ->
                                                          (fun t ->
                                                             let rec handle_intro_exists
                                                               rest1 t1 =
                                                               match rest1
                                                               with
                                                               | [] ->
                                                                   check g t1
                                                                    pre ()
                                                                    post_hint
                                                               | (Pulse_Syntax_Base.Tm_ExistsSL
                                                                   (u, ty, p,
                                                                    se))::rest2
                                                                   ->
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (378))
                                                                    (Prims.of_int (15)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    =
                                                                    default_binder_annot;
                                                                    Pulse_Syntax_Base.head1
                                                                    =
                                                                    (wr
                                                                    (Pulse_Syntax_Base.Tm_Protect
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    =
                                                                    (wr
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.erased
                                                                    = true;
                                                                    Pulse_Syntax_Base.p1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (u, ty,
                                                                    p, se));
                                                                    Pulse_Syntax_Base.witnesses
                                                                    = []
                                                                    }))
                                                                    }));
                                                                    Pulse_Syntax_Base.body1
                                                                    =
                                                                    (wr
                                                                    (Pulse_Syntax_Base.Tm_Protect
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    = t1
                                                                    }))
                                                                    }))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (handle_intro_exists
                                                                    rest2
                                                                    (wr t2)))
                                                                    uu___1)
                                                               | uu___1 ->
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (47)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    t0))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (66)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (terms_to_string
                                                                    failure.Pulse_Checker_Framing.remaining_context))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (45)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (terms_to_string
                                                                    rest1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Failed to satisfy the following preconditions:\n"
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    "\nContext has\n"))
                                                                    (Prims.strcat
                                                                    x
                                                                    "\nat command "))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
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
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    uu___2))))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___2) in
                                                             Obj.magic
                                                               (handle_intro_exists
                                                                  rest t))
                                                            uu___1))) uu___)))
                                  uu___))) uu___)
let rec (maybe_add_elims :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term Prims.list ->
      Pulse_Syntax_Base.st_term ->
        (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (395))
             (Prims.of_int (18)) (Prims.of_int (395)) (Prims.of_int (44)))
          (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (396))
             (Prims.of_int (4)) (Prims.of_int (426)) (Prims.of_int (30)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                fun t' ->
                  {
                    Pulse_Syntax_Base.term1 = t';
                    Pulse_Syntax_Base.range = (t.Pulse_Syntax_Base.range)
                  }))
          (fun uu___ ->
             (fun wr ->
                match ctxt with
                | [] ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t)))
                | (Pulse_Syntax_Base.Tm_ExistsSL (u, ty, b, se))::rest ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range "Pulse.Checker.fst"
                               (Prims.of_int (399)) (Prims.of_int (14))
                               (Prims.of_int (399)) (Prims.of_int (86)))
                            (FStar_Range.mk_range "Pulse.Checker.fst"
                               (Prims.of_int (399)) (Prims.of_int (89))
                               (Prims.of_int (409)) (Prims.of_int (35)))
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ ->
                                  wr
                                    (Pulse_Syntax_Base.Tm_Protect
                                       {
                                         Pulse_Syntax_Base.t =
                                           (wr
                                              (Pulse_Syntax_Base.Tm_ElimExists
                                                 {
                                                   Pulse_Syntax_Base.p =
                                                     (Pulse_Syntax_Base.Tm_ExistsSL
                                                        (u, ty, b, se))
                                                 }))
                                       })))
                            (fun uu___ ->
                               (fun e ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.fst"
                                          (Prims.of_int (400))
                                          (Prims.of_int (14))
                                          (Prims.of_int (400))
                                          (Prims.of_int (21)))
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.fst"
                                          (Prims.of_int (400))
                                          (Prims.of_int (24))
                                          (Prims.of_int (409))
                                          (Prims.of_int (35)))
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___ -> Pulse_Typing.fresh g))
                                       (fun uu___ ->
                                          (fun x ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (401))
                                                     (Prims.of_int (15))
                                                     (Prims.of_int (401))
                                                     (Prims.of_int (24)))
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.fst"
                                                     (Prims.of_int (401))
                                                     (Prims.of_int (27))
                                                     (Prims.of_int (409))
                                                     (Prims.of_int (35)))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___ ->
                                                        Pulse_Syntax_Base.v_as_nv
                                                          x))
                                                  (fun uu___ ->
                                                     (fun px ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (402))
                                                                (Prims.of_int (14))
                                                                (Prims.of_int (402))
                                                                (Prims.of_int (33)))
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (402))
                                                                (Prims.of_int (36))
                                                                (Prims.of_int (409))
                                                                (Prims.of_int (35)))
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___ ->
                                                                   Pulse_Typing.extend
                                                                    x
                                                                    (FStar_Pervasives.Inl
                                                                    ty) g))
                                                             (fun uu___ ->
                                                                (fun g1 ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (31)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (409))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    b px))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun b1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (37)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (409))
                                                                    (Prims.of_int (35)))
                                                                    (Obj.magic
                                                                    (maybe_add_elims
                                                                    g1 [b1] t))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun t1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (31)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (409))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    t1 x))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (408))
                                                                    (Prims.of_int (54)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (409))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (409))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    =
                                                                    default_binder_annot;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e;
                                                                    Pulse_Syntax_Base.body1
                                                                    =
                                                                    (wr
                                                                    (Pulse_Syntax_Base.Tm_Protect
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    = t2
                                                                    }))
                                                                    }))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun t3
                                                                    ->
                                                                    Obj.magic
                                                                    (maybe_add_elims
                                                                    g1 rest
                                                                    (wr t3)))
                                                                    uu___)))
                                                                    uu___)))
                                                                    uu___)))
                                                                    uu___)))
                                                                  uu___)))
                                                       uu___))) uu___)))
                                 uu___)))
                | (Pulse_Syntax_Base.Tm_Pure p)::rest ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range "Pulse.Checker.fst"
                               (Prims.of_int (412)) (Prims.of_int (8))
                               (Prims.of_int (414)) (Prims.of_int (33)))
                            (FStar_Range.mk_range "Pulse.Checker.fst"
                               (Prims.of_int (416)) (Prims.of_int (6))
                               (Prims.of_int (420)) (Prims.of_int (7)))
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ ->
                                  wr
                                    (Pulse_Syntax_Base.Tm_STApp
                                       {
                                         Pulse_Syntax_Base.head =
                                           (Pulse_Syntax_Pure.tm_fvar
                                              (Pulse_Syntax_Base.as_fv
                                                 elim_pure_explicit_lid));
                                         Pulse_Syntax_Base.arg_qual =
                                           FStar_Pervasives_Native.None;
                                         Pulse_Syntax_Base.arg = p
                                       })))
                            (fun uu___ ->
                               (fun elim_pure_tm ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.fst"
                                          (Prims.of_int (416))
                                          (Prims.of_int (9))
                                          (Prims.of_int (420))
                                          (Prims.of_int (7)))
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.fst"
                                          (Prims.of_int (416))
                                          (Prims.of_int (6))
                                          (Prims.of_int (420))
                                          (Prims.of_int (7)))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.fst"
                                                (Prims.of_int (417))
                                                (Prims.of_int (18))
                                                (Prims.of_int (419))
                                                (Prims.of_int (73)))
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.fst"
                                                (Prims.of_int (416))
                                                (Prims.of_int (9))
                                                (Prims.of_int (420))
                                                (Prims.of_int (7)))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.fst"
                                                      (Prims.of_int (419))
                                                      (Prims.of_int (25))
                                                      (Prims.of_int (419))
                                                      (Prims.of_int (73)))
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.fst"
                                                      (Prims.of_int (417))
                                                      (Prims.of_int (18))
                                                      (Prims.of_int (419))
                                                      (Prims.of_int (73)))
                                                   (Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.fst"
                                                            (Prims.of_int (419))
                                                            (Prims.of_int (28))
                                                            (Prims.of_int (419))
                                                            (Prims.of_int (73)))
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.fst"
                                                            (Prims.of_int (419))
                                                            (Prims.of_int (25))
                                                            (Prims.of_int (419))
                                                            (Prims.of_int (73)))
                                                         (Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (419))
                                                                  (Prims.of_int (42))
                                                                  (Prims.of_int (419))
                                                                  (Prims.of_int (70)))
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.fst"
                                                                  (Prims.of_int (419))
                                                                  (Prims.of_int (28))
                                                                  (Prims.of_int (419))
                                                                  (Prims.of_int (73)))
                                                               (Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (70)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (70)))
                                                                    (Obj.magic
                                                                    (maybe_add_elims
                                                                    g rest t))
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    = uu___
                                                                    }))))
                                                               (fun uu___ ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___1 ->
                                                                    Pulse_Syntax_Base.Tm_Protect
                                                                    uu___))))
                                                         (fun uu___ ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___1 ->
                                                                 wr uu___))))
                                                   (fun uu___ ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           {
                                                             Pulse_Syntax_Base.binder
                                                               =
                                                               default_binder_annot;
                                                             Pulse_Syntax_Base.head1
                                                               =
                                                               (wr
                                                                  (Pulse_Syntax_Base.Tm_Protect
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    =
                                                                    elim_pure_tm
                                                                    }));
                                                             Pulse_Syntax_Base.body1
                                                               = uu___
                                                           }))))
                                             (fun uu___ ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___1 ->
                                                     Pulse_Syntax_Base.Tm_Bind
                                                       uu___))))
                                       (fun uu___ ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___1 -> wr uu___)))) uu___)))
                | (Pulse_Syntax_Base.Tm_Star (p, q))::rest ->
                    Obj.magic
                      (Obj.repr (maybe_add_elims g (p :: q :: rest) t))
                | uu___::rest ->
                    Obj.magic (Obj.repr (maybe_add_elims g rest t))) uu___)
let rec (unprotect : Pulse_Syntax_Base.st_term -> Pulse_Syntax_Base.st_term)
  =
  fun t ->
    let wr t0 =
      {
        Pulse_Syntax_Base.term1 = t0;
        Pulse_Syntax_Base.range = (t.Pulse_Syntax_Base.range)
      } in
    let protect t1 =
      {
        Pulse_Syntax_Base.term1 =
          (Pulse_Syntax_Base.Tm_Protect { Pulse_Syntax_Base.t = t1 });
        Pulse_Syntax_Base.range = (t1.Pulse_Syntax_Base.range)
      } in
    match t.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_Protect
        {
          Pulse_Syntax_Base.t =
            {
              Pulse_Syntax_Base.term1 = Pulse_Syntax_Base.Tm_Bind
                { Pulse_Syntax_Base.binder = binder;
                  Pulse_Syntax_Base.head1 = head;
                  Pulse_Syntax_Base.body1 = body;_};
              Pulse_Syntax_Base.range = uu___;_};_}
        ->
        wr
          (Pulse_Syntax_Base.Tm_Bind
             {
               Pulse_Syntax_Base.binder = binder;
               Pulse_Syntax_Base.head1 = (protect head);
               Pulse_Syntax_Base.body1 = body
             })
    | Pulse_Syntax_Base.Tm_Protect
        {
          Pulse_Syntax_Base.t =
            {
              Pulse_Syntax_Base.term1 = Pulse_Syntax_Base.Tm_If
                { Pulse_Syntax_Base.b1 = b; Pulse_Syntax_Base.then_ = then_;
                  Pulse_Syntax_Base.else_ = else_;
                  Pulse_Syntax_Base.post2 = post;_};
              Pulse_Syntax_Base.range = uu___;_};_}
        ->
        wr
          (Pulse_Syntax_Base.Tm_If
             {
               Pulse_Syntax_Base.b1 = b;
               Pulse_Syntax_Base.then_ = (protect then_);
               Pulse_Syntax_Base.else_ = (protect else_);
               Pulse_Syntax_Base.post2 = post
             })
    | Pulse_Syntax_Base.Tm_Protect { Pulse_Syntax_Base.t = t1;_} ->
        unprotect t1
    | uu___ -> t
let (auto_elims :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.st_term ->
        (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun ctxt ->
             fun t ->
               match t.Pulse_Syntax_Base.term1 with
               | Pulse_Syntax_Base.Tm_Protect uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> unprotect t)))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (444)) (Prims.of_int (15))
                              (Prims.of_int (444)) (Prims.of_int (33)))
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (444)) (Prims.of_int (36))
                              (Prims.of_int (446)) (Prims.of_int (15)))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 Pulse_Checker_Framing.vprop_as_list ctxt))
                           (fun uu___1 ->
                              (fun ctxt1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (445))
                                         (Prims.of_int (12))
                                         (Prims.of_int (445))
                                         (Prims.of_int (36)))
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (446))
                                         (Prims.of_int (4))
                                         (Prims.of_int (446))
                                         (Prims.of_int (15)))
                                      (Obj.magic (maybe_add_elims g ctxt1 t))
                                      (fun t1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 -> unprotect t1))))
                                uu___1)))) uu___2 uu___1 uu___
let rec (print_st_head : Pulse_Syntax_Base.st_term -> Prims.string) =
  fun t ->
    match t.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_Abs uu___ -> "Abs"
    | Pulse_Syntax_Base.Tm_Protect p -> print_st_head p.Pulse_Syntax_Base.t
    | Pulse_Syntax_Base.Tm_Return p -> print_head p.Pulse_Syntax_Base.term
    | Pulse_Syntax_Base.Tm_Bind uu___ -> "Bind"
    | Pulse_Syntax_Base.Tm_TotBind uu___ -> "TotBind"
    | Pulse_Syntax_Base.Tm_If uu___ -> "If"
    | Pulse_Syntax_Base.Tm_While uu___ -> "While"
    | Pulse_Syntax_Base.Tm_Admit uu___ -> "Admit"
    | Pulse_Syntax_Base.Tm_Par uu___ -> "Par"
    | Pulse_Syntax_Base.Tm_Rewrite uu___ -> "Rewrite"
    | Pulse_Syntax_Base.Tm_WithLocal uu___ -> "WithLocal"
    | Pulse_Syntax_Base.Tm_STApp
        { Pulse_Syntax_Base.head = p; Pulse_Syntax_Base.arg_qual = uu___;
          Pulse_Syntax_Base.arg = uu___1;_}
        -> print_head p
    | Pulse_Syntax_Base.Tm_IntroExists uu___ -> "IntroExists"
    | Pulse_Syntax_Base.Tm_ElimExists uu___ -> "ElimExists"
and (print_head : Pulse_Syntax_Base.term -> Prims.string) =
  fun t -> "<pure term>"
let rec (print_skel : Pulse_Syntax_Base.st_term -> Prims.string) =
  fun t ->
    match t.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_Abs
        { Pulse_Syntax_Base.b = uu___; Pulse_Syntax_Base.q = uu___1;
          Pulse_Syntax_Base.pre1 = uu___2; Pulse_Syntax_Base.body = body;
          Pulse_Syntax_Base.ret_ty = uu___3;
          Pulse_Syntax_Base.post1 = uu___4;_}
        -> Prims.strcat "(fun _ -> " (Prims.strcat (print_skel body) ")")
    | Pulse_Syntax_Base.Tm_Protect { Pulse_Syntax_Base.t = p;_} ->
        Prims.strcat "(Protect " (Prims.strcat (print_skel p) ")")
    | Pulse_Syntax_Base.Tm_Return
        { Pulse_Syntax_Base.ctag = uu___;
          Pulse_Syntax_Base.insert_eq = uu___1; Pulse_Syntax_Base.term = p;_}
        -> print_head p
    | Pulse_Syntax_Base.Tm_Bind
        { Pulse_Syntax_Base.binder = uu___; Pulse_Syntax_Base.head1 = e1;
          Pulse_Syntax_Base.body1 = e2;_}
        ->
        Prims.strcat
          (Prims.strcat "(Bind " (Prims.strcat (print_skel e1) " "))
          (Prims.strcat (print_skel e2) ")")
    | Pulse_Syntax_Base.Tm_TotBind
        { Pulse_Syntax_Base.head2 = uu___; Pulse_Syntax_Base.body2 = e2;_} ->
        Prims.strcat "(TotBind _ " (Prims.strcat (print_skel e2) ")")
    | Pulse_Syntax_Base.Tm_If uu___ -> "If"
    | Pulse_Syntax_Base.Tm_While uu___ -> "While"
    | Pulse_Syntax_Base.Tm_Admit uu___ -> "Admit"
    | Pulse_Syntax_Base.Tm_Par uu___ -> "Par"
    | Pulse_Syntax_Base.Tm_Rewrite uu___ -> "Rewrite"
    | Pulse_Syntax_Base.Tm_WithLocal uu___ -> "WithLocal"
    | Pulse_Syntax_Base.Tm_STApp
        { Pulse_Syntax_Base.head = p; Pulse_Syntax_Base.arg_qual = uu___;
          Pulse_Syntax_Base.arg = uu___1;_}
        -> print_head p
    | Pulse_Syntax_Base.Tm_IntroExists uu___ -> "IntroExists"
    | Pulse_Syntax_Base.Tm_ElimExists uu___ -> "ElimExists"
let rec (check' : Prims.bool -> Pulse_Checker_Common.check_t) =
  fun allow_inst ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (506)) (Prims.of_int (4))
                   (Prims.of_int (508)) (Prims.of_int (10)))
                (FStar_Range.mk_range "Pulse.Checker.fst"
                   (Prims.of_int (510)) (Prims.of_int (2))
                   (Prims.of_int (588)) (Prims.of_int (18)))
                (if allow_inst
                 then Obj.magic (Obj.repr (auto_elims g pre t))
                 else
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> t))))
                (fun uu___ ->
                   (fun t1 ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (510)) (Prims.of_int (2))
                              (Prims.of_int (515)) (Prims.of_int (3)))
                           (FStar_Range.mk_range "Pulse.Checker.fst"
                              (Prims.of_int (515)) (Prims.of_int (4))
                              (Prims.of_int (588)) (Prims.of_int (18)))
                           (if
                              Pulse_RuntimeUtils.debug_at_level g
                                "proof_states"
                            then
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (512))
                                         (Prims.of_int (12))
                                         (Prims.of_int (514))
                                         (Prims.of_int (68)))
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (511))
                                         (Prims.of_int (7))
                                         (Prims.of_int (515))
                                         (Prims.of_int (3)))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (514))
                                               (Prims.of_int (26))
                                               (Prims.of_int (514))
                                               (Prims.of_int (67)))
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.fst"
                                               (Prims.of_int (512))
                                               (Prims.of_int (12))
                                               (Prims.of_int (514))
                                               (Prims.of_int (68)))
                                            (Obj.magic
                                               (Pulse_Syntax_Printer.term_to_string
                                                  pre))
                                            (fun uu___ ->
                                               (fun uu___ ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (512))
                                                          (Prims.of_int (12))
                                                          (Prims.of_int (514))
                                                          (Prims.of_int (68)))
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.fst"
                                                          (Prims.of_int (512))
                                                          (Prims.of_int (12))
                                                          (Prims.of_int (514))
                                                          (Prims.of_int (68)))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.fst"
                                                                (Prims.of_int (513))
                                                                (Prims.of_int (26))
                                                                (Prims.of_int (513))
                                                                (Prims.of_int (53)))
                                                             (FStar_Range.mk_range
                                                                "FStar.Printf.fst"
                                                                (Prims.of_int (121))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (123))
                                                                (Prims.of_int (44)))
                                                             (Obj.magic
                                                                (FStar_Tactics_Builtins.range_to_string
                                                                   t1.Pulse_Syntax_Base.range))
                                                             (fun uu___1 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___2
                                                                    ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "At "
                                                                    (Prims.strcat
                                                                    uu___1
                                                                    ": precondition is "))
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
                                              (FStar_Tactics_Builtins.print
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
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (516))
                                         (Prims.of_int (10))
                                         (Prims.of_int (516))
                                         (Prims.of_int (43)))
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.fst"
                                         (Prims.of_int (517))
                                         (Prims.of_int (2))
                                         (Prims.of_int (588))
                                         (Prims.of_int (18)))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            Pulse_Checker_Pure.push_context
                                              (tag_of_st_term t1) g))
                                      (fun uu___1 ->
                                         (fun g1 ->
                                            Obj.magic
                                              (FStar_Tactics_Derived.try_with
                                                 (fun uu___1 ->
                                                    (fun uu___1 ->
                                                       match () with
                                                       | () ->
                                                           (match t1.Pulse_Syntax_Base.term1
                                                            with
                                                            | Pulse_Syntax_Base.Tm_Protect
                                                                uu___2 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Protect should have been removed"))
                                                            | Pulse_Syntax_Base.Tm_Return
                                                                uu___2 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (Pulse_Checker_Return.check_return
                                                                    allow_inst
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint))
                                                            | Pulse_Syntax_Base.Tm_Abs
                                                                uu___2 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (Pulse_Checker_Abs.check_abs
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint
                                                                    (check'
                                                                    true)))
                                                            | Pulse_Syntax_Base.Tm_STApp
                                                                uu___2 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (Pulse_Checker_STApp.check_stapp
                                                                    allow_inst
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint
                                                                    check'))
                                                            | Pulse_Syntax_Base.Tm_Bind
                                                                uu___2 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (Pulse_Checker_Bind.check_bind
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint
                                                                    (check'
                                                                    true)))
                                                            | Pulse_Syntax_Base.Tm_TotBind
                                                                uu___2 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (Pulse_Checker_Bind.check_tot_bind
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint
                                                                    (check'
                                                                    true)))
                                                            | Pulse_Syntax_Base.Tm_If
                                                                {
                                                                  Pulse_Syntax_Base.b1
                                                                    = b;
                                                                  Pulse_Syntax_Base.then_
                                                                    = e1;
                                                                  Pulse_Syntax_Base.else_
                                                                    = e2;
                                                                  Pulse_Syntax_Base.post2
                                                                    = post_if;_}
                                                                ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (61)))
                                                                    (match 
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
                                                                    uu___2 ->
                                                                    p)))
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    p,
                                                                    FStar_Pervasives_Native.None)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Checker_Common.intro_post_hint
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    p))
                                                                    | 
                                                                    (uu___2,
                                                                    uu___3)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Either two annotations for if post or none")))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_If.check_if
                                                                    g1 b e1
                                                                    e2 pre ()
                                                                    post
                                                                    (check'
                                                                    true)))
                                                                    uu___2)))
                                                            | Pulse_Syntax_Base.Tm_ElimExists
                                                                uu___2 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (Pulse_Checker_Exists.check_elim_exists
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint))
                                                            | Pulse_Syntax_Base.Tm_IntroExists
                                                                {
                                                                  Pulse_Syntax_Base.erased
                                                                    = uu___2;
                                                                  Pulse_Syntax_Base.p1
                                                                    = uu___3;
                                                                  Pulse_Syntax_Base.witnesses
                                                                    =
                                                                    witnesses;_}
                                                                ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (552))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (558))
                                                                    (Prims.of_int (19)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (560))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (569))
                                                                    (Prims.of_int (7)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match witnesses
                                                                    with
                                                                    | 
                                                                    w::[] ->
                                                                    (match w
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Unknown
                                                                    -> true
                                                                    | 
                                                                    uu___5 ->
                                                                    false)
                                                                    | 
                                                                    uu___5 ->
                                                                    true))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    should_infer_witnesses
                                                                    ->
                                                                    if
                                                                    should_infer_witnesses
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (562))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (562))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.fst"
                                                                    (Prims.of_int (565))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (565))
                                                                    (Prims.of_int (65)))
                                                                    (Obj.magic
                                                                    (maybe_infer_intro_exists
                                                                    g1 t1 pre))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    unary_intros
                                                                    ->
                                                                    Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    g1
                                                                    unary_intros
                                                                    pre ()
                                                                    post_hint))
                                                                    uu___4))
                                                                    else
                                                                    Obj.magic
                                                                    (Pulse_Checker_Exists.check_intro_exists_either
                                                                    g1 t1
                                                                    FStar_Pervasives_Native.None
                                                                    pre ()
                                                                    post_hint))
                                                                    uu___4)))
                                                            | Pulse_Syntax_Base.Tm_While
                                                                uu___2 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (Pulse_Checker_While.check_while
                                                                    allow_inst
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint
                                                                    check'))
                                                            | Pulse_Syntax_Base.Tm_Admit
                                                                uu___2 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (Pulse_Checker_Admit.check_admit
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint))
                                                            | Pulse_Syntax_Base.Tm_Par
                                                                uu___2 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (Pulse_Checker_Par.check_par
                                                                    allow_inst
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint
                                                                    check'))
                                                            | Pulse_Syntax_Base.Tm_WithLocal
                                                                uu___2 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (Pulse_Checker_WithLocal.check_withlocal
                                                                    allow_inst
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint
                                                                    check'))
                                                            | Pulse_Syntax_Base.Tm_Rewrite
                                                                uu___2 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (Pulse_Checker_Rewrite.check_rewrite
                                                                    g1 t1 pre
                                                                    ()
                                                                    post_hint))))
                                                      uu___1)
                                                 (fun uu___1 ->
                                                    (fun uu___1 ->
                                                       match uu___1 with
                                                       | Pulse_Checker_Common.Framing_failure
                                                           failure ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (handle_framing_failure
                                                                   g1 t1 pre
                                                                   ()
                                                                   post_hint
                                                                   failure
                                                                   (check'
                                                                    true)))
                                                       | e ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (FStar_Tactics_Effect.raise
                                                                   e)))
                                                      uu___1))) uu___1)))
                                uu___))) uu___)
let (check : Pulse_Checker_Common.check_t) = check' true