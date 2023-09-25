open Prims
exception Extraction_failure of Prims.string 
let (uu___is_Extraction_failure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Extraction_failure uu___ -> true | uu___ -> false
let (__proj__Extraction_failure__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | Extraction_failure uu___ -> uu___
type env =
  {
  uenv_inner: Pulse_Extract_CompilerLib.uenv ;
  coreenv: Pulse_Typing_Env.env }
let (__proj__Mkenv__item__uenv_inner : env -> Pulse_Extract_CompilerLib.uenv)
  =
  fun projectee ->
    match projectee with | { uenv_inner; coreenv;_} -> uenv_inner
let (__proj__Mkenv__item__coreenv : env -> Pulse_Typing_Env.env) =
  fun projectee -> match projectee with | { uenv_inner; coreenv;_} -> coreenv
type name = (Pulse_Syntax_Base.ppname * Prims.nat)
let (uenv_of_env : env -> Pulse_Extract_CompilerLib.uenv) =
  fun g ->
    Pulse_Extract_CompilerLib.set_tcenv g.uenv_inner
      (Pulse_Typing.elab_env g.coreenv)
let (term_as_mlexpr :
  env ->
    Pulse_Syntax_Base.term ->
      (Pulse_Extract_CompilerLib.mlexpr, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun t ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   match Pulse_Extract_CompilerLib.term_as_mlexpr
                           (uenv_of_env g) (Pulse_Elaborate_Pure.elab_term t)
                   with
                   | (mlt, uu___1, uu___2) -> mlt))) uu___1 uu___
let (term_as_mlty :
  env ->
    Pulse_Syntax_Base.term ->
      (Pulse_Extract_CompilerLib.mlty, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun t ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   Pulse_Extract_CompilerLib.term_as_mlty (uenv_of_env g)
                     (Pulse_Elaborate_Pure.elab_term t)))) uu___1 uu___
let (extend_env :
  env ->
    Pulse_Syntax_Base.binder ->
      ((env * Pulse_Extract_CompilerLib.mlident *
         Pulse_Extract_CompilerLib.mlty * name),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun b ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (39)) (Prims.of_int (15)) (Prims.of_int (39))
                 (Prims.of_int (41)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (39)) (Prims.of_int (44)) (Prims.of_int (47))
                 (Prims.of_int (64)))))
        (Obj.magic (term_as_mlty g b.Pulse_Syntax_Base.binder_ty))
        (fun uu___ ->
           (fun mlty ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (40)) (Prims.of_int (12))
                            (Prims.of_int (40)) (Prims.of_int (29)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (40)) (Prims.of_int (32))
                            (Prims.of_int (47)) (Prims.of_int (64)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> Pulse_Typing_Env.fresh g.coreenv))
                   (fun uu___ ->
                      (fun x ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (41))
                                       (Prims.of_int (18))
                                       (Prims.of_int (41))
                                       (Prims.of_int (72)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (42)) (Prims.of_int (4))
                                       (Prims.of_int (47))
                                       (Prims.of_int (64)))))
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___ ->
                                    Pulse_Typing_Env.push_binding g.coreenv x
                                      b.Pulse_Syntax_Base.binder_ppname
                                      b.Pulse_Syntax_Base.binder_ty))
                              (fun uu___ ->
                                 (fun coreenv ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (42))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (44))
                                                  (Prims.of_int (67)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (44))
                                                  (Prims.of_int (68))
                                                  (Prims.of_int (47))
                                                  (Prims.of_int (64)))))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Extract.Main.fst"
                                                        (Prims.of_int (42))
                                                        (Prims.of_int (11))
                                                        (Prims.of_int (44))
                                                        (Prims.of_int (67)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Extract.Main.fst"
                                                        (Prims.of_int (42))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (44))
                                                        (Prims.of_int (67)))))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (44))
                                                              (Prims.of_int (38))
                                                              (Prims.of_int (44))
                                                              (Prims.of_int (66)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (42))
                                                              (Prims.of_int (11))
                                                              (Prims.of_int (44))
                                                              (Prims.of_int (67)))))
                                                     (Obj.magic
                                                        (Pulse_Syntax_Printer.term_to_string
                                                           b.Pulse_Syntax_Base.binder_ty))
                                                     (fun uu___ ->
                                                        (fun uu___ ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (67)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (67)))))
                                                                (Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (43))
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
                                                                    (Pulse_Syntax_Printer.binder_to_string
                                                                    b))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Extending environment with "
                                                                    (Prims.strcat
                                                                    uu___1
                                                                    " : "))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
                                                                (fun uu___1
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    uu___1
                                                                    uu___))))
                                                          uu___)))
                                               (fun uu___ ->
                                                  (fun uu___ ->
                                                     Obj.magic
                                                       (FStar_Tactics_V2_Builtins.dump
                                                          uu___)) uu___)))
                                         (fun uu___ ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___1 ->
                                                 match Pulse_Extract_CompilerLib.extend_bv
                                                         g.uenv_inner
                                                         b.Pulse_Syntax_Base.binder_ppname
                                                         x mlty
                                                 with
                                                 | (uenv_inner, mlident) ->
                                                     ({ uenv_inner; coreenv },
                                                       mlident, mlty,
                                                       ((b.Pulse_Syntax_Base.binder_ppname),
                                                         x)))))) uu___)))
                        uu___))) uu___)
let rec (name_as_mlpath :
  FStar_Reflection_Types.name ->
    (Pulse_Extract_CompilerLib.mlpath, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun x ->
       match x with
       | [] ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_V2_Derived.fail "Unexpected empty name"))
       | x1::[] ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ([], x1))))
       | x1::xs ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (55)) (Prims.of_int (18))
                            (Prims.of_int (55)) (Prims.of_int (35)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (54)) (Prims.of_int (16))
                            (Prims.of_int (56)) (Prims.of_int (16)))))
                   (Obj.magic (name_as_mlpath xs))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           match uu___ with | (xs1, x2) -> ((x2 :: xs1), x2))))))
      uu___
let (extract_constant :
  env ->
    FStar_Reflection_V2_Data.vconst ->
      (Pulse_Extract_CompilerLib.mlconstant, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun c ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (61)) (Prims.of_int (12)) (Prims.of_int (61))
                 (Prims.of_int (36)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (61)) (Prims.of_int (39)) (Prims.of_int (65))
                 (Prims.of_int (17)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              FStar_Reflection_V2_Builtins.pack_ln
                (FStar_Reflection_V2_Data.Tv_Const c)))
        (fun uu___ ->
           (fun e ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (62)) (Prims.of_int (20))
                            (Prims.of_int (62)) (Prims.of_int (64)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (61)) (Prims.of_int (39))
                            (Prims.of_int (65)) (Prims.of_int (17)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ ->
                         Pulse_Extract_CompilerLib.term_as_mlexpr
                           (uenv_of_env g) e))
                   (fun uu___ ->
                      (fun uu___ ->
                         match uu___ with
                         | (mle, uu___1, uu___2) ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (63))
                                           (Prims.of_int (10))
                                           (Prims.of_int (63))
                                           (Prims.of_int (34)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (63))
                                           (Prims.of_int (4))
                                           (Prims.of_int (65))
                                           (Prims.of_int (17)))))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 ->
                                        Pulse_Extract_CompilerLib.mlconstant_of_mlexpr
                                          mle))
                                  (fun uu___3 ->
                                     match uu___3 with
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Tactics_Effect.raise
                                           (Extraction_failure
                                              "Failed to extract constant")
                                     | FStar_Pervasives_Native.Some c1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 -> c1)))) uu___)))
             uu___)
let rec (extend_env_pat_core :
  env ->
    Pulse_Syntax_Base.pattern ->
      ((env * Pulse_Extract_CompilerLib.mlpattern Prims.list *
         Pulse_Typing_Env.binding Prims.list),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun p ->
           match p with
           | Pulse_Syntax_Base.Pat_Dot_Term uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 -> (g, [], []))))
           | Pulse_Syntax_Base.Pat_Var pp ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          match Pulse_Extract_CompilerLib.extend_bv
                                  g.uenv_inner
                                  (Pulse_Syntax_Base.mk_ppname pp
                                     FStar_Range.range_0)
                                  (Pulse_Typing_Env.fresh g.coreenv)
                                  Pulse_Extract_CompilerLib.mlty_top
                          with
                          | (uenv_inner, mlident) ->
                              ({
                                 uenv_inner;
                                 coreenv =
                                   (Pulse_Typing_Env.push_binding g.coreenv
                                      (Pulse_Typing_Env.fresh g.coreenv)
                                      (Pulse_Syntax_Base.mk_ppname pp
                                         FStar_Range.range_0)
                                      Pulse_Syntax_Base.tm_unknown)
                               },
                                [Pulse_Extract_CompilerLib.mlp_var mlident],
                                [((Pulse_Typing_Env.fresh g.coreenv),
                                   Pulse_Syntax_Base.tm_unknown)]))))
           | Pulse_Syntax_Base.Pat_Cons (f, pats) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (82)) (Prims.of_int (8))
                                (Prims.of_int (87)) (Prims.of_int (14)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (80)) (Prims.of_int (24))
                                (Prims.of_int (89)) (Prims.of_int (68)))))
                       (Obj.magic
                          (FStar_Tactics_Util.fold_left
                             (fun uu___ ->
                                fun uu___1 ->
                                  match (uu___, uu___1) with
                                  | ((g1, pats1, bindings), (p1, uu___2)) ->
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (84))
                                                 (Prims.of_int (38))
                                                 (Prims.of_int (84))
                                                 (Prims.of_int (61)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (83))
                                                 (Prims.of_int (44))
                                                 (Prims.of_int (85))
                                                 (Prims.of_int (47)))))
                                        (Obj.magic
                                           (extend_env_pat_core g1 p1))
                                        (fun uu___3 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___4 ->
                                                match uu___3 with
                                                | (g2, pats', bindings') ->
                                                    (g2,
                                                      (FStar_List_Tot_Base.op_At
                                                         pats1 pats'),
                                                      (FStar_List_Tot_Base.op_At
                                                         bindings bindings')))))
                             (g, [], []) pats))
                       (fun uu___ ->
                          (fun uu___ ->
                             match uu___ with
                             | (g1, pats1, bindings) ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (89))
                                               (Prims.of_int (9))
                                               (Prims.of_int (89))
                                               (Prims.of_int (58)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (89))
                                               (Prims.of_int (6))
                                               (Prims.of_int (89))
                                               (Prims.of_int (68)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Extract.Main.fst"
                                                     (Prims.of_int (89))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (89))
                                                     (Prims.of_int (57)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Extract.Main.fst"
                                                     (Prims.of_int (89))
                                                     (Prims.of_int (9))
                                                     (Prims.of_int (89))
                                                     (Prims.of_int (58)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Extract.Main.fst"
                                                           (Prims.of_int (89))
                                                           (Prims.of_int (26))
                                                           (Prims.of_int (89))
                                                           (Prims.of_int (52)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Extract.Main.fst"
                                                           (Prims.of_int (89))
                                                           (Prims.of_int (10))
                                                           (Prims.of_int (89))
                                                           (Prims.of_int (57)))))
                                                  (Obj.magic
                                                     (name_as_mlpath
                                                        f.Pulse_Syntax_Base.fv_name))
                                                  (fun uu___1 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___2 ->
                                                          Pulse_Extract_CompilerLib.mlp_constructor
                                                            uu___1 pats1))))
                                            (fun uu___1 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 -> [uu___1]))))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              (g1, uu___1, bindings)))))
                            uu___)))
           | Pulse_Syntax_Base.Pat_Constant c ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (91)) (Prims.of_int (14))
                                (Prims.of_int (91)) (Prims.of_int (34)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (92)) (Prims.of_int (6))
                                (Prims.of_int (92)) (Prims.of_int (26)))))
                       (Obj.magic (extract_constant g c))
                       (fun c1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ ->
                               (g, [Pulse_Extract_CompilerLib.mlp_const c1],
                                 [])))))) uu___1 uu___
let (extend_env_pat :
  env ->
    Pulse_Syntax_Base.pattern ->
      ((env * Pulse_Extract_CompilerLib.mlpattern * Pulse_Typing_Env.binding
         Prims.list),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (94)) (Prims.of_int (20)) (Prims.of_int (94))
                 (Prims.of_int (43)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (93)) (Prims.of_int (24)) (Prims.of_int (97))
                 (Prims.of_int (72))))) (Obj.magic (extend_env_pat_core g p))
        (fun uu___ ->
           match uu___ with
           | (g1, pats, bs) ->
               (match pats with
                | p1::[] ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___1 -> (g1, p1, bs))
                | uu___1 ->
                    FStar_Tactics_Effect.raise
                      (Extraction_failure "Unexpected extraction of pattern")))
let (unit_val : Pulse_Syntax_Base.term) =
  Pulse_Syntax_Base.tm_fstar Pulse_Reflection_Util.unit_tm
    FStar_Range.range_0
let (is_erasable :
  Pulse_Syntax_Base.st_term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun p ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (101)) (Prims.of_int (12)) (Prims.of_int (101))
               (Prims.of_int (33)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (102)) (Prims.of_int (2)) (Prims.of_int (104))
               (Prims.of_int (14)))))
      (Obj.magic (FStar_Tactics_Unseal.unseal p.Pulse_Syntax_Base.effect_tag))
      (fun tag ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              match tag with
              | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.STT_Ghost) ->
                  true
              | uu___1 -> false))
let rec (extract :
  env ->
    Pulse_Syntax_Base.st_term ->
      ((Pulse_Extract_CompilerLib.mlexpr * Pulse_Extract_CompilerLib.e_tag),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (108)) (Prims.of_int (24))
                 (Prims.of_int (108)) (Prims.of_int (48)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (109)) (Prims.of_int (4)) (Prims.of_int (213))
                 (Prims.of_int (7)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              (Pulse_Extract_CompilerLib.mle_unit,
                Pulse_Extract_CompilerLib.e_tag_erasable)))
        (fun uu___ ->
           (fun erased_result ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (109)) (Prims.of_int (4))
                            (Prims.of_int (111)) (Prims.of_int (36)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (112)) (Prims.of_int (4))
                            (Prims.of_int (213)) (Prims.of_int (7)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                  (Prims.of_int (109)) (Prims.of_int (11))
                                  (Prims.of_int (111)) (Prims.of_int (36)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                  (Prims.of_int (109)) (Prims.of_int (4))
                                  (Prims.of_int (111)) (Prims.of_int (36)))))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (111))
                                        (Prims.of_int (14))
                                        (Prims.of_int (111))
                                        (Prims.of_int (35)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (109))
                                        (Prims.of_int (11))
                                        (Prims.of_int (111))
                                        (Prims.of_int (36)))))
                               (Obj.magic
                                  (Pulse_Syntax_Printer.st_term_to_string p))
                               (fun uu___ ->
                                  (fun uu___ ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (109))
                                                   (Prims.of_int (11))
                                                   (Prims.of_int (111))
                                                   (Prims.of_int (36)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (109))
                                                   (Prims.of_int (11))
                                                   (Prims.of_int (111))
                                                   (Prims.of_int (36)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (110))
                                                         (Prims.of_int (14))
                                                         (Prims.of_int (110))
                                                         (Prims.of_int (41)))))
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
                                                      p.Pulse_Syntax_Base.range2))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        fun x ->
                                                          Prims.strcat
                                                            (Prims.strcat
                                                               "Extracting term@"
                                                               (Prims.strcat
                                                                  uu___1
                                                                  ":\n"))
                                                            (Prims.strcat x
                                                               "\n")))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 -> uu___1 uu___))))
                                    uu___)))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_V2_Builtins.dump uu___))
                              uu___)))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (112))
                                       (Prims.of_int (7))
                                       (Prims.of_int (112))
                                       (Prims.of_int (20)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (112))
                                       (Prims.of_int (4))
                                       (Prims.of_int (213))
                                       (Prims.of_int (7)))))
                              (Obj.magic (is_erasable p))
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    if uu___1
                                    then
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 -> erased_result)))
                                    else
                                      Obj.magic
                                        (Obj.repr
                                           (match p.Pulse_Syntax_Base.term1
                                            with
                                            | Pulse_Syntax_Base.Tm_IntroPure
                                                uu___3 ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        erased_result))
                                            | Pulse_Syntax_Base.Tm_ElimExists
                                                uu___3 ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        erased_result))
                                            | Pulse_Syntax_Base.Tm_IntroExists
                                                uu___3 ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        erased_result))
                                            | Pulse_Syntax_Base.Tm_Rewrite
                                                uu___3 ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        erased_result))
                                            | Pulse_Syntax_Base.Tm_Abs
                                                { Pulse_Syntax_Base.b = b;
                                                  Pulse_Syntax_Base.q = q;
                                                  Pulse_Syntax_Base.ascription
                                                    = uu___3;
                                                  Pulse_Syntax_Base.body =
                                                    body;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (123))
                                                              (Prims.of_int (37))
                                                              (Prims.of_int (123))
                                                              (Prims.of_int (51)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (122))
                                                              (Prims.of_int (32))
                                                              (Prims.of_int (127))
                                                              (Prims.of_int (23)))))
                                                     (Obj.magic
                                                        (extend_env g b))
                                                     (fun uu___4 ->
                                                        (fun uu___4 ->
                                                           match uu___4 with
                                                           | (g1, mlident,
                                                              mlty, name1) ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (47)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (23)))))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body
                                                                    name1))
                                                                    (
                                                                    fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    (extract
                                                                    g1 body1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (body2,
                                                                    uu___7)
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_fun
                                                                    [
                                                                    (mlident,
                                                                    mlty)]
                                                                    body2),
                                                                    Pulse_Extract_CompilerLib.e_tag_pure)))))
                                                                    uu___5)))
                                                          uu___4))
                                            | Pulse_Syntax_Base.Tm_Return
                                                {
                                                  Pulse_Syntax_Base.ctag =
                                                    uu___3;
                                                  Pulse_Syntax_Base.insert_eq
                                                    = uu___4;
                                                  Pulse_Syntax_Base.term =
                                                    term;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (130))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (130))
                                                              (Prims.of_int (29)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (130))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (131))
                                                              (Prims.of_int (18)))))
                                                     (Obj.magic
                                                        (term_as_mlexpr g
                                                           term))
                                                     (fun uu___5 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___6 ->
                                                             (uu___5,
                                                               Pulse_Extract_CompilerLib.e_tag_pure))))
                                            | Pulse_Syntax_Base.Tm_STApp
                                                {
                                                  Pulse_Syntax_Base.head =
                                                    head;
                                                  Pulse_Syntax_Base.arg_qual
                                                    = uu___3;
                                                  Pulse_Syntax_Base.arg = arg;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (134))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (134))
                                                              (Prims.of_int (40)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (134))
                                                              (Prims.of_int (43))
                                                              (Prims.of_int (136))
                                                              (Prims.of_int (40)))))
                                                     (Obj.magic
                                                        (term_as_mlexpr g
                                                           head))
                                                     (fun uu___4 ->
                                                        (fun head1 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (38)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (40)))))
                                                                (Obj.magic
                                                                   (term_as_mlexpr
                                                                    g arg))
                                                                (fun arg1 ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ((Pulse_Extract_CompilerLib.mle_app
                                                                    head1
                                                                    [arg1]),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                          uu___4))
                                            | Pulse_Syntax_Base.Tm_Bind
                                                {
                                                  Pulse_Syntax_Base.binder =
                                                    binder;
                                                  Pulse_Syntax_Base.head1 =
                                                    head;
                                                  Pulse_Syntax_Base.body1 =
                                                    body;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (139))
                                                              (Prims.of_int (11))
                                                              (Prims.of_int (139))
                                                              (Prims.of_int (27)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (139))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (155))
                                                              (Prims.of_int (9)))))
                                                     (Obj.magic
                                                        (is_erasable head))
                                                     (fun uu___3 ->
                                                        (fun uu___3 ->
                                                           if uu___3
                                                           then
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (61)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (24)))))
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    unit_val)]))
                                                                  (fun uu___4
                                                                    ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    body1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (143))
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
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    head))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Erasing head of bind "
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    "\nopened body to "))
                                                                    (Prims.strcat
                                                                    x "")))))
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
                                                                    (FStar_Tactics_V2_Builtins.dump
                                                                    uu___4))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (extract
                                                                    g body1))
                                                                    uu___4)))
                                                                    uu___4))
                                                           else
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (38)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (9)))))
                                                                  (Obj.magic
                                                                    (extract
                                                                    g head))
                                                                  (fun uu___5
                                                                    ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (head1,
                                                                    uu___6)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    (extend_env
                                                                    g binder))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (g1,
                                                                    mlident,
                                                                    mlty,
                                                                    name1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body
                                                                    name1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    (extract
                                                                    g1 body1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (body2,
                                                                    uu___10)
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_let
                                                                    (Pulse_Extract_CompilerLib.mk_mlletbinding
                                                                    false
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mk_mllb
                                                                    mlident
                                                                    ([],
                                                                    mlty)
                                                                    head1])
                                                                    body2),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___5)))
                                                          uu___3))
                                            | Pulse_Syntax_Base.Tm_TotBind
                                                {
                                                  Pulse_Syntax_Base.binder1 =
                                                    binder;
                                                  Pulse_Syntax_Base.head2 =
                                                    head;
                                                  Pulse_Syntax_Base.body2 =
                                                    body;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (159))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (159))
                                                              (Prims.of_int (40)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (159))
                                                              (Prims.of_int (43))
                                                              (Prims.of_int (165))
                                                              (Prims.of_int (47)))))
                                                     (Obj.magic
                                                        (term_as_mlexpr g
                                                           head))
                                                     (fun uu___3 ->
                                                        (fun head1 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (56)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (47)))))
                                                                (Obj.magic
                                                                   (extend_env
                                                                    g binder))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (g1,
                                                                    mlident,
                                                                    mlty,
                                                                    name1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body
                                                                    name1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (extract
                                                                    g1 body1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (body2,
                                                                    uu___6)
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_let
                                                                    (Pulse_Extract_CompilerLib.mk_mlletbinding
                                                                    false
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mk_mllb
                                                                    mlident
                                                                    ([],
                                                                    mlty)
                                                                    head1])
                                                                    body2),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                                    uu___4)))
                                                                    uu___3)))
                                                          uu___3))
                                            | Pulse_Syntax_Base.Tm_If
                                                { Pulse_Syntax_Base.b1 = b;
                                                  Pulse_Syntax_Base.then_ =
                                                    then_;
                                                  Pulse_Syntax_Base.else_ =
                                                    else_;
                                                  Pulse_Syntax_Base.post1 =
                                                    uu___3;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (168))
                                                              (Prims.of_int (16))
                                                              (Prims.of_int (168))
                                                              (Prims.of_int (34)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (168))
                                                              (Prims.of_int (37))
                                                              (Prims.of_int (171))
                                                              (Prims.of_int (49)))))
                                                     (Obj.magic
                                                        (term_as_mlexpr g b))
                                                     (fun uu___4 ->
                                                        (fun b1 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (38)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (49)))))
                                                                (Obj.magic
                                                                   (extract g
                                                                    then_))
                                                                (fun uu___4
                                                                   ->
                                                                   (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (then_1,
                                                                    uu___5)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    (extract
                                                                    g else_))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (else_1,
                                                                    uu___8)
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_if
                                                                    b1 then_1
                                                                    (FStar_Pervasives_Native.Some
                                                                    else_1)),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                                    uu___4)))
                                                          uu___4))
                                            | Pulse_Syntax_Base.Tm_Match
                                                { Pulse_Syntax_Base.sc = sc;
                                                  Pulse_Syntax_Base.returns_
                                                    = uu___3;
                                                  Pulse_Syntax_Base.brs = brs;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (174))
                                                              (Prims.of_int (17))
                                                              (Prims.of_int (174))
                                                              (Prims.of_int (36)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (174))
                                                              (Prims.of_int (39))
                                                              (Prims.of_int (182))
                                                              (Prims.of_int (38)))))
                                                     (Obj.magic
                                                        (term_as_mlexpr g sc))
                                                     (fun uu___4 ->
                                                        (fun sc1 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (19)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (38)))))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___4 ->
                                                                    fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (pat,
                                                                    body) ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (extend_env_pat
                                                                    g pat))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (g1,
                                                                    pat1, bs)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Checker_Match.open_st_term_bs
                                                                    body bs))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (extract
                                                                    g1 body1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (body2,
                                                                    uu___9)
                                                                    ->
                                                                    (pat1,
                                                                    body2)))))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                (fun uu___4
                                                                   ->
                                                                   (fun
                                                                    extract_branch
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    extract_branch
                                                                    brs))
                                                                    (fun brs1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ((Pulse_Extract_CompilerLib.mle_match
                                                                    sc1 brs1),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                                    uu___4)))
                                                          uu___4))
                                            | Pulse_Syntax_Base.Tm_While
                                                {
                                                  Pulse_Syntax_Base.invariant
                                                    = uu___3;
                                                  Pulse_Syntax_Base.condition
                                                    = condition;
                                                  Pulse_Syntax_Base.condition_var
                                                    = uu___4;
                                                  Pulse_Syntax_Base.body3 =
                                                    body;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (186))
                                                              (Prims.of_int (27))
                                                              (Prims.of_int (186))
                                                              (Prims.of_int (46)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (185))
                                                              (Prims.of_int (39))
                                                              (Prims.of_int (191))
                                                              (Prims.of_int (23)))))
                                                     (Obj.magic
                                                        (extract g condition))
                                                     (fun uu___5 ->
                                                        (fun uu___5 ->
                                                           match uu___5 with
                                                           | (condition1,
                                                              uu___6) ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (36)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (23)))))
                                                                    (
                                                                    Obj.magic
                                                                    (extract
                                                                    g body))
                                                                    (
                                                                    fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (body1,
                                                                    uu___9)
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_app
                                                                    (Pulse_Extract_CompilerLib.mle_name
                                                                    (["Pulse";
                                                                    "Lib";
                                                                    "Core"],
                                                                    "while_"))
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mle_fun
                                                                    [
                                                                    ("_",
                                                                    Pulse_Extract_CompilerLib.mlty_unit)]
                                                                    condition1;
                                                                    Pulse_Extract_CompilerLib.mle_fun
                                                                    [
                                                                    ("_",
                                                                    Pulse_Extract_CompilerLib.mlty_unit)]
                                                                    body1]),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                          uu___5))
                                            | Pulse_Syntax_Base.Tm_Par
                                                {
                                                  Pulse_Syntax_Base.pre1 =
                                                    uu___3;
                                                  Pulse_Syntax_Base.body11 =
                                                    body1;
                                                  Pulse_Syntax_Base.post11 =
                                                    uu___4;
                                                  Pulse_Syntax_Base.pre2 =
                                                    uu___5;
                                                  Pulse_Syntax_Base.body21 =
                                                    body2;
                                                  Pulse_Syntax_Base.post2 =
                                                    uu___6;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (194))
                                                              (Prims.of_int (23))
                                                              (Prims.of_int (194))
                                                              (Prims.of_int (38)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (193))
                                                              (Prims.of_int (34))
                                                              (Prims.of_int (199))
                                                              (Prims.of_int (23)))))
                                                     (Obj.magic
                                                        (extract g body1))
                                                     (fun uu___7 ->
                                                        (fun uu___7 ->
                                                           match uu___7 with
                                                           | (body11, uu___8)
                                                               ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (38)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (23)))))
                                                                    (
                                                                    Obj.magic
                                                                    (extract
                                                                    g body2))
                                                                    (
                                                                    fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (body21,
                                                                    uu___11)
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_app
                                                                    (Pulse_Extract_CompilerLib.mle_name
                                                                    (["Pulse";
                                                                    "Lib";
                                                                    "Core"],
                                                                    "par"))
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mle_fun
                                                                    [
                                                                    ("_",
                                                                    Pulse_Extract_CompilerLib.mlty_unit)]
                                                                    body11;
                                                                    Pulse_Extract_CompilerLib.mle_fun
                                                                    [
                                                                    ("_",
                                                                    Pulse_Extract_CompilerLib.mlty_unit)]
                                                                    body21]),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                          uu___7))
                                            | Pulse_Syntax_Base.Tm_WithLocal
                                                {
                                                  Pulse_Syntax_Base.binder2 =
                                                    binder;
                                                  Pulse_Syntax_Base.initializer1
                                                    = initializer1;
                                                  Pulse_Syntax_Base.body4 =
                                                    body;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (202))
                                                              (Prims.of_int (26))
                                                              (Prims.of_int (202))
                                                              (Prims.of_int (54)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (202))
                                                              (Prims.of_int (57))
                                                              (Prims.of_int (209))
                                                              (Prims.of_int (47)))))
                                                     (Obj.magic
                                                        (term_as_mlexpr g
                                                           initializer1))
                                                     (fun uu___3 ->
                                                        (fun initializer2 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (94)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (47)))))
                                                                (Obj.magic
                                                                   (extend_env
                                                                    g
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    =
                                                                    (binder.Pulse_Syntax_Base.binder_ty);
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    =
                                                                    (binder.Pulse_Syntax_Base.binder_ppname)
                                                                    }))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (g1,
                                                                    mlident,
                                                                    mlty,
                                                                    name1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body
                                                                    name1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (extract
                                                                    g1 body1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (body2,
                                                                    uu___6)
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_let
                                                                    (Pulse_Extract_CompilerLib.mk_mlletbinding
                                                                    false
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mk_mllb
                                                                    mlident
                                                                    ([],
                                                                    mlty)
                                                                    (Pulse_Extract_CompilerLib.mle_app
                                                                    (Pulse_Extract_CompilerLib.mle_name
                                                                    (["Pulse";
                                                                    "Lib";
                                                                    "Reference"],
                                                                    "alloc"))
                                                                    [initializer2])])
                                                                    body2),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                                    uu___4)))
                                                                    uu___3)))
                                                          uu___3))
                                            | Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                {
                                                  Pulse_Syntax_Base.hint_type
                                                    = uu___3;
                                                  Pulse_Syntax_Base.binders =
                                                    uu___4;
                                                  Pulse_Syntax_Base.t3 = t;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_V2_Derived.fail
                                                     "Unexpected constructor: ProofHintWithBinders should have been desugared away")
                                            | Pulse_Syntax_Base.Tm_Admit
                                                uu___3 ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (212))
                                                              (Prims.of_int (30))
                                                              (Prims.of_int (212))
                                                              (Prims.of_int (149)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (212))
                                                              (Prims.of_int (22))
                                                              (Prims.of_int (212))
                                                              (Prims.of_int (149)))))
                                                     (Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (148)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (149)))))
                                                           (Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (147)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                 (Obj.magic
                                                                    (
                                                                    Pulse_Syntax_Printer.st_term_to_string
                                                                    p))
                                                                 (fun uu___4
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "Cannot extract code with admit: "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    "\n")))))
                                                           (fun uu___4 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___5
                                                                   ->
                                                                   Extraction_failure
                                                                    uu___4))))
                                                     (fun uu___4 ->
                                                        FStar_Tactics_Effect.raise
                                                          uu___4))))) uu___1)))
                        uu___))) uu___)
let (extract_pulse :
  Pulse_Extract_CompilerLib.uenv ->
    Pulse_Syntax_Base.st_term ->
      (((Pulse_Extract_CompilerLib.mlexpr * Pulse_Extract_CompilerLib.e_tag *
          Pulse_Extract_CompilerLib.mlty),
         Prims.string) FStar_Pervasives.either,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (220)) (Prims.of_int (4)) (Prims.of_int (220))
                 (Prims.of_int (75)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (221)) (Prims.of_int (4)) (Prims.of_int (229))
                 (Prims.of_int (77)))))
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                       (Prims.of_int (220)) (Prims.of_int (11))
                       (Prims.of_int (220)) (Prims.of_int (75)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                       (Prims.of_int (220)) (Prims.of_int (4))
                       (Prims.of_int (220)) (Prims.of_int (75)))))
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                             (Prims.of_int (220)) (Prims.of_int (53))
                             (Prims.of_int (220)) (Prims.of_int (74)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "prims.fst"
                             (Prims.of_int (590)) (Prims.of_int (19))
                             (Prims.of_int (590)) (Prims.of_int (31)))))
                    (Obj.magic (Pulse_Syntax_Printer.st_term_to_string p))
                    (fun uu___ ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 ->
                            Prims.strcat "About to extract:\n"
                              (Prims.strcat uu___ "\n")))))
              (fun uu___ ->
                 (fun uu___ ->
                    Obj.magic (FStar_Tactics_V2_Builtins.dump uu___)) uu___)))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_V2_Derived.try_with
                   (fun uu___1 ->
                      match () with
                      | () ->
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Extract.Main.fst"
                                     (Prims.of_int (222)) (Prims.of_int (20))
                                     (Prims.of_int (222)) (Prims.of_int (74)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Extract.Main.fst"
                                     (Prims.of_int (221)) (Prims.of_int (7))
                                     (Prims.of_int (224)) (Prims.of_int (29)))))
                            (Obj.magic
                               (extract
                                  {
                                    uenv_inner = g;
                                    coreenv =
                                      (Pulse_Extract_CompilerLib.initial_core_env
                                         g)
                                  } p))
                            (fun uu___2 ->
                               (fun uu___2 ->
                                  match uu___2 with
                                  | (tm, tag) ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (223))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (223))
                                                    (Prims.of_int (74)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (224))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (224))
                                                    (Prims.of_int (29)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (223))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (223))
                                                          (Prims.of_int (74)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (223))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (223))
                                                          (Prims.of_int (74)))))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___3 ->
                                                       Prims.strcat
                                                         "Extracted term: "
                                                         (Prims.strcat
                                                            (Pulse_Extract_CompilerLib.mlexpr_to_string
                                                               tm) "\n")))
                                                 (fun uu___3 ->
                                                    (fun uu___3 ->
                                                       Obj.magic
                                                         (FStar_Tactics_V2_Builtins.dump
                                                            uu___3)) uu___3)))
                                           (fun uu___3 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___4 ->
                                                   FStar_Pervasives.Inl
                                                     (tm, tag,
                                                       Pulse_Extract_CompilerLib.mlty_top)))))
                                 uu___2))
                   (fun uu___1 ->
                      (fun uu___1 ->
                         Obj.magic
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 ->
                                 match uu___1 with
                                 | Extraction_failure msg ->
                                     FStar_Pervasives.Inr msg
                                 | e ->
                                     FStar_Pervasives.Inr
                                       (Prims.strcat
                                          "Unexpected extraction error: "
                                          (Prims.strcat
                                             (Pulse_RuntimeUtils.print_exn e)
                                             ""))))) uu___1))) uu___)