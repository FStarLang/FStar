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
let (topenv_of_env : env -> FStar_Reflection_Typing.fstar_top_env) =
  fun g -> Pulse_Typing_Env.fstar_env g.coreenv
let (tcenv_of_env : env -> FStar_Reflection_Types.env) =
  fun g -> Pulse_Typing.elab_env g.coreenv
let (uenv_of_env : env -> Pulse_Extract_CompilerLib.uenv) =
  fun g -> Pulse_Extract_CompilerLib.set_tcenv g.uenv_inner (tcenv_of_env g)
let (debug :
  env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun f ->
           if
             Pulse_RuntimeUtils.debug_at_level
               (Pulse_Typing_Env.fstar_env g.coreenv) "pulse_extraction"
           then
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (57)) (Prims.of_int (17))
                              (Prims.of_int (57)) (Prims.of_int (22)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (57)) (Prims.of_int (9))
                              (Prims.of_int (57)) (Prims.of_int (22)))))
                     (Obj.magic (f ()))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic (FStar_Tactics_V2_Builtins.print uu___))
                          uu___)))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
        uu___1 uu___
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
                           (uenv_of_env g)
                           (Pulse_Extract_CompilerLib.normalize_for_extraction
                              (uenv_of_env g) t)
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
                   Pulse_Extract_CompilerLib.term_as_mlty (uenv_of_env g) t)))
        uu___1 uu___
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
                 (Prims.of_int (73)) (Prims.of_int (15)) (Prims.of_int (73))
                 (Prims.of_int (41)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (73)) (Prims.of_int (44)) (Prims.of_int (80))
                 (Prims.of_int (64)))))
        (Obj.magic (term_as_mlty g b.Pulse_Syntax_Base.binder_ty))
        (fun uu___ ->
           (fun mlty ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (74)) (Prims.of_int (12))
                            (Prims.of_int (74)) (Prims.of_int (29)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (74)) (Prims.of_int (32))
                            (Prims.of_int (80)) (Prims.of_int (64)))))
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
                                       (Prims.of_int (75))
                                       (Prims.of_int (18))
                                       (Prims.of_int (75))
                                       (Prims.of_int (72)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (76)) (Prims.of_int (4))
                                       (Prims.of_int (80))
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
                                                  (Prims.of_int (76))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (78))
                                                  (Prims.of_int (67)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (78))
                                                  (Prims.of_int (68))
                                                  (Prims.of_int (80))
                                                  (Prims.of_int (64)))))
                                         (Obj.magic
                                            (debug g
                                               (fun uu___ ->
                                                  FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (78))
                                                             (Prims.of_int (38))
                                                             (Prims.of_int (78))
                                                             (Prims.of_int (66)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (76))
                                                             (Prims.of_int (22))
                                                             (Prims.of_int (78))
                                                             (Prims.of_int (66)))))
                                                    (Obj.magic
                                                       (Pulse_Syntax_Printer.term_to_string
                                                          b.Pulse_Syntax_Base.binder_ty))
                                                    (fun uu___1 ->
                                                       (fun uu___1 ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (66)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (66)))))
                                                               (Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.binder_to_string
                                                                    b))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Extending environment with "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " : "))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
                                                               (fun uu___2 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    uu___2
                                                                    uu___1))))
                                                         uu___1))))
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
                            (Prims.of_int (88)) (Prims.of_int (18))
                            (Prims.of_int (88)) (Prims.of_int (35)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (87)) (Prims.of_int (16))
                            (Prims.of_int (89)) (Prims.of_int (16)))))
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
                 (Prims.of_int (94)) (Prims.of_int (12)) (Prims.of_int (94))
                 (Prims.of_int (36)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (94)) (Prims.of_int (39)) (Prims.of_int (98))
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
                            (Prims.of_int (95)) (Prims.of_int (20))
                            (Prims.of_int (95)) (Prims.of_int (56)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (94)) (Prims.of_int (39))
                            (Prims.of_int (98)) (Prims.of_int (17)))))
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
                                           (Prims.of_int (96))
                                           (Prims.of_int (10))
                                           (Prims.of_int (96))
                                           (Prims.of_int (38)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (96))
                                           (Prims.of_int (4))
                                           (Prims.of_int (98))
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
           | Pulse_Syntax_Base.Pat_Var (pp, sort) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (105)) (Prims.of_int (14))
                                (Prims.of_int (105)) (Prims.of_int (31)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (105)) (Prims.of_int (34))
                                (Prims.of_int (114)) (Prims.of_int (25)))))
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
                                           (Prims.of_int (106))
                                           (Prims.of_int (15))
                                           (Prims.of_int (106))
                                           (Prims.of_int (47)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (106))
                                           (Prims.of_int (50))
                                           (Prims.of_int (114))
                                           (Prims.of_int (25)))))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ ->
                                        Pulse_Syntax_Base.mk_ppname pp
                                          FStar_Range.range_0))
                                  (fun uu___ ->
                                     (fun pp1 ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Extract.Main.fst"
                                                      (Prims.of_int (107))
                                                      (Prims.of_int (15))
                                                      (Prims.of_int (107))
                                                      (Prims.of_int (28)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Extract.Main.fst"
                                                      (Prims.of_int (107))
                                                      (Prims.of_int (31))
                                                      (Prims.of_int (114))
                                                      (Prims.of_int (25)))))
                                             (Obj.magic
                                                (FStar_Tactics_Unseal.unseal
                                                   sort))
                                             (fun uu___ ->
                                                (fun ty ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Extract.Main.fst"
                                                                 (Prims.of_int (108))
                                                                 (Prims.of_int (15))
                                                                 (Prims.of_int (108))
                                                                 (Prims.of_int (41)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Extract.Main.fst"
                                                                 (Prims.of_int (109))
                                                                 (Prims.of_int (6))
                                                                 (Prims.of_int (114))
                                                                 (Prims.of_int (25)))))
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___ ->
                                                              Pulse_Syntax_Pure.wr
                                                                ty
                                                                (FStar_Reflection_V2_Builtins.range_of_term
                                                                   ty)))
                                                        (fun uu___ ->
                                                           (fun ty1 ->
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (106)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (25)))))
                                                                   (Obj.magic
                                                                    (debug g
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (105)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (105)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty1))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (105)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (105)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Unseal.unseal
                                                                    pp1.Pulse_Syntax_Base.name))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Pushing pat_var "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " : "))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    uu___2
                                                                    uu___1))))
                                                                    uu___1))))
                                                                   (fun uu___
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    match 
                                                                    Pulse_Extract_CompilerLib.extend_bv
                                                                    g.uenv_inner
                                                                    pp1 x
                                                                    Pulse_Extract_CompilerLib.mlty_top
                                                                    with
                                                                    | 
                                                                    (uenv_inner,
                                                                    mlident)
                                                                    ->
                                                                    ({
                                                                    uenv_inner;
                                                                    coreenv =
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g.coreenv
                                                                    x pp1 ty1)
                                                                    },
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mlp_var
                                                                    mlident],
                                                                    [
                                                                    (x,
                                                                    Pulse_Syntax_Pure.tm_unknown)])))))
                                                             uu___))) uu___)))
                                       uu___))) uu___)))
           | Pulse_Syntax_Base.Pat_Cons (f, pats) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (118)) (Prims.of_int (8))
                                (Prims.of_int (123)) (Prims.of_int (14)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (116)) (Prims.of_int (24))
                                (Prims.of_int (125)) (Prims.of_int (72)))))
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
                                                 (Prims.of_int (120))
                                                 (Prims.of_int (38))
                                                 (Prims.of_int (120))
                                                 (Prims.of_int (61)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (119))
                                                 (Prims.of_int (44))
                                                 (Prims.of_int (121))
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
                                               (Prims.of_int (125))
                                               (Prims.of_int (9))
                                               (Prims.of_int (125))
                                               (Prims.of_int (62)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (125))
                                               (Prims.of_int (6))
                                               (Prims.of_int (125))
                                               (Prims.of_int (72)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Extract.Main.fst"
                                                     (Prims.of_int (125))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (125))
                                                     (Prims.of_int (61)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Extract.Main.fst"
                                                     (Prims.of_int (125))
                                                     (Prims.of_int (9))
                                                     (Prims.of_int (125))
                                                     (Prims.of_int (62)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Extract.Main.fst"
                                                           (Prims.of_int (125))
                                                           (Prims.of_int (30))
                                                           (Prims.of_int (125))
                                                           (Prims.of_int (56)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Extract.Main.fst"
                                                           (Prims.of_int (125))
                                                           (Prims.of_int (10))
                                                           (Prims.of_int (125))
                                                           (Prims.of_int (61)))))
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
                                (Prims.of_int (127)) (Prims.of_int (14))
                                (Prims.of_int (127)) (Prims.of_int (34)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (128)) (Prims.of_int (6))
                                (Prims.of_int (128)) (Prims.of_int (30)))))
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
                 (Prims.of_int (130)) (Prims.of_int (20))
                 (Prims.of_int (130)) (Prims.of_int (43)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (129)) (Prims.of_int (24))
                 (Prims.of_int (133)) (Prims.of_int (72)))))
        (Obj.magic (extend_env_pat_core g p))
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
  Pulse_Syntax_Pure.wr Pulse_Reflection_Util.unit_tm FStar_Range.range_0
let (is_erasable :
  Pulse_Syntax_Base.st_term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun p ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (137)) (Prims.of_int (12)) (Prims.of_int (137))
               (Prims.of_int (33)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (138)) (Prims.of_int (2)) (Prims.of_int (140))
               (Prims.of_int (14)))))
      (Obj.magic (FStar_Tactics_Unseal.unseal p.Pulse_Syntax_Base.effect_tag))
      (fun tag ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              match tag with
              | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.STT_Ghost) ->
                  true
              | uu___1 -> false))
let (head_and_args :
  Pulse_Syntax_Base.term ->
    (FStar_Reflection_Types.term * FStar_Reflection_V2_Data.argv Prims.list)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    FStar_Pervasives_Native.Some
      (FStar_Reflection_V2_Collect.collect_app_ln t)
let (term_eq_string :
  Prims.string -> FStar_Reflection_Types.term -> Prims.bool) =
  fun s ->
    fun t ->
      match FStar_Reflection_V2_Builtins.inspect_ln t with
      | FStar_Reflection_V2_Data.Tv_Const (FStar_Reflection_V2_Data.C_String
          s') -> s = s'
      | uu___ -> false
let (maybe_unfold_head :
  env ->
    FStar_Reflection_Types.term ->
      ((Pulse_Syntax_Base.st_term, FStar_Reflection_Types.term)
         FStar_Pervasives.either FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun head ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (152)) (Prims.of_int (4)) (Prims.of_int (152))
                 (Prims.of_int (89)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (153)) (Prims.of_int (4)) (Prims.of_int (179))
                 (Prims.of_int (15)))))
        (Obj.magic
           (debug g
              (fun uu___ ->
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (152)) (Prims.of_int (65))
                            (Prims.of_int (152)) (Prims.of_int (88)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic (FStar_Tactics_V2_Builtins.term_to_string head))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Prims.strcat "Maybe unfolding head "
                             (Prims.strcat uu___1 "\n"))))))
        (fun uu___ ->
           (fun uu___ ->
              match FStar_Reflection_V2_Builtins.inspect_ln head with
              | FStar_Reflection_V2_Data.Tv_FVar f ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Extract.Main.fst"
                                   (Prims.of_int (155)) (Prims.of_int (17))
                                   (Prims.of_int (155)) (Prims.of_int (31)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Extract.Main.fst"
                                   (Prims.of_int (156)) (Prims.of_int (6))
                                   (Prims.of_int (174)) (Prims.of_int (17)))))
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 ->
                                FStar_Reflection_V2_Builtins.inspect_fv f))
                          (fun uu___1 ->
                             (fun name1 ->
                                match FStar_Reflection_V2_Builtins.lookup_typ
                                        (topenv_of_env g) name1
                                with
                                | FStar_Pervasives_Native.None ->
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___1 ->
                                               FStar_Pervasives_Native.None)))
                                | FStar_Pervasives_Native.Some se ->
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Extract.Main.fst"
                                                     (Prims.of_int (159))
                                                     (Prims.of_int (20))
                                                     (Prims.of_int (159))
                                                     (Prims.of_int (37)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Extract.Main.fst"
                                                     (Prims.of_int (159))
                                                     (Prims.of_int (40))
                                                     (Prims.of_int (174))
                                                     (Prims.of_int (17)))))
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 ->
                                                  FStar_Reflection_V2_Builtins.sigelt_attrs
                                                    se))
                                            (fun uu___1 ->
                                               (fun attrs ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Extract.Main.fst"
                                                                (Prims.of_int (160))
                                                                (Prims.of_int (20))
                                                                (Prims.of_int (160))
                                                                (Prims.of_int (37)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Extract.Main.fst"
                                                                (Prims.of_int (161))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (174))
                                                                (Prims.of_int (17)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___1 ->
                                                             FStar_Reflection_V2_Builtins.sigelt_quals
                                                               se))
                                                       (fun uu___1 ->
                                                          (fun quals ->
                                                             if
                                                               (FStar_List_Tot_Base.existsb
                                                                  (term_eq_string
                                                                    "inline")
                                                                  attrs)
                                                                 ||
                                                                 (FStar_List_Tot_Base.existsb
                                                                    (
                                                                    fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V2_Data.Inline_for_extraction
                                                                    -> true
                                                                    | 
                                                                    uu___2 ->
                                                                    false)
                                                                    quals)
                                                             then
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    match 
                                                                    Pulse_Extract_CompilerLib.sigelt_extension_data
                                                                    se
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    (debug g
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    head))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "Unfolded head "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    (debug g
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    se1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "to "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Inl
                                                                    se1)))))
                                                                    uu___1)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_NamedView.inspect_sigelt
                                                                    se))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_NamedView.Sg_Let
                                                                    {
                                                                    FStar_Tactics_NamedView.isrec
                                                                    = false;
                                                                    FStar_Tactics_NamedView.lbs
                                                                    =
                                                                    {
                                                                    FStar_Tactics_NamedView.lb_fv
                                                                    = uu___3;
                                                                    FStar_Tactics_NamedView.lb_us
                                                                    = [];
                                                                    FStar_Tactics_NamedView.lb_typ
                                                                    = uu___4;
                                                                    FStar_Tactics_NamedView.lb_def
                                                                    = lb_def;_}::[];_}
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Inr
                                                                    lb_def)
                                                                    | 
                                                                    uu___3 ->
                                                                    FStar_Pervasives_Native.None))))
                                                             else
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives_Native.None))))
                                                            uu___1))) uu___1))))
                               uu___1)))
              | FStar_Reflection_V2_Data.Tv_UInst (f, uu___1) ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> FStar_Pervasives_Native.None)))
              | uu___1 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> FStar_Pervasives_Native.None))))
             uu___)
let rec (st_term_abs_take_n_args :
  Prims.nat ->
    Pulse_Syntax_Base.st_term -> (Pulse_Syntax_Base.st_term * Prims.nat))
  =
  fun n_args ->
    fun t ->
      if n_args = Prims.int_zero
      then (t, Prims.int_zero)
      else
        (match t.Pulse_Syntax_Base.term1 with
         | Pulse_Syntax_Base.Tm_Abs
             { Pulse_Syntax_Base.b = uu___1; Pulse_Syntax_Base.q = uu___2;
               Pulse_Syntax_Base.ascription = uu___3;
               Pulse_Syntax_Base.body = body;_}
             -> st_term_abs_take_n_args (n_args - Prims.int_one) body
         | uu___1 -> (t, n_args))
let rec (term_abs_take_n_args :
  Prims.nat ->
    FStar_Reflection_Types.term -> (FStar_Reflection_Types.term * Prims.nat))
  =
  fun n_args ->
    fun t ->
      if n_args = Prims.int_zero
      then (t, Prims.int_zero)
      else
        (match FStar_Reflection_V2_Builtins.inspect_ln t with
         | FStar_Reflection_V2_Data.Tv_Abs (uu___1, body) ->
             term_abs_take_n_args (n_args - Prims.int_one) body
         | uu___1 -> (t, n_args))
let (abs_take_n_args :
  Prims.nat ->
    (Pulse_Syntax_Base.st_term, FStar_Reflection_Types.term)
      FStar_Pervasives.either ->
      (((Pulse_Syntax_Base.st_term, FStar_Reflection_Types.term)
         FStar_Pervasives.either * Prims.nat),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun n_args ->
         fun t ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   match t with
                   | FStar_Pervasives.Inl t1 ->
                       (match st_term_abs_take_n_args n_args t1 with
                        | (t2, n_args1) ->
                            ((FStar_Pervasives.Inl t2), n_args1))
                   | FStar_Pervasives.Inr t1 ->
                       (match term_abs_take_n_args n_args t1 with
                        | (t2, n_args1) ->
                            ((FStar_Pervasives.Inr t2), n_args1))))) uu___1
        uu___
let rec (unascribe :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       match FStar_Reflection_V2_Builtins.inspect_ln t with
       | FStar_Reflection_V2_Data.Tv_AscribedT (e, uu___, uu___1, uu___2) ->
           Obj.magic (Obj.repr (unascribe e))
       | FStar_Reflection_V2_Data.Tv_AscribedC (e, uu___, uu___1, uu___2) ->
           Obj.magic (Obj.repr (unascribe e))
       | uu___ ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> t))))
      uu___
let (maybe_inline :
  env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (Pulse_Syntax_Base.st_term FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun head ->
      fun arg ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (216)) (Prims.of_int (2))
                   (Prims.of_int (217)) (Prims.of_int (44)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (218)) (Prims.of_int (2))
                   (Prims.of_int (302)) (Prims.of_int (46)))))
          (Obj.magic
             (debug g
                (fun uu___ ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (217)) (Prims.of_int (22))
                              (Prims.of_int (217)) (Prims.of_int (43)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "prims.fst"
                              (Prims.of_int (611)) (Prims.of_int (19))
                              (Prims.of_int (611)) (Prims.of_int (31)))))
                     (Obj.magic (Pulse_Syntax_Printer.term_to_string head))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             Prims.strcat "Considering inlining "
                               (Prims.strcat uu___1 "\n"))))))
          (fun uu___ ->
             (fun uu___ ->
                match head_and_args head with
                | FStar_Pervasives_Native.None ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> FStar_Pervasives_Native.None)))
                | FStar_Pervasives_Native.Some (head1, args) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Extract.Main.fst"
                                     (Prims.of_int (221)) (Prims.of_int (4))
                                     (Prims.of_int (223)) (Prims.of_int (41)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Extract.Main.fst"
                                     (Prims.of_int (224)) (Prims.of_int (4))
                                     (Prims.of_int (302)) (Prims.of_int (46)))))
                            (Obj.magic
                               (debug g
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (221))
                                                (Prims.of_int (22))
                                                (Prims.of_int (223))
                                                (Prims.of_int (40)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (221))
                                                (Prims.of_int (22))
                                                (Prims.of_int (223))
                                                (Prims.of_int (40)))))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Extract.Main.fst"
                                                      (Prims.of_int (222))
                                                      (Prims.of_int (22))
                                                      (Prims.of_int (222))
                                                      (Prims.of_int (45)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Printf.fst"
                                                      (Prims.of_int (122))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (124))
                                                      (Prims.of_int (44)))))
                                             (Obj.magic
                                                (FStar_Tactics_V2_Builtins.term_to_string
                                                   head1))
                                             (fun uu___2 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___3 ->
                                                     fun x ->
                                                       Prims.strcat
                                                         (Prims.strcat
                                                            "head="
                                                            (Prims.strcat
                                                               uu___2
                                                               " with "))
                                                         (Prims.strcat
                                                            (Prims.string_of_int
                                                               x) " args\n")))))
                                       (fun uu___2 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___3 ->
                                               uu___2
                                                 (FStar_List_Tot_Base.length
                                                    args))))))
                            (fun uu___1 ->
                               (fun uu___1 ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (224))
                                                (Prims.of_int (10))
                                                (Prims.of_int (224))
                                                (Prims.of_int (34)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (224))
                                                (Prims.of_int (4))
                                                (Prims.of_int (302))
                                                (Prims.of_int (46)))))
                                       (Obj.magic (maybe_unfold_head g head1))
                                       (fun uu___2 ->
                                          (fun uu___2 ->
                                             match uu___2 with
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (226))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (227))
                                                               (Prims.of_int (52)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (228))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (228))
                                                               (Prims.of_int (10)))))
                                                      (Obj.magic
                                                         (debug g
                                                            (fun uu___3 ->
                                                               FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (51)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_V2_Builtins.term_to_string
                                                                    head1))
                                                                 (fun uu___4
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "No unfolding of "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    "\n"))))))
                                                      (fun uu___3 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              FStar_Pervasives_Native.None)))
                                             | FStar_Pervasives_Native.Some
                                                 def ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (235))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (235))
                                                               (Prims.of_int (26)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (235))
                                                               (Prims.of_int (29))
                                                               (Prims.of_int (302))
                                                               (Prims.of_int (46)))))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            fun a ->
                                                              Pulse_Syntax_Pure.wr
                                                                a
                                                                FStar_Range.range_0))
                                                      (fun uu___3 ->
                                                         (fun as_term ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (21)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (46)))))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    (FStar_List_Tot_Base.map
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (t, q) ->
                                                                    ((as_term
                                                                    t),
                                                                    (if
                                                                    FStar_Reflection_V2_Data.uu___is_Q_Implicit
                                                                    q
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.Implicit
                                                                    else
                                                                    FStar_Pervasives_Native.None)))
                                                                    args)
                                                                    [
                                                                    (arg,
                                                                    FStar_Pervasives_Native.None)]))
                                                                 (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    all_args
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_List_Tot_Base.length
                                                                    all_args))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    n_args ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (abs_take_n_args
                                                                    n_args
                                                                    def))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (body,
                                                                    remaining_args)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_List_Tot_Base.splitAt
                                                                    (n_args -
                                                                    remaining_args)
                                                                    all_args))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (args1,
                                                                    rest) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_List_Tot_Base.fold_right
                                                                    (fun arg1
                                                                    ->
                                                                    fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (i,
                                                                    subst) ->
                                                                    ((i +
                                                                    Prims.int_one),
                                                                    ((FStar_Reflection_Typing.DT
                                                                    (i,
                                                                    (FStar_Pervasives_Native.fst
                                                                    arg1)))
                                                                    ::
                                                                    subst)))
                                                                    args1
                                                                    (Prims.int_zero,
                                                                    [])))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (uu___6,
                                                                    subst) ->
                                                                    (match body
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Inl
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body1
                                                                    subst))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    applied_body
                                                                    ->
                                                                    match rest
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    applied_body)))
                                                                    | 
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (79)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (fun x ->
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    (FStar_Pervasives_Native.fst
                                                                    x)) rest))
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
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (266))
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
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    head1))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Partial or over application of inlined Pulse definition is not yet supported\n"
                                                                    (Prims.strcat
                                                                    uu___9
                                                                    " has "))
                                                                    (Prims.strcat
                                                                    (Prims.string_of_int
                                                                    x)
                                                                    " arguments, but "))
                                                                    (Prims.strcat
                                                                    x1
                                                                    " were left unapplied")))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    uu___9
                                                                    (FStar_List_Tot_Base.length
                                                                    args1)))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    uu___9
                                                                    uu___8))))
                                                                    uu___8)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    uu___8))))
                                                                    uu___7))
                                                                    | 
                                                                    FStar_Pervasives.Inr
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (unascribe
                                                                    (Pulse_Syntax_Naming.subst_host_term
                                                                    body1
                                                                    subst)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    applied_body
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    fun head2
                                                                    ->
                                                                    fun arg1
                                                                    ->
                                                                    fun
                                                                    arg_qual
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    =
                                                                    (Pulse_Syntax_Pure.wr
                                                                    head2
                                                                    (FStar_Reflection_V2_Builtins.range_of_term
                                                                    head2));
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    =
                                                                    arg_qual;
                                                                    Pulse_Syntax_Base.arg
                                                                    = arg1
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    FStar_Range.range_0;
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    Pulse_Syntax_Base.default_effect_hint
                                                                    }))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    mk_st_app
                                                                    ->
                                                                    match rest
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    FStar_Reflection_V2_Builtins.inspect_ln
                                                                    applied_body
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V2_Data.Tv_App
                                                                    (head2,
                                                                    (arg1,
                                                                    aqual))
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    mk_st_app
                                                                    head2
                                                                    (Pulse_Syntax_Pure.wr
                                                                    arg1
                                                                    (FStar_Reflection_V2_Builtins.range_of_term
                                                                    arg1))
                                                                    (if
                                                                    FStar_Reflection_V2_Data.uu___is_Q_Implicit
                                                                    aqual
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.Implicit
                                                                    else
                                                                    FStar_Pervasives_Native.None)))
                                                                    | 
                                                                    uu___7 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    applied_body))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "Cannot inline F* definitions of stt terms whose body is not an application; got "
                                                                    (Prims.strcat
                                                                    uu___8 "")))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    uu___8))))
                                                                    | 
                                                                    rest1 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    match 
                                                                    FStar_List_Tot_Base.splitAt
                                                                    ((FStar_List_Tot_Base.length
                                                                    rest1) -
                                                                    Prims.int_one)
                                                                    rest1
                                                                    with
                                                                    | 
                                                                    (rest2,
                                                                    last::[])
                                                                    ->
                                                                    mk_st_app
                                                                    (FStar_List_Tot_Base.fold_left
                                                                    (fun
                                                                    head2 ->
                                                                    fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (tm,
                                                                    qual) ->
                                                                    FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    (head2,
                                                                    (tm,
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    qual
                                                                    then
                                                                    FStar_Reflection_V2_Data.Q_Implicit
                                                                    else
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))))
                                                                    applied_body
                                                                    rest2)
                                                                    (FStar_Pervasives_Native.fst
                                                                    last)
                                                                    (FStar_Pervasives_Native.snd
                                                                    last)))))
                                                                    uu___7)))
                                                                    uu___7))))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                           uu___3))) uu___2)))
                                 uu___1)))) uu___)
let (fresh : env -> Pulse_Syntax_Base.var) =
  fun g -> Pulse_Typing_Env.fresh g.coreenv
let (push_binding :
  env -> Pulse_Syntax_Base.var -> Pulse_Syntax_Base.binder -> env) =
  fun g ->
    fun x ->
      fun b ->
        {
          uenv_inner = (g.uenv_inner);
          coreenv =
            (Pulse_Typing_Env.push_binding g.coreenv x
               b.Pulse_Syntax_Base.binder_ppname
               b.Pulse_Syntax_Base.binder_ty)
        }
let (with_open :
  env ->
    Pulse_Syntax_Base.binder ->
      Pulse_Syntax_Base.st_term ->
        (env ->
           Pulse_Syntax_Base.st_term ->
             (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
          -> (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun b ->
      fun e ->
        fun f ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                     (Prims.of_int (311)) (Prims.of_int (10))
                     (Prims.of_int (311)) (Prims.of_int (17)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                     (Prims.of_int (311)) (Prims.of_int (20))
                     (Prims.of_int (314)) (Prims.of_int (22)))))
            (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> fresh g))
            (fun uu___ ->
               (fun x ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (312)) (Prims.of_int (10))
                                (Prims.of_int (312)) (Prims.of_int (82)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (312)) (Prims.of_int (85))
                                (Prims.of_int (314)) (Prims.of_int (22)))))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ ->
                             Pulse_Syntax_Naming.open_st_term' e
                               (Pulse_Syntax_Pure.tm_var
                                  {
                                    Pulse_Syntax_Base.nm_index = x;
                                    Pulse_Syntax_Base.nm_ppname =
                                      (b.Pulse_Syntax_Base.binder_ppname)
                                  }) Prims.int_zero))
                       (fun uu___ ->
                          (fun e1 ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (313))
                                           (Prims.of_int (10))
                                           (Prims.of_int (313))
                                           (Prims.of_int (34)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (314))
                                           (Prims.of_int (2))
                                           (Prims.of_int (314))
                                           (Prims.of_int (22)))))
                                  (Obj.magic (f (push_binding g x b) e1))
                                  (fun e2 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___ ->
                                          Pulse_Syntax_Naming.close_st_term'
                                            e2 x Prims.int_zero)))) uu___)))
                 uu___)
let (is_internal_binder :
  Pulse_Syntax_Base.binder ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (318)) (Prims.of_int (10)) (Prims.of_int (318))
               (Prims.of_int (39)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (319)) (Prims.of_int (2)) (Prims.of_int (324))
               (Prims.of_int (11)))))
      (Obj.magic
         (FStar_Tactics_Unseal.unseal
            (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name))
      (fun s ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
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
                Pulse_Syntax_Base.default_effect_hint
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
  env ->
    Pulse_Syntax_Base.st_term ->
      (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (366)) (Prims.of_int (16))
                 (Prims.of_int (366)) (Prims.of_int (31)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (366)) (Prims.of_int (36))
                 (Prims.of_int (428)) (Prims.of_int (23)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              fun t ->
                {
                  Pulse_Syntax_Base.term1 = t;
                  Pulse_Syntax_Base.range1 = (e.Pulse_Syntax_Base.range1);
                  Pulse_Syntax_Base.effect_tag =
                    (e.Pulse_Syntax_Base.effect_tag)
                }))
        (fun uu___ ->
           (fun ret ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (367)) (Prims.of_int (22))
                            (Prims.of_int (367)) (Prims.of_int (54)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (369)) (Prims.of_int (2))
                            (Prims.of_int (428)) (Prims.of_int (23)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ ->
                         fun b -> fun e1 -> with_open g b e1 simplify_st_term))
                   (fun uu___ ->
                      (fun with_open1 ->
                         match e.Pulse_Syntax_Base.term1 with
                         | Pulse_Syntax_Base.Tm_Return uu___ ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> e)))
                         | Pulse_Syntax_Base.Tm_IntroPure uu___ ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> e)))
                         | Pulse_Syntax_Base.Tm_ElimExists uu___ ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> e)))
                         | Pulse_Syntax_Base.Tm_IntroExists uu___ ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> e)))
                         | Pulse_Syntax_Base.Tm_STApp uu___ ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> e)))
                         | Pulse_Syntax_Base.Tm_Rewrite uu___ ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> e)))
                         | Pulse_Syntax_Base.Tm_Admit uu___ ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> e)))
                         | Pulse_Syntax_Base.Tm_ProofHintWithBinders uu___ ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> e)))
                         | Pulse_Syntax_Base.Tm_Abs
                             { Pulse_Syntax_Base.b = b;
                               Pulse_Syntax_Base.q = q;
                               Pulse_Syntax_Base.ascription = ascription;
                               Pulse_Syntax_Base.body = body;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (380))
                                              (Prims.of_int (8))
                                              (Prims.of_int (380))
                                              (Prims.of_int (62)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (380))
                                              (Prims.of_int (4))
                                              (Prims.of_int (380))
                                              (Prims.of_int (62)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (380))
                                                    (Prims.of_int (18))
                                                    (Prims.of_int (380))
                                                    (Prims.of_int (59)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (380))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (380))
                                                    (Prims.of_int (62)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (380))
                                                          (Prims.of_int (43))
                                                          (Prims.of_int (380))
                                                          (Prims.of_int (59)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (380))
                                                          (Prims.of_int (18))
                                                          (Prims.of_int (380))
                                                          (Prims.of_int (59)))))
                                                 (Obj.magic
                                                    (with_open1 b body))
                                                 (fun uu___ ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___1 ->
                                                         {
                                                           Pulse_Syntax_Base.b
                                                             = b;
                                                           Pulse_Syntax_Base.q
                                                             = q;
                                                           Pulse_Syntax_Base.ascription
                                                             = ascription;
                                                           Pulse_Syntax_Base.body
                                                             = uu___
                                                         }))))
                                           (fun uu___ ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   Pulse_Syntax_Base.Tm_Abs
                                                     uu___))))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> ret uu___))))
                         | Pulse_Syntax_Base.Tm_Bind
                             { Pulse_Syntax_Base.binder = binder;
                               Pulse_Syntax_Base.head1 = head;
                               Pulse_Syntax_Base.body1 = body;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (383))
                                              (Prims.of_int (29))
                                              (Prims.of_int (383))
                                              (Prims.of_int (54)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (384))
                                              (Prims.of_int (4))
                                              (Prims.of_int (398))
                                              (Prims.of_int (7)))))
                                     (Obj.magic (is_internal_binder binder))
                                     (fun uu___ ->
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
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (389))
                                                             (Prims.of_int (25))
                                                             (Prims.of_int (389))
                                                             (Prims.of_int (39)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (389))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (390))
                                                             (Prims.of_int (66)))))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___1 ->
                                                          is_return head))
                                                    (fun uu___1 ->
                                                       (fun uu___1 ->
                                                          match uu___1 with
                                                          | FStar_Pervasives_Native.Some
                                                              head1 ->
                                                              Obj.magic
                                                                (simplify_st_term
                                                                   g
                                                                   (Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    [
                                                                    FStar_Reflection_Typing.DT
                                                                    (Prims.int_zero,
                                                                    head1)])))
                                                         uu___1))
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
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (395))
                                                                  (Prims.of_int (19))
                                                                  (Prims.of_int (395))
                                                                  (Prims.of_int (42)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (395))
                                                                  (Prims.of_int (45))
                                                                  (Prims.of_int (397))
                                                                  (Prims.of_int (44)))))
                                                         (Obj.magic
                                                            (simplify_st_term
                                                               g head))
                                                         (fun uu___2 ->
                                                            (fun head1 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (40)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (44)))))
                                                                    (
                                                                    Obj.magic
                                                                    (with_open1
                                                                    binder
                                                                    body))
                                                                    (
                                                                    fun body1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
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
                                                              uu___2))))
                                          uu___)))
                         | Pulse_Syntax_Base.Tm_TotBind
                             { Pulse_Syntax_Base.binder1 = binder;
                               Pulse_Syntax_Base.head2 = head;
                               Pulse_Syntax_Base.body2 = body;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (401))
                                              (Prims.of_int (8))
                                              (Prims.of_int (401))
                                              (Prims.of_int (67)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (401))
                                              (Prims.of_int (4))
                                              (Prims.of_int (401))
                                              (Prims.of_int (67)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (401))
                                                    (Prims.of_int (22))
                                                    (Prims.of_int (401))
                                                    (Prims.of_int (64)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (401))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (401))
                                                    (Prims.of_int (67)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (401))
                                                          (Prims.of_int (43))
                                                          (Prims.of_int (401))
                                                          (Prims.of_int (64)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (401))
                                                          (Prims.of_int (22))
                                                          (Prims.of_int (401))
                                                          (Prims.of_int (64)))))
                                                 (Obj.magic
                                                    (with_open1 binder body))
                                                 (fun uu___ ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___1 ->
                                                         {
                                                           Pulse_Syntax_Base.binder1
                                                             = binder;
                                                           Pulse_Syntax_Base.head2
                                                             = head;
                                                           Pulse_Syntax_Base.body2
                                                             = uu___
                                                         }))))
                                           (fun uu___ ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   Pulse_Syntax_Base.Tm_TotBind
                                                     uu___))))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> ret uu___))))
                         | Pulse_Syntax_Base.Tm_If
                             { Pulse_Syntax_Base.b1 = b;
                               Pulse_Syntax_Base.then_ = then_;
                               Pulse_Syntax_Base.else_ = else_;
                               Pulse_Syntax_Base.post1 = post;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (404))
                                              (Prims.of_int (8))
                                              (Prims.of_int (404))
                                              (Prims.of_int (95)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (404))
                                              (Prims.of_int (4))
                                              (Prims.of_int (404))
                                              (Prims.of_int (95)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (404))
                                                    (Prims.of_int (17))
                                                    (Prims.of_int (404))
                                                    (Prims.of_int (92)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (404))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (404))
                                                    (Prims.of_int (95)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (404))
                                                          (Prims.of_int (28))
                                                          (Prims.of_int (404))
                                                          (Prims.of_int (52)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (404))
                                                          (Prims.of_int (17))
                                                          (Prims.of_int (404))
                                                          (Prims.of_int (92)))))
                                                 (Obj.magic
                                                    (simplify_st_term g then_))
                                                 (fun uu___ ->
                                                    (fun uu___ ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (86)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (92)))))
                                                            (Obj.magic
                                                               (simplify_st_term
                                                                  g else_))
                                                            (fun uu___1 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___2
                                                                    ->
                                                                    {
                                                                    Pulse_Syntax_Base.b1
                                                                    = b;
                                                                    Pulse_Syntax_Base.then_
                                                                    = uu___;
                                                                    Pulse_Syntax_Base.else_
                                                                    = uu___1;
                                                                    Pulse_Syntax_Base.post1
                                                                    = post
                                                                    }))))
                                                      uu___)))
                                           (fun uu___ ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   Pulse_Syntax_Base.Tm_If
                                                     uu___))))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> ret uu___))))
                         | Pulse_Syntax_Base.Tm_Match
                             { Pulse_Syntax_Base.sc = sc;
                               Pulse_Syntax_Base.returns_ = returns_;
                               Pulse_Syntax_Base.brs = brs;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (407))
                                              (Prims.of_int (8))
                                              (Prims.of_int (407))
                                              (Prims.of_int (72)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (407))
                                              (Prims.of_int (4))
                                              (Prims.of_int (407))
                                              (Prims.of_int (72)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (407))
                                                    (Prims.of_int (20))
                                                    (Prims.of_int (407))
                                                    (Prims.of_int (69)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (407))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (407))
                                                    (Prims.of_int (72)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (407))
                                                          (Prims.of_int (40))
                                                          (Prims.of_int (407))
                                                          (Prims.of_int (69)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (407))
                                                          (Prims.of_int (20))
                                                          (Prims.of_int (407))
                                                          (Prims.of_int (69)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Util.map
                                                       (simplify_branch g)
                                                       brs))
                                                 (fun uu___ ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___1 ->
                                                         {
                                                           Pulse_Syntax_Base.sc
                                                             = sc;
                                                           Pulse_Syntax_Base.returns_
                                                             = returns_;
                                                           Pulse_Syntax_Base.brs
                                                             = uu___
                                                         }))))
                                           (fun uu___ ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   Pulse_Syntax_Base.Tm_Match
                                                     uu___))))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> ret uu___))))
                         | Pulse_Syntax_Base.Tm_While
                             { Pulse_Syntax_Base.invariant = invariant;
                               Pulse_Syntax_Base.condition = condition;
                               Pulse_Syntax_Base.condition_var =
                                 condition_var;
                               Pulse_Syntax_Base.body3 = body;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (410))
                                              (Prims.of_int (20))
                                              (Prims.of_int (410))
                                              (Prims.of_int (48)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (410))
                                              (Prims.of_int (51))
                                              (Prims.of_int (412))
                                              (Prims.of_int (76)))))
                                     (Obj.magic
                                        (simplify_st_term g condition))
                                     (fun uu___ ->
                                        (fun condition1 ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (411))
                                                         (Prims.of_int (15))
                                                         (Prims.of_int (411))
                                                         (Prims.of_int (38)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (412))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (412))
                                                         (Prims.of_int (74)))))
                                                (Obj.magic
                                                   (simplify_st_term g body))
                                                (fun body1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___ ->
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
                                                            (e.Pulse_Syntax_Base.effect_tag)
                                                        })))) uu___)))
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
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (415))
                                              (Prims.of_int (16))
                                              (Prims.of_int (415))
                                              (Prims.of_int (40)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (415))
                                              (Prims.of_int (43))
                                              (Prims.of_int (417))
                                              (Prims.of_int (71)))))
                                     (Obj.magic (simplify_st_term g body1))
                                     (fun uu___ ->
                                        (fun body11 ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (416))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (416))
                                                         (Prims.of_int (40)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (417))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (417))
                                                         (Prims.of_int (69)))))
                                                (Obj.magic
                                                   (simplify_st_term g body2))
                                                (fun body21 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___ ->
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
                                                            (e.Pulse_Syntax_Base.effect_tag)
                                                        })))) uu___)))
                         | Pulse_Syntax_Base.Tm_WithLocal
                             { Pulse_Syntax_Base.binder2 = binder;
                               Pulse_Syntax_Base.initializer1 = initializer1;
                               Pulse_Syntax_Base.body4 = body;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (420))
                                              (Prims.of_int (8))
                                              (Prims.of_int (420))
                                              (Prims.of_int (76)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (420))
                                              (Prims.of_int (4))
                                              (Prims.of_int (420))
                                              (Prims.of_int (76)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (420))
                                                    (Prims.of_int (24))
                                                    (Prims.of_int (420))
                                                    (Prims.of_int (73)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (420))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (420))
                                                    (Prims.of_int (76)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (420))
                                                          (Prims.of_int (52))
                                                          (Prims.of_int (420))
                                                          (Prims.of_int (73)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (420))
                                                          (Prims.of_int (24))
                                                          (Prims.of_int (420))
                                                          (Prims.of_int (73)))))
                                                 (Obj.magic
                                                    (with_open1 binder body))
                                                 (fun uu___ ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___1 ->
                                                         {
                                                           Pulse_Syntax_Base.binder2
                                                             = binder;
                                                           Pulse_Syntax_Base.initializer1
                                                             = initializer1;
                                                           Pulse_Syntax_Base.body4
                                                             = uu___
                                                         }))))
                                           (fun uu___ ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   Pulse_Syntax_Base.Tm_WithLocal
                                                     uu___))))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> ret uu___))))
                         | Pulse_Syntax_Base.Tm_WithLocalArray
                             { Pulse_Syntax_Base.binder3 = binder;
                               Pulse_Syntax_Base.initializer2 = initializer1;
                               Pulse_Syntax_Base.length = length;
                               Pulse_Syntax_Base.body5 = body;_}
                             ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (423))
                                              (Prims.of_int (8))
                                              (Prims.of_int (423))
                                              (Prims.of_int (89)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (423))
                                              (Prims.of_int (4))
                                              (Prims.of_int (423))
                                              (Prims.of_int (89)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (423))
                                                    (Prims.of_int (29))
                                                    (Prims.of_int (423))
                                                    (Prims.of_int (86)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (423))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (423))
                                                    (Prims.of_int (89)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (423))
                                                          (Prims.of_int (65))
                                                          (Prims.of_int (423))
                                                          (Prims.of_int (86)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (423))
                                                          (Prims.of_int (29))
                                                          (Prims.of_int (423))
                                                          (Prims.of_int (86)))))
                                                 (Obj.magic
                                                    (with_open1 binder body))
                                                 (fun uu___ ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___1 ->
                                                         {
                                                           Pulse_Syntax_Base.binder3
                                                             = binder;
                                                           Pulse_Syntax_Base.initializer2
                                                             = initializer1;
                                                           Pulse_Syntax_Base.length
                                                             = length;
                                                           Pulse_Syntax_Base.body5
                                                             = uu___
                                                         }))))
                                           (fun uu___ ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   Pulse_Syntax_Base.Tm_WithLocalArray
                                                     uu___))))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> ret uu___))))
                         | Pulse_Syntax_Base.Tm_WithInv
                             { Pulse_Syntax_Base.name1 = uu___;
                               Pulse_Syntax_Base.body6 = body;
                               Pulse_Syntax_Base.returns_inv = uu___1;_}
                             ->
                             Obj.magic (Obj.repr (simplify_st_term g body))
                         | Pulse_Syntax_Base.Tm_Unreachable ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ -> e)))) uu___))) uu___)
and (simplify_branch :
  env ->
    Pulse_Syntax_Base.branch ->
      (Pulse_Syntax_Base.branch, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun b ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (431)) (Prims.of_int (18))
                 (Prims.of_int (431)) (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (430)) (Prims.of_int (55))
                 (Prims.of_int (435)) (Prims.of_int (62)))))
        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> b))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (pat, body) ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (432)) (Prims.of_int (17))
                                (Prims.of_int (432)) (Prims.of_int (37)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (431)) (Prims.of_int (22))
                                (Prims.of_int (435)) (Prims.of_int (62)))))
                       (Obj.magic (extend_env_pat g pat))
                       (fun uu___1 ->
                          (fun uu___1 ->
                             match uu___1 with
                             | (g1, uu___2, bs) ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (433))
                                               (Prims.of_int (13))
                                               (Prims.of_int (433))
                                               (Prims.of_int (56)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (433))
                                               (Prims.of_int (59))
                                               (Prims.of_int (435))
                                               (Prims.of_int (62)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 ->
                                            Pulse_Checker_Match.open_st_term_bs
                                              body bs))
                                      (fun uu___3 ->
                                         (fun body1 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (434))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (434))
                                                          (Prims.of_int (36)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (435))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (435))
                                                          (Prims.of_int (62)))))
                                                 (Obj.magic
                                                    (simplify_st_term g1
                                                       body1))
                                                 (fun body2 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         (pat,
                                                           (Pulse_Syntax_Naming.close_st_term_n
                                                              body2
                                                              (FStar_List_Tot_Base.map
                                                                 FStar_Pervasives_Native.fst
                                                                 bs)))))))
                                           uu___3))) uu___1))) uu___)
let (erase_type_for_extraction :
  env ->
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
                     (tcenv_of_env g) t))) uu___1 uu___
let rec (erase_ghost_subterms :
  env ->
    Pulse_Syntax_Base.st_term ->
      (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (443)) (Prims.of_int (22))
                 (Prims.of_int (443)) (Prims.of_int (50)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (443)) (Prims.of_int (53))
                 (Prims.of_int (526)) (Prims.of_int (5)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> fun g1 -> Pulse_Typing_Env.fresh g1.coreenv))
        (fun uu___ ->
           (fun fresh1 ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (445)) (Prims.of_int (6))
                            (Prims.of_int (445)) (Prims.of_int (77)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (445)) (Prims.of_int (82))
                            (Prims.of_int (526)) (Prims.of_int (5)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ ->
                         fun g1 ->
                           fun x ->
                             fun b ->
                               {
                                 uenv_inner = (g1.uenv_inner);
                                 coreenv =
                                   (Pulse_Typing_Env.push_binding g1.coreenv
                                      x b.Pulse_Syntax_Base.binder_ppname
                                      b.Pulse_Syntax_Base.binder_ty)
                               }))
                   (fun uu___ ->
                      (fun push_binding1 ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (447))
                                       (Prims.of_int (71))
                                       (Prims.of_int (451))
                                       (Prims.of_int (24)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (451))
                                       (Prims.of_int (27))
                                       (Prims.of_int (526))
                                       (Prims.of_int (5)))))
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___ ->
                                    fun g1 ->
                                      fun b ->
                                        fun e ->
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Extract.Main.fst"
                                                     (Prims.of_int (448))
                                                     (Prims.of_int (12))
                                                     (Prims.of_int (448))
                                                     (Prims.of_int (19)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Extract.Main.fst"
                                                     (Prims.of_int (448))
                                                     (Prims.of_int (22))
                                                     (Prims.of_int (451))
                                                     (Prims.of_int (24)))))
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 -> fresh1 g1))
                                            (fun uu___1 ->
                                               (fun x ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Extract.Main.fst"
                                                                (Prims.of_int (449))
                                                                (Prims.of_int (12))
                                                                (Prims.of_int (449))
                                                                (Prims.of_int (84)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Extract.Main.fst"
                                                                (Prims.of_int (449))
                                                                (Prims.of_int (87))
                                                                (Prims.of_int (451))
                                                                (Prims.of_int (24)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___1 ->
                                                             Pulse_Syntax_Naming.open_st_term'
                                                               e
                                                               (Pulse_Syntax_Pure.tm_var
                                                                  {
                                                                    Pulse_Syntax_Base.nm_index
                                                                    = x;
                                                                    Pulse_Syntax_Base.nm_ppname
                                                                    =
                                                                    (b.Pulse_Syntax_Base.binder_ppname)
                                                                  })
                                                               Prims.int_zero))
                                                       (fun uu___1 ->
                                                          (fun e1 ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (55)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (24)))))
                                                                  (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    (push_binding1
                                                                    g1 x b)
                                                                    e1))
                                                                  (fun e2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Syntax_Naming.close_st_term'
                                                                    e2 x
                                                                    Prims.int_zero))))
                                                            uu___1))) uu___1)))
                              (fun uu___ ->
                                 (fun open_erase_close ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (454))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (454))
                                                  (Prims.of_int (94)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (455))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (526))
                                                  (Prims.of_int (5)))))
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___ ->
                                               {
                                                 Pulse_Syntax_Base.term1 =
                                                   (Pulse_Syntax_Base.Tm_Return
                                                      {
                                                        Pulse_Syntax_Base.expected_type
                                                          =
                                                          Pulse_Syntax_Pure.tm_unknown;
                                                        Pulse_Syntax_Base.insert_eq
                                                          = false;
                                                        Pulse_Syntax_Base.term
                                                          = unit_val
                                                      });
                                                 Pulse_Syntax_Base.range1 =
                                                   (p.Pulse_Syntax_Base.range1);
                                                 Pulse_Syntax_Base.effect_tag
                                                   =
                                                   (p.Pulse_Syntax_Base.effect_tag)
                                               }))
                                         (fun uu___ ->
                                            (fun unit_tm ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (456))
                                                             (Prims.of_int (27))
                                                             (Prims.of_int (456))
                                                             (Prims.of_int (42)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (457))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (526))
                                                             (Prims.of_int (5)))))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___ ->
                                                          fun t ->
                                                            {
                                                              Pulse_Syntax_Base.term1
                                                                = t;
                                                              Pulse_Syntax_Base.range1
                                                                =
                                                                (p.Pulse_Syntax_Base.range1);
                                                              Pulse_Syntax_Base.effect_tag
                                                                =
                                                                (p.Pulse_Syntax_Base.effect_tag)
                                                            }))
                                                    (fun uu___ ->
                                                       (fun ret ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (457))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (457))
                                                                    (Prims.of_int (18)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (457))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (5)))))
                                                               (Obj.magic
                                                                  (is_erasable
                                                                    p))
                                                               (fun uu___ ->
                                                                  (fun uu___
                                                                    ->
                                                                    if uu___
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    unit_tm)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    p.Pulse_Syntax_Base.term1
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_IntroPure
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    unit_tm))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_ElimExists
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    unit_tm))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_IntroExists
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    unit_tm))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Rewrite
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    unit_tm))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Abs
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
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (467))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (467))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (open_erase_close
                                                                    g b body))
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
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
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Return
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    p))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_STApp
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    p))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = binder;
                                                                    Pulse_Syntax_Base.head1
                                                                    = head;
                                                                    Pulse_Syntax_Base.body1
                                                                    = body;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (is_erasable
                                                                    head))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    if uu___2
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    [
                                                                    FStar_Reflection_Typing.DT
                                                                    (Prims.int_zero,
                                                                    unit_val)]))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g body1))
                                                                    uu___3))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g head))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    head1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (open_erase_close
                                                                    g binder
                                                                    body))
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
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
                                                                    uu___4)))
                                                                    uu___2))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_TotBind
                                                                    {
                                                                    Pulse_Syntax_Base.binder1
                                                                    = binder;
                                                                    Pulse_Syntax_Base.head2
                                                                    = head;
                                                                    Pulse_Syntax_Base.body2
                                                                    = body;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (erase_type_for_extraction
                                                                    g
                                                                    binder.Pulse_Syntax_Base.binder_ty))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    if uu___2
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    [
                                                                    FStar_Reflection_Typing.DT
                                                                    (Prims.int_zero,
                                                                    unit_val)]))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g body1))
                                                                    uu___3))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (open_erase_close
                                                                    g binder
                                                                    body))
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ret
                                                                    (Pulse_Syntax_Base.Tm_TotBind
                                                                    {
                                                                    Pulse_Syntax_Base.binder1
                                                                    = binder;
                                                                    Pulse_Syntax_Base.head2
                                                                    = head;
                                                                    Pulse_Syntax_Base.body2
                                                                    = body1
                                                                    })))))
                                                                    uu___2))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_If
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
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g then_))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    then_1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g else_))
                                                                    (fun
                                                                    else_1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
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
                                                                    uu___2))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Match
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
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (496))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (496))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (erase_ghost_subterms_branch
                                                                    g) brs))
                                                                    (fun brs1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
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
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_While
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
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (501))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g
                                                                    condition))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    condition1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (500))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (500))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (501))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (501))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g body))
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
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
                                                                    uu___2))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Par
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
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (504))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (504))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (504))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g body1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    body11 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g body2))
                                                                    (fun
                                                                    body21 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
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
                                                                    uu___2))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_WithLocal
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
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (509))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (509))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    (open_erase_close
                                                                    g binder
                                                                    body))
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
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
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_WithLocalArray
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
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    (open_erase_close
                                                                    g binder
                                                                    body))
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
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
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Unreachable
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    p))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Admit
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    p))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "erase_ghost_subterms: Unexpected constructor: ProofHintWithBinders should have been desugared away")
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_WithInv
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
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (80)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (80)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (77)))))
                                                                    (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g body))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    {
                                                                    Pulse_Syntax_Base.name1
                                                                    = name1;
                                                                    Pulse_Syntax_Base.body6
                                                                    = uu___2;
                                                                    Pulse_Syntax_Base.returns_inv
                                                                    =
                                                                    returns_inv
                                                                    }))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Base.Tm_WithInv
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ret
                                                                    uu___2))))))
                                                                    uu___)))
                                                         uu___))) uu___)))
                                   uu___))) uu___))) uu___)
and (erase_ghost_subterms_branch :
  env ->
    Pulse_Syntax_Base.branch ->
      (Pulse_Syntax_Base.branch, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun b ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (529)) (Prims.of_int (18))
                 (Prims.of_int (529)) (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (528)) (Prims.of_int (67))
                 (Prims.of_int (533)) (Prims.of_int (62)))))
        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> b))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (pat, body) ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (530)) (Prims.of_int (17))
                                (Prims.of_int (530)) (Prims.of_int (37)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (529)) (Prims.of_int (22))
                                (Prims.of_int (533)) (Prims.of_int (62)))))
                       (Obj.magic (extend_env_pat g pat))
                       (fun uu___1 ->
                          (fun uu___1 ->
                             match uu___1 with
                             | (g1, uu___2, bs) ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (531))
                                               (Prims.of_int (13))
                                               (Prims.of_int (531))
                                               (Prims.of_int (56)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (531))
                                               (Prims.of_int (59))
                                               (Prims.of_int (533))
                                               (Prims.of_int (62)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 ->
                                            Pulse_Checker_Match.open_st_term_bs
                                              body bs))
                                      (fun uu___3 ->
                                         (fun body1 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (532))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (532))
                                                          (Prims.of_int (40)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (533))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (533))
                                                          (Prims.of_int (62)))))
                                                 (Obj.magic
                                                    (erase_ghost_subterms g1
                                                       body1))
                                                 (fun body2 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         (pat,
                                                           (Pulse_Syntax_Naming.close_st_term_n
                                                              body2
                                                              (FStar_List_Tot_Base.map
                                                                 FStar_Pervasives_Native.fst
                                                                 bs)))))))
                                           uu___3))) uu___1))) uu___)
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
                 (Prims.of_int (537)) (Prims.of_int (24))
                 (Prims.of_int (537)) (Prims.of_int (56)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (538)) (Prims.of_int (4)) (Prims.of_int (692))
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
                            (Prims.of_int (538)) (Prims.of_int (4))
                            (Prims.of_int (540)) (Prims.of_int (36)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (541)) (Prims.of_int (4))
                            (Prims.of_int (692)) (Prims.of_int (7)))))
                   (Obj.magic
                      (debug g
                         (fun uu___ ->
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (540))
                                       (Prims.of_int (14))
                                       (Prims.of_int (540))
                                       (Prims.of_int (35)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (538))
                                       (Prims.of_int (22))
                                       (Prims.of_int (540))
                                       (Prims.of_int (35)))))
                              (Obj.magic
                                 (Pulse_Syntax_Printer.st_term_to_string p))
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (538))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (540))
                                                  (Prims.of_int (35)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (538))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (540))
                                                  (Prims.of_int (35)))))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Extract.Main.fst"
                                                        (Prims.of_int (539))
                                                        (Prims.of_int (14))
                                                        (Prims.of_int (539))
                                                        (Prims.of_int (41)))))
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
                                                     p.Pulse_Syntax_Base.range1))
                                               (fun uu___2 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___3 ->
                                                       fun x ->
                                                         Prims.strcat
                                                           (Prims.strcat
                                                              "Extracting term@"
                                                              (Prims.strcat
                                                                 uu___2 ":\n"))
                                                           (Prims.strcat x
                                                              "\n")))))
                                         (fun uu___2 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___3 -> uu___2 uu___1))))
                                   uu___1))))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (541))
                                       (Prims.of_int (7))
                                       (Prims.of_int (541))
                                       (Prims.of_int (20)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (541))
                                       (Prims.of_int (4))
                                       (Prims.of_int (692))
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
                                                              (Prims.of_int (552))
                                                              (Prims.of_int (37))
                                                              (Prims.of_int (552))
                                                              (Prims.of_int (51)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (551))
                                                              (Prims.of_int (32))
                                                              (Prims.of_int (560))
                                                              (Prims.of_int (27)))))
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
                                                                    (Prims.of_int (554))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (556))
                                                                    (Prims.of_int (37)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (556))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (560))
                                                                    (Prims.of_int (27)))))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (554))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (555))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (554))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (556))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Unseal.unseal
                                                                    b.Pulse_Syntax_Base.binder_attrs))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (term_as_mlexpr
                                                                    g1)
                                                                    uu___5))
                                                                    uu___5)))
                                                                    (
                                                                    fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    mlattrs
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (557))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (557))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (557))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (560))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body
                                                                    name1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (558))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (558))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (557))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (560))
                                                                    (Prims.of_int (27)))))
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
                                                                    mlty,
                                                                    mlattrs)]
                                                                    body2),
                                                                    Pulse_Extract_CompilerLib.e_tag_pure)))))
                                                                    uu___5)))
                                                                    uu___5)))
                                                          uu___4))
                                            | Pulse_Syntax_Base.Tm_Return
                                                {
                                                  Pulse_Syntax_Base.expected_type
                                                    = uu___3;
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
                                                              (Prims.of_int (563))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (563))
                                                              (Prims.of_int (29)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (563))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (564))
                                                              (Prims.of_int (22)))))
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
                                                              (Prims.of_int (567))
                                                              (Prims.of_int (14))
                                                              (Prims.of_int (567))
                                                              (Prims.of_int (37)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (566))
                                                              (Prims.of_int (34))
                                                              (Prims.of_int (575))
                                                              (Prims.of_int (7)))))
                                                     (Obj.magic
                                                        (maybe_inline g head
                                                           arg))
                                                     (fun uu___4 ->
                                                        (fun uu___4 ->
                                                           match uu___4 with
                                                           | FStar_Pervasives_Native.None
                                                               ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (569))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (569))
                                                                    (Prims.of_int (42)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (569))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (50)))))
                                                                    (
                                                                    Obj.magic
                                                                    (term_as_mlexpr
                                                                    g head))
                                                                    (
                                                                    fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    head1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (570))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (570))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (term_as_mlexpr
                                                                    g arg))
                                                                    (fun arg1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ((Pulse_Extract_CompilerLib.mle_app
                                                                    head1
                                                                    [arg1]),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                                    uu___5))
                                                           | FStar_Pervasives_Native.Some
                                                               t ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (84)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (574))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (574))
                                                                    (Prims.of_int (21)))))
                                                                    (
                                                                    Obj.magic
                                                                    (debug g
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    t))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    "Inlined to: "
                                                                    (Prims.strcat
                                                                    uu___6
                                                                    "\n"))))))
                                                                    (
                                                                    fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (extract
                                                                    g t))
                                                                    uu___5)))
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
                                                              (Prims.of_int (578))
                                                              (Prims.of_int (17))
                                                              (Prims.of_int (578))
                                                              (Prims.of_int (33)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (578))
                                                              (Prims.of_int (36))
                                                              (Prims.of_int (603))
                                                              (Prims.of_int (9)))))
                                                     (Obj.magic
                                                        (is_erasable head))
                                                     (fun uu___3 ->
                                                        (fun eh ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (61)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (9)))))
                                                                (Obj.magic
                                                                   (erase_type_for_extraction
                                                                    g
                                                                    binder.Pulse_Syntax_Base.binder_ty))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun et ->
                                                                    if
                                                                    eh ||
                                                                    ((Pulse_Syntax_Base.uu___is_Tm_Abs
                                                                    head.Pulse_Syntax_Base.term1)
                                                                    && et)
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (591))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (594))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    [
                                                                    FStar_Reflection_Typing.DT
                                                                    (Prims.int_zero,
                                                                    unit_val)]))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (591))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (594))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (594))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    (debug g
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (591))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    (Pulse_Show.show
                                                                    Pulse_Show.tac_showable_st_term
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
                                                                    (Prims.of_int (591))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (591))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (592))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (592))
                                                                    (Prims.of_int (41)))))
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
                                                                    Pulse_Show.tac_showable_st_term
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
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (extract
                                                                    g body1))
                                                                    uu___3)))
                                                                    uu___3))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (596))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (596))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (extract
                                                                    g head))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (head1,
                                                                    uu___5)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (597))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (597))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (596))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (602))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (extend_env
                                                                    g binder))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
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
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (602))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body
                                                                    name1))
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
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (602))
                                                                    (Prims.of_int (57)))))
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
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___4)))
                                                                    uu___3)))
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
                                                              (Prims.of_int (607))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (607))
                                                              (Prims.of_int (40)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (607))
                                                              (Prims.of_int (43))
                                                              (Prims.of_int (613))
                                                              (Prims.of_int (55)))))
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
                                                                    (Prims.of_int (608))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (608))
                                                                    (Prims.of_int (56)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (607))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (55)))))
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
                                                                    (Prims.of_int (609))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (609))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (609))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (55)))))
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
                                                                    (Prims.of_int (610))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (610))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (609))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (55)))))
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
                                                              (Prims.of_int (616))
                                                              (Prims.of_int (16))
                                                              (Prims.of_int (616))
                                                              (Prims.of_int (34)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (616))
                                                              (Prims.of_int (37))
                                                              (Prims.of_int (619))
                                                              (Prims.of_int (57)))))
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
                                                                    (Prims.of_int (617))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (617))
                                                                    (Prims.of_int (38)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (619))
                                                                    (Prims.of_int (57)))))
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
                                                                    (Prims.of_int (618))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (618))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (617))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (619))
                                                                    (Prims.of_int (57)))))
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
                                                              (Prims.of_int (622))
                                                              (Prims.of_int (17))
                                                              (Prims.of_int (622))
                                                              (Prims.of_int (36)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (622))
                                                              (Prims.of_int (39))
                                                              (Prims.of_int (634))
                                                              (Prims.of_int (46)))))
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
                                                                    (Prims.of_int (623))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (631))
                                                                    (Prims.of_int (19)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (632))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (46)))))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___4 ->
                                                                    fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (pat0,
                                                                    body) ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (624))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (624))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (623))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (631))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (extend_env_pat
                                                                    g pat0))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (g1, pat,
                                                                    bs) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (631))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (debug g1
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.pattern_to_string
                                                                    pat0))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "Extracting branch with pattern "
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (631))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Checker_Match.open_st_term_bs
                                                                    body bs))
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
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (631))
                                                                    (Prims.of_int (19)))))
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
                                                                    (pat,
                                                                    body2)))))
                                                                    uu___8)))
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
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (46)))))
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
                                                              (Prims.of_int (638))
                                                              (Prims.of_int (27))
                                                              (Prims.of_int (638))
                                                              (Prims.of_int (46)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (637))
                                                              (Prims.of_int (39))
                                                              (Prims.of_int (643))
                                                              (Prims.of_int (27)))))
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
                                                                    (Prims.of_int (639))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (639))
                                                                    (Prims.of_int (36)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (638))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (643))
                                                                    (Prims.of_int (27)))))
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
                                                                    Pulse_Extract_CompilerLib.mlty_unit,
                                                                    [])]
                                                                    condition1;
                                                                    Pulse_Extract_CompilerLib.mle_fun
                                                                    [
                                                                    ("_",
                                                                    Pulse_Extract_CompilerLib.mlty_unit,
                                                                    [])]
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
                                                              (Prims.of_int (646))
                                                              (Prims.of_int (23))
                                                              (Prims.of_int (646))
                                                              (Prims.of_int (38)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (645))
                                                              (Prims.of_int (34))
                                                              (Prims.of_int (651))
                                                              (Prims.of_int (27)))))
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
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (38)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (646))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (651))
                                                                    (Prims.of_int (27)))))
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
                                                                    Pulse_Extract_CompilerLib.mlty_unit,
                                                                    [])]
                                                                    body11;
                                                                    Pulse_Extract_CompilerLib.mle_fun
                                                                    [
                                                                    ("_",
                                                                    Pulse_Extract_CompilerLib.mlty_unit,
                                                                    [])]
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
                                                              (Prims.of_int (654))
                                                              (Prims.of_int (26))
                                                              (Prims.of_int (654))
                                                              (Prims.of_int (54)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (654))
                                                              (Prims.of_int (57))
                                                              (Prims.of_int (661))
                                                              (Prims.of_int (55)))))
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
                                                                    (Prims.of_int (655))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (655))
                                                                    (Prims.of_int (94)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (654))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (55)))))
                                                                (Obj.magic
                                                                   (extend_env
                                                                    g
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    =
                                                                    (binder.Pulse_Syntax_Base.binder_ty);
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    =
                                                                    (binder.Pulse_Syntax_Base.binder_ppname);
                                                                    Pulse_Syntax_Base.binder_attrs
                                                                    =
                                                                    (binder.Pulse_Syntax_Base.binder_attrs)
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
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (55)))))
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
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (55)))))
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
                                                                    Pulse_Extract_CompilerLib.mk_mut_mllb
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
                                            | Pulse_Syntax_Base.Tm_WithLocalArray
                                                {
                                                  Pulse_Syntax_Base.binder3 =
                                                    binder;
                                                  Pulse_Syntax_Base.initializer2
                                                    = initializer1;
                                                  Pulse_Syntax_Base.length =
                                                    length;
                                                  Pulse_Syntax_Base.body5 =
                                                    body;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (664))
                                                              (Prims.of_int (26))
                                                              (Prims.of_int (664))
                                                              (Prims.of_int (54)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (664))
                                                              (Prims.of_int (57))
                                                              (Prims.of_int (677))
                                                              (Prims.of_int (55)))))
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
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (44)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (55)))))
                                                                (Obj.magic
                                                                   (term_as_mlexpr
                                                                    g length))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun
                                                                    length1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (extend_env
                                                                    g
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    =
                                                                    (binder.Pulse_Syntax_Base.binder_ty);
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    =
                                                                    (binder.Pulse_Syntax_Base.binder_ppname);
                                                                    Pulse_Syntax_Base.binder_attrs
                                                                    =
                                                                    (binder.Pulse_Syntax_Base.binder_attrs)
                                                                    }))
                                                                    (fun
                                                                    uu___3 ->
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
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (55)))))
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
                                                                    (Prims.of_int (668))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (668))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (55)))))
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
                                                                    Pulse_Extract_CompilerLib.mk_mut_mllb
                                                                    mlident
                                                                    ([],
                                                                    mlty)
                                                                    (Pulse_Extract_CompilerLib.mle_app
                                                                    (Pulse_Extract_CompilerLib.mle_name
                                                                    (["Pulse";
                                                                    "Lib";
                                                                    "Array";
                                                                    "Core"],
                                                                    "alloc"))
                                                                    [initializer2;
                                                                    length1])])
                                                                    body2),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                          uu___3))
                                            | Pulse_Syntax_Base.Tm_WithInv
                                                {
                                                  Pulse_Syntax_Base.name1 =
                                                    uu___3;
                                                  Pulse_Syntax_Base.body6 =
                                                    body;
                                                  Pulse_Syntax_Base.returns_inv
                                                    = uu___4;_}
                                                -> Obj.repr (extract g body)
                                            | Pulse_Syntax_Base.Tm_Unreachable
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___3 ->
                                                        ((Pulse_Extract_CompilerLib.mle_app
                                                            (Pulse_Extract_CompilerLib.mle_name
                                                               (["Pulse";
                                                                "Lib";
                                                                "Core"],
                                                                 "unreachable"))
                                                            [Pulse_Extract_CompilerLib.mle_unit]),
                                                          Pulse_Extract_CompilerLib.e_tag_impure)))
                                            | Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                {
                                                  Pulse_Syntax_Base.hint_type
                                                    = uu___3;
                                                  Pulse_Syntax_Base.binders =
                                                    uu___4;
                                                  Pulse_Syntax_Base.t = t;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_V2_Derived.fail
                                                     "Unexpected constructor: ProofHintWithBinders should have been desugared away")
                                            | Pulse_Syntax_Base.Tm_Admit
                                                uu___3 ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        ((Pulse_Extract_CompilerLib.mle_app
                                                            (Pulse_Extract_CompilerLib.mle_name
                                                               ([],
                                                                 "failwith"))
                                                            [Pulse_Extract_CompilerLib.mle_unit]),
                                                          Pulse_Extract_CompilerLib.e_tag_impure))))))
                                   uu___1))) uu___))) uu___)
let rec map_dv : 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun f ->
    fun l -> match l with | [] -> [] | hd::tl -> (f hd) :: (map_dv f tl)
let rec (generalize :
  env ->
    FStar_Reflection_Types.typ ->
      Pulse_Syntax_Base.st_term FStar_Pervasives_Native.option ->
        ((env * Pulse_Extract_CompilerLib.mlty_param Prims.list *
           FStar_Reflection_Types.typ * Pulse_Syntax_Base.st_term
           FStar_Pervasives_Native.option),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun e ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (705)) (Prims.of_int (2))
                   (Prims.of_int (705)) (Prims.of_int (84)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (705)) (Prims.of_int (85))
                   (Prims.of_int (745)) (Prims.of_int (20)))))
          (Obj.magic
             (debug g
                (fun uu___ ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (705)) (Prims.of_int (63))
                              (Prims.of_int (705)) (Prims.of_int (83)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "prims.fst"
                              (Prims.of_int (611)) (Prims.of_int (19))
                              (Prims.of_int (611)) (Prims.of_int (31)))))
                     (Obj.magic (FStar_Tactics_V2_Builtins.term_to_string t))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             Prims.strcat "Generalizing arrow:\n"
                               (Prims.strcat uu___1 "\n"))))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (706)) (Prims.of_int (11))
                              (Prims.of_int (706)) (Prims.of_int (25)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (707)) (Prims.of_int (2))
                              (Prims.of_int (745)) (Prims.of_int (20)))))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           FStar_Reflection_V2_Builtins.inspect_ln t))
                     (fun uu___1 ->
                        (fun tv ->
                           match tv with
                           | FStar_Reflection_V2_Data.Tv_Arrow (b, c) ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (709))
                                                (Prims.of_int (25))
                                                (Prims.of_int (709))
                                                (Prims.of_int (43)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (708))
                                                (Prims.of_int (21))
                                                (Prims.of_int (743))
                                                (Prims.of_int (20)))))
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 ->
                                             FStar_Reflection_V2_Builtins.inspect_binder
                                               b))
                                       (fun uu___1 ->
                                          (fun uu___1 ->
                                             match uu___1 with
                                             | {
                                                 FStar_Reflection_V2_Data.sort2
                                                   = sort;
                                                 FStar_Reflection_V2_Data.qual
                                                   = uu___2;
                                                 FStar_Reflection_V2_Data.attrs
                                                   = uu___3;
                                                 FStar_Reflection_V2_Data.ppname2
                                                   = ppname;_}
                                                 ->
                                                 if
                                                   FStar_Reflection_V2_Data.uu___is_Tv_Unknown
                                                     (FStar_Reflection_V2_Builtins.inspect_ln
                                                        sort)
                                                 then
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.raise
                                                           (Extraction_failure
                                                              "Unexpected unknown sort when generalizing")))
                                                 else
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (712))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (712))
                                                                    (Prims.of_int (41)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (712))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (743))
                                                                    (Prims.of_int (20)))))
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___5 ->
                                                                 Pulse_Extract_CompilerLib.is_type
                                                                   g.uenv_inner
                                                                   sort))
                                                           (fun uu___5 ->
                                                              (fun uu___5 ->
                                                                 if uu___5
                                                                 then
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (713))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (713))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (714))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Reflection_V2_Builtins.inspect_comp
                                                                    c))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    cview ->
                                                                    match cview
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V2_Data.C_Total
                                                                    t1 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (716))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (716))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (716))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g.coreenv))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (717))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (717))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (717))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Var
                                                                    (FStar_Reflection_V2_Builtins.pack_namedv
                                                                    {
                                                                    FStar_Reflection_V2_Data.uniq
                                                                    = x;
                                                                    FStar_Reflection_V2_Data.sort
                                                                    =
                                                                    FStar_Reflection_Typing.sort_default;
                                                                    FStar_Reflection_V2_Data.ppname
                                                                    = ppname
                                                                    }))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun xt
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (718))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (718))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (718))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Reflection_V2_Builtins.subst_term
                                                                    [
                                                                    FStar_Syntax_Syntax.DT
                                                                    (Prims.int_zero,
                                                                    xt)] t1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (724))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (718))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match e
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    = b1;
                                                                    Pulse_Syntax_Base.q
                                                                    = uu___7;
                                                                    Pulse_Syntax_Base.ascription
                                                                    = uu___8;
                                                                    Pulse_Syntax_Base.body
                                                                    = body;_};
                                                                    Pulse_Syntax_Base.range1
                                                                    = uu___9;
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    = uu___10;_}
                                                                    ->
                                                                    ((FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    [
                                                                    FStar_Reflection_Typing.DT
                                                                    (Prims.int_zero,
                                                                    (Pulse_Syntax_Pure.wr
                                                                    xt
                                                                    FStar_Range.range_0))])),
                                                                    (b1.Pulse_Syntax_Base.binder_attrs))
                                                                    | 
                                                                    uu___7 ->
                                                                    (e,
                                                                    (Pulse_Syntax_Base.binder_attrs_default
                                                                    ()))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (e1,
                                                                    attrs) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (725))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (725))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (725))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (725))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (725))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (725))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (725))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Unseal.unseal
                                                                    attrs))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (term_as_mlexpr
                                                                    g) uu___7))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    mlattrs
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (12)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Reflection_V2_Builtins.pack_namedv
                                                                    {
                                                                    FStar_Reflection_V2_Data.uniq
                                                                    = x;
                                                                    FStar_Reflection_V2_Data.sort
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    sort);
                                                                    FStar_Reflection_V2_Data.ppname
                                                                    = ppname
                                                                    }))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    namedv ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (731))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (731))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (731))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Extract_CompilerLib.extend_ty
                                                                    g.uenv_inner
                                                                    namedv))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun uenv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (737))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (737))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g.coreenv
                                                                    x
                                                                    (Pulse_Syntax_Base.mk_ppname
                                                                    ppname
                                                                    FStar_Range.range_0)
                                                                    (Pulse_Syntax_Pure.wr
                                                                    sort
                                                                    FStar_Range.range_0)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    coreenv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (738))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (738))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (738))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    {
                                                                    uenv_inner
                                                                    = uenv;
                                                                    coreenv
                                                                    }))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun g1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (739))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (739))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (738))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    (generalize
                                                                    g1 t2 e1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (g2, tys,
                                                                    t3, e2)
                                                                    ->
                                                                    (g2,
                                                                    ((Pulse_Extract_CompilerLib.mk_ty_param
                                                                    (Pulse_Extract_CompilerLib.lookup_ty
                                                                    g2.uenv_inner
                                                                    namedv)
                                                                    mlattrs)
                                                                    :: tys),
                                                                    t3, e2)))))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    | 
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.raise
                                                                    (Extraction_failure
                                                                    "Unexpected effectful arrow"))))
                                                                    uu___6)))
                                                                 else
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (g, [],
                                                                    t, e)))))
                                                                uu___5))))
                                            uu___1)))
                           | uu___1 ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 -> (g, [], t, e)))))
                          uu___1))) uu___)
let (debug_ :
  env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  = debug
let rec find_map :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun l ->
      match l with
      | [] -> FStar_Pervasives_Native.None
      | hd::tl ->
          let x = f hd in
          if FStar_Pervasives_Native.uu___is_Some x then x else find_map f tl
let (is_recursive :
  env ->
    FStar_Reflection_Types.fv ->
      FStar_Reflection_Types.sigelt ->
        (Prims.string FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun knot_name ->
      fun selt ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (756)) (Prims.of_int (16))
                   (Prims.of_int (756)) (Prims.of_int (38)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (756)) (Prims.of_int (41))
                   (Prims.of_int (778)) (Prims.of_int (39)))))
          (Obj.magic (Pulse_RuntimeUtils.get_attributes selt))
          (fun attrs ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___ ->
                  find_map
                    (fun t ->
                       match FStar_Reflection_V2_Builtins.inspect_ln t with
                       | FStar_Reflection_V2_Data.Tv_App (uu___1, uu___2) ->
                           (match FStar_Reflection_V2_Collect.collect_app_ln
                                    t
                            with
                            | (hd, args) ->
                                if
                                  FStar_Reflection_V2_Derived.is_fvar hd
                                    "FStar.Pervasives.Native.Mktuple2"
                                then
                                  (match args with
                                   | uu___3::uu___4::(tag, uu___5)::(value,
                                                                    uu___6)::[]
                                       ->
                                       (match ((match FStar_Reflection_V2_Builtins.inspect_ln
                                                        tag
                                                with
                                                | FStar_Reflection_V2_Data.Tv_Const
                                                    (FStar_Reflection_V2_Data.C_String
                                                    s) ->
                                                    FStar_Pervasives_Native.Some
                                                      s
                                                | uu___7 ->
                                                    FStar_Pervasives_Native.None),
                                                (match FStar_Reflection_V2_Builtins.inspect_ln
                                                         value
                                                 with
                                                 | FStar_Reflection_V2_Data.Tv_Const
                                                     (FStar_Reflection_V2_Data.C_String
                                                     s) ->
                                                     FStar_Pervasives_Native.Some
                                                       s
                                                 | uu___7 ->
                                                     FStar_Pervasives_Native.None))
                                        with
                                        | (FStar_Pervasives_Native.Some
                                           "pulse.recursive.knot",
                                           FStar_Pervasives_Native.Some v) ->
                                            FStar_Pervasives_Native.Some v
                                        | uu___7 ->
                                            FStar_Pervasives_Native.None)
                                   | uu___3 -> FStar_Pervasives_Native.None)
                                else FStar_Pervasives_Native.None)
                       | uu___1 -> FStar_Pervasives_Native.None) attrs))
let rec (extract_recursive :
  env ->
    Pulse_Syntax_Base.st_term ->
      FStar_Reflection_Types.fv ->
        ((Pulse_Extract_CompilerLib.mlexpr * Pulse_Extract_CompilerLib.e_tag),
          unit) FStar_Tactics_Effect.tac_repr)
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
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (786))
                                        (Prims.of_int (37))
                                        (Prims.of_int (786))
                                        (Prims.of_int (51)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (785))
                                        (Prims.of_int (19))
                                        (Prims.of_int (794))
                                        (Prims.of_int (27)))))
                               (Obj.magic (extend_env g b))
                               (fun uu___2 ->
                                  (fun uu___2 ->
                                     match uu___2 with
                                     | (g1, mlident, mlty, name1) ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Extract.Main.fst"
                                                       (Prims.of_int (787))
                                                       (Prims.of_int (19))
                                                       (Prims.of_int (787))
                                                       (Prims.of_int (47)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Extract.Main.fst"
                                                       (Prims.of_int (787))
                                                       (Prims.of_int (50))
                                                       (Prims.of_int (794))
                                                       (Prims.of_int (27)))))
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___3 ->
                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                      body name1))
                                              (fun uu___3 ->
                                                 (fun body1 ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (788))
                                                                  (Prims.of_int (22))
                                                                  (Prims.of_int (788))
                                                                  (Prims.of_int (55)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (787))
                                                                  (Prims.of_int (50))
                                                                  (Prims.of_int (794))
                                                                  (Prims.of_int (27)))))
                                                         (Obj.magic
                                                            (extract_recursive
                                                               g1 body1
                                                               rec_name))
                                                         (fun uu___3 ->
                                                            (fun uu___3 ->
                                                               match uu___3
                                                               with
                                                               | (body2,
                                                                  uu___4) ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (790))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (792))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (794))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (794))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (790))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (791))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (790))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (792))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Unseal.unseal
                                                                    b.Pulse_Syntax_Base.binder_attrs))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (term_as_mlexpr
                                                                    g1)
                                                                    uu___5))
                                                                    uu___5)))
                                                                    (fun
                                                                    attrs ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ((Pulse_Extract_CompilerLib.mle_fun
                                                                    [
                                                                    (mlident,
                                                                    mlty,
                                                                    attrs)]
                                                                    body2),
                                                                    Pulse_Extract_CompilerLib.e_tag_pure)))))
                                                              uu___3)))
                                                   uu___3))) uu___2)
                         | uu___1 ->
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (796))
                                        (Prims.of_int (19))
                                        (Prims.of_int (796))
                                        (Prims.of_int (100)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (796))
                                        (Prims.of_int (103))
                                        (Prims.of_int (798))
                                        (Prims.of_int (17)))))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 ->
                                     Pulse_Syntax_Naming.subst_st_term body
                                       [FStar_Reflection_Typing.DT
                                          (Prims.int_zero,
                                            (Pulse_Syntax_Pure.wr
                                               (FStar_Reflection_V2_Builtins.pack_ln
                                                  (FStar_Reflection_V2_Data.Tv_FVar
                                                     rec_name))
                                               FStar_Range.range_0))]))
                               (fun uu___2 ->
                                  (fun body1 ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (797))
                                                   (Prims.of_int (24))
                                                   (Prims.of_int (797))
                                                   (Prims.of_int (38)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (796))
                                                   (Prims.of_int (103))
                                                   (Prims.of_int (798))
                                                   (Prims.of_int (17)))))
                                          (Obj.magic (extract g body1))
                                          (fun uu___2 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___3 ->
                                                  match uu___2 with
                                                  | (body2, tag) ->
                                                      (body2, tag))))) uu___2)))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_V2_Derived.fail
                           "Unexpected recursive definition of non-function")))
          uu___2 uu___1 uu___
let extract_recursive_knot :
  'uuuuu .
    env ->
      Pulse_Syntax_Base.st_term ->
        FStar_Reflection_Types.fv ->
          FStar_Reflection_Types.term ->
            ((Pulse_Extract_CompilerLib.mlmodule1 Prims.list, 'uuuuu)
               FStar_Pervasives.either,
              unit) FStar_Tactics_Effect.tac_repr
  =
  fun g ->
    fun p ->
      fun knot_name ->
        fun knot_typ ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                     (Prims.of_int (805)) (Prims.of_int (33))
                     (Prims.of_int (805)) (Prims.of_int (63)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                     (Prims.of_int (804)) (Prims.of_int (63))
                     (Prims.of_int (818)) (Prims.of_int (33)))))
            (Obj.magic
               (generalize g knot_typ (FStar_Pervasives_Native.Some p)))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | (g1, tys, lb_typ, FStar_Pervasives_Native.Some p1) ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Extract.Main.fst"
                                    (Prims.of_int (806)) (Prims.of_int (15))
                                    (Prims.of_int (806)) (Prims.of_int (51)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Extract.Main.fst"
                                    (Prims.of_int (806)) (Prims.of_int (54))
                                    (Prims.of_int (818)) (Prims.of_int (33)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 Pulse_Extract_CompilerLib.term_as_mlty
                                   g1.uenv_inner lb_typ))
                           (fun uu___1 ->
                              (fun mlty ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (807))
                                               (Prims.of_int (34))
                                               (Prims.of_int (807))
                                               (Prims.of_int (82)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (806))
                                               (Prims.of_int (54))
                                               (Prims.of_int (818))
                                               (Prims.of_int (33)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            Pulse_Extract_CompilerLib.extend_fv
                                              g1.uenv_inner knot_name
                                              (tys, mlty)))
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            match uu___1 with
                                            | (uenv, _mli, _ml_binding) ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (808))
                                                              (Prims.of_int (14))
                                                              (Prims.of_int (808))
                                                              (Prims.of_int (38)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (808))
                                                              (Prims.of_int (43))
                                                              (Prims.of_int (818))
                                                              (Prims.of_int (33)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           {
                                                             uenv_inner =
                                                               uenv;
                                                             coreenv =
                                                               (g1.coreenv)
                                                           }))
                                                     (fun uu___2 ->
                                                        (fun g2 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (809))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (809))
                                                                    (Prims.of_int (49)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (808))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (818))
                                                                    (Prims.of_int (33)))))
                                                                (Obj.magic
                                                                   (extract_recursive
                                                                    g2 p1
                                                                    knot_name))
                                                                (fun uu___2
                                                                   ->
                                                                   (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (tm, tag)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (810))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (814))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (816))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (818))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (811))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (811))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (812))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (814))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Reflection_V2_Builtins.inspect_fv
                                                                    knot_name))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun lids
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (812))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (813))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (814))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (814))
                                                                    (Prims.of_int (30)))))
                                                                    (if
                                                                    Prims.uu___is_Nil
                                                                    lids
                                                                    then
                                                                    FStar_Tactics_Effect.raise
                                                                    (Extraction_failure
                                                                    "Unexpected empty name")
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_List_Tot_Base.last
                                                                    lids))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    fv_name
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (816))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (816))
                                                                    (Prims.of_int (100)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (818))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (818))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    (debug_
                                                                    g2
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Extracted term ("
                                                                    (Prims.strcat
                                                                    fv_name
                                                                    "): "))
                                                                    (Prims.strcat
                                                                    (Pulse_Extract_CompilerLib.mlexpr_to_string
                                                                    tm) "\n"))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Inl
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mlm_let
                                                                    true
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mk_mllb
                                                                    fv_name
                                                                    (tys,
                                                                    mlty) tm]]))))
                                                                    uu___3)))
                                                                    uu___2)))
                                                          uu___2))) uu___1)))
                                uu___1))) uu___)
let (extract_attrs :
  Pulse_Extract_CompilerLib.uenv ->
    FStar_Reflection_Types.sigelt ->
      (Pulse_Extract_CompilerLib.mlexpr Prims.list, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun se ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (821)) (Prims.of_int (2)) (Prims.of_int (821))
                 (Prims.of_int (25)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (821)) (Prims.of_int (2)) (Prims.of_int (822))
                 (Prims.of_int (76)))))
        (Obj.magic (Pulse_RuntimeUtils.get_attributes se))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Util.map
                   (fun uu___1 ->
                      (fun t ->
                         Obj.magic
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 match Pulse_Extract_CompilerLib.term_as_mlexpr
                                         g t
                                 with
                                 | (mlattr, uu___2, uu___3) -> mlattr)))
                        uu___1) uu___)) uu___)
let (extract_dv_binder :
  Pulse_Syntax_Base.binder ->
    Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option ->
      (Pulse_Extract_CompilerLib.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun q ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (827)) (Prims.of_int (4)) (Prims.of_int (829))
                 (Prims.of_int (15)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (830)) (Prims.of_int (2)) (Prims.of_int (834))
                 (Prims.of_int (70)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              match q with
              | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.Implicit) ->
                  FStar_Pervasives_Native.Some
                    Pulse_Extract_CompilerLib.implicit_qual
              | uu___1 -> FStar_Pervasives_Native.None))
        (fun uu___ ->
           (fun q1 ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (831)) (Prims.of_int (4))
                            (Prims.of_int (831)) (Prims.of_int (37)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (830)) (Prims.of_int (2))
                            (Prims.of_int (834)) (Prims.of_int (70)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ ->
                         Pulse_Extract_CompilerLib.rt_term_to_term
                           b.Pulse_Syntax_Base.binder_ty))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (832))
                                       (Prims.of_int (4))
                                       (Prims.of_int (832))
                                       (Prims.of_int (35)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (830))
                                       (Prims.of_int (2))
                                       (Prims.of_int (834))
                                       (Prims.of_int (70)))))
                              (Obj.magic
                                 (FStar_Tactics_Unseal.unseal
                                    (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name))
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (834))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (834))
                                                  (Prims.of_int (70)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (830))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (834))
                                                  (Prims.of_int (70)))))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Extract.Main.fst"
                                                        (Prims.of_int (834))
                                                        (Prims.of_int (44))
                                                        (Prims.of_int (834))
                                                        (Prims.of_int (69)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Extract.Main.fst"
                                                        (Prims.of_int (834))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (834))
                                                        (Prims.of_int (70)))))
                                               (Obj.magic
                                                  (FStar_Tactics_Unseal.unseal
                                                     b.Pulse_Syntax_Base.binder_attrs))
                                               (fun uu___2 ->
                                                  (fun uu___2 ->
                                                     Obj.magic
                                                       (FStar_Tactics_Util.map
                                                          (fun uu___3 ->
                                                             (fun t ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Extract_CompilerLib.rt_term_to_term
                                                                    t)))
                                                               uu___3) uu___2))
                                                    uu___2)))
                                         (fun uu___2 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___3 ->
                                                 Pulse_Extract_CompilerLib.mk_binder
                                                   uu___ uu___1 q1 uu___2))))
                                   uu___1))) uu___))) uu___)
let rec (extract_dv_pattern :
  Pulse_Syntax_Base.pattern ->
    (Pulse_Extract_CompilerLib.pattern, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun p ->
       match p with
       | Pulse_Syntax_Base.Pat_Cons (fv, pats) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (839)) (Prims.of_int (13))
                            (Prims.of_int (839)) (Prims.of_int (33)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (839)) (Prims.of_int (36))
                            (Prims.of_int (841)) (Prims.of_int (27)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ ->
                         Pulse_Extract_CompilerLib.mk_fv
                           fv.Pulse_Syntax_Base.fv_name))
                   (fun uu___ ->
                      (fun fv1 ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (840))
                                       (Prims.of_int (15))
                                       (Prims.of_int (840))
                                       (Prims.of_int (63)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (841))
                                       (Prims.of_int (4))
                                       (Prims.of_int (841))
                                       (Prims.of_int (27)))))
                              (Obj.magic
                                 (FStar_Tactics_Util.map extract_dv_pattern
                                    (FStar_List_Tot_Base.map
                                       FStar_Pervasives_Native.fst pats)))
                              (fun pats1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ ->
                                      Pulse_Extract_CompilerLib.mk_pat_cons
                                        fv1 pats1)))) uu___)))
       | Pulse_Syntax_Base.Pat_Constant c ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Pulse_Extract_CompilerLib.mk_pat_constant
                        (Pulse_Extract_CompilerLib.mk_const c))))
       | Pulse_Syntax_Base.Pat_Var (ppname, sort) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (843)) (Prims.of_int (42))
                            (Prims.of_int (843)) (Prims.of_int (59)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (843)) (Prims.of_int (27))
                            (Prims.of_int (843)) (Prims.of_int (101)))))
                   (Obj.magic (FStar_Tactics_Unseal.unseal ppname))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (843))
                                       (Prims.of_int (60))
                                       (Prims.of_int (843))
                                       (Prims.of_int (101)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (843))
                                       (Prims.of_int (27))
                                       (Prims.of_int (843))
                                       (Prims.of_int (101)))))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Extract.Main.fst"
                                             (Prims.of_int (843))
                                             (Prims.of_int (61))
                                             (Prims.of_int (843))
                                             (Prims.of_int (77)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Extract.Main.fst"
                                             (Prims.of_int (843))
                                             (Prims.of_int (60))
                                             (Prims.of_int (843))
                                             (Prims.of_int (101)))))
                                    (Obj.magic
                                       (FStar_Tactics_Unseal.unseal sort))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Pulse_Extract_CompilerLib.rt_term_to_term
                                              uu___1))))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      Pulse_Extract_CompilerLib.mk_pat_var
                                        uu___ uu___1)))) uu___)))
       | Pulse_Syntax_Base.Pat_Dot_Term t ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (844)) (Prims.of_int (37))
                            (Prims.of_int (844)) (Prims.of_int (83)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (844)) (Prims.of_int (22))
                            (Prims.of_int (844)) (Prims.of_int (83)))))
                   (Obj.magic
                      (FStar_Tactics_Util.map_opt
                         (fun uu___ ->
                            (fun t1 ->
                               Obj.magic
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___ ->
                                       Pulse_Extract_CompilerLib.rt_term_to_term
                                         t1))) uu___) t))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           Pulse_Extract_CompilerLib.mk_dot_pat uu___)))))
      uu___
let rec (extract_dv :
  Pulse_Syntax_Base.st_term ->
    (Pulse_Extract_CompilerLib.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun p ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (851)) (Prims.of_int (5)) (Prims.of_int (851))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (851)) (Prims.of_int (2)) (Prims.of_int (932))
               (Prims.of_int (5))))) (Obj.magic (is_erasable p))
      (fun uu___ ->
         (fun uu___ ->
            if uu___
            then
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___1 ->
                         Pulse_Extract_CompilerLib.mk_return
                           Pulse_Extract_CompilerLib.unit_tm)))
            else
              Obj.magic
                (Obj.repr
                   (match p.Pulse_Syntax_Base.term1 with
                    | Pulse_Syntax_Base.Tm_IntroPure uu___2 ->
                        Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 ->
                                Pulse_Extract_CompilerLib.mk_return
                                  Pulse_Extract_CompilerLib.unit_tm))
                    | Pulse_Syntax_Base.Tm_ElimExists uu___2 ->
                        Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 ->
                                Pulse_Extract_CompilerLib.mk_return
                                  Pulse_Extract_CompilerLib.unit_tm))
                    | Pulse_Syntax_Base.Tm_IntroExists uu___2 ->
                        Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 ->
                                Pulse_Extract_CompilerLib.mk_return
                                  Pulse_Extract_CompilerLib.unit_tm))
                    | Pulse_Syntax_Base.Tm_Rewrite uu___2 ->
                        Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 ->
                                Pulse_Extract_CompilerLib.mk_return
                                  Pulse_Extract_CompilerLib.unit_tm))
                    | Pulse_Syntax_Base.Tm_ProofHintWithBinders uu___2 ->
                        Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 ->
                                Pulse_Extract_CompilerLib.mk_return
                                  Pulse_Extract_CompilerLib.unit_tm))
                    | Pulse_Syntax_Base.Tm_Abs
                        { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = q;
                          Pulse_Syntax_Base.ascription = uu___2;
                          Pulse_Syntax_Base.body = body;_}
                        ->
                        Obj.repr
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Extract.Main.fst"
                                      (Prims.of_int (861))
                                      (Prims.of_int (14))
                                      (Prims.of_int (861))
                                      (Prims.of_int (35)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Extract.Main.fst"
                                      (Prims.of_int (861))
                                      (Prims.of_int (38))
                                      (Prims.of_int (863))
                                      (Prims.of_int (23)))))
                             (Obj.magic (extract_dv_binder b q))
                             (fun uu___3 ->
                                (fun b1 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (862))
                                                 (Prims.of_int (17))
                                                 (Prims.of_int (862))
                                                 (Prims.of_int (32)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (863))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (863))
                                                 (Prims.of_int (23)))))
                                        (Obj.magic (extract_dv body))
                                        (fun body1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                Pulse_Extract_CompilerLib.mk_abs
                                                  b1 body1)))) uu___3))
                    | Pulse_Syntax_Base.Tm_Return
                        { Pulse_Syntax_Base.expected_type = uu___2;
                          Pulse_Syntax_Base.insert_eq = uu___3;
                          Pulse_Syntax_Base.term = term;_}
                        ->
                        Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___4 ->
                                Pulse_Extract_CompilerLib.mk_return
                                  (Pulse_Extract_CompilerLib.rt_term_to_term
                                     term)))
                    | Pulse_Syntax_Base.Tm_STApp
                        { Pulse_Syntax_Base.head = head;
                          Pulse_Syntax_Base.arg_qual = arg_qual;
                          Pulse_Syntax_Base.arg = arg;_}
                        ->
                        Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 ->
                                Pulse_Extract_CompilerLib.mk_app
                                  (Pulse_Extract_CompilerLib.rt_term_to_term
                                     head)
                                  (match arg_qual with
                                   | FStar_Pervasives_Native.Some
                                       (Pulse_Syntax_Base.Implicit) ->
                                       FStar_Pervasives_Native.Some
                                         Pulse_Extract_CompilerLib.implicit_arg_qual
                                   | uu___3 -> FStar_Pervasives_Native.None)
                                  (Pulse_Extract_CompilerLib.rt_term_to_term
                                     arg)))
                    | Pulse_Syntax_Base.Tm_Bind
                        { Pulse_Syntax_Base.binder = binder;
                          Pulse_Syntax_Base.head1 = head;
                          Pulse_Syntax_Base.body1 = body;_}
                        ->
                        Obj.repr
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Extract.Main.fst"
                                      (Prims.of_int (876))
                                      (Prims.of_int (14))
                                      (Prims.of_int (876))
                                      (Prims.of_int (43)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Extract.Main.fst"
                                      (Prims.of_int (876))
                                      (Prims.of_int (46))
                                      (Prims.of_int (882))
                                      (Prims.of_int (24)))))
                             (Obj.magic
                                (extract_dv_binder binder
                                   FStar_Pervasives_Native.None))
                             (fun uu___2 ->
                                (fun b ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (877))
                                                 (Prims.of_int (15))
                                                 (Prims.of_int (877))
                                                 (Prims.of_int (30)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (877))
                                                 (Prims.of_int (33))
                                                 (Prims.of_int (882))
                                                 (Prims.of_int (24)))))
                                        (Obj.magic (extract_dv head))
                                        (fun uu___2 ->
                                           (fun e1 ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Extract.Main.fst"
                                                            (Prims.of_int (878))
                                                            (Prims.of_int (15))
                                                            (Prims.of_int (878))
                                                            (Prims.of_int (30)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Extract.Main.fst"
                                                            (Prims.of_int (882))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (882))
                                                            (Prims.of_int (24)))))
                                                   (Obj.magic
                                                      (extract_dv body))
                                                   (fun e2 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           Pulse_Extract_CompilerLib.mk_let
                                                             b e1 e2))))
                                             uu___2))) uu___2))
                    | Pulse_Syntax_Base.Tm_TotBind
                        { Pulse_Syntax_Base.binder1 = binder;
                          Pulse_Syntax_Base.head2 = head;
                          Pulse_Syntax_Base.body2 = body;_}
                        ->
                        Obj.repr
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Extract.Main.fst"
                                      (Prims.of_int (885))
                                      (Prims.of_int (14))
                                      (Prims.of_int (885))
                                      (Prims.of_int (43)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Extract.Main.fst"
                                      (Prims.of_int (885))
                                      (Prims.of_int (46))
                                      (Prims.of_int (888))
                                      (Prims.of_int (24)))))
                             (Obj.magic
                                (extract_dv_binder binder
                                   FStar_Pervasives_Native.None))
                             (fun uu___2 ->
                                (fun b ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (886))
                                                 (Prims.of_int (15))
                                                 (Prims.of_int (886))
                                                 (Prims.of_int (55)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (886))
                                                 (Prims.of_int (58))
                                                 (Prims.of_int (888))
                                                 (Prims.of_int (24)))))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              Pulse_Extract_CompilerLib.mk_return
                                                (Pulse_Extract_CompilerLib.rt_term_to_term
                                                   head)))
                                        (fun uu___2 ->
                                           (fun e1 ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Extract.Main.fst"
                                                            (Prims.of_int (887))
                                                            (Prims.of_int (15))
                                                            (Prims.of_int (887))
                                                            (Prims.of_int (30)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Extract.Main.fst"
                                                            (Prims.of_int (888))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (888))
                                                            (Prims.of_int (24)))))
                                                   (Obj.magic
                                                      (extract_dv body))
                                                   (fun e2 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           Pulse_Extract_CompilerLib.mk_let
                                                             b e1 e2))))
                                             uu___2))) uu___2))
                    | Pulse_Syntax_Base.Tm_If
                        { Pulse_Syntax_Base.b1 = b;
                          Pulse_Syntax_Base.then_ = then_;
                          Pulse_Syntax_Base.else_ = else_;
                          Pulse_Syntax_Base.post1 = uu___2;_}
                        ->
                        Obj.repr
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Extract.Main.fst"
                                      (Prims.of_int (891))
                                      (Prims.of_int (14))
                                      (Prims.of_int (891))
                                      (Prims.of_int (35)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Extract.Main.fst"
                                      (Prims.of_int (891))
                                      (Prims.of_int (38))
                                      (Prims.of_int (894))
                                      (Prims.of_int (29)))))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___3 ->
                                   Pulse_Extract_CompilerLib.rt_term_to_term
                                     b))
                             (fun uu___3 ->
                                (fun b1 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (892))
                                                 (Prims.of_int (18))
                                                 (Prims.of_int (892))
                                                 (Prims.of_int (34)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (892))
                                                 (Prims.of_int (37))
                                                 (Prims.of_int (894))
                                                 (Prims.of_int (29)))))
                                        (Obj.magic (extract_dv then_))
                                        (fun uu___3 ->
                                           (fun then_1 ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Extract.Main.fst"
                                                            (Prims.of_int (893))
                                                            (Prims.of_int (18))
                                                            (Prims.of_int (893))
                                                            (Prims.of_int (34)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Extract.Main.fst"
                                                            (Prims.of_int (894))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (894))
                                                            (Prims.of_int (29)))))
                                                   (Obj.magic
                                                      (extract_dv else_))
                                                   (fun else_1 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___3 ->
                                                           Pulse_Extract_CompilerLib.mk_if
                                                             b1 then_1 else_1))))
                                             uu___3))) uu___3))
                    | Pulse_Syntax_Base.Tm_Match
                        { Pulse_Syntax_Base.sc = sc;
                          Pulse_Syntax_Base.returns_ = uu___2;
                          Pulse_Syntax_Base.brs = brs;_}
                        ->
                        Obj.repr
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Extract.Main.fst"
                                      (Prims.of_int (897))
                                      (Prims.of_int (19))
                                      (Prims.of_int (897))
                                      (Prims.of_int (43)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Extract.Main.fst"
                                      (Prims.of_int (897)) (Prims.of_int (6))
                                      (Prims.of_int (897))
                                      (Prims.of_int (73)))))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___3 ->
                                   Pulse_Extract_CompilerLib.rt_term_to_term
                                     sc))
                             (fun uu___3 ->
                                (fun uu___3 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (897))
                                                 (Prims.of_int (44))
                                                 (Prims.of_int (897))
                                                 (Prims.of_int (73)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (897))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (897))
                                                 (Prims.of_int (73)))))
                                        (Obj.magic
                                           (FStar_Tactics_Util.map
                                              extract_dv_branch brs))
                                        (fun uu___4 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___5 ->
                                                Pulse_Extract_CompilerLib.mk_match
                                                  uu___3 uu___4)))) uu___3))
                    | Pulse_Syntax_Base.Tm_While
                        { Pulse_Syntax_Base.invariant = uu___2;
                          Pulse_Syntax_Base.condition = condition;
                          Pulse_Syntax_Base.condition_var = uu___3;
                          Pulse_Syntax_Base.body3 = body;_}
                        ->
                        Obj.repr
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Extract.Main.fst"
                                      (Prims.of_int (900))
                                      (Prims.of_int (22))
                                      (Prims.of_int (900))
                                      (Prims.of_int (42)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Extract.Main.fst"
                                      (Prims.of_int (900))
                                      (Prims.of_int (45))
                                      (Prims.of_int (908))
                                      (Prims.of_int (52)))))
                             (Obj.magic (extract_dv condition))
                             (fun uu___4 ->
                                (fun condition1 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (901))
                                                 (Prims.of_int (17))
                                                 (Prims.of_int (901))
                                                 (Prims.of_int (32)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (903))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (908))
                                                 (Prims.of_int (52)))))
                                        (Obj.magic (extract_dv body))
                                        (fun body1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___4 ->
                                                Pulse_Extract_CompilerLib.mk_app
                                                  (Pulse_Extract_CompilerLib.mk_app
                                                     (Pulse_Extract_CompilerLib.mk_fv_tm
                                                        (Pulse_Extract_CompilerLib.mk_fv
                                                           ["Pulse";
                                                           "Dv";
                                                           "while_"]))
                                                     FStar_Pervasives_Native.None
                                                     (Pulse_Extract_CompilerLib.mk_abs
                                                        (Pulse_Extract_CompilerLib.mk_binder
                                                           Pulse_Extract_CompilerLib.unit_ty
                                                           "while_cond"
                                                           FStar_Pervasives_Native.None
                                                           []) condition1))
                                                  FStar_Pervasives_Native.None
                                                  (Pulse_Extract_CompilerLib.mk_abs
                                                     (Pulse_Extract_CompilerLib.mk_binder
                                                        Pulse_Extract_CompilerLib.unit_ty
                                                        "while_body"
                                                        FStar_Pervasives_Native.None
                                                        []) body1))))) uu___4))
                    | Pulse_Syntax_Base.Tm_Par
                        { Pulse_Syntax_Base.pre1 = uu___2;
                          Pulse_Syntax_Base.body11 = body1;
                          Pulse_Syntax_Base.post11 = uu___3;
                          Pulse_Syntax_Base.pre2 = uu___4;
                          Pulse_Syntax_Base.body21 = body2;
                          Pulse_Syntax_Base.post2 = uu___5;_}
                        ->
                        Obj.repr
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Extract.Main.fst"
                                      (Prims.of_int (911))
                                      (Prims.of_int (18))
                                      (Prims.of_int (911))
                                      (Prims.of_int (34)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Extract.Main.fst"
                                      (Prims.of_int (911))
                                      (Prims.of_int (37))
                                      (Prims.of_int (919))
                                      (Prims.of_int (49)))))
                             (Obj.magic (extract_dv body1))
                             (fun uu___6 ->
                                (fun body11 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (912))
                                                 (Prims.of_int (18))
                                                 (Prims.of_int (912))
                                                 (Prims.of_int (34)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (914))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (919))
                                                 (Prims.of_int (49)))))
                                        (Obj.magic (extract_dv body2))
                                        (fun body21 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___6 ->
                                                Pulse_Extract_CompilerLib.mk_app
                                                  (Pulse_Extract_CompilerLib.mk_app
                                                     (Pulse_Extract_CompilerLib.mk_fv_tm
                                                        (Pulse_Extract_CompilerLib.mk_fv
                                                           ["Pulse";
                                                           "Dv";
                                                           "par_"]))
                                                     FStar_Pervasives_Native.None
                                                     (Pulse_Extract_CompilerLib.mk_abs
                                                        (Pulse_Extract_CompilerLib.mk_binder
                                                           Pulse_Extract_CompilerLib.unit_ty
                                                           "par_b1"
                                                           FStar_Pervasives_Native.None
                                                           []) body11))
                                                  FStar_Pervasives_Native.None
                                                  (Pulse_Extract_CompilerLib.mk_abs
                                                     (Pulse_Extract_CompilerLib.mk_binder
                                                        Pulse_Extract_CompilerLib.unit_ty
                                                        "par_b2"
                                                        FStar_Pervasives_Native.None
                                                        []) body21)))))
                                  uu___6))
                    | Pulse_Syntax_Base.Tm_WithLocal uu___2 ->
                        Obj.repr
                          (FStar_Tactics_V2_Derived.fail
                             "Pulse extraction to dv : WithLocal not yet supported")
                    | Pulse_Syntax_Base.Tm_WithLocalArray uu___2 ->
                        Obj.repr
                          (FStar_Tactics_V2_Derived.fail
                             "Pulse extraction to dv : WithLocalArray not yet supported")
                    | Pulse_Syntax_Base.Tm_Admit uu___2 ->
                        Obj.repr
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Extract.Main.fst"
                                      (Prims.of_int (925)) (Prims.of_int (6))
                                      (Prims.of_int (925))
                                      (Prims.of_int (59)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Extract.Main.fst"
                                      (Prims.of_int (926)) (Prims.of_int (6))
                                      (Prims.of_int (926))
                                      (Prims.of_int (31)))))
                             (Obj.magic
                                (FStar_Tactics_V2_Builtins.print
                                   "Admit in dv extraction is currently ignored"))
                             (fun uu___3 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___4 ->
                                     Pulse_Extract_CompilerLib.mk_return
                                       Pulse_Extract_CompilerLib.unit_tm)))
                    | Pulse_Syntax_Base.Tm_Unreachable ->
                        Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 ->
                                Pulse_Extract_CompilerLib.mk_return
                                  Pulse_Extract_CompilerLib.unit_tm))
                    | Pulse_Syntax_Base.Tm_WithInv
                        { Pulse_Syntax_Base.name1 = uu___2;
                          Pulse_Syntax_Base.body6 = body;
                          Pulse_Syntax_Base.returns_inv = uu___3;_}
                        -> Obj.repr (extract_dv body)))) uu___)
and (extract_dv_branch :
  Pulse_Syntax_Base.branch ->
    (Pulse_Extract_CompilerLib.branch, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (935)) (Prims.of_int (18)) (Prims.of_int (935))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (934)) (Prims.of_int (71)) (Prims.of_int (936))
               (Prims.of_int (58)))))
      (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> b))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | (pat, body) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (936)) (Prims.of_int (16))
                              (Prims.of_int (936)) (Prims.of_int (40)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (936)) (Prims.of_int (2))
                              (Prims.of_int (936)) (Prims.of_int (58)))))
                     (Obj.magic (extract_dv_pattern pat))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Extract.Main.fst"
                                         (Prims.of_int (936))
                                         (Prims.of_int (41))
                                         (Prims.of_int (936))
                                         (Prims.of_int (58)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Extract.Main.fst"
                                         (Prims.of_int (936))
                                         (Prims.of_int (2))
                                         (Prims.of_int (936))
                                         (Prims.of_int (58)))))
                                (Obj.magic (extract_dv body))
                                (fun uu___2 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 ->
                                        Pulse_Extract_CompilerLib.mk_branch
                                          uu___1 uu___2)))) uu___1))) uu___)
let (extract_dv_typ :
  FStar_Reflection_Types.typ ->
    (Pulse_Extract_CompilerLib.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (939)) (Prims.of_int (14)) (Prims.of_int (939))
               (Prims.of_int (35)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (938)) (Prims.of_int (47)) (Prims.of_int (962))
               (Prims.of_int (89)))))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> FStar_Reflection_V2_Collect.collect_arr_ln_bs t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | (bs, c) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (940)) (Prims.of_int (11))
                              (Prims.of_int (948)) (Prims.of_int (12)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (949)) (Prims.of_int (2))
                              (Prims.of_int (962)) (Prims.of_int (89)))))
                     (Obj.magic
                        (FStar_Tactics_Util.map
                           (fun b ->
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Extract.Main.fst"
                                         (Prims.of_int (941))
                                         (Prims.of_int (16))
                                         (Prims.of_int (941))
                                         (Prims.of_int (34)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Extract.Main.fst"
                                         (Prims.of_int (942))
                                         (Prims.of_int (4))
                                         (Prims.of_int (948))
                                         (Prims.of_int (8)))))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 ->
                                      FStar_Reflection_V2_Builtins.inspect_binder
                                        b))
                                (fun uu___1 ->
                                   (fun bview ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (943))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (943))
                                                    (Prims.of_int (38)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (942))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (948))
                                                    (Prims.of_int (8)))))
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___1 ->
                                                 Pulse_Extract_CompilerLib.rt_term_to_term
                                                   bview.FStar_Reflection_V2_Data.sort2))
                                           (fun uu___1 ->
                                              (fun uu___1 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (944))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (944))
                                                               (Prims.of_int (29)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (942))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (948))
                                                               (Prims.of_int (8)))))
                                                      (Obj.magic
                                                         (FStar_Tactics_Unseal.unseal
                                                            bview.FStar_Reflection_V2_Data.ppname2))
                                                      (fun uu___2 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___3 ->
                                                              Pulse_Extract_CompilerLib.mk_binder
                                                                uu___1 uu___2
                                                                (match 
                                                                   bview.FStar_Reflection_V2_Data.qual
                                                                 with
                                                                 | FStar_Reflection_V2_Data.Q_Implicit
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    Pulse_Extract_CompilerLib.implicit_qual
                                                                 | uu___4 ->
                                                                    FStar_Pervasives_Native.None)
                                                                [])))) uu___1)))
                                     uu___1)) bs))
                     (fun uu___1 ->
                        (fun bs1 ->
                           match FStar_Reflection_V2_Builtins.inspect_comp c
                           with
                           | FStar_Reflection_V2_Data.C_Total t1 ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Extract.Main.fst"
                                             (Prims.of_int (951))
                                             (Prims.of_int (19))
                                             (Prims.of_int (951))
                                             (Prims.of_int (37)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Extract.Main.fst"
                                             (Prims.of_int (950))
                                             (Prims.of_int (24))
                                             (Prims.of_int (958))
                                             (Prims.of_int (32)))))
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___1 ->
                                          FStar_Reflection_V2_Collect.collect_app_ln
                                            t1))
                                    (fun uu___1 ->
                                       (fun uu___1 ->
                                          match uu___1 with
                                          | (hd, args) ->
                                              if
                                                (FStar_List_Tot_Base.length
                                                   args)
                                                  = Prims.int_zero
                                              then
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Extract.Main.fst"
                                                                 (Prims.of_int (956))
                                                                 (Prims.of_int (16))
                                                                 (Prims.of_int (956))
                                                                 (Prims.of_int (100)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Extract.Main.fst"
                                                                 (Prims.of_int (956))
                                                                 (Prims.of_int (9))
                                                                 (Prims.of_int (956))
                                                                 (Prims.of_int (100)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (956))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (956))
                                                                    (Prims.of_int (99)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                              (Obj.magic
                                                                 (FStar_Tactics_V2_Builtins.term_to_string
                                                                    t1))
                                                              (fun uu___2 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "Unexpected return type in extract_dv_typ: "
                                                                    (Prims.strcat
                                                                    uu___2 "")))))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_V2_Derived.fail
                                                             uu___2)))
                                              else
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___3 ->
                                                           Pulse_Extract_CompilerLib.mk_arrow
                                                             bs1
                                                             (Pulse_Extract_CompilerLib.rt_term_to_term
                                                                (FStar_Pervasives_Native.fst
                                                                   (FStar_List_Tot_Base.hd
                                                                    args)))))))
                                         uu___1))
                           | uu___1 ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Extract.Main.fst"
                                             (Prims.of_int (962))
                                             (Prims.of_int (6))
                                             (Prims.of_int (962))
                                             (Prims.of_int (89)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Extract.Main.fst"
                                             (Prims.of_int (961))
                                             (Prims.of_int (4))
                                             (Prims.of_int (962))
                                             (Prims.of_int (89)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (962))
                                                   (Prims.of_int (68))
                                                   (Prims.of_int (962))
                                                   (Prims.of_int (88)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "prims.fst"
                                                   (Prims.of_int (611))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (611))
                                                   (Prims.of_int (31)))))
                                          (Obj.magic
                                             (FStar_Tactics_V2_Builtins.term_to_string
                                                t))
                                          (fun uu___2 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___3 ->
                                                  Prims.strcat
                                                    "Unexpected arrow comp in extract_dv_typ: "
                                                    (Prims.strcat uu___2 "")))))
                                    (fun uu___2 ->
                                       FStar_Tactics_V2_Derived.fail uu___2)))
                          uu___1))) uu___)
let (extract_pulse_dv :
  Pulse_Extract_CompilerLib.uenv ->
    Pulse_Syntax_Base.st_term ->
      (Pulse_Extract_CompilerLib.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uenv ->
    fun p ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (965)) (Prims.of_int (12))
                 (Prims.of_int (965)) (Prims.of_int (62)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (965)) (Prims.of_int (67))
                 (Prims.of_int (969)) (Prims.of_int (14)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              {
                uenv_inner = uenv;
                coreenv = (Pulse_Extract_CompilerLib.initial_core_env uenv)
              }))
        (fun uu___ ->
           (fun g ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (966)) (Prims.of_int (10))
                            (Prims.of_int (966)) (Prims.of_int (34)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (966)) (Prims.of_int (37))
                            (Prims.of_int (969)) (Prims.of_int (14)))))
                   (Obj.magic (erase_ghost_subterms g p))
                   (fun uu___ ->
                      (fun p1 ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (967))
                                       (Prims.of_int (10))
                                       (Prims.of_int (967))
                                       (Prims.of_int (30)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (969))
                                       (Prims.of_int (2))
                                       (Prims.of_int (969))
                                       (Prims.of_int (14)))))
                              (Obj.magic (simplify_st_term g p1))
                              (fun uu___ ->
                                 (fun p2 -> Obj.magic (extract_dv p2)) uu___)))
                        uu___))) uu___)
let (extract_pulse :
  Pulse_Extract_CompilerLib.uenv ->
    FStar_Reflection_Types.sigelt ->
      Pulse_Syntax_Base.st_term ->
        ((Pulse_Extract_CompilerLib.mlmodule, Prims.string)
           FStar_Pervasives.either,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uenv ->
    fun selt ->
      fun p ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (974)) (Prims.of_int (12))
                   (Prims.of_int (974)) (Prims.of_int (62)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (975)) (Prims.of_int (2))
                   (Prims.of_int (1026)) (Prims.of_int (75)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                {
                  uenv_inner = uenv;
                  coreenv = (Pulse_Extract_CompilerLib.initial_core_env uenv)
                }))
          (fun uu___ ->
             (fun g ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (975)) (Prims.of_int (2))
                              (Prims.of_int (975)) (Prims.of_int (83)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (977)) (Prims.of_int (2))
                              (Prims.of_int (1026)) (Prims.of_int (75)))))
                     (Obj.magic
                        (debug g
                           (fun uu___ ->
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Extract.Main.fst"
                                         (Prims.of_int (975))
                                         (Prims.of_int (61))
                                         (Prims.of_int (975))
                                         (Prims.of_int (82)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "prims.fst"
                                         (Prims.of_int (611))
                                         (Prims.of_int (19))
                                         (Prims.of_int (611))
                                         (Prims.of_int (31)))))
                                (Obj.magic
                                   (Pulse_Syntax_Printer.st_term_to_string p))
                                (fun uu___1 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 ->
                                        Prims.strcat "About to extract:\n"
                                          (Prims.strcat uu___1 "\n"))))))
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
                                                  (Prims.of_int (978))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (978))
                                                  (Prims.of_int (43)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (979))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (1021))
                                                  (Prims.of_int (59)))))
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 ->
                                               FStar_Reflection_V2_Builtins.inspect_sigelt
                                                 selt))
                                         (fun uu___2 ->
                                            (fun sigelt_view ->
                                               match sigelt_view with
                                               | FStar_Reflection_V2_Data.Sg_Let
                                                   (is_rec, lbs) ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (if
                                                           is_rec ||
                                                             ((FStar_List_Tot_Base.length
                                                                 lbs)
                                                                <>
                                                                Prims.int_one)
                                                         then
                                                           Obj.repr
                                                             (FStar_Tactics_Effect.raise
                                                                (Extraction_failure
                                                                   "Extraction of recursive lets is not yet supported"))
                                                         else
                                                           Obj.repr
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (984))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (984))
                                                                    (Prims.of_int (60)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (983))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1019))
                                                                    (Prims.of_int (7)))))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    FStar_Reflection_V2_Builtins.inspect_lb
                                                                    (FStar_List_Tot_Base.hd
                                                                    lbs)))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStar_Reflection_V2_Data.lb_fv
                                                                    = lb_fv;
                                                                    FStar_Reflection_V2_Data.lb_us
                                                                    = uu___4;
                                                                    FStar_Reflection_V2_Data.lb_typ
                                                                    = lb_typ;
                                                                    FStar_Reflection_V2_Data.lb_def
                                                                    = uu___5;_}
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (985))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (985))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (985))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1018))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (is_recursive
                                                                    g lb_fv
                                                                    selt))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (extract_recursive_knot
                                                                    g p lb_fv
                                                                    lb_typ)
                                                                    | 
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (989))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (989))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (989))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (1018))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g p))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun p1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (990))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (990))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (990))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (1018))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (simplify_st_term
                                                                    g p1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun p2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (991))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (991))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (992))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (1018))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Reflection_V2_Builtins.inspect_fv
                                                                    lb_fv))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    fv_name
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (992))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (993))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (995))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (1018))
                                                                    (Prims.of_int (57)))))
                                                                    (if
                                                                    Prims.uu___is_Nil
                                                                    fv_name
                                                                    then
                                                                    FStar_Tactics_Effect.raise
                                                                    (Extraction_failure
                                                                    "Unexpected empty name")
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (996))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (1008))
                                                                    (Prims.of_int (15)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1009))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1018))
                                                                    (Prims.of_int (57)))))
                                                                    (if
                                                                    Pulse_RuntimeUtils.debug_at_level_no_module
                                                                    "extract_div"
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (998))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (998))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (998))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (1007))
                                                                    (Prims.of_int (83)))))
                                                                    (Obj.magic
                                                                    (extract_pulse_dv
                                                                    uenv p2))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun t ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (999))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (999))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (999))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (1007))
                                                                    (Prims.of_int (83)))))
                                                                    (Obj.magic
                                                                    (extract_dv_typ
                                                                    lb_typ))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun ty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1003))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (1006))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1007))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1007))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Pulse_Extract_CompilerLib.mk_non_rec_siglet
                                                                    (FStar_List_Tot_Base.last
                                                                    fv_name)
                                                                    t ty))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun sg
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1007))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (1007))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1007))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1007))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "Sigelt: "
                                                                    (Prims.strcat
                                                                    (Pulse_Extract_CompilerLib.sigelt_to_string
                                                                    sg) "")))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___9))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
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
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1011))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (1011))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1009))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (1018))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (generalize
                                                                    g lb_typ
                                                                    (FStar_Pervasives_Native.Some
                                                                    p2)))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    (g1, tys,
                                                                    lb_typ1,
                                                                    FStar_Pervasives_Native.Some
                                                                    p3) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1012))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (1012))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1012))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (1018))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Extract_CompilerLib.term_as_mlty
                                                                    g1.uenv_inner
                                                                    lb_typ1))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun mlty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1013))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (1013))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1012))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (1018))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (extract
                                                                    g1 p3))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (tm, tag)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1014))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (1014))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1015))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (1018))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_List_Tot_Base.last
                                                                    fv_name))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    fv_name1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1015))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (1015))
                                                                    (Prims.of_int (106)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1015))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (1018))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (debug_
                                                                    g1
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Extracted term ("
                                                                    (Prims.strcat
                                                                    fv_name1
                                                                    "): "))
                                                                    (Prims.strcat
                                                                    (Pulse_Extract_CompilerLib.mlexpr_to_string
                                                                    tm) "\n"))))
                                                                    uu___12)))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1016))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (1016))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1018))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (1018))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (extract_attrs
                                                                    uenv selt))
                                                                    (fun
                                                                    attrs ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pervasives.Inl
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mlm_let_with_attrs
                                                                    false
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mk_mllb_with_attrs
                                                                    fv_name1
                                                                    (tys,
                                                                    mlty) tm
                                                                    attrs]
                                                                    attrs]))))
                                                                    uu___12)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___6)))
                                                                    uu___3))))
                                               | uu___2 ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.raise
                                                           (Extraction_failure
                                                              "Unexpected sigelt"))))
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
                                                          (Pulse_RuntimeUtils.print_exn
                                                             e) "")))))
                                     uu___1))) uu___))) uu___)
let (extract_pulse_sig :
  Pulse_Extract_CompilerLib.uenv ->
    FStar_Reflection_Types.sigelt ->
      Pulse_Syntax_Base.st_term ->
        (((Pulse_Extract_CompilerLib.uenv * Pulse_Extract_CompilerLib.iface),
           Prims.string) FStar_Pervasives.either,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun selt ->
      fun p ->
        FStar_Tactics_V2_Derived.try_with
          (fun uu___ ->
             match () with
             | () ->
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (1033)) (Prims.of_int (22))
                            (Prims.of_int (1033)) (Prims.of_int (43)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (1034)) (Prims.of_int (4))
                            (Prims.of_int (1047)) (Prims.of_int (59)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___1 ->
                         FStar_Reflection_V2_Builtins.inspect_sigelt selt))
                   (fun uu___1 ->
                      (fun sigelt_view ->
                         match sigelt_view with
                         | FStar_Reflection_V2_Data.Sg_Let (is_rec, lbs) ->
                             Obj.magic
                               (Obj.repr
                                  (if
                                     is_rec ||
                                       ((FStar_List_Tot_Base.length lbs) <>
                                          Prims.int_one)
                                   then
                                     Obj.repr
                                       (FStar_Tactics_Effect.raise
                                          (Extraction_failure
                                             "Extraction of iface for recursive lets is not yet supported"))
                                   else
                                     Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (1039))
                                                   (Prims.of_int (30))
                                                   (Prims.of_int (1039))
                                                   (Prims.of_int (60)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (1038))
                                                   (Prims.of_int (10))
                                                   (Prims.of_int (1046))
                                                   (Prims.of_int (53)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                FStar_Reflection_V2_Builtins.inspect_lb
                                                  (FStar_List_Tot_Base.hd lbs)))
                                          (fun uu___2 ->
                                             (fun uu___2 ->
                                                match uu___2 with
                                                | {
                                                    FStar_Reflection_V2_Data.lb_fv
                                                      = lb_fv;
                                                    FStar_Reflection_V2_Data.lb_us
                                                      = uu___3;
                                                    FStar_Reflection_V2_Data.lb_typ
                                                      = lb_typ;
                                                    FStar_Reflection_V2_Data.lb_def
                                                      = uu___4;_}
                                                    ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (1040))
                                                                  (Prims.of_int (17))
                                                                  (Prims.of_int (1040))
                                                                  (Prims.of_int (18)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (1040))
                                                                  (Prims.of_int (21))
                                                                  (Prims.of_int (1046))
                                                                  (Prims.of_int (53)))))
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___5 -> g))
                                                         (fun uu___5 ->
                                                            (fun g0 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1041))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (1041))
                                                                    (Prims.of_int (62)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1041))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (1046))
                                                                    (Prims.of_int (53)))))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    {
                                                                    uenv_inner
                                                                    = g;
                                                                    coreenv =
                                                                    (Pulse_Extract_CompilerLib.initial_core_env
                                                                    g)
                                                                    }))
                                                                    (
                                                                    fun
                                                                    uu___5 ->
                                                                    (fun g1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1042))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (1042))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1041))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (1046))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    (generalize
                                                                    g1 lb_typ
                                                                    FStar_Pervasives_Native.None))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (g2, tys,
                                                                    lb_typ1,
                                                                    uu___6)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1043))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1043))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1044))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (1046))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    (debug_
                                                                    g2
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (1043))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (1043))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    lb_typ1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "Extracting ml typ: "
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match 
                                                                    Pulse_Extract_CompilerLib.extend_fv
                                                                    g0 lb_fv
                                                                    (tys,
                                                                    (Pulse_Extract_CompilerLib.term_as_mlty
                                                                    g2.uenv_inner
                                                                    lb_typ1))
                                                                    with
                                                                    | 
                                                                    (g3,
                                                                    uu___9,
                                                                    e_bnd) ->
                                                                    FStar_Pervasives.Inl
                                                                    (g3,
                                                                    (Pulse_Extract_CompilerLib.iface_of_bindings
                                                                    [
                                                                    (lb_fv,
                                                                    e_bnd)]))))))
                                                                    uu___5)))
                                                                    uu___5)))
                                                              uu___5)))
                                               uu___2))))
                         | uu___1 ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.raise
                                     (Extraction_failure "Unexpected sigelt"))))
                        uu___1))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        match uu___ with
                        | Extraction_failure msg -> FStar_Pervasives.Inr msg
                        | e ->
                            FStar_Pervasives.Inr
                              (Prims.strcat
                                 "Unexpected extraction error (iface): "
                                 (Prims.strcat
                                    (Pulse_RuntimeUtils.print_exn e) "")))))
               uu___)