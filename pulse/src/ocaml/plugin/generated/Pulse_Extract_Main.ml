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
                  (let uu___ = f () in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (54)) (Prims.of_int (17))
                              (Prims.of_int (54)) (Prims.of_int (22)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (54)) (Prims.of_int (9))
                              (Prims.of_int (54)) (Prims.of_int (22)))))
                     (Obj.magic uu___)
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic (FStar_Tactics_V2_Builtins.print uu___1))
                          uu___1)))
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
                   let uenv = uenv_of_env g in
                   let t1 =
                     Pulse_Extract_CompilerLib.normalize_for_extraction uenv
                       t in
                   let uu___1 =
                     Pulse_Extract_CompilerLib.term_as_mlexpr uenv t1 in
                   match uu___1 with | (mlt, uu___2, uu___3) -> mlt))) uu___1
        uu___
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
      let uu___ = term_as_mlty g b.Pulse_Syntax_Base.binder_ty in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (70)) (Prims.of_int (15)) (Prims.of_int (70))
                 (Prims.of_int (41)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (70)) (Prims.of_int (44)) (Prims.of_int (77))
                 (Prims.of_int (64))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun mlty ->
              let uu___1 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 -> Pulse_Typing_Env.fresh g.coreenv)) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (71)) (Prims.of_int (12))
                            (Prims.of_int (71)) (Prims.of_int (29)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (71)) (Prims.of_int (32))
                            (Prims.of_int (77)) (Prims.of_int (64)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun x ->
                         let uu___2 =
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___3 ->
                                   Pulse_Typing_Env.push_binding g.coreenv x
                                     b.Pulse_Syntax_Base.binder_ppname
                                     b.Pulse_Syntax_Base.binder_ty)) in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (72))
                                       (Prims.of_int (18))
                                       (Prims.of_int (72))
                                       (Prims.of_int (72)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (73)) (Prims.of_int (4))
                                       (Prims.of_int (77))
                                       (Prims.of_int (64)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 (fun coreenv ->
                                    let uu___3 =
                                      debug g
                                        (fun uu___4 ->
                                           let uu___5 =
                                             Pulse_Syntax_Printer.term_to_string
                                               b.Pulse_Syntax_Base.binder_ty in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Extract.Main.fst"
                                                      (Prims.of_int (75))
                                                      (Prims.of_int (38))
                                                      (Prims.of_int (75))
                                                      (Prims.of_int (66)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Extract.Main.fst"
                                                      (Prims.of_int (73))
                                                      (Prims.of_int (22))
                                                      (Prims.of_int (75))
                                                      (Prims.of_int (66)))))
                                             (Obj.magic uu___5)
                                             (fun uu___6 ->
                                                (fun uu___6 ->
                                                   let uu___7 =
                                                     let uu___8 =
                                                       Pulse_Syntax_Printer.binder_to_string
                                                         b in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Extract.Main.fst"
                                                                (Prims.of_int (74))
                                                                (Prims.of_int (38))
                                                                (Prims.of_int (74))
                                                                (Prims.of_int (58)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Printf.fst"
                                                                (Prims.of_int (122))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (124))
                                                                (Prims.of_int (44)))))
                                                       (Obj.magic uu___8)
                                                       (fun uu___9 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___10 ->
                                                               fun x1 ->
                                                                 Prims.strcat
                                                                   (Prims.strcat
                                                                    "Extending environment with "
                                                                    (Prims.strcat
                                                                    uu___9
                                                                    " : "))
                                                                   (Prims.strcat
                                                                    x1 "\n"))) in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Extract.Main.fst"
                                                                 (Prims.of_int (73))
                                                                 (Prims.of_int (22))
                                                                 (Prims.of_int (75))
                                                                 (Prims.of_int (66)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Extract.Main.fst"
                                                                 (Prims.of_int (73))
                                                                 (Prims.of_int (22))
                                                                 (Prims.of_int (75))
                                                                 (Prims.of_int (66)))))
                                                        (Obj.magic uu___7)
                                                        (fun uu___8 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___9 ->
                                                                uu___8 uu___6))))
                                                  uu___6)) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (73))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (75))
                                                  (Prims.of_int (67)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (75))
                                                  (Prims.of_int (68))
                                                  (Prims.of_int (77))
                                                  (Prims.of_int (64)))))
                                         (Obj.magic uu___3)
                                         (fun uu___4 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___5 ->
                                                 let uu___6 =
                                                   Pulse_Extract_CompilerLib.extend_bv
                                                     g.uenv_inner
                                                     b.Pulse_Syntax_Base.binder_ppname
                                                     x mlty in
                                                 match uu___6 with
                                                 | (uenv_inner, mlident) ->
                                                     ({ uenv_inner; coreenv },
                                                       mlident, mlty,
                                                       ((b.Pulse_Syntax_Base.binder_ppname),
                                                         x)))))) uu___3)))
                        uu___2))) uu___1)
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
                (let uu___ = name_as_mlpath xs in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (85)) (Prims.of_int (18))
                            (Prims.of_int (85)) (Prims.of_int (35)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (84)) (Prims.of_int (16))
                            (Prims.of_int (86)) (Prims.of_int (16)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           match uu___1 with | (xs1, x2) -> ((x2 :: xs1), x2))))))
      uu___
let (extract_constant :
  env ->
    FStar_Reflection_V2_Data.vconst ->
      (Pulse_Extract_CompilerLib.mlconstant, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun c ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                FStar_Reflection_V2_Builtins.pack_ln
                  (FStar_Reflection_V2_Data.Tv_Const c))) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (91)) (Prims.of_int (12)) (Prims.of_int (91))
                 (Prims.of_int (36)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (91)) (Prims.of_int (39)) (Prims.of_int (95))
                 (Prims.of_int (17))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun e ->
              let uu___1 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        Pulse_Extract_CompilerLib.term_as_mlexpr
                          (uenv_of_env g) e)) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (92)) (Prims.of_int (20))
                            (Prims.of_int (92)) (Prims.of_int (64)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (91)) (Prims.of_int (39))
                            (Prims.of_int (95)) (Prims.of_int (17)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun uu___2 ->
                         match uu___2 with
                         | (mle, uu___3, uu___4) ->
                             let uu___5 =
                               Obj.magic
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 ->
                                       Pulse_Extract_CompilerLib.mlconstant_of_mlexpr
                                         mle)) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (93))
                                           (Prims.of_int (10))
                                           (Prims.of_int (93))
                                           (Prims.of_int (34)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (93))
                                           (Prims.of_int (4))
                                           (Prims.of_int (95))
                                           (Prims.of_int (17)))))
                                  (Obj.magic uu___5)
                                  (fun uu___6 ->
                                     match uu___6 with
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Tactics_Effect.raise
                                           (Extraction_failure
                                              "Failed to extract constant")
                                     | FStar_Pervasives_Native.Some c1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___7 -> c1)))) uu___2)))
             uu___1)
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
                    (let uu___ =
                       Obj.magic
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> Pulse_Typing_Env.fresh g.coreenv)) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (102)) (Prims.of_int (14))
                                (Prims.of_int (102)) (Prims.of_int (31)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (102)) (Prims.of_int (34))
                                (Prims.of_int (111)) (Prims.of_int (25)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun x ->
                             let uu___1 =
                               Obj.magic
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       Pulse_Syntax_Base.mk_ppname pp
                                         FStar_Range.range_0)) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (103))
                                           (Prims.of_int (15))
                                           (Prims.of_int (103))
                                           (Prims.of_int (47)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (103))
                                           (Prims.of_int (50))
                                           (Prims.of_int (111))
                                           (Prims.of_int (25)))))
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun pp1 ->
                                        let uu___2 =
                                          FStar_Tactics_Unseal.unseal sort in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Extract.Main.fst"
                                                      (Prims.of_int (104))
                                                      (Prims.of_int (15))
                                                      (Prims.of_int (104))
                                                      (Prims.of_int (28)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Extract.Main.fst"
                                                      (Prims.of_int (104))
                                                      (Prims.of_int (31))
                                                      (Prims.of_int (111))
                                                      (Prims.of_int (25)))))
                                             (Obj.magic uu___2)
                                             (fun uu___3 ->
                                                (fun ty ->
                                                   let uu___3 =
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___4 ->
                                                             Pulse_Syntax_Pure.wr
                                                               ty
                                                               (FStar_Reflection_V2_Builtins.range_of_term
                                                                  ty))) in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Extract.Main.fst"
                                                                 (Prims.of_int (105))
                                                                 (Prims.of_int (15))
                                                                 (Prims.of_int (105))
                                                                 (Prims.of_int (41)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Extract.Main.fst"
                                                                 (Prims.of_int (106))
                                                                 (Prims.of_int (6))
                                                                 (Prims.of_int (111))
                                                                 (Prims.of_int (25)))))
                                                        (Obj.magic uu___3)
                                                        (fun uu___4 ->
                                                           (fun ty1 ->
                                                              let uu___4 =
                                                                debug g
                                                                  (fun uu___5
                                                                    ->
                                                                    let uu___6
                                                                    =
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    ty1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (105)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (105)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    FStar_Tactics_Unseal.unseal
                                                                    pp1.Pulse_Syntax_Base.name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (106))
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
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Pushing pat_var "
                                                                    (Prims.strcat
                                                                    uu___10
                                                                    " : "))
                                                                    (Prims.strcat
                                                                    x1 "\n"))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (105)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (105)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    uu___9
                                                                    uu___7))))
                                                                    uu___7)) in
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (106)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (25)))))
                                                                   (Obj.magic
                                                                    uu___4)
                                                                   (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    let coreenv
                                                                    =
                                                                    Pulse_Typing_Env.push_binding
                                                                    g.coreenv
                                                                    x pp1 ty1 in
                                                                    let uu___7
                                                                    =
                                                                    Pulse_Extract_CompilerLib.extend_bv
                                                                    g.uenv_inner
                                                                    pp1 x
                                                                    Pulse_Extract_CompilerLib.mlty_top in
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (uenv_inner,
                                                                    mlident)
                                                                    ->
                                                                    ({
                                                                    uenv_inner;
                                                                    coreenv
                                                                    },
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mlp_var
                                                                    mlident],
                                                                    [
                                                                    (x,
                                                                    Pulse_Syntax_Pure.tm_unknown)])))))
                                                             uu___4))) uu___3)))
                                       uu___2))) uu___1)))
           | Pulse_Syntax_Base.Pat_Cons (f, pats) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       FStar_Tactics_Util.fold_left
                         (fun uu___1 ->
                            fun uu___2 ->
                              match (uu___1, uu___2) with
                              | ((g1, pats1, bindings), (p1, uu___3)) ->
                                  let uu___4 = extend_env_pat_core g1 p1 in
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Extract.Main.fst"
                                             (Prims.of_int (117))
                                             (Prims.of_int (38))
                                             (Prims.of_int (117))
                                             (Prims.of_int (61)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Extract.Main.fst"
                                             (Prims.of_int (116))
                                             (Prims.of_int (44))
                                             (Prims.of_int (118))
                                             (Prims.of_int (47)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___6 ->
                                            match uu___5 with
                                            | (g2, pats', bindings') ->
                                                (g2,
                                                  (FStar_List_Tot_Base.op_At
                                                     pats1 pats'),
                                                  (FStar_List_Tot_Base.op_At
                                                     bindings bindings')))))
                         (g, [], []) pats in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (115)) (Prims.of_int (8))
                                (Prims.of_int (120)) (Prims.of_int (14)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (113)) (Prims.of_int (24))
                                (Prims.of_int (122)) (Prims.of_int (68)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             match uu___1 with
                             | (g1, pats1, bindings) ->
                                 let uu___2 =
                                   let uu___3 =
                                     let uu___4 =
                                       name_as_mlpath
                                         f.Pulse_Syntax_Base.fv_name in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (122))
                                                (Prims.of_int (26))
                                                (Prims.of_int (122))
                                                (Prims.of_int (52)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (122))
                                                (Prims.of_int (10))
                                                (Prims.of_int (122))
                                                (Prims.of_int (57)))))
                                       (Obj.magic uu___4)
                                       (fun uu___5 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___6 ->
                                               Pulse_Extract_CompilerLib.mlp_constructor
                                                 uu___5 pats1)) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (122))
                                              (Prims.of_int (10))
                                              (Prims.of_int (122))
                                              (Prims.of_int (57)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (122))
                                              (Prims.of_int (9))
                                              (Prims.of_int (122))
                                              (Prims.of_int (58)))))
                                     (Obj.magic uu___3)
                                     (fun uu___4 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___5 -> [uu___4])) in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (122))
                                               (Prims.of_int (9))
                                               (Prims.of_int (122))
                                               (Prims.of_int (58)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (122))
                                               (Prims.of_int (6))
                                               (Prims.of_int (122))
                                               (Prims.of_int (68)))))
                                      (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 ->
                                              (g1, uu___3, bindings)))))
                            uu___1)))
           | Pulse_Syntax_Base.Pat_Constant c ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = extract_constant g c in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (124)) (Prims.of_int (14))
                                (Prims.of_int (124)) (Prims.of_int (34)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (125)) (Prims.of_int (6))
                                (Prims.of_int (125)) (Prims.of_int (26)))))
                       (Obj.magic uu___)
                       (fun c1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
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
      let uu___ = extend_env_pat_core g p in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (127)) (Prims.of_int (20))
                 (Prims.of_int (127)) (Prims.of_int (43)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (126)) (Prims.of_int (24))
                 (Prims.of_int (130)) (Prims.of_int (72)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           match uu___1 with
           | (g1, pats, bs) ->
               (match pats with
                | p1::[] ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___2 -> (g1, p1, bs))
                | uu___2 ->
                    FStar_Tactics_Effect.raise
                      (Extraction_failure "Unexpected extraction of pattern")))
let (unit_val : Pulse_Syntax_Base.term) =
  Pulse_Syntax_Pure.wr Pulse_Reflection_Util.unit_tm FStar_Range.range_0
let (is_erasable :
  Pulse_Syntax_Base.st_term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun p ->
    let uu___ = FStar_Tactics_Unseal.unseal p.Pulse_Syntax_Base.effect_tag in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (134)) (Prims.of_int (12)) (Prims.of_int (134))
               (Prims.of_int (33)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (135)) (Prims.of_int (2)) (Prims.of_int (137))
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
      let uu___ =
        debug g
          (fun uu___1 ->
             let uu___2 = FStar_Tactics_V2_Builtins.term_to_string head in
             FStar_Tactics_Effect.tac_bind
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                        (Prims.of_int (149)) (Prims.of_int (65))
                        (Prims.of_int (149)) (Prims.of_int (88)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                        (Prims.of_int (19)) (Prims.of_int (611))
                        (Prims.of_int (31))))) (Obj.magic uu___2)
               (fun uu___3 ->
                  FStar_Tactics_Effect.lift_div_tac
                    (fun uu___4 ->
                       Prims.strcat "Maybe unfolding head "
                         (Prims.strcat uu___3 "\n")))) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (149)) (Prims.of_int (4)) (Prims.of_int (149))
                 (Prims.of_int (89)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (150)) (Prims.of_int (4)) (Prims.of_int (176))
                 (Prims.of_int (15))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match FStar_Reflection_V2_Builtins.inspect_ln head with
              | FStar_Reflection_V2_Data.Tv_FVar f ->
                  Obj.magic
                    (Obj.repr
                       (let uu___2 =
                          Obj.magic
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 ->
                                  FStar_Reflection_V2_Builtins.inspect_fv f)) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Extract.Main.fst"
                                   (Prims.of_int (152)) (Prims.of_int (17))
                                   (Prims.of_int (152)) (Prims.of_int (31)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Extract.Main.fst"
                                   (Prims.of_int (153)) (Prims.of_int (6))
                                   (Prims.of_int (171)) (Prims.of_int (17)))))
                          (Obj.magic uu___2)
                          (fun uu___3 ->
                             (fun name1 ->
                                match FStar_Reflection_V2_Builtins.lookup_typ
                                        (topenv_of_env g) name1
                                with
                                | FStar_Pervasives_Native.None ->
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___3 ->
                                               FStar_Pervasives_Native.None)))
                                | FStar_Pervasives_Native.Some se ->
                                    Obj.magic
                                      (Obj.repr
                                         (let uu___3 =
                                            Obj.magic
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___4 ->
                                                    FStar_Reflection_V2_Builtins.sigelt_attrs
                                                      se)) in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Extract.Main.fst"
                                                     (Prims.of_int (156))
                                                     (Prims.of_int (20))
                                                     (Prims.of_int (156))
                                                     (Prims.of_int (37)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Extract.Main.fst"
                                                     (Prims.of_int (156))
                                                     (Prims.of_int (40))
                                                     (Prims.of_int (171))
                                                     (Prims.of_int (17)))))
                                            (Obj.magic uu___3)
                                            (fun uu___4 ->
                                               (fun attrs ->
                                                  let uu___4 =
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___5 ->
                                                            FStar_Reflection_V2_Builtins.sigelt_quals
                                                              se)) in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Extract.Main.fst"
                                                                (Prims.of_int (157))
                                                                (Prims.of_int (20))
                                                                (Prims.of_int (157))
                                                                (Prims.of_int (37)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Extract.Main.fst"
                                                                (Prims.of_int (158))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (171))
                                                                (Prims.of_int (17)))))
                                                       (Obj.magic uu___4)
                                                       (fun uu___5 ->
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
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V2_Data.Inline_for_extraction
                                                                    -> true
                                                                    | 
                                                                    uu___6 ->
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
                                                                    let uu___5
                                                                    =
                                                                    debug g
                                                                    (fun
                                                                    uu___6 ->
                                                                    let uu___7
                                                                    =
                                                                    FStar_Tactics_V2_Builtins.term_to_string
                                                                    head in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "Unfolded head "
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    "\n")))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    let uu___7
                                                                    =
                                                                    debug g
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    Pulse_Syntax_Printer.st_term_to_string
                                                                    se1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Prims.strcat
                                                                    "to "
                                                                    (Prims.strcat
                                                                    uu___10
                                                                    "\n")))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Inl
                                                                    se1)))))
                                                                    uu___6)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    let uu___5
                                                                    =
                                                                    FStar_Tactics_NamedView.inspect_sigelt
                                                                    se in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___6
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
                                                                    = uu___8;
                                                                    FStar_Tactics_NamedView.lb_us
                                                                    = [];
                                                                    FStar_Tactics_NamedView.lb_typ
                                                                    = uu___9;
                                                                    FStar_Tactics_NamedView.lb_def
                                                                    = lb_def;_}::[];_}
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Inr
                                                                    lb_def)
                                                                    | 
                                                                    uu___8 ->
                                                                    FStar_Pervasives_Native.None))))
                                                             else
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.None))))
                                                            uu___5))) uu___4))))
                               uu___3)))
              | FStar_Reflection_V2_Data.Tv_UInst (f, uu___2) ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> FStar_Pervasives_Native.None)))
              | uu___2 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> FStar_Pervasives_Native.None))))
             uu___1)
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
        let uu___ =
          debug g
            (fun uu___1 ->
               let uu___2 = Pulse_Syntax_Printer.term_to_string head in
               FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                          (Prims.of_int (214)) (Prims.of_int (22))
                          (Prims.of_int (214)) (Prims.of_int (43)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                          (Prims.of_int (19)) (Prims.of_int (611))
                          (Prims.of_int (31))))) (Obj.magic uu___2)
                 (fun uu___3 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___4 ->
                         Prims.strcat "Considering inlining "
                           (Prims.strcat uu___3 "\n")))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (213)) (Prims.of_int (2))
                   (Prims.of_int (214)) (Prims.of_int (44)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (215)) (Prims.of_int (2))
                   (Prims.of_int (299)) (Prims.of_int (46)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match head_and_args head with
                | FStar_Pervasives_Native.None ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> FStar_Pervasives_Native.None)))
                | FStar_Pervasives_Native.Some (head1, args) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 =
                            debug g
                              (fun uu___3 ->
                                 let uu___4 =
                                   let uu___5 =
                                     FStar_Tactics_V2_Builtins.term_to_string
                                       head1 in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (219))
                                              (Prims.of_int (22))
                                              (Prims.of_int (219))
                                              (Prims.of_int (45)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Printf.fst"
                                              (Prims.of_int (122))
                                              (Prims.of_int (8))
                                              (Prims.of_int (124))
                                              (Prims.of_int (44)))))
                                     (Obj.magic uu___5)
                                     (fun uu___6 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___7 ->
                                             fun x ->
                                               Prims.strcat
                                                 (Prims.strcat "head="
                                                    (Prims.strcat uu___6
                                                       " with "))
                                                 (Prims.strcat
                                                    (Prims.string_of_int x)
                                                    " args\n"))) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Extract.Main.fst"
                                            (Prims.of_int (218))
                                            (Prims.of_int (22))
                                            (Prims.of_int (220))
                                            (Prims.of_int (40)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Extract.Main.fst"
                                            (Prims.of_int (218))
                                            (Prims.of_int (22))
                                            (Prims.of_int (220))
                                            (Prims.of_int (40)))))
                                   (Obj.magic uu___4)
                                   (fun uu___5 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___6 ->
                                           uu___5
                                             (FStar_List_Tot_Base.length args)))) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Extract.Main.fst"
                                     (Prims.of_int (218)) (Prims.of_int (4))
                                     (Prims.of_int (220)) (Prims.of_int (41)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Extract.Main.fst"
                                     (Prims.of_int (221)) (Prims.of_int (4))
                                     (Prims.of_int (299)) (Prims.of_int (46)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun uu___3 ->
                                  let uu___4 = maybe_unfold_head g head1 in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (221))
                                                (Prims.of_int (10))
                                                (Prims.of_int (221))
                                                (Prims.of_int (34)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (221))
                                                (Prims.of_int (4))
                                                (Prims.of_int (299))
                                                (Prims.of_int (46)))))
                                       (Obj.magic uu___4)
                                       (fun uu___5 ->
                                          (fun uu___5 ->
                                             match uu___5 with
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 let uu___6 =
                                                   debug g
                                                     (fun uu___7 ->
                                                        let uu___8 =
                                                          FStar_Tactics_V2_Builtins.term_to_string
                                                            head1 in
                                                        FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Extract.Main.fst"
                                                                   (Prims.of_int (224))
                                                                   (Prims.of_int (28))
                                                                   (Prims.of_int (224))
                                                                   (Prims.of_int (51)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Prims.fst"
                                                                   (Prims.of_int (611))
                                                                   (Prims.of_int (19))
                                                                   (Prims.of_int (611))
                                                                   (Prims.of_int (31)))))
                                                          (Obj.magic uu___8)
                                                          (fun uu___9 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___10
                                                                  ->
                                                                  Prims.strcat
                                                                    "No unfolding of "
                                                                    (
                                                                    Prims.strcat
                                                                    uu___9
                                                                    "\n")))) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (223))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (224))
                                                               (Prims.of_int (52)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (225))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (225))
                                                               (Prims.of_int (10)))))
                                                      (Obj.magic uu___6)
                                                      (fun uu___7 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___8 ->
                                                              FStar_Pervasives_Native.None)))
                                             | FStar_Pervasives_Native.Some
                                                 def ->
                                                 let uu___6 =
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___7 ->
                                                           fun a ->
                                                             Pulse_Syntax_Pure.wr
                                                               a
                                                               FStar_Range.range_0)) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (232))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (232))
                                                               (Prims.of_int (26)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (232))
                                                               (Prims.of_int (29))
                                                               (Prims.of_int (299))
                                                               (Prims.of_int (46)))))
                                                      (Obj.magic uu___6)
                                                      (fun uu___7 ->
                                                         (fun as_term ->
                                                            let uu___7 =
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___8 ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    (FStar_List_Tot_Base.map
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
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
                                                                    FStar_Pervasives_Native.None)])) in
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (21)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (46)))))
                                                                 (Obj.magic
                                                                    uu___7)
                                                                 (fun uu___8
                                                                    ->
                                                                    (fun
                                                                    all_args
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_List_Tot_Base.length
                                                                    all_args)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    n_args ->
                                                                    let uu___9
                                                                    =
                                                                    abs_take_n_args
                                                                    n_args
                                                                    def in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    (body,
                                                                    remaining_args)
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_List_Tot_Base.splitAt
                                                                    (n_args -
                                                                    remaining_args)
                                                                    all_args)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    (args1,
                                                                    rest) ->
                                                                    let uu___13
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_List_Tot_Base.fold_right
                                                                    (fun arg1
                                                                    ->
                                                                    fun
                                                                    uu___15
                                                                    ->
                                                                    match uu___15
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
                                                                    []))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    match uu___14
                                                                    with
                                                                    | 
                                                                    (uu___15,
                                                                    subst) ->
                                                                    (match body
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Inl
                                                                    body1 ->
                                                                    let uu___16
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body1
                                                                    subst)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
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
                                                                    uu___17
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    applied_body)))
                                                                    | 
                                                                    uu___17
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    FStar_Tactics_Util.map
                                                                    (fun x ->
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    (FStar_Pervasives_Native.fst
                                                                    x)) rest in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (79)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_String.concat
                                                                    ", "
                                                                    uu___21)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStar_Tactics_V2_Builtins.term_to_string
                                                                    head1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (263))
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
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Partial or over application of inlined Pulse definition is not yet supported\n"
                                                                    (Prims.strcat
                                                                    uu___24
                                                                    " has "))
                                                                    (Prims.strcat
                                                                    (Prims.string_of_int
                                                                    x)
                                                                    " arguments, but "))
                                                                    (Prims.strcat
                                                                    x1
                                                                    " were left unapplied"))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    uu___23
                                                                    (FStar_List_Tot_Base.length
                                                                    args1))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    uu___22
                                                                    uu___20))))
                                                                    uu___20) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    uu___19))))
                                                                    uu___17))
                                                                    | 
                                                                    FStar_Pervasives.Inr
                                                                    body1 ->
                                                                    let uu___16
                                                                    =
                                                                    unascribe
                                                                    (Pulse_Syntax_Naming.subst_host_term
                                                                    body1
                                                                    subst) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    applied_body
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
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
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
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
                                                                    uu___18
                                                                    ->
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
                                                                    uu___18
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    FStar_Tactics_V2_Builtins.term_to_string
                                                                    applied_body in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    Prims.strcat
                                                                    "Cannot inline F* definitions of stt terms whose body is not an application; got "
                                                                    (Prims.strcat
                                                                    uu___21
                                                                    ""))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    uu___20))))
                                                                    | 
                                                                    rest1 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
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
                                                                    uu___19
                                                                    ->
                                                                    match uu___19
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
                                                                    uu___18)))
                                                                    uu___17))))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                           uu___7))) uu___5)))
                                 uu___3)))) uu___1)
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
          let uu___ =
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> fresh g)) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                     (Prims.of_int (308)) (Prims.of_int (10))
                     (Prims.of_int (308)) (Prims.of_int (17)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                     (Prims.of_int (308)) (Prims.of_int (20))
                     (Prims.of_int (311)) (Prims.of_int (22)))))
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
                                (Prims.of_int (309)) (Prims.of_int (10))
                                (Prims.of_int (309)) (Prims.of_int (82)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (309)) (Prims.of_int (85))
                                (Prims.of_int (311)) (Prims.of_int (22)))))
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
                                           (Prims.of_int (310))
                                           (Prims.of_int (10))
                                           (Prims.of_int (310))
                                           (Prims.of_int (34)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (311))
                                           (Prims.of_int (2))
                                           (Prims.of_int (311))
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
      FStar_Tactics_Unseal.unseal
        (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (315)) (Prims.of_int (10)) (Prims.of_int (315))
               (Prims.of_int (39)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (316)) (Prims.of_int (2)) (Prims.of_int (321))
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
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                fun t ->
                  {
                    Pulse_Syntax_Base.term1 = t;
                    Pulse_Syntax_Base.range1 = (e.Pulse_Syntax_Base.range1);
                    Pulse_Syntax_Base.effect_tag =
                      (e.Pulse_Syntax_Base.effect_tag)
                  })) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (363)) (Prims.of_int (16))
                 (Prims.of_int (363)) (Prims.of_int (31)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (363)) (Prims.of_int (36))
                 (Prims.of_int (425)) (Prims.of_int (23)))))
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
                            (Prims.of_int (364)) (Prims.of_int (22))
                            (Prims.of_int (364)) (Prims.of_int (54)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (366)) (Prims.of_int (2))
                            (Prims.of_int (425)) (Prims.of_int (23)))))
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
                                                  (Prims.of_int (377))
                                                  (Prims.of_int (43))
                                                  (Prims.of_int (377))
                                                  (Prims.of_int (59)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (377))
                                                  (Prims.of_int (18))
                                                  (Prims.of_int (377))
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
                                                (Prims.of_int (377))
                                                (Prims.of_int (18))
                                                (Prims.of_int (377))
                                                (Prims.of_int (59)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (377))
                                                (Prims.of_int (8))
                                                (Prims.of_int (377))
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
                                              (Prims.of_int (377))
                                              (Prims.of_int (8))
                                              (Prims.of_int (377))
                                              (Prims.of_int (62)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (377))
                                              (Prims.of_int (4))
                                              (Prims.of_int (377))
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
                                              (Prims.of_int (380))
                                              (Prims.of_int (29))
                                              (Prims.of_int (380))
                                              (Prims.of_int (54)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (381))
                                              (Prims.of_int (4))
                                              (Prims.of_int (395))
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
                                                              (Prims.of_int (386))
                                                              (Prims.of_int (25))
                                                              (Prims.of_int (386))
                                                              (Prims.of_int (39)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (386))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (387))
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
                                                                  (Prims.of_int (392))
                                                                  (Prims.of_int (19))
                                                                  (Prims.of_int (392))
                                                                  (Prims.of_int (42)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (392))
                                                                  (Prims.of_int (45))
                                                                  (Prims.of_int (394))
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
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (40)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (394))
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
                                                  (Prims.of_int (398))
                                                  (Prims.of_int (43))
                                                  (Prims.of_int (398))
                                                  (Prims.of_int (64)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (398))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (398))
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
                                                (Prims.of_int (398))
                                                (Prims.of_int (22))
                                                (Prims.of_int (398))
                                                (Prims.of_int (64)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (398))
                                                (Prims.of_int (8))
                                                (Prims.of_int (398))
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
                                              (Prims.of_int (398))
                                              (Prims.of_int (8))
                                              (Prims.of_int (398))
                                              (Prims.of_int (67)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (398))
                                              (Prims.of_int (4))
                                              (Prims.of_int (398))
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
                                                  (Prims.of_int (401))
                                                  (Prims.of_int (28))
                                                  (Prims.of_int (401))
                                                  (Prims.of_int (52)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (401))
                                                  (Prims.of_int (17))
                                                  (Prims.of_int (401))
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
                                                             (Prims.of_int (401))
                                                             (Prims.of_int (62))
                                                             (Prims.of_int (401))
                                                             (Prims.of_int (86)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (401))
                                                             (Prims.of_int (17))
                                                             (Prims.of_int (401))
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
                                                (Prims.of_int (401))
                                                (Prims.of_int (17))
                                                (Prims.of_int (401))
                                                (Prims.of_int (92)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (401))
                                                (Prims.of_int (8))
                                                (Prims.of_int (401))
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
                                              (Prims.of_int (401))
                                              (Prims.of_int (8))
                                              (Prims.of_int (401))
                                              (Prims.of_int (95)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (401))
                                              (Prims.of_int (4))
                                              (Prims.of_int (401))
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
                                                  (Prims.of_int (404))
                                                  (Prims.of_int (40))
                                                  (Prims.of_int (404))
                                                  (Prims.of_int (69)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (404))
                                                  (Prims.of_int (20))
                                                  (Prims.of_int (404))
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
                                                (Prims.of_int (404))
                                                (Prims.of_int (20))
                                                (Prims.of_int (404))
                                                (Prims.of_int (69)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (404))
                                                (Prims.of_int (8))
                                                (Prims.of_int (404))
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
                                              (Prims.of_int (404))
                                              (Prims.of_int (8))
                                              (Prims.of_int (404))
                                              (Prims.of_int (72)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (404))
                                              (Prims.of_int (4))
                                              (Prims.of_int (404))
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
                                              (Prims.of_int (407))
                                              (Prims.of_int (20))
                                              (Prims.of_int (407))
                                              (Prims.of_int (48)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (407))
                                              (Prims.of_int (51))
                                              (Prims.of_int (409))
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
                                                         (Prims.of_int (408))
                                                         (Prims.of_int (15))
                                                         (Prims.of_int (408))
                                                         (Prims.of_int (38)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (409))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (409))
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
                                                            (e.Pulse_Syntax_Base.effect_tag)
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
                                              (Prims.of_int (412))
                                              (Prims.of_int (16))
                                              (Prims.of_int (412))
                                              (Prims.of_int (40)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (412))
                                              (Prims.of_int (43))
                                              (Prims.of_int (414))
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
                                                         (Prims.of_int (413))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (413))
                                                         (Prims.of_int (40)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (414))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (414))
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
                                                            (e.Pulse_Syntax_Base.effect_tag)
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
                                                  (Prims.of_int (417))
                                                  (Prims.of_int (52))
                                                  (Prims.of_int (417))
                                                  (Prims.of_int (73)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (417))
                                                  (Prims.of_int (24))
                                                  (Prims.of_int (417))
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
                                                (Prims.of_int (417))
                                                (Prims.of_int (24))
                                                (Prims.of_int (417))
                                                (Prims.of_int (73)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (417))
                                                (Prims.of_int (8))
                                                (Prims.of_int (417))
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
                                              (Prims.of_int (417))
                                              (Prims.of_int (8))
                                              (Prims.of_int (417))
                                              (Prims.of_int (76)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (417))
                                              (Prims.of_int (4))
                                              (Prims.of_int (417))
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
                                                  (Prims.of_int (420))
                                                  (Prims.of_int (65))
                                                  (Prims.of_int (420))
                                                  (Prims.of_int (86)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (420))
                                                  (Prims.of_int (29))
                                                  (Prims.of_int (420))
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
                                                (Prims.of_int (420))
                                                (Prims.of_int (29))
                                                (Prims.of_int (420))
                                                (Prims.of_int (86)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (420))
                                                (Prims.of_int (8))
                                                (Prims.of_int (420))
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
                                              (Prims.of_int (420))
                                              (Prims.of_int (8))
                                              (Prims.of_int (420))
                                              (Prims.of_int (89)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (420))
                                              (Prims.of_int (4))
                                              (Prims.of_int (420))
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
                         | Pulse_Syntax_Base.Tm_Unreachable ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 -> e)))) uu___2))) uu___1)
and (simplify_branch :
  env ->
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
                 (Prims.of_int (428)) (Prims.of_int (18))
                 (Prims.of_int (428)) (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (427)) (Prims.of_int (55))
                 (Prims.of_int (432)) (Prims.of_int (62)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | (pat, body) ->
                  let uu___2 = extend_env_pat g pat in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (429)) (Prims.of_int (17))
                                (Prims.of_int (429)) (Prims.of_int (37)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (428)) (Prims.of_int (22))
                                (Prims.of_int (432)) (Prims.of_int (62)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          (fun uu___3 ->
                             match uu___3 with
                             | (g1, uu___4, bs) ->
                                 let uu___5 =
                                   Obj.magic
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___6 ->
                                           Pulse_Checker_Match.open_st_term_bs
                                             body bs)) in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (430))
                                               (Prims.of_int (13))
                                               (Prims.of_int (430))
                                               (Prims.of_int (56)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (430))
                                               (Prims.of_int (59))
                                               (Prims.of_int (432))
                                               (Prims.of_int (62)))))
                                      (Obj.magic uu___5)
                                      (fun uu___6 ->
                                         (fun body1 ->
                                            let uu___6 =
                                              simplify_st_term g1 body1 in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (431))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (431))
                                                          (Prims.of_int (36)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (432))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (432))
                                                          (Prims.of_int (62)))))
                                                 (Obj.magic uu___6)
                                                 (fun body2 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___7 ->
                                                         (pat,
                                                           (Pulse_Syntax_Naming.close_st_term_n
                                                              body2
                                                              (FStar_List_Tot_Base.map
                                                                 FStar_Pervasives_Native.fst
                                                                 bs)))))))
                                           uu___6))) uu___3))) uu___1)
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
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> fun g1 -> Pulse_Typing_Env.fresh g1.coreenv)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (440)) (Prims.of_int (22))
                 (Prims.of_int (440)) (Prims.of_int (50)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (440)) (Prims.of_int (53))
                 (Prims.of_int (523)) (Prims.of_int (5))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun fresh1 ->
              let uu___1 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        fun g1 ->
                          fun x ->
                            fun b ->
                              {
                                uenv_inner = (g1.uenv_inner);
                                coreenv =
                                  (Pulse_Typing_Env.push_binding g1.coreenv x
                                     b.Pulse_Syntax_Base.binder_ppname
                                     b.Pulse_Syntax_Base.binder_ty)
                              })) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (442)) (Prims.of_int (6))
                            (Prims.of_int (442)) (Prims.of_int (77)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (442)) (Prims.of_int (82))
                            (Prims.of_int (523)) (Prims.of_int (5)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun push_binding1 ->
                         let uu___2 =
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___3 ->
                                   fun g1 ->
                                     fun b ->
                                       fun e ->
                                         let uu___4 =
                                           Obj.magic
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___5 -> fresh1 g1)) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (445))
                                                    (Prims.of_int (12))
                                                    (Prims.of_int (445))
                                                    (Prims.of_int (19)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (445))
                                                    (Prims.of_int (22))
                                                    (Prims.of_int (448))
                                                    (Prims.of_int (24)))))
                                           (Obj.magic uu___4)
                                           (fun uu___5 ->
                                              (fun x ->
                                                 let uu___5 =
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___6 ->
                                                           Pulse_Syntax_Naming.open_st_term'
                                                             e
                                                             (Pulse_Syntax_Pure.tm_var
                                                                {
                                                                  Pulse_Syntax_Base.nm_index
                                                                    = x;
                                                                  Pulse_Syntax_Base.nm_ppname
                                                                    =
                                                                    (
                                                                    b.Pulse_Syntax_Base.binder_ppname)
                                                                })
                                                             Prims.int_zero)) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (446))
                                                               (Prims.of_int (12))
                                                               (Prims.of_int (446))
                                                               (Prims.of_int (84)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (446))
                                                               (Prims.of_int (87))
                                                               (Prims.of_int (448))
                                                               (Prims.of_int (24)))))
                                                      (Obj.magic uu___5)
                                                      (fun uu___6 ->
                                                         (fun e1 ->
                                                            let uu___6 =
                                                              erase_ghost_subterms
                                                                (push_binding1
                                                                   g1 x b) e1 in
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (447))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (447))
                                                                    (Prims.of_int (55)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (24)))))
                                                                 (Obj.magic
                                                                    uu___6)
                                                                 (fun e2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Naming.close_st_term'
                                                                    e2 x
                                                                    Prims.int_zero))))
                                                           uu___6))) uu___5))) in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (444))
                                       (Prims.of_int (71))
                                       (Prims.of_int (448))
                                       (Prims.of_int (24)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (448))
                                       (Prims.of_int (27))
                                       (Prims.of_int (523))
                                       (Prims.of_int (5)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 (fun open_erase_close ->
                                    let uu___3 =
                                      Obj.magic
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 ->
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
                                              })) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (451))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (451))
                                                  (Prims.of_int (94)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (452))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (523))
                                                  (Prims.of_int (5)))))
                                         (Obj.magic uu___3)
                                         (fun uu___4 ->
                                            (fun unit_tm ->
                                               let uu___4 =
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___5 ->
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
                                                           })) in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (453))
                                                             (Prims.of_int (27))
                                                             (Prims.of_int (453))
                                                             (Prims.of_int (42)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Extract.Main.fst"
                                                             (Prims.of_int (454))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (523))
                                                             (Prims.of_int (5)))))
                                                    (Obj.magic uu___4)
                                                    (fun uu___5 ->
                                                       (fun ret ->
                                                          let uu___5 =
                                                            is_erasable p in
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (18)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (5)))))
                                                               (Obj.magic
                                                                  uu___5)
                                                               (fun uu___6 ->
                                                                  (fun uu___6
                                                                    ->
                                                                    if uu___6
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    unit_tm)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    p.Pulse_Syntax_Base.term1
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_IntroPure
                                                                    uu___8 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    unit_tm))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_ElimExists
                                                                    uu___8 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    unit_tm))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_IntroExists
                                                                    uu___8 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    unit_tm))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Rewrite
                                                                    uu___8 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
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
                                                                    (let uu___8
                                                                    =
                                                                    open_erase_close
                                                                    g b body in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
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
                                                                    uu___8 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    p))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_STApp
                                                                    uu___8 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
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
                                                                    (let uu___8
                                                                    =
                                                                    is_erasable
                                                                    head in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (472))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (472))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (472))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    if uu___9
                                                                    then
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    [
                                                                    FStar_Reflection_Typing.DT
                                                                    (Prims.int_zero,
                                                                    unit_val)])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (473))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (473))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g body1))
                                                                    uu___11))
                                                                    else
                                                                    (let uu___11
                                                                    =
                                                                    erase_ghost_subterms
                                                                    g head in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    head1 ->
                                                                    let uu___12
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
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
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
                                                                    uu___12))))
                                                                    uu___9))
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
                                                                    (let uu___8
                                                                    =
                                                                    erase_type_for_extraction
                                                                    g
                                                                    binder.Pulse_Syntax_Base.binder_ty in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    if uu___9
                                                                    then
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    [
                                                                    FStar_Reflection_Typing.DT
                                                                    (Prims.int_zero,
                                                                    unit_val)])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (erase_ghost_subterms
                                                                    g body1))
                                                                    uu___11))
                                                                    else
                                                                    (let uu___11
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
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
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
                                                                    uu___9))
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
                                                                    (let uu___8
                                                                    =
                                                                    erase_ghost_subterms
                                                                    g then_ in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (489))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    then_1 ->
                                                                    let uu___9
                                                                    =
                                                                    erase_ghost_subterms
                                                                    g else_ in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (489))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (489))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    else_1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
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
                                                                    uu___9))
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
                                                                    (let uu___8
                                                                    =
                                                                    FStar_Tactics_Util.map
                                                                    (erase_ghost_subterms_branch
                                                                    g) brs in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun brs1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
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
                                                                    (let uu___8
                                                                    =
                                                                    erase_ghost_subterms
                                                                    g
                                                                    condition in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (496))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (496))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (496))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    condition1
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    erase_ghost_subterms
                                                                    g body in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
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
                                                                    uu___9))
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
                                                                    (let uu___8
                                                                    =
                                                                    erase_ghost_subterms
                                                                    g body1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (501))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (501))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (501))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    body11 ->
                                                                    let uu___9
                                                                    =
                                                                    erase_ghost_subterms
                                                                    g body2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    body21 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
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
                                                                    uu___9))
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
                                                                    (let uu___8
                                                                    =
                                                                    open_erase_close
                                                                    g binder
                                                                    body in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (507))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (507))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
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
                                                                    (let uu___8
                                                                    =
                                                                    open_erase_close
                                                                    g binder
                                                                    body in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
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
                                                                    uu___8 ->
                                                                    p))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Admit
                                                                    uu___8 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    p))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                                    uu___8 ->
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
                                                                    (let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    erase_ghost_subterms
                                                                    g body in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (77)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    {
                                                                    Pulse_Syntax_Base.name1
                                                                    = name1;
                                                                    Pulse_Syntax_Base.body6
                                                                    = uu___11;
                                                                    Pulse_Syntax_Base.returns_inv
                                                                    =
                                                                    returns_inv
                                                                    })) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (80)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Syntax_Base.Tm_WithInv
                                                                    uu___10)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (80)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    ret
                                                                    uu___9))))))
                                                                    uu___6)))
                                                         uu___5))) uu___4)))
                                   uu___3))) uu___2))) uu___1)
and (erase_ghost_subterms_branch :
  env ->
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
                 (Prims.of_int (526)) (Prims.of_int (18))
                 (Prims.of_int (526)) (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (525)) (Prims.of_int (67))
                 (Prims.of_int (530)) (Prims.of_int (62)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | (pat, body) ->
                  let uu___2 = extend_env_pat g pat in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (527)) (Prims.of_int (17))
                                (Prims.of_int (527)) (Prims.of_int (37)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (526)) (Prims.of_int (22))
                                (Prims.of_int (530)) (Prims.of_int (62)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          (fun uu___3 ->
                             match uu___3 with
                             | (g1, uu___4, bs) ->
                                 let uu___5 =
                                   Obj.magic
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___6 ->
                                           Pulse_Checker_Match.open_st_term_bs
                                             body bs)) in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (528))
                                               (Prims.of_int (13))
                                               (Prims.of_int (528))
                                               (Prims.of_int (56)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (528))
                                               (Prims.of_int (59))
                                               (Prims.of_int (530))
                                               (Prims.of_int (62)))))
                                      (Obj.magic uu___5)
                                      (fun uu___6 ->
                                         (fun body1 ->
                                            let uu___6 =
                                              erase_ghost_subterms g1 body1 in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (529))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (529))
                                                          (Prims.of_int (40)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (530))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (530))
                                                          (Prims.of_int (62)))))
                                                 (Obj.magic uu___6)
                                                 (fun body2 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___7 ->
                                                         (pat,
                                                           (Pulse_Syntax_Naming.close_st_term_n
                                                              body2
                                                              (FStar_List_Tot_Base.map
                                                                 FStar_Pervasives_Native.fst
                                                                 bs)))))))
                                           uu___6))) uu___3))) uu___1)
let rec (extract :
  env ->
    Pulse_Syntax_Base.st_term ->
      ((Pulse_Extract_CompilerLib.mlexpr * Pulse_Extract_CompilerLib.e_tag),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                (Pulse_Extract_CompilerLib.mle_unit,
                  Pulse_Extract_CompilerLib.e_tag_erasable))) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (534)) (Prims.of_int (24))
                 (Prims.of_int (534)) (Prims.of_int (48)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (535)) (Prims.of_int (4)) (Prims.of_int (687))
                 (Prims.of_int (7))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun erased_result ->
              let uu___1 =
                debug g
                  (fun uu___2 ->
                     let uu___3 = Pulse_Syntax_Printer.st_term_to_string p in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (537)) (Prims.of_int (14))
                                (Prims.of_int (537)) (Prims.of_int (35)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (535)) (Prims.of_int (22))
                                (Prims.of_int (537)) (Prims.of_int (35)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          (fun uu___4 ->
                             let uu___5 =
                               let uu___6 =
                                 FStar_Tactics_V2_Builtins.range_to_string
                                   p.Pulse_Syntax_Base.range1 in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Extract.Main.fst"
                                          (Prims.of_int (536))
                                          (Prims.of_int (14))
                                          (Prims.of_int (536))
                                          (Prims.of_int (41)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Printf.fst"
                                          (Prims.of_int (122))
                                          (Prims.of_int (8))
                                          (Prims.of_int (124))
                                          (Prims.of_int (44)))))
                                 (Obj.magic uu___6)
                                 (fun uu___7 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___8 ->
                                         fun x ->
                                           Prims.strcat
                                             (Prims.strcat "Extracting term@"
                                                (Prims.strcat uu___7 ":\n"))
                                             (Prims.strcat x "\n"))) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (535))
                                           (Prims.of_int (22))
                                           (Prims.of_int (537))
                                           (Prims.of_int (35)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (535))
                                           (Prims.of_int (22))
                                           (Prims.of_int (537))
                                           (Prims.of_int (35)))))
                                  (Obj.magic uu___5)
                                  (fun uu___6 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___7 -> uu___6 uu___4))))
                            uu___4)) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (535)) (Prims.of_int (4))
                            (Prims.of_int (537)) (Prims.of_int (36)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (538)) (Prims.of_int (4))
                            (Prims.of_int (687)) (Prims.of_int (7)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun uu___2 ->
                         let uu___3 = is_erasable p in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (538))
                                       (Prims.of_int (7))
                                       (Prims.of_int (538))
                                       (Prims.of_int (20)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (538))
                                       (Prims.of_int (4))
                                       (Prims.of_int (687))
                                       (Prims.of_int (7)))))
                              (Obj.magic uu___3)
                              (fun uu___4 ->
                                 (fun uu___4 ->
                                    if uu___4
                                    then
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___5 -> erased_result)))
                                    else
                                      Obj.magic
                                        (Obj.repr
                                           (match p.Pulse_Syntax_Base.term1
                                            with
                                            | Pulse_Syntax_Base.Tm_IntroPure
                                                uu___6 ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___7 ->
                                                        erased_result))
                                            | Pulse_Syntax_Base.Tm_ElimExists
                                                uu___6 ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___7 ->
                                                        erased_result))
                                            | Pulse_Syntax_Base.Tm_IntroExists
                                                uu___6 ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___7 ->
                                                        erased_result))
                                            | Pulse_Syntax_Base.Tm_Rewrite
                                                uu___6 ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___7 ->
                                                        erased_result))
                                            | Pulse_Syntax_Base.Tm_Abs
                                                { Pulse_Syntax_Base.b = b;
                                                  Pulse_Syntax_Base.q = q;
                                                  Pulse_Syntax_Base.ascription
                                                    = uu___6;
                                                  Pulse_Syntax_Base.body =
                                                    body;_}
                                                ->
                                                Obj.repr
                                                  (let uu___7 =
                                                     extend_env g b in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (549))
                                                              (Prims.of_int (37))
                                                              (Prims.of_int (549))
                                                              (Prims.of_int (51)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (548))
                                                              (Prims.of_int (32))
                                                              (Prims.of_int (557))
                                                              (Prims.of_int (23)))))
                                                     (Obj.magic uu___7)
                                                     (fun uu___8 ->
                                                        (fun uu___8 ->
                                                           match uu___8 with
                                                           | (g1, mlident,
                                                              mlty, name1) ->
                                                               let uu___9 =
                                                                 let uu___10
                                                                   =
                                                                   FStar_Tactics_Unseal.unseal
                                                                    b.Pulse_Syntax_Base.binder_attrs in
                                                                 FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (551))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (552))
                                                                    (Prims.of_int (21)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (551))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (553))
                                                                    (Prims.of_int (37)))))
                                                                   (Obj.magic
                                                                    uu___10)
                                                                   (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (term_as_mlexpr
                                                                    g1)
                                                                    uu___11))
                                                                    uu___11) in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (551))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (553))
                                                                    (Prims.of_int (37)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (553))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (557))
                                                                    (Prims.of_int (23)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___9)
                                                                    (
                                                                    fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    mlattrs
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body
                                                                    name1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (554))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (554))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (554))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (557))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    body1 ->
                                                                    let uu___11
                                                                    =
                                                                    extract
                                                                    g1 body1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (555))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (555))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (554))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (557))
                                                                    (Prims.of_int (23)))))
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
                                                                    (body2,
                                                                    uu___14)
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_fun
                                                                    [
                                                                    (mlident,
                                                                    mlty,
                                                                    mlattrs)]
                                                                    body2),
                                                                    Pulse_Extract_CompilerLib.e_tag_pure)))))
                                                                    uu___11)))
                                                                    uu___10)))
                                                          uu___8))
                                            | Pulse_Syntax_Base.Tm_Return
                                                {
                                                  Pulse_Syntax_Base.expected_type
                                                    = uu___6;
                                                  Pulse_Syntax_Base.insert_eq
                                                    = uu___7;
                                                  Pulse_Syntax_Base.term =
                                                    term;_}
                                                ->
                                                Obj.repr
                                                  (let uu___8 =
                                                     term_as_mlexpr g term in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (560))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (560))
                                                              (Prims.of_int (29)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (560))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (561))
                                                              (Prims.of_int (18)))))
                                                     (Obj.magic uu___8)
                                                     (fun uu___9 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___10 ->
                                                             (uu___9,
                                                               Pulse_Extract_CompilerLib.e_tag_pure))))
                                            | Pulse_Syntax_Base.Tm_STApp
                                                {
                                                  Pulse_Syntax_Base.head =
                                                    head;
                                                  Pulse_Syntax_Base.arg_qual
                                                    = uu___6;
                                                  Pulse_Syntax_Base.arg = arg;_}
                                                ->
                                                Obj.repr
                                                  (let uu___7 =
                                                     maybe_inline g head arg in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (564))
                                                              (Prims.of_int (14))
                                                              (Prims.of_int (564))
                                                              (Prims.of_int (37)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (563))
                                                              (Prims.of_int (34))
                                                              (Prims.of_int (572))
                                                              (Prims.of_int (7)))))
                                                     (Obj.magic uu___7)
                                                     (fun uu___8 ->
                                                        (fun uu___8 ->
                                                           match uu___8 with
                                                           | FStar_Pervasives_Native.None
                                                               ->
                                                               let uu___9 =
                                                                 term_as_mlexpr
                                                                   g head in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (566))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (566))
                                                                    (Prims.of_int (42)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (566))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (568))
                                                                    (Prims.of_int (42)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___9)
                                                                    (
                                                                    fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    head1 ->
                                                                    let uu___10
                                                                    =
                                                                    term_as_mlexpr
                                                                    g arg in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (567))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (567))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (568))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (568))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun arg1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_app
                                                                    head1
                                                                    [arg1]),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                                    uu___10))
                                                           | FStar_Pervasives_Native.Some
                                                               t ->
                                                               let uu___9 =
                                                                 debug g
                                                                   (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Pulse_Syntax_Printer.st_term_to_string
                                                                    t in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (570))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (570))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
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
                                                                    Prims.strcat
                                                                    "Inlined to: "
                                                                    (Prims.strcat
                                                                    uu___12
                                                                    "\n")))) in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (570))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (570))
                                                                    (Prims.of_int (84)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (21)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___9)
                                                                    (
                                                                    fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (extract
                                                                    g t))
                                                                    uu___10)))
                                                          uu___8))
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
                                                  (let uu___6 =
                                                     is_erasable head in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (575))
                                                              (Prims.of_int (17))
                                                              (Prims.of_int (575))
                                                              (Prims.of_int (33)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (575))
                                                              (Prims.of_int (36))
                                                              (Prims.of_int (600))
                                                              (Prims.of_int (9)))))
                                                     (Obj.magic uu___6)
                                                     (fun uu___7 ->
                                                        (fun eh ->
                                                           let uu___7 =
                                                             erase_type_for_extraction
                                                               g
                                                               binder.Pulse_Syntax_Base.binder_ty in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (61)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (9)))))
                                                                (Obj.magic
                                                                   uu___7)
                                                                (fun uu___8
                                                                   ->
                                                                   (fun et ->
                                                                    if
                                                                    eh ||
                                                                    ((Pulse_Syntax_Base.uu___is_Tm_Abs
                                                                    head.Pulse_Syntax_Base.term1)
                                                                    && et)
                                                                    then
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Pulse_Syntax_Naming.subst_st_term
                                                                    body
                                                                    [
                                                                    FStar_Reflection_Typing.DT
                                                                    (Prims.int_zero,
                                                                    unit_val)])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (587))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (587))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (591))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    body1 ->
                                                                    let uu___9
                                                                    =
                                                                    debug g
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Pulse_Show.show
                                                                    Pulse_Show.tac_showable_st_term
                                                                    body1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (41)))))
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
                                                                    Pulse_Show.show
                                                                    Pulse_Show.tac_showable_st_term
                                                                    head in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (589))
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
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Erasing head of bind "
                                                                    (Prims.strcat
                                                                    uu___15
                                                                    "\nopened body to "))
                                                                    (Prims.strcat
                                                                    x ""))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (41)))))
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
                                                                    uu___12)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (591))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (591))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (extract
                                                                    g body1))
                                                                    uu___10)))
                                                                    uu___9))
                                                                    else
                                                                    (let uu___9
                                                                    =
                                                                    extract g
                                                                    head in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (592))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    (head1,
                                                                    uu___11)
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    extend_env
                                                                    g binder in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (594))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (594))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    (g1,
                                                                    mlident,
                                                                    mlty,
                                                                    name1) ->
                                                                    let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body
                                                                    name1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    body1 ->
                                                                    let uu___15
                                                                    =
                                                                    extract
                                                                    g1 body1 in
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
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    match uu___16
                                                                    with
                                                                    | 
                                                                    (body2,
                                                                    uu___18)
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
                                                                    uu___15)))
                                                                    uu___13)))
                                                                    uu___10))))
                                                                    uu___8)))
                                                          uu___7))
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
                                                  (let uu___6 =
                                                     term_as_mlexpr g head in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (604))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (604))
                                                              (Prims.of_int (40)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (604))
                                                              (Prims.of_int (43))
                                                              (Prims.of_int (610))
                                                              (Prims.of_int (47)))))
                                                     (Obj.magic uu___6)
                                                     (fun uu___7 ->
                                                        (fun head1 ->
                                                           let uu___7 =
                                                             extend_env g
                                                               binder in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (605))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (605))
                                                                    (Prims.of_int (56)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (604))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (610))
                                                                    (Prims.of_int (47)))))
                                                                (Obj.magic
                                                                   uu___7)
                                                                (fun uu___8
                                                                   ->
                                                                   (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (g1,
                                                                    mlident,
                                                                    mlty,
                                                                    name1) ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body
                                                                    name1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (610))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    body1 ->
                                                                    let uu___10
                                                                    =
                                                                    extract
                                                                    g1 body1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (607))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (607))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (610))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (body2,
                                                                    uu___13)
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
                                                                    uu___10)))
                                                                    uu___8)))
                                                          uu___7))
                                            | Pulse_Syntax_Base.Tm_If
                                                { Pulse_Syntax_Base.b1 = b;
                                                  Pulse_Syntax_Base.then_ =
                                                    then_;
                                                  Pulse_Syntax_Base.else_ =
                                                    else_;
                                                  Pulse_Syntax_Base.post1 =
                                                    uu___6;_}
                                                ->
                                                Obj.repr
                                                  (let uu___7 =
                                                     term_as_mlexpr g b in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (613))
                                                              (Prims.of_int (16))
                                                              (Prims.of_int (613))
                                                              (Prims.of_int (34)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (613))
                                                              (Prims.of_int (37))
                                                              (Prims.of_int (616))
                                                              (Prims.of_int (49)))))
                                                     (Obj.magic uu___7)
                                                     (fun uu___8 ->
                                                        (fun b1 ->
                                                           let uu___8 =
                                                             extract g then_ in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (614))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (614))
                                                                    (Prims.of_int (38)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (49)))))
                                                                (Obj.magic
                                                                   uu___8)
                                                                (fun uu___9
                                                                   ->
                                                                   (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (then_1,
                                                                    uu___10)
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    extract g
                                                                    else_ in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (615))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (615))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (614))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (49)))))
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
                                                                    (else_1,
                                                                    uu___14)
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_if
                                                                    b1 then_1
                                                                    (FStar_Pervasives_Native.Some
                                                                    else_1)),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                                    uu___9)))
                                                          uu___8))
                                            | Pulse_Syntax_Base.Tm_Match
                                                { Pulse_Syntax_Base.sc = sc;
                                                  Pulse_Syntax_Base.returns_
                                                    = uu___6;
                                                  Pulse_Syntax_Base.brs = brs;_}
                                                ->
                                                Obj.repr
                                                  (let uu___7 =
                                                     term_as_mlexpr g sc in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (619))
                                                              (Prims.of_int (17))
                                                              (Prims.of_int (619))
                                                              (Prims.of_int (36)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (619))
                                                              (Prims.of_int (39))
                                                              (Prims.of_int (631))
                                                              (Prims.of_int (38)))))
                                                     (Obj.magic uu___7)
                                                     (fun uu___8 ->
                                                        (fun sc1 ->
                                                           let uu___8 =
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___9
                                                                    ->
                                                                    fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    (pat0,
                                                                    body) ->
                                                                    let uu___11
                                                                    =
                                                                    extend_env_pat
                                                                    g pat0 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (621))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (621))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    (g1, pat,
                                                                    bs) ->
                                                                    let uu___13
                                                                    =
                                                                    debug g1
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    Pulse_Syntax_Printer.pattern_to_string
                                                                    pat0 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (624))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (624))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Prims.strcat
                                                                    "Extracting branch with pattern "
                                                                    (Prims.strcat
                                                                    uu___16
                                                                    "\n")))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Pulse_Checker_Match.open_st_term_bs
                                                                    body bs)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (626))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (626))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (626))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    body1 ->
                                                                    let uu___16
                                                                    =
                                                                    extract
                                                                    g1 body1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (626))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    match uu___17
                                                                    with
                                                                    | 
                                                                    (body2,
                                                                    uu___19)
                                                                    ->
                                                                    (pat,
                                                                    body2)))))
                                                                    uu___16)))
                                                                    uu___14)))
                                                                    uu___12))) in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (19)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (631))
                                                                    (Prims.of_int (38)))))
                                                                (Obj.magic
                                                                   uu___8)
                                                                (fun uu___9
                                                                   ->
                                                                   (fun
                                                                    extract_branch
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    FStar_Tactics_Util.map
                                                                    extract_branch
                                                                    brs in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (631))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (631))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun brs1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    ((Pulse_Extract_CompilerLib.mle_match
                                                                    sc1 brs1),
                                                                    Pulse_Extract_CompilerLib.e_tag_impure)))))
                                                                    uu___9)))
                                                          uu___8))
                                            | Pulse_Syntax_Base.Tm_While
                                                {
                                                  Pulse_Syntax_Base.invariant
                                                    = uu___6;
                                                  Pulse_Syntax_Base.condition
                                                    = condition;
                                                  Pulse_Syntax_Base.condition_var
                                                    = uu___7;
                                                  Pulse_Syntax_Base.body3 =
                                                    body;_}
                                                ->
                                                Obj.repr
                                                  (let uu___8 =
                                                     extract g condition in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (635))
                                                              (Prims.of_int (27))
                                                              (Prims.of_int (635))
                                                              (Prims.of_int (46)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (634))
                                                              (Prims.of_int (39))
                                                              (Prims.of_int (640))
                                                              (Prims.of_int (23)))))
                                                     (Obj.magic uu___8)
                                                     (fun uu___9 ->
                                                        (fun uu___9 ->
                                                           match uu___9 with
                                                           | (condition1,
                                                              uu___10) ->
                                                               let uu___11 =
                                                                 extract g
                                                                   body in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (636))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (636))
                                                                    (Prims.of_int (36)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (23)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___11)
                                                                    (
                                                                    fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    (body1,
                                                                    uu___14)
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
                                                          uu___9))
                                            | Pulse_Syntax_Base.Tm_Par
                                                {
                                                  Pulse_Syntax_Base.pre1 =
                                                    uu___6;
                                                  Pulse_Syntax_Base.body11 =
                                                    body1;
                                                  Pulse_Syntax_Base.post11 =
                                                    uu___7;
                                                  Pulse_Syntax_Base.pre2 =
                                                    uu___8;
                                                  Pulse_Syntax_Base.body21 =
                                                    body2;
                                                  Pulse_Syntax_Base.post2 =
                                                    uu___9;_}
                                                ->
                                                Obj.repr
                                                  (let uu___10 =
                                                     extract g body1 in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (643))
                                                              (Prims.of_int (23))
                                                              (Prims.of_int (643))
                                                              (Prims.of_int (38)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (642))
                                                              (Prims.of_int (34))
                                                              (Prims.of_int (648))
                                                              (Prims.of_int (23)))))
                                                     (Obj.magic uu___10)
                                                     (fun uu___11 ->
                                                        (fun uu___11 ->
                                                           match uu___11 with
                                                           | (body11,
                                                              uu___12) ->
                                                               let uu___13 =
                                                                 extract g
                                                                   body2 in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (38)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (643))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (648))
                                                                    (Prims.of_int (23)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___13)
                                                                    (
                                                                    fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    match uu___14
                                                                    with
                                                                    | 
                                                                    (body21,
                                                                    uu___16)
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
                                                          uu___11))
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
                                                  (let uu___6 =
                                                     term_as_mlexpr g
                                                       initializer1 in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (651))
                                                              (Prims.of_int (26))
                                                              (Prims.of_int (651))
                                                              (Prims.of_int (54)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (651))
                                                              (Prims.of_int (57))
                                                              (Prims.of_int (658))
                                                              (Prims.of_int (47)))))
                                                     (Obj.magic uu___6)
                                                     (fun uu___7 ->
                                                        (fun initializer2 ->
                                                           let uu___7 =
                                                             extend_env g
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
                                                               } in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (94)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (651))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (658))
                                                                    (Prims.of_int (47)))))
                                                                (Obj.magic
                                                                   uu___7)
                                                                (fun uu___8
                                                                   ->
                                                                   (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (g1,
                                                                    mlident,
                                                                    mlty,
                                                                    name1) ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body
                                                                    name1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (653))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (653))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (653))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (658))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    body1 ->
                                                                    let uu___10
                                                                    =
                                                                    extract
                                                                    g1 body1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (654))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (654))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (653))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (658))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (body2,
                                                                    uu___13)
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
                                                                    uu___10)))
                                                                    uu___8)))
                                                          uu___7))
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
                                                  (let uu___6 =
                                                     term_as_mlexpr g
                                                       initializer1 in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (661))
                                                              (Prims.of_int (26))
                                                              (Prims.of_int (661))
                                                              (Prims.of_int (54)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (661))
                                                              (Prims.of_int (57))
                                                              (Prims.of_int (674))
                                                              (Prims.of_int (47)))))
                                                     (Obj.magic uu___6)
                                                     (fun uu___7 ->
                                                        (fun initializer2 ->
                                                           let uu___7 =
                                                             term_as_mlexpr g
                                                               length in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (44)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (674))
                                                                    (Prims.of_int (47)))))
                                                                (Obj.magic
                                                                   uu___7)
                                                                (fun uu___8
                                                                   ->
                                                                   (fun
                                                                    length1
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    extend_env
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
                                                                    } in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (674))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (g1,
                                                                    mlident,
                                                                    mlty,
                                                                    name1) ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body
                                                                    name1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (674))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    body1 ->
                                                                    let uu___11
                                                                    =
                                                                    extract
                                                                    g1 body1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (674))
                                                                    (Prims.of_int (47)))))
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
                                                                    (body2,
                                                                    uu___14)
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
                                                                    uu___11)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                          uu___7))
                                            | Pulse_Syntax_Base.Tm_WithInv
                                                {
                                                  Pulse_Syntax_Base.name1 =
                                                    uu___6;
                                                  Pulse_Syntax_Base.body6 =
                                                    body;
                                                  Pulse_Syntax_Base.returns_inv
                                                    = uu___7;_}
                                                -> Obj.repr (extract g body)
                                            | Pulse_Syntax_Base.Tm_Unreachable
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___6 ->
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
                                                    = uu___6;
                                                  Pulse_Syntax_Base.binders =
                                                    uu___7;
                                                  Pulse_Syntax_Base.t = t;_}
                                                ->
                                                Obj.repr
                                                  (FStar_Tactics_V2_Derived.fail
                                                     "Unexpected constructor: ProofHintWithBinders should have been desugared away")
                                            | Pulse_Syntax_Base.Tm_Admit
                                                uu___6 ->
                                                Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___7 ->
                                                        ((Pulse_Extract_CompilerLib.mle_app
                                                            (Pulse_Extract_CompilerLib.mle_name
                                                               ([],
                                                                 "failwith"))
                                                            [Pulse_Extract_CompilerLib.mle_unit]),
                                                          Pulse_Extract_CompilerLib.e_tag_impure))))))
                                   uu___4))) uu___2))) uu___1)
let rec map_dv : 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun f ->
    fun l ->
      match l with
      | [] -> []
      | hd::tl ->
          let uu___ = f hd in let uu___1 = map_dv f tl in uu___ :: uu___1
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
        let uu___ =
          debug g
            (fun uu___1 ->
               let uu___2 = FStar_Tactics_V2_Builtins.term_to_string t in
               FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                          (Prims.of_int (700)) (Prims.of_int (63))
                          (Prims.of_int (700)) (Prims.of_int (83)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                          (Prims.of_int (19)) (Prims.of_int (611))
                          (Prims.of_int (31))))) (Obj.magic uu___2)
                 (fun uu___3 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___4 ->
                         Prims.strcat "Generalizing arrow:\n"
                           (Prims.strcat uu___3 "\n")))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (700)) (Prims.of_int (2))
                   (Prims.of_int (700)) (Prims.of_int (84)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (700)) (Prims.of_int (85))
                   (Prims.of_int (740)) (Prims.of_int (20)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 =
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___3 ->
                          FStar_Reflection_V2_Builtins.inspect_ln t)) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (701)) (Prims.of_int (11))
                              (Prims.of_int (701)) (Prims.of_int (25)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (702)) (Prims.of_int (2))
                              (Prims.of_int (740)) (Prims.of_int (20)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun tv ->
                           match tv with
                           | FStar_Reflection_V2_Data.Tv_Arrow (b, c) ->
                               Obj.magic
                                 (Obj.repr
                                    (let uu___3 =
                                       Obj.magic
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___4 ->
                                               FStar_Reflection_V2_Builtins.inspect_binder
                                                 b)) in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (704))
                                                (Prims.of_int (25))
                                                (Prims.of_int (704))
                                                (Prims.of_int (43)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Extract.Main.fst"
                                                (Prims.of_int (703))
                                                (Prims.of_int (21))
                                                (Prims.of_int (738))
                                                (Prims.of_int (20)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun uu___4 ->
                                             match uu___4 with
                                             | {
                                                 FStar_Reflection_V2_Data.sort2
                                                   = sort;
                                                 FStar_Reflection_V2_Data.qual
                                                   = uu___5;
                                                 FStar_Reflection_V2_Data.attrs
                                                   = uu___6;
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
                                                        (let uu___8 =
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___9
                                                                   ->
                                                                   Pulse_Extract_CompilerLib.is_type
                                                                    g.uenv_inner
                                                                    sort)) in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (37)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (738))
                                                                    (Prims.of_int (20)))))
                                                           (Obj.magic uu___8)
                                                           (fun uu___9 ->
                                                              (fun uu___9 ->
                                                                 if uu___9
                                                                 then
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Reflection_V2_Builtins.inspect_comp
                                                                    c)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (708))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (708))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (737))
                                                                    (Prims.of_int (73)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    cview ->
                                                                    match cview
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V2_Data.C_Total
                                                                    t1 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g.coreenv)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (711))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (711))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (711))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (736))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun x ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
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
                                                                    })))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (712))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (712))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (712))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (736))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun xt
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Reflection_V2_Builtins.subst_term
                                                                    [
                                                                    FStar_Syntax_Syntax.DT
                                                                    (Prims.int_zero,
                                                                    xt)] t1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (713))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (713))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (713))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (736))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun t2
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
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
                                                                    = uu___16;
                                                                    Pulse_Syntax_Base.ascription
                                                                    = uu___17;
                                                                    Pulse_Syntax_Base.body
                                                                    = body;_};
                                                                    Pulse_Syntax_Base.range1
                                                                    = uu___18;
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    = uu___19;_}
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
                                                                    uu___16
                                                                    ->
                                                                    (e,
                                                                    (Pulse_Syntax_Base.binder_attrs_default
                                                                    ())))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (715))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (719))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (713))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (736))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    match uu___15
                                                                    with
                                                                    | 
                                                                    (e1,
                                                                    attrs) ->
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStar_Tactics_Unseal.unseal
                                                                    attrs in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (term_as_mlexpr
                                                                    g)
                                                                    uu___18))
                                                                    uu___18) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (736))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    mlattrs
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
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
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (725))
                                                                    (Prims.of_int (12)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (725))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (736))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    namedv ->
                                                                    let uu___18
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    Pulse_Extract_CompilerLib.extend_ty
                                                                    g.uenv_inner
                                                                    namedv)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (736))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun uenv
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g.coreenv
                                                                    x
                                                                    (Pulse_Syntax_Base.mk_ppname
                                                                    ppname
                                                                    FStar_Range.range_0)
                                                                    (Pulse_Syntax_Pure.wr
                                                                    sort
                                                                    FStar_Range.range_0))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (728))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (736))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    coreenv
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    {
                                                                    uenv_inner
                                                                    = uenv;
                                                                    coreenv
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (736))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun g1
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    generalize
                                                                    g1 t2 e1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (734))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (734))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (736))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    match uu___22
                                                                    with
                                                                    | 
                                                                    (g2, tys,
                                                                    t3, e2)
                                                                    ->
                                                                    let ty_param
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    Pulse_Extract_CompilerLib.lookup_ty
                                                                    g2.uenv_inner
                                                                    namedv in
                                                                    Pulse_Extract_CompilerLib.mk_ty_param
                                                                    uu___24
                                                                    mlattrs in
                                                                    (g2,
                                                                    (ty_param
                                                                    :: tys),
                                                                    t3, e2)))))
                                                                    uu___21)))
                                                                    uu___20)))
                                                                    uu___19)))
                                                                    uu___18)))
                                                                    uu___17)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                    | 
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.raise
                                                                    (Extraction_failure
                                                                    "Unexpected effectful arrow"))))
                                                                    uu___11)))
                                                                 else
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (g, [],
                                                                    t, e)))))
                                                                uu___9))))
                                            uu___4)))
                           | uu___3 ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___4 -> (g, [], t, e)))))
                          uu___3))) uu___1)
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
        let uu___ = Pulse_RuntimeUtils.get_attributes selt in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (751)) (Prims.of_int (16))
                   (Prims.of_int (751)) (Prims.of_int (38)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (751)) (Prims.of_int (41))
                   (Prims.of_int (773)) (Prims.of_int (39)))))
          (Obj.magic uu___)
          (fun attrs ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  find_map
                    (fun t ->
                       match FStar_Reflection_V2_Builtins.inspect_ln t with
                       | FStar_Reflection_V2_Data.Tv_App (uu___2, uu___3) ->
                           (match FStar_Reflection_V2_Collect.collect_app_ln
                                    t
                            with
                            | (hd, args) ->
                                if
                                  FStar_Reflection_V2_Derived.is_fvar hd
                                    "FStar.Pervasives.Native.Mktuple2"
                                then
                                  (match args with
                                   | uu___4::uu___5::(tag, uu___6)::(value,
                                                                    uu___7)::[]
                                       ->
                                       (match ((match FStar_Reflection_V2_Builtins.inspect_ln
                                                        tag
                                                with
                                                | FStar_Reflection_V2_Data.Tv_Const
                                                    (FStar_Reflection_V2_Data.C_String
                                                    s) ->
                                                    FStar_Pervasives_Native.Some
                                                      s
                                                | uu___8 ->
                                                    FStar_Pervasives_Native.None),
                                                (match FStar_Reflection_V2_Builtins.inspect_ln
                                                         value
                                                 with
                                                 | FStar_Reflection_V2_Data.Tv_Const
                                                     (FStar_Reflection_V2_Data.C_String
                                                     s) ->
                                                     FStar_Pervasives_Native.Some
                                                       s
                                                 | uu___8 ->
                                                     FStar_Pervasives_Native.None))
                                        with
                                        | (FStar_Pervasives_Native.Some
                                           "pulse.recursive.knot",
                                           FStar_Pervasives_Native.Some v) ->
                                            FStar_Pervasives_Native.Some v
                                        | uu___8 ->
                                            FStar_Pervasives_Native.None)
                                   | uu___4 -> FStar_Pervasives_Native.None)
                                else FStar_Pervasives_Native.None)
                       | uu___2 -> FStar_Pervasives_Native.None) attrs))
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
                             let uu___2 = extend_env g b in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (781))
                                        (Prims.of_int (37))
                                        (Prims.of_int (781))
                                        (Prims.of_int (51)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (780))
                                        (Prims.of_int (19))
                                        (Prims.of_int (789))
                                        (Prims.of_int (23)))))
                               (Obj.magic uu___2)
                               (fun uu___3 ->
                                  (fun uu___3 ->
                                     match uu___3 with
                                     | (g1, mlident, mlty, name1) ->
                                         let uu___4 =
                                           Obj.magic
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___5 ->
                                                   Pulse_Syntax_Naming.open_st_term_nv
                                                     body name1)) in
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Extract.Main.fst"
                                                       (Prims.of_int (782))
                                                       (Prims.of_int (19))
                                                       (Prims.of_int (782))
                                                       (Prims.of_int (47)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Extract.Main.fst"
                                                       (Prims.of_int (782))
                                                       (Prims.of_int (50))
                                                       (Prims.of_int (789))
                                                       (Prims.of_int (23)))))
                                              (Obj.magic uu___4)
                                              (fun uu___5 ->
                                                 (fun body1 ->
                                                    let uu___5 =
                                                      extract_recursive g1
                                                        body1 rec_name in
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (783))
                                                                  (Prims.of_int (22))
                                                                  (Prims.of_int (783))
                                                                  (Prims.of_int (55)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (782))
                                                                  (Prims.of_int (50))
                                                                  (Prims.of_int (789))
                                                                  (Prims.of_int (23)))))
                                                         (Obj.magic uu___5)
                                                         (fun uu___6 ->
                                                            (fun uu___6 ->
                                                               match uu___6
                                                               with
                                                               | (body2,
                                                                  uu___7) ->
                                                                   let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    FStar_Tactics_Unseal.unseal
                                                                    b.Pulse_Syntax_Base.binder_attrs in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (785))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (786))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (785))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (787))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (term_as_mlexpr
                                                                    g1)
                                                                    uu___10))
                                                                    uu___10) in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (785))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (787))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (789))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (789))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    attrs ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ((Pulse_Extract_CompilerLib.mle_fun
                                                                    [
                                                                    (mlident,
                                                                    mlty,
                                                                    attrs)]
                                                                    body2),
                                                                    Pulse_Extract_CompilerLib.e_tag_pure)))))
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
                                                 (FStar_Reflection_V2_Builtins.pack_ln
                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                       rec_name))
                                                 FStar_Range.range_0))])) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (791))
                                        (Prims.of_int (19))
                                        (Prims.of_int (791))
                                        (Prims.of_int (100)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (791))
                                        (Prims.of_int (103))
                                        (Prims.of_int (793))
                                        (Prims.of_int (17)))))
                               (Obj.magic uu___2)
                               (fun uu___3 ->
                                  (fun body1 ->
                                     let uu___3 = extract g body1 in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (792))
                                                   (Prims.of_int (24))
                                                   (Prims.of_int (792))
                                                   (Prims.of_int (38)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (791))
                                                   (Prims.of_int (103))
                                                   (Prims.of_int (793))
                                                   (Prims.of_int (17)))))
                                          (Obj.magic uu___3)
                                          (fun uu___4 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___5 ->
                                                  match uu___4 with
                                                  | (body2, tag) ->
                                                      (body2, tag))))) uu___3)))
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
          let uu___ = generalize g knot_typ (FStar_Pervasives_Native.Some p) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                     (Prims.of_int (800)) (Prims.of_int (33))
                     (Prims.of_int (800)) (Prims.of_int (63)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                     (Prims.of_int (799)) (Prims.of_int (63))
                     (Prims.of_int (813)) (Prims.of_int (29)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  match uu___1 with
                  | (g1, tys, lb_typ, FStar_Pervasives_Native.Some p1) ->
                      let uu___2 =
                        Obj.magic
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 ->
                                Pulse_Extract_CompilerLib.term_as_mlty
                                  g1.uenv_inner lb_typ)) in
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Extract.Main.fst"
                                    (Prims.of_int (801)) (Prims.of_int (15))
                                    (Prims.of_int (801)) (Prims.of_int (51)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Extract.Main.fst"
                                    (Prims.of_int (801)) (Prims.of_int (54))
                                    (Prims.of_int (813)) (Prims.of_int (29)))))
                           (Obj.magic uu___2)
                           (fun uu___3 ->
                              (fun mlty ->
                                 let uu___3 =
                                   Obj.magic
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___4 ->
                                           Pulse_Extract_CompilerLib.extend_fv
                                             g1.uenv_inner knot_name
                                             (tys, mlty))) in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (802))
                                               (Prims.of_int (34))
                                               (Prims.of_int (802))
                                               (Prims.of_int (78)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (801))
                                               (Prims.of_int (54))
                                               (Prims.of_int (813))
                                               (Prims.of_int (29)))))
                                      (Obj.magic uu___3)
                                      (fun uu___4 ->
                                         (fun uu___4 ->
                                            match uu___4 with
                                            | (uenv, _mli, _ml_binding) ->
                                                let uu___5 =
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___6 ->
                                                          {
                                                            uenv_inner = uenv;
                                                            coreenv =
                                                              (g1.coreenv)
                                                          })) in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (803))
                                                              (Prims.of_int (14))
                                                              (Prims.of_int (803))
                                                              (Prims.of_int (38)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (803))
                                                              (Prims.of_int (43))
                                                              (Prims.of_int (813))
                                                              (Prims.of_int (29)))))
                                                     (Obj.magic uu___5)
                                                     (fun uu___6 ->
                                                        (fun g2 ->
                                                           let uu___6 =
                                                             extract_recursive
                                                               g2 p1
                                                               knot_name in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (804))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (804))
                                                                    (Prims.of_int (49)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (803))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (813))
                                                                    (Prims.of_int (29)))))
                                                                (Obj.magic
                                                                   uu___6)
                                                                (fun uu___7
                                                                   ->
                                                                   (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (tm, tag)
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Reflection_V2_Builtins.inspect_fv
                                                                    knot_name)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (806))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (806))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (807))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (809))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun lids
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    if
                                                                    Prims.uu___is_Nil
                                                                    lids
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.raise
                                                                    (Extraction_failure
                                                                    "Unexpected empty name"))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (807))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (808))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (809))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (809))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_List_Tot_Base.last
                                                                    lids))))
                                                                    uu___10) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (805))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (809))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (811))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (813))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    fv_name
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    debug_ g2
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Pulse_Extract_CompilerLib.mlexpr_to_string
                                                                    tm in
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Extracted term ("
                                                                    (Prims.strcat
                                                                    fv_name
                                                                    "): "))
                                                                    (Prims.strcat
                                                                    uu___12
                                                                    "\n"))))
                                                                    uu___10) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (811))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (811))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (813))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (813))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Pervasives.Inl
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mlm_let
                                                                    true
                                                                    [
                                                                    Pulse_Extract_CompilerLib.mk_mllb
                                                                    fv_name
                                                                    (tys,
                                                                    mlty) tm]]))))
                                                                    uu___9)))
                                                                    uu___7)))
                                                          uu___6))) uu___4)))
                                uu___3))) uu___1)
let (extract_attrs :
  Pulse_Extract_CompilerLib.uenv ->
    FStar_Reflection_Types.sigelt ->
      (Pulse_Extract_CompilerLib.mlexpr Prims.list, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun se ->
      let uu___ = Pulse_RuntimeUtils.get_attributes se in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (816)) (Prims.of_int (2)) (Prims.of_int (816))
                 (Prims.of_int (25)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (816)) (Prims.of_int (2)) (Prims.of_int (817))
                 (Prims.of_int (76))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              Obj.magic
                (FStar_Tactics_Util.map
                   (fun uu___2 ->
                      (fun t ->
                         Obj.magic
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 ->
                                 let uu___3 =
                                   Pulse_Extract_CompilerLib.term_as_mlexpr g
                                     t in
                                 match uu___3 with
                                 | (mlattr, uu___4, uu___5) -> mlattr)))
                        uu___2) uu___1)) uu___1)
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
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  {
                    uenv_inner = uenv;
                    coreenv =
                      (Pulse_Extract_CompilerLib.initial_core_env uenv)
                  })) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (822)) (Prims.of_int (12))
                   (Prims.of_int (822)) (Prims.of_int (58)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (824)) (Prims.of_int (2))
                   (Prims.of_int (858)) (Prims.of_int (75)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun g ->
                let uu___1 =
                  debug g
                    (fun uu___2 ->
                       let uu___3 = Pulse_Syntax_Printer.st_term_to_string p in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                  (Prims.of_int (824)) (Prims.of_int (61))
                                  (Prims.of_int (824)) (Prims.of_int (82)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Prims.fst"
                                  (Prims.of_int (611)) (Prims.of_int (19))
                                  (Prims.of_int (611)) (Prims.of_int (31)))))
                         (Obj.magic uu___3)
                         (fun uu___4 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___5 ->
                                 Prims.strcat "About to extract:\n"
                                   (Prims.strcat uu___4 "\n")))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (824)) (Prims.of_int (2))
                              (Prims.of_int (824)) (Prims.of_int (83)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (826)) (Prims.of_int (2))
                              (Prims.of_int (858)) (Prims.of_int (75)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           Obj.magic
                             (FStar_Tactics_V2_Derived.try_with
                                (fun uu___3 ->
                                   match () with
                                   | () ->
                                       let uu___4 =
                                         Obj.magic
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___5 ->
                                                 FStar_Reflection_V2_Builtins.inspect_sigelt
                                                   selt)) in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (827))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (827))
                                                  (Prims.of_int (43)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (828))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (853))
                                                  (Prims.of_int (59)))))
                                         (Obj.magic uu___4)
                                         (fun uu___5 ->
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
                                                             (let uu___6 =
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Reflection_V2_Builtins.inspect_lb
                                                                    (FStar_List_Tot_Base.hd
                                                                    lbs))) in
                                                              FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (833))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (833))
                                                                    (Prims.of_int (60)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (832))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (851))
                                                                    (Prims.of_int (7)))))
                                                                (Obj.magic
                                                                   uu___6)
                                                                (fun uu___7
                                                                   ->
                                                                   (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStar_Reflection_V2_Data.lb_fv
                                                                    = lb_fv;
                                                                    FStar_Reflection_V2_Data.lb_us
                                                                    = uu___8;
                                                                    FStar_Reflection_V2_Data.lb_typ
                                                                    = lb_typ;
                                                                    FStar_Reflection_V2_Data.lb_def
                                                                    = uu___9;_}
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    is_recursive
                                                                    g lb_fv
                                                                    selt in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (834))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (834))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (834))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (53)))))
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
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (extract_recursive_knot
                                                                    g p lb_fv
                                                                    lb_typ)
                                                                    | 
                                                                    uu___12
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    generalize
                                                                    g lb_typ
                                                                    (FStar_Pervasives_Native.Some
                                                                    p) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (838))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (838))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (837))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    match uu___14
                                                                    with
                                                                    | 
                                                                    (g1, tys,
                                                                    lb_typ1,
                                                                    FStar_Pervasives_Native.Some
                                                                    p1) ->
                                                                    let uu___15
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Pulse_Extract_CompilerLib.term_as_mlty
                                                                    g1.uenv_inner
                                                                    lb_typ1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (839))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (839))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (839))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun mlty
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Reflection_V2_Builtins.inspect_fv
                                                                    lb_fv)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (840))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (840))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (841))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    fv_name
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    if
                                                                    Prims.uu___is_Nil
                                                                    fv_name
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.raise
                                                                    (Extraction_failure
                                                                    "Unexpected empty name"))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    -> ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (841))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (842))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (842))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (53)))))
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
                                                                    erase_ghost_subterms
                                                                    g1 p1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun p2
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    simplify_st_term
                                                                    g1 p2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (844))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (844))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (844))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun p3
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    extract
                                                                    g1 p3 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (845))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (845))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (844))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    match uu___22
                                                                    with
                                                                    | 
                                                                    (tm, tag)
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_List_Tot_Base.last
                                                                    fv_name)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (846))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (846))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (847))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun
                                                                    fv_name1
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    debug_ g1
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    Pulse_Extract_CompilerLib.mlexpr_to_string
                                                                    tm in
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Extracted term ("
                                                                    (Prims.strcat
                                                                    fv_name1
                                                                    "): "))
                                                                    (Prims.strcat
                                                                    uu___27
                                                                    "\n"))))
                                                                    uu___25) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (847))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (847))
                                                                    (Prims.of_int (102)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (847))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    uu___24)
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    extract_attrs
                                                                    uenv selt in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (848))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (848))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    attrs ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___27
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
                                                                    uu___25)))
                                                                    uu___24)))
                                                                    uu___22)))
                                                                    uu___21)))
                                                                    uu___20)))
                                                                    uu___18)))
                                                                    uu___17)))
                                                                    uu___16)))
                                                                    uu___14)))
                                                                    uu___11)))
                                                                    uu___7))))
                                               | uu___5 ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.raise
                                                           (Extraction_failure
                                                              "Unexpected sigelt"))))
                                              uu___5))
                                (fun uu___3 ->
                                   (fun uu___3 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 ->
                                              match uu___3 with
                                              | Extraction_failure msg ->
                                                  FStar_Pervasives.Inr msg
                                              | e ->
                                                  FStar_Pervasives.Inr
                                                    (Prims.strcat
                                                       "Unexpected extraction error: "
                                                       (Prims.strcat
                                                          (Pulse_RuntimeUtils.print_exn
                                                             e) "")))))
                                     uu___3))) uu___2))) uu___1)
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
                 let uu___1 =
                   Obj.magic
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           FStar_Reflection_V2_Builtins.inspect_sigelt selt)) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (865)) (Prims.of_int (22))
                            (Prims.of_int (865)) (Prims.of_int (43)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (866)) (Prims.of_int (4))
                            (Prims.of_int (879)) (Prims.of_int (59)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
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
                                       (let uu___3 =
                                          Obj.magic
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___4 ->
                                                  FStar_Reflection_V2_Builtins.inspect_lb
                                                    (FStar_List_Tot_Base.hd
                                                       lbs))) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (871))
                                                   (Prims.of_int (30))
                                                   (Prims.of_int (871))
                                                   (Prims.of_int (60)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (870))
                                                   (Prims.of_int (10))
                                                   (Prims.of_int (878))
                                                   (Prims.of_int (49)))))
                                          (Obj.magic uu___3)
                                          (fun uu___4 ->
                                             (fun uu___4 ->
                                                match uu___4 with
                                                | {
                                                    FStar_Reflection_V2_Data.lb_fv
                                                      = lb_fv;
                                                    FStar_Reflection_V2_Data.lb_us
                                                      = uu___5;
                                                    FStar_Reflection_V2_Data.lb_typ
                                                      = lb_typ;
                                                    FStar_Reflection_V2_Data.lb_def
                                                      = uu___6;_}
                                                    ->
                                                    let uu___7 =
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___8 -> g)) in
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (872))
                                                                  (Prims.of_int (17))
                                                                  (Prims.of_int (872))
                                                                  (Prims.of_int (18)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (872))
                                                                  (Prims.of_int (21))
                                                                  (Prims.of_int (878))
                                                                  (Prims.of_int (49)))))
                                                         (Obj.magic uu___7)
                                                         (fun uu___8 ->
                                                            (fun g0 ->
                                                               let uu___8 =
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    {
                                                                    uenv_inner
                                                                    = g;
                                                                    coreenv =
                                                                    (Pulse_Extract_CompilerLib.initial_core_env
                                                                    g)
                                                                    })) in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (873))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (873))
                                                                    (Prims.of_int (58)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (873))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (878))
                                                                    (Prims.of_int (49)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___8)
                                                                    (
                                                                    fun
                                                                    uu___9 ->
                                                                    (fun g1
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    generalize
                                                                    g1 lb_typ
                                                                    FStar_Pervasives_Native.None in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (873))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (878))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    (g2, tys,
                                                                    lb_typ1,
                                                                    uu___11)
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    debug_ g2
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    FStar_Tactics_V2_Builtins.term_to_string
                                                                    lb_typ1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (875))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (875))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Prims.strcat
                                                                    "Extracting ml typ: "
                                                                    (Prims.strcat
                                                                    uu___15
                                                                    "\n")))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (875))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (875))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (875))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (878))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let mlty
                                                                    =
                                                                    Pulse_Extract_CompilerLib.term_as_mlty
                                                                    g2.uenv_inner
                                                                    lb_typ1 in
                                                                    let uu___15
                                                                    =
                                                                    Pulse_Extract_CompilerLib.extend_fv
                                                                    g0 lb_fv
                                                                    (tys,
                                                                    mlty) in
                                                                    match uu___15
                                                                    with
                                                                    | 
                                                                    (g3,
                                                                    uu___16,
                                                                    e_bnd) ->
                                                                    FStar_Pervasives.Inl
                                                                    (g3,
                                                                    (Pulse_Extract_CompilerLib.iface_of_bindings
                                                                    [
                                                                    (lb_fv,
                                                                    e_bnd)]))))))
                                                                    uu___10)))
                                                                    uu___9)))
                                                              uu___8)))
                                               uu___4))))
                         | uu___2 ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.raise
                                     (Extraction_failure "Unexpected sigelt"))))
                        uu___2))
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