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
                              (Prims.of_int (57)) (Prims.of_int (17))
                              (Prims.of_int (57)) (Prims.of_int (22)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (57)) (Prims.of_int (9))
                              (Prims.of_int (57)) (Prims.of_int (22)))))
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
                 (Prims.of_int (73)) (Prims.of_int (15)) (Prims.of_int (73))
                 (Prims.of_int (41)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (73)) (Prims.of_int (44)) (Prims.of_int (80))
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
                            (Prims.of_int (74)) (Prims.of_int (12))
                            (Prims.of_int (74)) (Prims.of_int (29)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (74)) (Prims.of_int (32))
                            (Prims.of_int (80)) (Prims.of_int (64)))))
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
                            (Prims.of_int (88)) (Prims.of_int (18))
                            (Prims.of_int (88)) (Prims.of_int (35)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (87)) (Prims.of_int (16))
                            (Prims.of_int (89)) (Prims.of_int (16)))))
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
                 (Prims.of_int (94)) (Prims.of_int (12)) (Prims.of_int (94))
                 (Prims.of_int (36)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (94)) (Prims.of_int (39)) (Prims.of_int (98))
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
                            (Prims.of_int (95)) (Prims.of_int (20))
                            (Prims.of_int (95)) (Prims.of_int (56)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (94)) (Prims.of_int (39))
                            (Prims.of_int (98)) (Prims.of_int (17)))))
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
                                (Prims.of_int (105)) (Prims.of_int (14))
                                (Prims.of_int (105)) (Prims.of_int (31)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (105)) (Prims.of_int (34))
                                (Prims.of_int (114)) (Prims.of_int (25)))))
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
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (106)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (114))
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
                                (Prims.of_int (118)) (Prims.of_int (8))
                                (Prims.of_int (123)) (Prims.of_int (14)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (116)) (Prims.of_int (24))
                                (Prims.of_int (125)) (Prims.of_int (72)))))
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
                                (Prims.of_int (127)) (Prims.of_int (14))
                                (Prims.of_int (127)) (Prims.of_int (34)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (128)) (Prims.of_int (6))
                                (Prims.of_int (128)) (Prims.of_int (30)))))
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
                 (Prims.of_int (130)) (Prims.of_int (20))
                 (Prims.of_int (130)) (Prims.of_int (43)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (129)) (Prims.of_int (24))
                 (Prims.of_int (133)) (Prims.of_int (72)))))
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
               (Prims.of_int (137)) (Prims.of_int (12)) (Prims.of_int (137))
               (Prims.of_int (33)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (138)) (Prims.of_int (2)) (Prims.of_int (140))
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
                        (Prims.of_int (152)) (Prims.of_int (65))
                        (Prims.of_int (152)) (Prims.of_int (88)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "prims.fst" (Prims.of_int (611))
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
                 (Prims.of_int (152)) (Prims.of_int (4)) (Prims.of_int (152))
                 (Prims.of_int (89)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (153)) (Prims.of_int (4)) (Prims.of_int (179))
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
                                   (Prims.of_int (155)) (Prims.of_int (17))
                                   (Prims.of_int (155)) (Prims.of_int (31)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Extract.Main.fst"
                                   (Prims.of_int (156)) (Prims.of_int (6))
                                   (Prims.of_int (174)) (Prims.of_int (17)))))
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
                          (Prims.of_int (217)) (Prims.of_int (22))
                          (Prims.of_int (217)) (Prims.of_int (43)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "prims.fst" (Prims.of_int (611))
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
                   (Prims.of_int (216)) (Prims.of_int (2))
                   (Prims.of_int (217)) (Prims.of_int (44)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                   (Prims.of_int (218)) (Prims.of_int (2))
                   (Prims.of_int (302)) (Prims.of_int (46)))))
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
                                     (Prims.of_int (221)) (Prims.of_int (4))
                                     (Prims.of_int (223)) (Prims.of_int (41)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Extract.Main.fst"
                                     (Prims.of_int (224)) (Prims.of_int (4))
                                     (Prims.of_int (302)) (Prims.of_int (46)))))
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
                                                                   (Prims.of_int (227))
                                                                   (Prims.of_int (28))
                                                                   (Prims.of_int (227))
                                                                   (Prims.of_int (51)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "prims.fst"
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
                     (Prims.of_int (311)) (Prims.of_int (10))
                     (Prims.of_int (311)) (Prims.of_int (17)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                     (Prims.of_int (311)) (Prims.of_int (20))
                     (Prims.of_int (314)) (Prims.of_int (22)))))
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
                                (Prims.of_int (312)) (Prims.of_int (10))
                                (Prims.of_int (312)) (Prims.of_int (82)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (312)) (Prims.of_int (85))
                                (Prims.of_int (314)) (Prims.of_int (22)))))
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
               (Prims.of_int (318)) (Prims.of_int (10)) (Prims.of_int (318))
               (Prims.of_int (39)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (319)) (Prims.of_int (2)) (Prims.of_int (324))
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
                 (Prims.of_int (366)) (Prims.of_int (16))
                 (Prims.of_int (366)) (Prims.of_int (31)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (366)) (Prims.of_int (36))
                 (Prims.of_int (428)) (Prims.of_int (23)))))
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
                            (Prims.of_int (367)) (Prims.of_int (22))
                            (Prims.of_int (367)) (Prims.of_int (54)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (369)) (Prims.of_int (2))
                            (Prims.of_int (428)) (Prims.of_int (23)))))
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
                 (Prims.of_int (431)) (Prims.of_int (18))
                 (Prims.of_int (431)) (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (430)) (Prims.of_int (55))
                 (Prims.of_int (435)) (Prims.of_int (62)))))
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
                                (Prims.of_int (432)) (Prims.of_int (17))
                                (Prims.of_int (432)) (Prims.of_int (37)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (431)) (Prims.of_int (22))
                                (Prims.of_int (435)) (Prims.of_int (62)))))
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
                 (Prims.of_int (443)) (Prims.of_int (22))
                 (Prims.of_int (443)) (Prims.of_int (50)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (443)) (Prims.of_int (53))
                 (Prims.of_int (526)) (Prims.of_int (5))))) (Obj.magic uu___)
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
                            (Prims.of_int (445)) (Prims.of_int (6))
                            (Prims.of_int (445)) (Prims.of_int (77)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (445)) (Prims.of_int (82))
                            (Prims.of_int (526)) (Prims.of_int (5)))))
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
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (55)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (451))
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
                 (Prims.of_int (529)) (Prims.of_int (18))
                 (Prims.of_int (529)) (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (528)) (Prims.of_int (67))
                 (Prims.of_int (533)) (Prims.of_int (62)))))
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
                                (Prims.of_int (530)) (Prims.of_int (17))
                                (Prims.of_int (530)) (Prims.of_int (37)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (529)) (Prims.of_int (22))
                                (Prims.of_int (533)) (Prims.of_int (62)))))
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
let (extract_dv_binder :
  Pulse_Syntax_Base.binder ->
    Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option ->
      (Pulse_Extract_CompilerLib.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun q ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                match q with
                | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.Implicit)
                    ->
                    FStar_Pervasives_Native.Some
                      Pulse_Extract_CompilerLib.implicit_qual
                | uu___2 -> FStar_Pervasives_Native.None)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (538)) (Prims.of_int (4)) (Prims.of_int (540))
                 (Prims.of_int (15)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (541)) (Prims.of_int (2)) (Prims.of_int (545))
                 (Prims.of_int (70))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun q1 ->
              let uu___1 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        Pulse_Extract_CompilerLib.rt_term_to_term
                          b.Pulse_Syntax_Base.binder_ty)) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (542)) (Prims.of_int (4))
                            (Prims.of_int (542)) (Prims.of_int (37)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (541)) (Prims.of_int (2))
                            (Prims.of_int (545)) (Prims.of_int (70)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun uu___2 ->
                         let uu___3 =
                           FStar_Tactics_Unseal.unseal
                             (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (543))
                                       (Prims.of_int (4))
                                       (Prims.of_int (543))
                                       (Prims.of_int (35)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (541))
                                       (Prims.of_int (2))
                                       (Prims.of_int (545))
                                       (Prims.of_int (70)))))
                              (Obj.magic uu___3)
                              (fun uu___4 ->
                                 (fun uu___4 ->
                                    let uu___5 =
                                      let uu___6 =
                                        FStar_Tactics_Unseal.unseal
                                          b.Pulse_Syntax_Base.binder_attrs in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (545))
                                                 (Prims.of_int (44))
                                                 (Prims.of_int (545))
                                                 (Prims.of_int (69)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Extract.Main.fst"
                                                 (Prims.of_int (545))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (545))
                                                 (Prims.of_int (70)))))
                                        (Obj.magic uu___6)
                                        (fun uu___7 ->
                                           (fun uu___7 ->
                                              Obj.magic
                                                (FStar_Tactics_Util.map
                                                   (fun uu___8 ->
                                                      (fun t ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___8 ->
                                                                 Pulse_Extract_CompilerLib.rt_term_to_term
                                                                   t)))
                                                        uu___8) uu___7))
                                             uu___7) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (545))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (545))
                                                  (Prims.of_int (70)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (541))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (545))
                                                  (Prims.of_int (70)))))
                                         (Obj.magic uu___5)
                                         (fun uu___6 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___7 ->
                                                 Pulse_Extract_CompilerLib.mk_binder
                                                   uu___2 uu___4 q1 uu___6))))
                                   uu___4))) uu___2))) uu___1)
let (extend_env' :
  env ->
    Pulse_Syntax_Base.ppname ->
      Pulse_Syntax_Base.typ ->
        ((env * Pulse_Syntax_Base.nvar), unit) FStar_Tactics_Effect.tac_repr)
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
                       ({
                          uenv_inner = (g.uenv_inner);
                          coreenv =
                            (Pulse_Typing_Env.push_binding g.coreenv
                               (Pulse_Typing_Env.fresh g.coreenv) ppname ty)
                        }, (ppname, (Pulse_Typing_Env.fresh g.coreenv))))))
          uu___2 uu___1 uu___
let (extend_env'_binder :
  env ->
    Pulse_Syntax_Base.binder ->
      ((env * Pulse_Syntax_Base.nvar), unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun b ->
      extend_env' g b.Pulse_Syntax_Base.binder_ppname
        b.Pulse_Syntax_Base.binder_ty
let rec (extract_dv_pattern :
  env ->
    Pulse_Syntax_Base.pattern ->
      ((env * Pulse_Extract_CompilerLib.pattern * Pulse_Typing_Env.binding
         Prims.list),
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
                               Pulse_Extract_CompilerLib.mk_fv
                                 fv.Pulse_Syntax_Base.fv_name)) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (560)) (Prims.of_int (13))
                                (Prims.of_int (560)) (Prims.of_int (33)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (560)) (Prims.of_int (36))
                                (Prims.of_int (562)) (Prims.of_int (34)))))
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
                                           (Prims.of_int (561))
                                           (Prims.of_int (22))
                                           (Prims.of_int (561))
                                           (Prims.of_int (67)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (560))
                                           (Prims.of_int (36))
                                           (Prims.of_int (562))
                                           (Prims.of_int (34)))))
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___3 ->
                                          match uu___2 with
                                          | (g1, pats1, bs) ->
                                              let uu___4 =
                                                Pulse_Extract_CompilerLib.mk_pat_cons
                                                  fv1 pats1 in
                                              (g1, uu___4, bs))))) uu___1)))
           | Pulse_Syntax_Base.Pat_Constant c ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          let uu___1 =
                            let uu___2 = Pulse_Extract_CompilerLib.mk_const c in
                            Pulse_Extract_CompilerLib.mk_pat_constant uu___2 in
                          (g, uu___1, []))))
           | Pulse_Syntax_Base.Pat_Var (ppname, sort) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = FStar_Tactics_Unseal.unseal ppname in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (566)) (Prims.of_int (13))
                                (Prims.of_int (566)) (Prims.of_int (28)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (566)) (Prims.of_int (31))
                                (Prims.of_int (569)) (Prims.of_int (36)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun pp ->
                             let uu___1 = FStar_Tactics_Unseal.unseal sort in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (567))
                                           (Prims.of_int (13))
                                           (Prims.of_int (567))
                                           (Prims.of_int (26)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Extract.Main.fst"
                                           (Prims.of_int (567))
                                           (Prims.of_int (29))
                                           (Prims.of_int (569))
                                           (Prims.of_int (36)))))
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun ty ->
                                        let uu___2 =
                                          extend_env' g
                                            (Pulse_Syntax_Base.mk_ppname
                                               ppname FStar_Range.range_0) ty in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Extract.Main.fst"
                                                      (Prims.of_int (568))
                                                      (Prims.of_int (20))
                                                      (Prims.of_int (568))
                                                      (Prims.of_int (69)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Extract.Main.fst"
                                                      (Prims.of_int (567))
                                                      (Prims.of_int (29))
                                                      (Prims.of_int (569))
                                                      (Prims.of_int (36)))))
                                             (Obj.magic uu___2)
                                             (fun uu___3 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___4 ->
                                                     match uu___3 with
                                                     | (g1, (uu___5, x)) ->
                                                         let uu___6 =
                                                           Pulse_Extract_CompilerLib.mk_pat_var
                                                             pp ty in
                                                         (g1, uu___6,
                                                           [(x, ty)])))))
                                       uu___2))) uu___1)))
           | Pulse_Syntax_Base.Pat_Dot_Term t ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          let uu___1 = Pulse_Extract_CompilerLib.mk_dot_pat t in
                          (g, uu___1, []))))) uu___1 uu___
and (extract_dv_patterns :
  env ->
    Pulse_Syntax_Base.pattern Prims.list ->
      ((env * Pulse_Extract_CompilerLib.pattern Prims.list *
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
                                (Prims.of_int (577)) (Prims.of_int (19))
                                (Prims.of_int (577)) (Prims.of_int (41)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (576)) (Prims.of_int (12))
                                (Prims.of_int (579)) (Prims.of_int (20)))))
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
                                               (Prims.of_int (578))
                                               (Prims.of_int (21))
                                               (Prims.of_int (578))
                                               (Prims.of_int (45)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (577))
                                               (Prims.of_int (44))
                                               (Prims.of_int (579))
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
    (Pulse_Extract_CompilerLib.term, unit) FStar_Tactics_Effect.tac_repr)
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
                             (Prims.of_int (582)) (Prims.of_int (93))
                             (Prims.of_int (582)) (Prims.of_int (111)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "prims.fst"
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
                           (Prims.of_int (582)) (Prims.of_int (23))
                           (Prims.of_int (582)) (Prims.of_int (112)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                           (Prims.of_int (582)) (Prims.of_int (16))
                           (Prims.of_int (582)) (Prims.of_int (112)))))
                  (Obj.magic uu___3)
                  (fun uu___4 -> FStar_Tactics_V2_Derived.fail uu___4))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (582)) (Prims.of_int (16)) (Prims.of_int (582))
               (Prims.of_int (112)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (583)) (Prims.of_int (2)) (Prims.of_int (587))
               (Prims.of_int (16))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun fail ->
            match FStar_Reflection_V2_Builtins.inspect_ln p with
            | FStar_Reflection_V2_Data.Tv_App (hd, (arg, uu___1)) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Pulse_Extract_CompilerLib.rt_term_to_term arg)))
            | uu___1 -> Obj.magic (Obj.repr (fail ()))) uu___1)
let (get_type_of_array :
  Pulse_Syntax_Base.term ->
    (Pulse_Extract_CompilerLib.term, unit) FStar_Tactics_Effect.tac_repr)
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
                             (Prims.of_int (590)) (Prims.of_int (96))
                             (Prims.of_int (590)) (Prims.of_int (114)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "prims.fst"
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
                           (Prims.of_int (590)) (Prims.of_int (23))
                           (Prims.of_int (590)) (Prims.of_int (115)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                           (Prims.of_int (590)) (Prims.of_int (16))
                           (Prims.of_int (590)) (Prims.of_int (115)))))
                  (Obj.magic uu___3)
                  (fun uu___4 -> FStar_Tactics_V2_Derived.fail uu___4))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (590)) (Prims.of_int (16)) (Prims.of_int (590))
               (Prims.of_int (115)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (591)) (Prims.of_int (2)) (Prims.of_int (595))
               (Prims.of_int (16))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun fail ->
            match FStar_Reflection_V2_Builtins.inspect_ln p with
            | FStar_Reflection_V2_Data.Tv_App (hd, (arg, uu___1)) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Pulse_Extract_CompilerLib.rt_term_to_term arg)))
            | uu___1 -> Obj.magic (Obj.repr (fail ()))) uu___1)
let rec (extract_dv :
  env ->
    Pulse_Syntax_Base.st_term ->
      (Pulse_Extract_CompilerLib.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      let uu___ = is_erasable p in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (599)) (Prims.of_int (5)) (Prims.of_int (599))
                 (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (599)) (Prims.of_int (2)) (Prims.of_int (698))
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
                                        (Prims.of_int (609))
                                        (Prims.of_int (15))
                                        (Prims.of_int (609))
                                        (Prims.of_int (36)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (609))
                                        (Prims.of_int (39))
                                        (Prims.of_int (612))
                                        (Prims.of_int (42)))))
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
                                                   (Prims.of_int (610))
                                                   (Prims.of_int (17))
                                                   (Prims.of_int (610))
                                                   (Prims.of_int (39)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (609))
                                                   (Prims.of_int (39))
                                                   (Prims.of_int (612))
                                                   (Prims.of_int (42)))))
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
                                                                  (Prims.of_int (611))
                                                                  (Prims.of_int (17))
                                                                  (Prims.of_int (611))
                                                                  (Prims.of_int (54)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (612))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (612))
                                                                  (Prims.of_int (42)))))
                                                         (Obj.magic uu___7)
                                                         (fun body1 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___8 ->
                                                                 Pulse_Extract_CompilerLib.mk_abs
                                                                   b'
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
                                  let uu___6 =
                                    Pulse_Extract_CompilerLib.rt_term_to_term
                                      term in
                                  Pulse_Extract_CompilerLib.mk_return uu___6))
                      | Pulse_Syntax_Base.Tm_STApp
                          { Pulse_Syntax_Base.head = head;
                            Pulse_Syntax_Base.arg_qual = arg_qual;
                            Pulse_Syntax_Base.arg = arg;_}
                          ->
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 ->
                                  let q =
                                    match arg_qual with
                                    | FStar_Pervasives_Native.Some
                                        (Pulse_Syntax_Base.Implicit) ->
                                        FStar_Pervasives_Native.Some
                                          Pulse_Extract_CompilerLib.implicit_arg_qual
                                    | uu___4 -> FStar_Pervasives_Native.None in
                                  let uu___4 =
                                    Pulse_Extract_CompilerLib.rt_term_to_term
                                      head in
                                  let uu___5 =
                                    Pulse_Extract_CompilerLib.rt_term_to_term
                                      arg in
                                  Pulse_Extract_CompilerLib.mk_app uu___4 q
                                    uu___5))
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
                                        (Prims.of_int (625))
                                        (Prims.of_int (15))
                                        (Prims.of_int (625))
                                        (Prims.of_int (44)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (625))
                                        (Prims.of_int (47))
                                        (Prims.of_int (629))
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
                                                   (Prims.of_int (626))
                                                   (Prims.of_int (15))
                                                   (Prims.of_int (626))
                                                   (Prims.of_int (32)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (626))
                                                   (Prims.of_int (35))
                                                   (Prims.of_int (629))
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
                                                              (Prims.of_int (627))
                                                              (Prims.of_int (17))
                                                              (Prims.of_int (627))
                                                              (Prims.of_int (44)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (626))
                                                              (Prims.of_int (35))
                                                              (Prims.of_int (629))
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
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (54)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (629))
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
                                        (Prims.of_int (632))
                                        (Prims.of_int (15))
                                        (Prims.of_int (632))
                                        (Prims.of_int (44)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (632))
                                        (Prims.of_int (47))
                                        (Prims.of_int (636))
                                        (Prims.of_int (43)))))
                               (Obj.magic uu___3)
                               (fun uu___4 ->
                                  (fun b' ->
                                     let uu___4 =
                                       Obj.magic
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___5 ->
                                               let uu___6 =
                                                 Pulse_Extract_CompilerLib.rt_term_to_term
                                                   head in
                                               Pulse_Extract_CompilerLib.mk_return
                                                 uu___6)) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (633))
                                                   (Prims.of_int (15))
                                                   (Prims.of_int (633))
                                                   (Prims.of_int (55)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (633))
                                                   (Prims.of_int (58))
                                                   (Prims.of_int (636))
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
                                                              (Prims.of_int (634))
                                                              (Prims.of_int (17))
                                                              (Prims.of_int (634))
                                                              (Prims.of_int (44)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (633))
                                                              (Prims.of_int (58))
                                                              (Prims.of_int (636))
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
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (52)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (636))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (636))
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
                            (let uu___4 =
                               Obj.magic
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___5 ->
                                       Pulse_Extract_CompilerLib.rt_term_to_term
                                         b)) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (639))
                                        (Prims.of_int (14))
                                        (Prims.of_int (639))
                                        (Prims.of_int (35)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (639))
                                        (Prims.of_int (38))
                                        (Prims.of_int (642))
                                        (Prims.of_int (29)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  (fun b1 ->
                                     let uu___5 = extract_dv g then_ in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (640))
                                                   (Prims.of_int (18))
                                                   (Prims.of_int (640))
                                                   (Prims.of_int (36)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (640))
                                                   (Prims.of_int (39))
                                                   (Prims.of_int (642))
                                                   (Prims.of_int (29)))))
                                          (Obj.magic uu___5)
                                          (fun uu___6 ->
                                             (fun then_1 ->
                                                let uu___6 =
                                                  extract_dv g else_ in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (641))
                                                              (Prims.of_int (18))
                                                              (Prims.of_int (641))
                                                              (Prims.of_int (36)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (642))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (642))
                                                              (Prims.of_int (29)))))
                                                     (Obj.magic uu___6)
                                                     (fun else_1 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___7 ->
                                                             Pulse_Extract_CompilerLib.mk_if
                                                               b1 then_1
                                                               else_1))))
                                               uu___6))) uu___5))
                      | Pulse_Syntax_Base.Tm_Match
                          { Pulse_Syntax_Base.sc = sc;
                            Pulse_Syntax_Base.returns_ = uu___3;
                            Pulse_Syntax_Base.brs = brs;_}
                          ->
                          Obj.repr
                            (let uu___4 =
                               Obj.magic
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___5 ->
                                       Pulse_Extract_CompilerLib.rt_term_to_term
                                         sc)) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (645))
                                        (Prims.of_int (19))
                                        (Prims.of_int (645))
                                        (Prims.of_int (43)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (645))
                                        (Prims.of_int (6))
                                        (Prims.of_int (645))
                                        (Prims.of_int (77)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  (fun uu___5 ->
                                     let uu___6 =
                                       FStar_Tactics_Util.map
                                         (extract_dv_branch g) brs in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (645))
                                                   (Prims.of_int (44))
                                                   (Prims.of_int (645))
                                                   (Prims.of_int (77)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (645))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (645))
                                                   (Prims.of_int (77)))))
                                          (Obj.magic uu___6)
                                          (fun uu___7 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___8 ->
                                                  Pulse_Extract_CompilerLib.mk_match
                                                    uu___5 uu___7)))) uu___5))
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
                                        (Prims.of_int (648))
                                        (Prims.of_int (22))
                                        (Prims.of_int (648))
                                        (Prims.of_int (44)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (648))
                                        (Prims.of_int (47))
                                        (Prims.of_int (656))
                                        (Prims.of_int (52)))))
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
                                                   (Prims.of_int (649))
                                                   (Prims.of_int (17))
                                                   (Prims.of_int (649))
                                                   (Prims.of_int (34)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (649))
                                                   (Prims.of_int (37))
                                                   (Prims.of_int (656))
                                                   (Prims.of_int (52)))))
                                          (Obj.magic uu___6)
                                          (fun body1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___7 ->
                                                  let unit_binder ppname =
                                                    Pulse_Extract_CompilerLib.mk_binder
                                                      Pulse_Extract_CompilerLib.unit_ty
                                                      ppname
                                                      FStar_Pervasives_Native.None
                                                      [] in
                                                  let uu___8 =
                                                    let uu___9 =
                                                      let uu___10 =
                                                        Pulse_Extract_CompilerLib.mk_fv
                                                          ["Pulse";
                                                          "Lib";
                                                          "Dv";
                                                          "while_"] in
                                                      Pulse_Extract_CompilerLib.mk_fv_tm
                                                        uu___10 in
                                                    let uu___10 =
                                                      let uu___11 =
                                                        unit_binder
                                                          "while_cond" in
                                                      Pulse_Extract_CompilerLib.mk_abs
                                                        uu___11 condition1 in
                                                    Pulse_Extract_CompilerLib.mk_app
                                                      uu___9
                                                      FStar_Pervasives_Native.None
                                                      uu___10 in
                                                  let uu___9 =
                                                    let uu___10 =
                                                      unit_binder
                                                        "while_body" in
                                                    Pulse_Extract_CompilerLib.mk_abs
                                                      uu___10 body1 in
                                                  Pulse_Extract_CompilerLib.mk_app
                                                    uu___8
                                                    FStar_Pervasives_Native.None
                                                    uu___9)))) uu___6))
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
                                        (Prims.of_int (659))
                                        (Prims.of_int (18))
                                        (Prims.of_int (659))
                                        (Prims.of_int (36)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (659))
                                        (Prims.of_int (39))
                                        (Prims.of_int (667))
                                        (Prims.of_int (49)))))
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
                                                   (Prims.of_int (660))
                                                   (Prims.of_int (18))
                                                   (Prims.of_int (660))
                                                   (Prims.of_int (36)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (660))
                                                   (Prims.of_int (39))
                                                   (Prims.of_int (667))
                                                   (Prims.of_int (49)))))
                                          (Obj.magic uu___8)
                                          (fun body21 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___9 ->
                                                  let unit_binder ppname =
                                                    Pulse_Extract_CompilerLib.mk_binder
                                                      Pulse_Extract_CompilerLib.unit_ty
                                                      ppname
                                                      FStar_Pervasives_Native.None
                                                      [] in
                                                  let uu___10 =
                                                    let uu___11 =
                                                      let uu___12 =
                                                        Pulse_Extract_CompilerLib.mk_fv
                                                          ["Pulse";
                                                          "Lib";
                                                          "Dv";
                                                          "par"] in
                                                      Pulse_Extract_CompilerLib.mk_fv_tm
                                                        uu___12 in
                                                    let uu___12 =
                                                      let uu___13 =
                                                        unit_binder "par_b1" in
                                                      Pulse_Extract_CompilerLib.mk_abs
                                                        uu___13 body11 in
                                                    Pulse_Extract_CompilerLib.mk_app
                                                      uu___11
                                                      FStar_Pervasives_Native.None
                                                      uu___12 in
                                                  let uu___11 =
                                                    let uu___12 =
                                                      unit_binder "par_b2" in
                                                    Pulse_Extract_CompilerLib.mk_abs
                                                      uu___12 body21 in
                                                  Pulse_Extract_CompilerLib.mk_app
                                                    uu___10
                                                    FStar_Pervasives_Native.None
                                                    uu___11)))) uu___8))
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
                                        (Prims.of_int (670))
                                        (Prims.of_int (15))
                                        (Prims.of_int (670))
                                        (Prims.of_int (44)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (670))
                                        (Prims.of_int (47))
                                        (Prims.of_int (675))
                                        (Prims.of_int (52)))))
                               (Obj.magic uu___3)
                               (fun uu___4 ->
                                  (fun b' ->
                                     let uu___4 =
                                       let uu___5 =
                                         let uu___6 =
                                           Obj.magic
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___7 ->
                                                   let uu___8 =
                                                     Pulse_Extract_CompilerLib.mk_fv
                                                       ["Pulse";
                                                       "Lib";
                                                       "Reference";
                                                       "alloc"] in
                                                   Pulse_Extract_CompilerLib.mk_fv_tm
                                                     uu___8)) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (671))
                                                    (Prims.of_int (45))
                                                    (Prims.of_int (671))
                                                    (Prims.of_int (110)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (671))
                                                    (Prims.of_int (33))
                                                    (Prims.of_int (672))
                                                    (Prims.of_int (72)))))
                                           (Obj.magic uu___6)
                                           (fun uu___7 ->
                                              (fun uu___7 ->
                                                 let uu___8 =
                                                   get_type_of_ref
                                                     binder.Pulse_Syntax_Base.binder_ty in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (672))
                                                               (Prims.of_int (37))
                                                               (Prims.of_int (672))
                                                               (Prims.of_int (71)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (671))
                                                               (Prims.of_int (33))
                                                               (Prims.of_int (672))
                                                               (Prims.of_int (72)))))
                                                      (Obj.magic uu___8)
                                                      (fun uu___9 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___10 ->
                                                              Pulse_Extract_CompilerLib.mk_app
                                                                uu___7
                                                                (FStar_Pervasives_Native.Some
                                                                   Pulse_Extract_CompilerLib.implicit_arg_qual)
                                                                uu___9))))
                                                uu___7) in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (671))
                                                  (Prims.of_int (33))
                                                  (Prims.of_int (672))
                                                  (Prims.of_int (72)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (671))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (672))
                                                  (Prims.of_int (111)))))
                                         (Obj.magic uu___5)
                                         (fun uu___6 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___7 ->
                                                 let uu___8 =
                                                   Pulse_Extract_CompilerLib.rt_term_to_term
                                                     initializer1 in
                                                 Pulse_Extract_CompilerLib.mk_app
                                                   uu___6
                                                   FStar_Pervasives_Native.None
                                                   uu___8)) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (671))
                                                   (Prims.of_int (22))
                                                   (Prims.of_int (672))
                                                   (Prims.of_int (111)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (672))
                                                   (Prims.of_int (114))
                                                   (Prims.of_int (675))
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
                                                              (Prims.of_int (673))
                                                              (Prims.of_int (17))
                                                              (Prims.of_int (673))
                                                              (Prims.of_int (44)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (672))
                                                              (Prims.of_int (114))
                                                              (Prims.of_int (675))
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
                                                                    (Prims.of_int (674))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (674))
                                                                    (Prims.of_int (54)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (675))
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
                                        (Prims.of_int (678))
                                        (Prims.of_int (15))
                                        (Prims.of_int (678))
                                        (Prims.of_int (44)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (678))
                                        (Prims.of_int (47))
                                        (Prims.of_int (688))
                                        (Prims.of_int (52)))))
                               (Obj.magic uu___3)
                               (fun uu___4 ->
                                  (fun b' ->
                                     let uu___4 =
                                       let uu___5 =
                                         let uu___6 =
                                           let uu___7 =
                                             Obj.magic
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___8 ->
                                                     let uu___9 =
                                                       Pulse_Extract_CompilerLib.mk_fv
                                                         ["Pulse";
                                                         "Lib";
                                                         "Array";
                                                         "Core";
                                                         "alloc"] in
                                                     Pulse_Extract_CompilerLib.mk_fv_tm
                                                       uu___9)) in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Extract.Main.fst"
                                                      (Prims.of_int (684))
                                                      (Prims.of_int (57))
                                                      (Prims.of_int (684))
                                                      (Prims.of_int (126)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Extract.Main.fst"
                                                      (Prims.of_int (684))
                                                      (Prims.of_int (45))
                                                      (Prims.of_int (685))
                                                      (Prims.of_int (74)))))
                                             (Obj.magic uu___7)
                                             (fun uu___8 ->
                                                (fun uu___8 ->
                                                   let uu___9 =
                                                     get_type_of_array
                                                       binder.Pulse_Syntax_Base.binder_ty in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Extract.Main.fst"
                                                                 (Prims.of_int (685))
                                                                 (Prims.of_int (37))
                                                                 (Prims.of_int (685))
                                                                 (Prims.of_int (73)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Extract.Main.fst"
                                                                 (Prims.of_int (684))
                                                                 (Prims.of_int (45))
                                                                 (Prims.of_int (685))
                                                                 (Prims.of_int (74)))))
                                                        (Obj.magic uu___9)
                                                        (fun uu___10 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___11 ->
                                                                Pulse_Extract_CompilerLib.mk_app
                                                                  uu___8
                                                                  (FStar_Pervasives_Native.Some
                                                                    Pulse_Extract_CompilerLib.implicit_arg_qual)
                                                                  uu___10))))
                                                  uu___8) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (684))
                                                    (Prims.of_int (45))
                                                    (Prims.of_int (685))
                                                    (Prims.of_int (74)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (684))
                                                    (Prims.of_int (33))
                                                    (Prims.of_int (685))
                                                    (Prims.of_int (114)))))
                                           (Obj.magic uu___6)
                                           (fun uu___7 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___8 ->
                                                   let uu___9 =
                                                     Pulse_Extract_CompilerLib.rt_term_to_term
                                                       initializer1 in
                                                   Pulse_Extract_CompilerLib.mk_app
                                                     uu___7
                                                     FStar_Pervasives_Native.None
                                                     uu___9)) in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (684))
                                                  (Prims.of_int (33))
                                                  (Prims.of_int (685))
                                                  (Prims.of_int (114)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (684))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (685))
                                                  (Prims.of_int (148)))))
                                         (Obj.magic uu___5)
                                         (fun uu___6 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___7 ->
                                                 let uu___8 =
                                                   Pulse_Extract_CompilerLib.rt_term_to_term
                                                     length in
                                                 Pulse_Extract_CompilerLib.mk_app
                                                   uu___6
                                                   FStar_Pervasives_Native.None
                                                   uu___8)) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (684))
                                                   (Prims.of_int (22))
                                                   (Prims.of_int (685))
                                                   (Prims.of_int (148)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (685))
                                                   (Prims.of_int (151))
                                                   (Prims.of_int (688))
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
                                                              (Prims.of_int (686))
                                                              (Prims.of_int (17))
                                                              (Prims.of_int (686))
                                                              (Prims.of_int (44)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (685))
                                                              (Prims.of_int (151))
                                                              (Prims.of_int (688))
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
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (54)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (688))
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
                            (let uu___4 =
                               FStar_Tactics_V2_Builtins.print
                                 "Admit in dv extraction is currently ignored" in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (691))
                                        (Prims.of_int (6))
                                        (Prims.of_int (691))
                                        (Prims.of_int (59)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (692))
                                        (Prims.of_int (6))
                                        (Prims.of_int (692))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 ->
                                       Pulse_Extract_CompilerLib.mk_return
                                         Pulse_Extract_CompilerLib.unit_tm)))
                      | Pulse_Syntax_Base.Tm_Unreachable ->
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 ->
                                  Pulse_Extract_CompilerLib.mk_return
                                    Pulse_Extract_CompilerLib.unit_tm))
                      | Pulse_Syntax_Base.Tm_WithInv
                          { Pulse_Syntax_Base.name1 = uu___3;
                            Pulse_Syntax_Base.body6 = body;
                            Pulse_Syntax_Base.returns_inv = uu___4;_}
                          -> Obj.repr (extract_dv g body)))) uu___1)
and (extract_dv_branch :
  env ->
    Pulse_Syntax_Base.branch ->
      (Pulse_Extract_CompilerLib.branch, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun b ->
      let uu___ =
        Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> b)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (701)) (Prims.of_int (18))
                 (Prims.of_int (701)) (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (700)) (Prims.of_int (73))
                 (Prims.of_int (703)) (Prims.of_int (102)))))
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
                                (Prims.of_int (702)) (Prims.of_int (19))
                                (Prims.of_int (702)) (Prims.of_int (43)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (701)) (Prims.of_int (22))
                                (Prims.of_int (703)) (Prims.of_int (102)))))
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
                                              (Prims.of_int (703))
                                              (Prims.of_int (41))
                                              (Prims.of_int (703))
                                              (Prims.of_int (101)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Extract.Main.fst"
                                              (Prims.of_int (703))
                                              (Prims.of_int (20))
                                              (Prims.of_int (703))
                                              (Prims.of_int (102)))))
                                     (Obj.magic uu___5)
                                     (fun uu___6 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___7 ->
                                             FStar_Reflection_Typing.close_term_bs
                                               bs uu___6)) in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (703))
                                               (Prims.of_int (20))
                                               (Prims.of_int (703))
                                               (Prims.of_int (102)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (703))
                                               (Prims.of_int (2))
                                               (Prims.of_int (703))
                                               (Prims.of_int (102)))))
                                      (Obj.magic uu___4)
                                      (fun uu___5 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___6 ->
                                              Pulse_Extract_CompilerLib.mk_branch
                                                pat1 uu___5)))) uu___3)))
             uu___1)
let (extract_dv_typ :
  FStar_Reflection_Types.typ ->
    (Pulse_Extract_CompilerLib.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_Reflection_V2_Collect.collect_arr_ln_bs t)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (706)) (Prims.of_int (14)) (Prims.of_int (706))
               (Prims.of_int (35)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (705)) (Prims.of_int (47)) (Prims.of_int (729))
               (Prims.of_int (89))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | (bs, c) ->
                let uu___2 =
                  FStar_Tactics_Util.map
                    (fun b ->
                       let uu___3 =
                         Obj.magic
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___4 ->
                                 FStar_Reflection_V2_Builtins.inspect_binder
                                   b)) in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                  (Prims.of_int (708)) (Prims.of_int (16))
                                  (Prims.of_int (708)) (Prims.of_int (34)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                  (Prims.of_int (709)) (Prims.of_int (4))
                                  (Prims.of_int (715)) (Prims.of_int (8)))))
                         (Obj.magic uu___3)
                         (fun uu___4 ->
                            (fun bview ->
                               let uu___4 =
                                 Obj.magic
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___5 ->
                                         Pulse_Extract_CompilerLib.rt_term_to_term
                                           bview.FStar_Reflection_V2_Data.sort2)) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Extract.Main.fst"
                                             (Prims.of_int (710))
                                             (Prims.of_int (6))
                                             (Prims.of_int (710))
                                             (Prims.of_int (38)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Extract.Main.fst"
                                             (Prims.of_int (709))
                                             (Prims.of_int (4))
                                             (Prims.of_int (715))
                                             (Prims.of_int (8)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       (fun uu___5 ->
                                          let uu___6 =
                                            FStar_Tactics_Unseal.unseal
                                              bview.FStar_Reflection_V2_Data.ppname2 in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Extract.Main.fst"
                                                        (Prims.of_int (711))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (711))
                                                        (Prims.of_int (29)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Extract.Main.fst"
                                                        (Prims.of_int (709))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (715))
                                                        (Prims.of_int (8)))))
                                               (Obj.magic uu___6)
                                               (fun uu___7 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___8 ->
                                                       Pulse_Extract_CompilerLib.mk_binder
                                                         uu___5 uu___7
                                                         (match bview.FStar_Reflection_V2_Data.qual
                                                          with
                                                          | FStar_Reflection_V2_Data.Q_Implicit
                                                              ->
                                                              FStar_Pervasives_Native.Some
                                                                Pulse_Extract_CompilerLib.implicit_qual
                                                          | uu___9 ->
                                                              FStar_Pervasives_Native.None)
                                                         [])))) uu___5)))
                              uu___4)) bs in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (707)) (Prims.of_int (11))
                              (Prims.of_int (715)) (Prims.of_int (12)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                              (Prims.of_int (716)) (Prims.of_int (2))
                              (Prims.of_int (729)) (Prims.of_int (89)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun bs1 ->
                           match FStar_Reflection_V2_Builtins.inspect_comp c
                           with
                           | FStar_Reflection_V2_Data.C_Total t1 ->
                               let uu___3 =
                                 Obj.magic
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___4 ->
                                         FStar_Reflection_V2_Collect.collect_app_ln
                                           t1)) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Extract.Main.fst"
                                             (Prims.of_int (718))
                                             (Prims.of_int (19))
                                             (Prims.of_int (718))
                                             (Prims.of_int (37)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Extract.Main.fst"
                                             (Prims.of_int (717))
                                             (Prims.of_int (24))
                                             (Prims.of_int (725))
                                             (Prims.of_int (32)))))
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       (fun uu___4 ->
                                          match uu___4 with
                                          | (hd, args) ->
                                              if
                                                (FStar_List_Tot_Base.length
                                                   args)
                                                  = Prims.int_zero
                                              then
                                                Obj.magic
                                                  (Obj.repr
                                                     (let uu___5 =
                                                        let uu___6 =
                                                          FStar_Tactics_V2_Builtins.term_to_string
                                                            t1 in
                                                        FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Extract.Main.fst"
                                                                   (Prims.of_int (723))
                                                                   (Prims.of_int (79))
                                                                   (Prims.of_int (723))
                                                                   (Prims.of_int (99)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "prims.fst"
                                                                   (Prims.of_int (611))
                                                                   (Prims.of_int (19))
                                                                   (Prims.of_int (611))
                                                                   (Prims.of_int (31)))))
                                                          (Obj.magic uu___6)
                                                          (fun uu___7 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___8 ->
                                                                  Prims.strcat
                                                                    "Unexpected return type in extract_dv_typ: "
                                                                    (
                                                                    Prims.strcat
                                                                    uu___7 ""))) in
                                                      FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Extract.Main.fst"
                                                                 (Prims.of_int (723))
                                                                 (Prims.of_int (16))
                                                                 (Prims.of_int (723))
                                                                 (Prims.of_int (100)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Extract.Main.fst"
                                                                 (Prims.of_int (723))
                                                                 (Prims.of_int (9))
                                                                 (Prims.of_int (723))
                                                                 (Prims.of_int (100)))))
                                                        (Obj.magic uu___5)
                                                        (fun uu___6 ->
                                                           FStar_Tactics_V2_Derived.fail
                                                             uu___6)))
                                              else
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___6 ->
                                                           let ret_typ =
                                                             Pulse_Extract_CompilerLib.rt_term_to_term
                                                               (FStar_Pervasives_Native.fst
                                                                  (FStar_List_Tot_Base.hd
                                                                    args)) in
                                                           Pulse_Extract_CompilerLib.mk_arrow
                                                             bs1 ret_typ))))
                                         uu___4))
                           | uu___3 ->
                               let uu___4 =
                                 let uu___5 =
                                   FStar_Tactics_V2_Builtins.term_to_string t in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Extract.Main.fst"
                                            (Prims.of_int (729))
                                            (Prims.of_int (68))
                                            (Prims.of_int (729))
                                            (Prims.of_int (88)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "prims.fst"
                                            (Prims.of_int (611))
                                            (Prims.of_int (19))
                                            (Prims.of_int (611))
                                            (Prims.of_int (31)))))
                                   (Obj.magic uu___5)
                                   (fun uu___6 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___7 ->
                                           Prims.strcat
                                             "Unexpected arrow comp in extract_dv_typ: "
                                             (Prims.strcat uu___6 ""))) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Extract.Main.fst"
                                             (Prims.of_int (729))
                                             (Prims.of_int (6))
                                             (Prims.of_int (729))
                                             (Prims.of_int (89)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Extract.Main.fst"
                                             (Prims.of_int (728))
                                             (Prims.of_int (4))
                                             (Prims.of_int (729))
                                             (Prims.of_int (89)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       FStar_Tactics_V2_Derived.fail uu___5)))
                          uu___3))) uu___1)
let (extract_pulse_dv :
  Pulse_Extract_CompilerLib.uenv ->
    Pulse_Syntax_Base.st_term ->
      (Pulse_Extract_CompilerLib.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uenv ->
    fun p ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                {
                  uenv_inner = uenv;
                  coreenv = (Pulse_Extract_CompilerLib.initial_core_env uenv)
                })) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (732)) (Prims.of_int (12))
                 (Prims.of_int (732)) (Prims.of_int (62)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (732)) (Prims.of_int (67))
                 (Prims.of_int (736)) (Prims.of_int (16)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun g ->
              let uu___1 = erase_ghost_subterms g p in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (733)) (Prims.of_int (10))
                            (Prims.of_int (733)) (Prims.of_int (34)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (733)) (Prims.of_int (37))
                            (Prims.of_int (736)) (Prims.of_int (16)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun p1 ->
                         let uu___2 = simplify_st_term g p1 in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (734))
                                       (Prims.of_int (10))
                                       (Prims.of_int (734))
                                       (Prims.of_int (30)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (736))
                                       (Prims.of_int (2))
                                       (Prims.of_int (736))
                                       (Prims.of_int (16)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 (fun p2 -> Obj.magic (extract_dv g p2))
                                   uu___3))) uu___2))) uu___1)
let rec (extract_dv_recursive :
  env ->
    Pulse_Syntax_Base.st_term ->
      FStar_Reflection_Types.fv ->
        (Pulse_Extract_CompilerLib.term, unit) FStar_Tactics_Effect.tac_repr)
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
                                        (Prims.of_int (744))
                                        (Prims.of_int (19))
                                        (Prims.of_int (744))
                                        (Prims.of_int (41)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (743))
                                        (Prims.of_int (19))
                                        (Prims.of_int (747))
                                        (Prims.of_int (65)))))
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
                                                       (Prims.of_int (745))
                                                       (Prims.of_int (19))
                                                       (Prims.of_int (745))
                                                       (Prims.of_int (41)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Extract.Main.fst"
                                                       (Prims.of_int (745))
                                                       (Prims.of_int (44))
                                                       (Prims.of_int (747))
                                                       (Prims.of_int (65)))))
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
                                                                  (Prims.of_int (746))
                                                                  (Prims.of_int (19))
                                                                  (Prims.of_int (746))
                                                                  (Prims.of_int (55)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (747))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (747))
                                                                  (Prims.of_int (65)))))
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
                                                                    (Prims.of_int (747))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (747))
                                                                    (Prims.of_int (42)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (747))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (747))
                                                                    (Prims.of_int (65)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___6)
                                                                    (
                                                                    fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Extract_CompilerLib.mk_abs
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
                                                 (FStar_Reflection_V2_Builtins.pack_ln
                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                       rec_name))
                                                 FStar_Range.range_0))])) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (749))
                                        (Prims.of_int (19))
                                        (Prims.of_int (749))
                                        (Prims.of_int (100)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Extract.Main.fst"
                                        (Prims.of_int (749))
                                        (Prims.of_int (103))
                                        (Prims.of_int (752))
                                        (Prims.of_int (25)))))
                               (Obj.magic uu___2)
                               (fun uu___3 ->
                                  (fun body1 ->
                                     let uu___3 = erase_ghost_subterms g p in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (750))
                                                   (Prims.of_int (16))
                                                   (Prims.of_int (750))
                                                   (Prims.of_int (40)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (750))
                                                   (Prims.of_int (43))
                                                   (Prims.of_int (752))
                                                   (Prims.of_int (25)))))
                                          (Obj.magic uu___3)
                                          (fun uu___4 ->
                                             (fun p1 ->
                                                let uu___4 =
                                                  simplify_st_term g p1 in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (751))
                                                              (Prims.of_int (16))
                                                              (Prims.of_int (751))
                                                              (Prims.of_int (36)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (752))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (752))
                                                              (Prims.of_int (25)))))
                                                     (Obj.magic uu___4)
                                                     (fun uu___5 ->
                                                        (fun p2 ->
                                                           Obj.magic
                                                             (extract_dv g
                                                                body1))
                                                          uu___5))) uu___4)))
                                    uu___3)))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_V2_Derived.fail
                           "Unexpected recursive definition of non-function")))
          uu___2 uu___1 uu___
let rec (extract_dv_ghost :
  env ->
    Pulse_Syntax_Base.st_term ->
      (Pulse_Extract_CompilerLib.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun p ->
           match p.Pulse_Syntax_Base.term1 with
           | Pulse_Syntax_Base.Tm_Abs
               { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = q;
                 Pulse_Syntax_Base.ascription = uu___;
                 Pulse_Syntax_Base.body = body;_}
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___1 = extend_env'_binder g b in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (761)) (Prims.of_int (19))
                                (Prims.of_int (761)) (Prims.of_int (41)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                                (Prims.of_int (760)) (Prims.of_int (31))
                                (Prims.of_int (765)) (Prims.of_int (5)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun uu___2 ->
                             match uu___2 with
                             | (g1, x) ->
                                 let uu___3 =
                                   Obj.magic
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___4 ->
                                           Pulse_Syntax_Naming.open_st_term_nv
                                             body x)) in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (762))
                                               (Prims.of_int (19))
                                               (Prims.of_int (762))
                                               (Prims.of_int (41)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Extract.Main.fst"
                                               (Prims.of_int (762))
                                               (Prims.of_int (44))
                                               (Prims.of_int (764))
                                               (Prims.of_int (65)))))
                                      (Obj.magic uu___3)
                                      (fun uu___4 ->
                                         (fun body1 ->
                                            let uu___4 =
                                              extract_dv_ghost g1 body1 in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (763))
                                                          (Prims.of_int (19))
                                                          (Prims.of_int (763))
                                                          (Prims.of_int (42)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (764))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (764))
                                                          (Prims.of_int (65)))))
                                                 (Obj.magic uu___4)
                                                 (fun uu___5 ->
                                                    (fun body2 ->
                                                       let uu___5 =
                                                         extract_dv_binder b
                                                           q in
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (764))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (764))
                                                                    (Prims.of_int (42)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (764))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (764))
                                                                    (Prims.of_int (65)))))
                                                            (Obj.magic uu___5)
                                                            (fun uu___6 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___7
                                                                    ->
                                                                    Pulse_Extract_CompilerLib.mk_abs
                                                                    uu___6
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    body2
                                                                    (FStar_Pervasives_Native.__proj__Mktuple2__item___2
                                                                    x))))))
                                                      uu___5))) uu___4)))
                            uu___2)))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 -> Pulse_Extract_CompilerLib.unit_tm))))
        uu___1 uu___