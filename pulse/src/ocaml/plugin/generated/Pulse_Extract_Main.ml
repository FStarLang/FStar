open Prims
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
                 (Prims.of_int (37)) (Prims.of_int (15)) (Prims.of_int (37))
                 (Prims.of_int (41)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (37)) (Prims.of_int (44)) (Prims.of_int (45))
                 (Prims.of_int (64)))))
        (Obj.magic (term_as_mlty g b.Pulse_Syntax_Base.binder_ty))
        (fun uu___ ->
           (fun mlty ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (38)) (Prims.of_int (12))
                            (Prims.of_int (38)) (Prims.of_int (29)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (38)) (Prims.of_int (32))
                            (Prims.of_int (45)) (Prims.of_int (64)))))
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
                                       (Prims.of_int (39))
                                       (Prims.of_int (18))
                                       (Prims.of_int (39))
                                       (Prims.of_int (72)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Extract.Main.fst"
                                       (Prims.of_int (40)) (Prims.of_int (4))
                                       (Prims.of_int (45))
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
                                                  (Prims.of_int (40))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (42))
                                                  (Prims.of_int (67)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Extract.Main.fst"
                                                  (Prims.of_int (42))
                                                  (Prims.of_int (68))
                                                  (Prims.of_int (45))
                                                  (Prims.of_int (64)))))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Extract.Main.fst"
                                                        (Prims.of_int (40))
                                                        (Prims.of_int (11))
                                                        (Prims.of_int (42))
                                                        (Prims.of_int (67)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Extract.Main.fst"
                                                        (Prims.of_int (40))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (42))
                                                        (Prims.of_int (67)))))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (42))
                                                              (Prims.of_int (38))
                                                              (Prims.of_int (42))
                                                              (Prims.of_int (66)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (40))
                                                              (Prims.of_int (11))
                                                              (Prims.of_int (42))
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
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (67)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (67)))))
                                                                (Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (41))
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
exception Extraction_failure of Prims.string 
let (uu___is_Extraction_failure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Extraction_failure uu___ -> true | uu___ -> false
let (__proj__Extraction_failure__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | Extraction_failure uu___ -> uu___
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
               (Prims.of_int (50)) (Prims.of_int (12)) (Prims.of_int (50))
               (Prims.of_int (33)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Extract.Main.fst"
               (Prims.of_int (51)) (Prims.of_int (2)) (Prims.of_int (53))
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
                 (Prims.of_int (57)) (Prims.of_int (24)) (Prims.of_int (57))
                 (Prims.of_int (48)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (58)) (Prims.of_int (4)) (Prims.of_int (148))
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
                            (Prims.of_int (58)) (Prims.of_int (7))
                            (Prims.of_int (58)) (Prims.of_int (20)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                            (Prims.of_int (58)) (Prims.of_int (4))
                            (Prims.of_int (148)) (Prims.of_int (7)))))
                   (Obj.magic (is_erasable p))
                   (fun uu___ ->
                      (fun uu___ ->
                         if uu___
                         then
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 -> erased_result)))
                         else
                           Obj.magic
                             (Obj.repr
                                (match p.Pulse_Syntax_Base.term1 with
                                 | Pulse_Syntax_Base.Tm_IntroPure uu___2 ->
                                     Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___3 -> erased_result))
                                 | Pulse_Syntax_Base.Tm_ElimExists uu___2 ->
                                     Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___3 -> erased_result))
                                 | Pulse_Syntax_Base.Tm_IntroExists uu___2 ->
                                     Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___3 -> erased_result))
                                 | Pulse_Syntax_Base.Tm_Rewrite uu___2 ->
                                     Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___3 -> erased_result))
                                 | Pulse_Syntax_Base.Tm_Abs
                                     { Pulse_Syntax_Base.b = b;
                                       Pulse_Syntax_Base.q = q;
                                       Pulse_Syntax_Base.ascription = uu___2;
                                       Pulse_Syntax_Base.body = body;_}
                                     ->
                                     Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (69))
                                                   (Prims.of_int (37))
                                                   (Prims.of_int (69))
                                                   (Prims.of_int (51)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (68))
                                                   (Prims.of_int (32))
                                                   (Prims.of_int (73))
                                                   (Prims.of_int (23)))))
                                          (Obj.magic (extend_env g b))
                                          (fun uu___3 ->
                                             (fun uu___3 ->
                                                match uu___3 with
                                                | (g1, mlident, mlty, name1)
                                                    ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (70))
                                                                  (Prims.of_int (19))
                                                                  (Prims.of_int (70))
                                                                  (Prims.of_int (47)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Extract.Main.fst"
                                                                  (Prims.of_int (70))
                                                                  (Prims.of_int (50))
                                                                  (Prims.of_int (73))
                                                                  (Prims.of_int (23)))))
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___4 ->
                                                               Pulse_Syntax_Naming.open_st_term_nv
                                                                 body name1))
                                                         (fun uu___4 ->
                                                            (fun body1 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (36)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (23)))))
                                                                    (
                                                                    Obj.magic
                                                                    (extract
                                                                    g1 body1))
                                                                    (
                                                                    fun
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
                                                                    ((Pulse_Extract_CompilerLib.mle_fun
                                                                    [
                                                                    (mlident,
                                                                    mlty)]
                                                                    body2),
                                                                    Pulse_Extract_CompilerLib.e_tag_pure)))))
                                                              uu___4)))
                                               uu___3))
                                 | Pulse_Syntax_Base.Tm_Return
                                     { Pulse_Syntax_Base.ctag = uu___2;
                                       Pulse_Syntax_Base.insert_eq = uu___3;
                                       Pulse_Syntax_Base.term = term;_}
                                     ->
                                     Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (76))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (76))
                                                   (Prims.of_int (29)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (76))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (77))
                                                   (Prims.of_int (18)))))
                                          (Obj.magic (term_as_mlexpr g term))
                                          (fun uu___4 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___5 ->
                                                  (uu___4,
                                                    Pulse_Extract_CompilerLib.e_tag_pure))))
                                 | Pulse_Syntax_Base.Tm_STApp
                                     { Pulse_Syntax_Base.head = head;
                                       Pulse_Syntax_Base.arg_qual = uu___2;
                                       Pulse_Syntax_Base.arg = arg;_}
                                     ->
                                     Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (80))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (80))
                                                   (Prims.of_int (40)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (80))
                                                   (Prims.of_int (43))
                                                   (Prims.of_int (82))
                                                   (Prims.of_int (40)))))
                                          (Obj.magic (term_as_mlexpr g head))
                                          (fun uu___3 ->
                                             (fun head1 ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (81))
                                                              (Prims.of_int (18))
                                                              (Prims.of_int (81))
                                                              (Prims.of_int (38)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (82))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (82))
                                                              (Prims.of_int (40)))))
                                                     (Obj.magic
                                                        (term_as_mlexpr g arg))
                                                     (fun arg1 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___3 ->
                                                             ((Pulse_Extract_CompilerLib.mle_app
                                                                 head1 
                                                                 [arg1]),
                                                               Pulse_Extract_CompilerLib.e_tag_impure)))))
                                               uu___3))
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
                                                   (Prims.of_int (85))
                                                   (Prims.of_int (11))
                                                   (Prims.of_int (85))
                                                   (Prims.of_int (27)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (85))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (98))
                                                   (Prims.of_int (9)))))
                                          (Obj.magic (is_erasable head))
                                          (fun uu___2 ->
                                             (fun uu___2 ->
                                                if uu___2
                                                then
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Extract.Main.fst"
                                                                (Prims.of_int (87))
                                                                (Prims.of_int (21))
                                                                (Prims.of_int (87))
                                                                (Prims.of_int (61)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Extract.Main.fst"
                                                                (Prims.of_int (88))
                                                                (Prims.of_int (10))
                                                                (Prims.of_int (88))
                                                                (Prims.of_int (24)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___3 ->
                                                             Pulse_Syntax_Naming.subst_st_term
                                                               body
                                                               [Pulse_Syntax_Naming.NT
                                                                  (Prims.int_zero,
                                                                    unit_val)]))
                                                       (fun uu___3 ->
                                                          (fun body1 ->
                                                             Obj.magic
                                                               (extract g
                                                                  body1))
                                                            uu___3))
                                                else
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Extract.Main.fst"
                                                                (Prims.of_int (91))
                                                                (Prims.of_int (24))
                                                                (Prims.of_int (91))
                                                                (Prims.of_int (38)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Extract.Main.fst"
                                                                (Prims.of_int (90))
                                                                (Prims.of_int (13))
                                                                (Prims.of_int (98))
                                                                (Prims.of_int (9)))))
                                                       (Obj.magic
                                                          (extract g head))
                                                       (fun uu___4 ->
                                                          (fun uu___4 ->
                                                             match uu___4
                                                             with
                                                             | (head1,
                                                                uu___5) ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (49)))))
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
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (49)))))
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
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (49)))))
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
                                                            uu___4))) uu___2))
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
                                                   (Prims.of_int (102))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (102))
                                                   (Prims.of_int (40)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (102))
                                                   (Prims.of_int (43))
                                                   (Prims.of_int (108))
                                                   (Prims.of_int (47)))))
                                          (Obj.magic (term_as_mlexpr g head))
                                          (fun uu___2 ->
                                             (fun head1 ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (103))
                                                              (Prims.of_int (37))
                                                              (Prims.of_int (103))
                                                              (Prims.of_int (56)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Extract.Main.fst"
                                                              (Prims.of_int (102))
                                                              (Prims.of_int (43))
                                                              (Prims.of_int (108))
                                                              (Prims.of_int (47)))))
                                                     (Obj.magic
                                                        (extend_env g binder))
                                                     (fun uu___2 ->
                                                        (fun uu___2 ->
                                                           match uu___2 with
                                                           | (g1, mlident,
                                                              mlty, name1) ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (47)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (47)))))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body
                                                                    name1))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Extract.Main.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (extract
                                                                    g1 body1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (body2,
                                                                    uu___5)
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
                                                                    uu___3)))
                                                          uu___2))) uu___2))
                                 | Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                     { Pulse_Syntax_Base.hint_type = uu___2;
                                       Pulse_Syntax_Base.binders = uu___3;
                                       Pulse_Syntax_Base.t3 = t;_}
                                     -> Obj.repr (extract g t)
                                 | Pulse_Syntax_Base.Tm_Admit uu___2 ->
                                     Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (147))
                                                   (Prims.of_int (21))
                                                   (Prims.of_int (147))
                                                   (Prims.of_int (140)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (147))
                                                   (Prims.of_int (13))
                                                   (Prims.of_int (147))
                                                   (Prims.of_int (140)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (147))
                                                         (Prims.of_int (41))
                                                         (Prims.of_int (147))
                                                         (Prims.of_int (139)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (147))
                                                         (Prims.of_int (21))
                                                         (Prims.of_int (147))
                                                         (Prims.of_int (140)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (147))
                                                               (Prims.of_int (96))
                                                               (Prims.of_int (147))
                                                               (Prims.of_int (138)))))
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
                                                            p))
                                                      (fun uu___3 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              Prims.strcat
                                                                "Cannot extract code with admit: "
                                                                (Prims.strcat
                                                                   uu___3
                                                                   "\n")))))
                                                (fun uu___3 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        Extraction_failure
                                                          uu___3))))
                                          (fun uu___3 ->
                                             FStar_Tactics_Effect.raise
                                               uu___3))
                                 | uu___2 ->
                                     Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (147))
                                                   (Prims.of_int (21))
                                                   (Prims.of_int (147))
                                                   (Prims.of_int (140)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Extract.Main.fst"
                                                   (Prims.of_int (147))
                                                   (Prims.of_int (13))
                                                   (Prims.of_int (147))
                                                   (Prims.of_int (140)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (147))
                                                         (Prims.of_int (41))
                                                         (Prims.of_int (147))
                                                         (Prims.of_int (139)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Extract.Main.fst"
                                                         (Prims.of_int (147))
                                                         (Prims.of_int (21))
                                                         (Prims.of_int (147))
                                                         (Prims.of_int (140)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Extract.Main.fst"
                                                               (Prims.of_int (147))
                                                               (Prims.of_int (96))
                                                               (Prims.of_int (147))
                                                               (Prims.of_int (138)))))
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
                                                            p))
                                                      (fun uu___3 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              Prims.strcat
                                                                "Cannot extract code with admit: "
                                                                (Prims.strcat
                                                                   uu___3
                                                                   "\n")))))
                                                (fun uu___3 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        Extraction_failure
                                                          uu___3))))
                                          (fun uu___3 ->
                                             FStar_Tactics_Effect.raise
                                               uu___3))))) uu___))) uu___)
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
                 (Prims.of_int (155)) (Prims.of_int (4)) (Prims.of_int (155))
                 (Prims.of_int (75)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                 (Prims.of_int (156)) (Prims.of_int (4)) (Prims.of_int (164))
                 (Prims.of_int (77)))))
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                       (Prims.of_int (155)) (Prims.of_int (11))
                       (Prims.of_int (155)) (Prims.of_int (75)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                       (Prims.of_int (155)) (Prims.of_int (4))
                       (Prims.of_int (155)) (Prims.of_int (75)))))
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Extract.Main.fst"
                             (Prims.of_int (155)) (Prims.of_int (53))
                             (Prims.of_int (155)) (Prims.of_int (74)))))
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
                                     (Prims.of_int (157)) (Prims.of_int (20))
                                     (Prims.of_int (157)) (Prims.of_int (74)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Extract.Main.fst"
                                     (Prims.of_int (156)) (Prims.of_int (7))
                                     (Prims.of_int (159)) (Prims.of_int (29)))))
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
                                                    (Prims.of_int (158))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (158))
                                                    (Prims.of_int (74)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Extract.Main.fst"
                                                    (Prims.of_int (159))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (159))
                                                    (Prims.of_int (29)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (158))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (158))
                                                          (Prims.of_int (74)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Extract.Main.fst"
                                                          (Prims.of_int (158))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (158))
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