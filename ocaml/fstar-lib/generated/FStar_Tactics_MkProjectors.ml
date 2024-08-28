open Prims
exception NotFound 
let (uu___is_NotFound : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | NotFound -> true | uu___ -> false
let (debug :
  (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
               (Prims.of_int (23)) (Prims.of_int (5)) (Prims.of_int (23))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
               (Prims.of_int (23)) (Prims.of_int (2)) (Prims.of_int (24))
               (Prims.of_int (16)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.debugging ()))
      (fun uu___ ->
         (fun uu___ ->
            if uu___
            then
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.MkProjectors.fst"
                               (Prims.of_int (24)) (Prims.of_int (10))
                               (Prims.of_int (24)) (Prims.of_int (16)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.MkProjectors.fst"
                               (Prims.of_int (24)) (Prims.of_int (4))
                               (Prims.of_int (24)) (Prims.of_int (16)))))
                      (Obj.magic (f ()))
                      (fun uu___1 ->
                         (fun uu___1 ->
                            Obj.magic
                              (FStar_Tactics_V2_Builtins.print uu___1))
                           uu___1)))
            else
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))))
           uu___)
let (mk_one_projector :
  Prims.string Prims.list ->
    Prims.nat -> Prims.nat -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun unf ->
    fun np ->
      fun i ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
                   (Prims.of_int (28)) (Prims.of_int (2)) (Prims.of_int (28))
                   (Prims.of_int (53)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
                   (Prims.of_int (28)) (Prims.of_int (54))
                   (Prims.of_int (48)) (Prims.of_int (41)))))
          (Obj.magic
             (debug
                (fun uu___ ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.MkProjectors.fst"
                              (Prims.of_int (28)) (Prims.of_int (19))
                              (Prims.of_int (28)) (Prims.of_int (48)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.MkProjectors.fst"
                              (Prims.of_int (28)) (Prims.of_int (50))
                              (Prims.of_int (28)) (Prims.of_int (52)))))
                     (Obj.magic
                        (FStar_Tactics_V2_Builtins.dump
                           "ENTRY mk_one_projector"))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> "")))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.MkProjectors.fst"
                              (Prims.of_int (29)) (Prims.of_int (16))
                              (Prims.of_int (29)) (Prims.of_int (32)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.MkProjectors.fst"
                              (Prims.of_int (29)) (Prims.of_int (35))
                              (Prims.of_int (48)) (Prims.of_int (41)))))
                     (Obj.magic
                        (FStar_Tactics_Util.repeatn np
                           FStar_Tactics_V2_Builtins.intro))
                     (fun uu___1 ->
                        (fun _params ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.MkProjectors.fst"
                                         (Prims.of_int (30))
                                         (Prims.of_int (24))
                                         (Prims.of_int (30))
                                         (Prims.of_int (32)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.MkProjectors.fst"
                                         (Prims.of_int (30))
                                         (Prims.of_int (35))
                                         (Prims.of_int (48))
                                         (Prims.of_int (41)))))
                                (Obj.magic
                                   (FStar_Tactics_V2_Builtins.intro ()))
                                (fun uu___1 ->
                                   (fun thing ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.MkProjectors.fst"
                                                    (Prims.of_int (31))
                                                    (Prims.of_int (10))
                                                    (Prims.of_int (31))
                                                    (Prims.of_int (26)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.MkProjectors.fst"
                                                    (Prims.of_int (32))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (48))
                                                    (Prims.of_int (41)))))
                                           (Obj.magic
                                              (FStar_Tactics_V2_Builtins.t_destruct
                                                 (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                    thing)))
                                           (fun uu___1 ->
                                              (fun r ->
                                                 match r with
                                                 | (cons, arity)::[] ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (48)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (15)))))
                                                             (if i >= arity
                                                              then
                                                                FStar_Tactics_V2_Derived.fail
                                                                  "proj: bad index in mk_one_projector"
                                                              else
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___2
                                                                    -> ()))
                                                             (fun uu___1 ->
                                                                (fun uu___1
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.repeatn
                                                                    i
                                                                    FStar_Tactics_V2_Builtins.intro))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.intro
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    the_b ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.repeatn
                                                                    ((arity -
                                                                    i) -
                                                                    Prims.int_one)
                                                                    FStar_Tactics_V2_Builtins.intro))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.intro
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun eq_b
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.rewrite
                                                                    eq_b))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.norm
                                                                    [FStar_Pervasives.iota;
                                                                    FStar_Pervasives.delta_only
                                                                    unf;
                                                                    FStar_Pervasives.zeta_full]))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.exact
                                                                    (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                                    the_b)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                  uu___1)))
                                                 | uu___1 ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_V2_Derived.fail
                                                             "proj: more than one case?")))
                                                uu___1))) uu___1))) uu___1)))
               uu___)
let _ =
  FStar_Tactics_Native.register_tactic
    "FStar.Tactics.MkProjectors.mk_one_projector" (Prims.of_int (4))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_3
               "FStar.Tactics.MkProjectors.mk_one_projector (plugin)"
               (FStar_Tactics_Native.from_tactic_3 mk_one_projector)
               (FStar_Syntax_Embeddings.e_list
                  FStar_Syntax_Embeddings.e_string)
               FStar_Syntax_Embeddings.e_int FStar_Syntax_Embeddings.e_int
               FStar_Syntax_Embeddings.e_unit psc ncb us args)
let (mk_one_method :
  Prims.string -> Prims.nat -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun proj ->
    fun np ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
                 (Prims.of_int (52)) (Prims.of_int (2)) (Prims.of_int (52))
                 (Prims.of_int (50)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
                 (Prims.of_int (52)) (Prims.of_int (51)) (Prims.of_int (58))
                 (Prims.of_int (70)))))
        (Obj.magic
           (debug
              (fun uu___ ->
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.MkProjectors.fst"
                            (Prims.of_int (52)) (Prims.of_int (19))
                            (Prims.of_int (52)) (Prims.of_int (45)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.MkProjectors.fst"
                            (Prims.of_int (52)) (Prims.of_int (47))
                            (Prims.of_int (52)) (Prims.of_int (49)))))
                   (Obj.magic
                      (FStar_Tactics_V2_Builtins.dump "ENTRY mk_one_method"))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> "")))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.MkProjectors.fst"
                            (Prims.of_int (53)) (Prims.of_int (11))
                            (Prims.of_int (53)) (Prims.of_int (26)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.MkProjectors.fst"
                            (Prims.of_int (53)) (Prims.of_int (29))
                            (Prims.of_int (58)) (Prims.of_int (70)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___1 ->
                         FStar_Reflection_V2_Builtins.explode_qn proj))
                   (fun uu___1 ->
                      (fun nm ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.MkProjectors.fst"
                                       (Prims.of_int (54))
                                       (Prims.of_int (15))
                                       (Prims.of_int (55))
                                       (Prims.of_int (69)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.MkProjectors.fst"
                                       (Prims.of_int (55))
                                       (Prims.of_int (72))
                                       (Prims.of_int (58))
                                       (Prims.of_int (70)))))
                              (Obj.magic
                                 (FStar_Tactics_Util.repeatn np
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.MkProjectors.fst"
                                                  (Prims.of_int (54))
                                                  (Prims.of_int (55))
                                                  (Prims.of_int (54))
                                                  (Prims.of_int (63)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.MkProjectors.fst"
                                                  (Prims.of_int (55))
                                                  (Prims.of_int (37))
                                                  (Prims.of_int (55))
                                                  (Prims.of_int (68)))))
                                         (Obj.magic
                                            (FStar_Tactics_V2_Builtins.intro
                                               ()))
                                         (fun b ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 ((FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                     b),
                                                   FStar_Reflection_V2_Data.Q_Implicit))))))
                              (fun uu___1 ->
                                 (fun params ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.MkProjectors.fst"
                                                  (Prims.of_int (56))
                                                  (Prims.of_int (24))
                                                  (Prims.of_int (56))
                                                  (Prims.of_int (32)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.MkProjectors.fst"
                                                  (Prims.of_int (56))
                                                  (Prims.of_int (35))
                                                  (Prims.of_int (58))
                                                  (Prims.of_int (70)))))
                                         (Obj.magic
                                            (FStar_Tactics_V2_Builtins.intro
                                               ()))
                                         (fun uu___1 ->
                                            (fun thing ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.MkProjectors.fst"
                                                             (Prims.of_int (57))
                                                             (Prims.of_int (13))
                                                             (Prims.of_int (57))
                                                             (Prims.of_int (40)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.MkProjectors.fst"
                                                             (Prims.of_int (58))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (58))
                                                             (Prims.of_int (70)))))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___1 ->
                                                          FStar_Tactics_NamedView.pack
                                                            (FStar_Tactics_NamedView.Tv_FVar
                                                               (FStar_Reflection_V2_Builtins.pack_fv
                                                                  nm))))
                                                    (fun uu___1 ->
                                                       (fun proj1 ->
                                                          Obj.magic
                                                            (FStar_Tactics_V2_Derived.exact
                                                               (FStar_Reflection_V2_Derived.mk_app
                                                                  proj1
                                                                  (FStar_List_Tot_Base.op_At
                                                                    params
                                                                    [
                                                                    ((FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                                    thing),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)]))))
                                                         uu___1))) uu___1)))
                                   uu___1))) uu___1))) uu___)
let _ =
  FStar_Tactics_Native.register_tactic
    "FStar.Tactics.MkProjectors.mk_one_method" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.MkProjectors.mk_one_method (plugin)"
               (FStar_Tactics_Native.from_tactic_2 mk_one_method)
               FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_int
               FStar_Syntax_Embeddings.e_unit psc ncb us args)
let (subst_map :
  (FStar_Tactics_NamedView.namedv * FStar_Reflection_Types.fv) Prims.list ->
    FStar_Tactics_NamedView.term ->
      FStar_Tactics_NamedView.term ->
        (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun ss ->
           fun r ->
             fun t ->
               Obj.magic
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       FStar_Reflection_V2_Builtins.subst_term
                         (FStar_List_Tot_Base.map
                            (fun uu___1 ->
                               match uu___1 with
                               | (x, fv) ->
                                   FStar_Syntax_Syntax.NT
                                     ((FStar_Reflection_V2_Builtins.pack_namedv
                                         x),
                                       (FStar_Reflection_V2_Derived.mk_e_app
                                          (FStar_Tactics_NamedView.pack
                                             (FStar_Tactics_NamedView.Tv_FVar
                                                fv)) [r]))) ss) t))) uu___2
          uu___1 uu___
let (binder_mk_implicit :
  FStar_Tactics_NamedView.binder -> FStar_Tactics_NamedView.binder) =
  fun b ->
    let q =
      match b.FStar_Tactics_NamedView.qual with
      | FStar_Reflection_V2_Data.Q_Explicit ->
          FStar_Reflection_V2_Data.Q_Implicit
      | q1 -> q1 in
    {
      FStar_Tactics_NamedView.uniq = (b.FStar_Tactics_NamedView.uniq);
      FStar_Tactics_NamedView.ppname = (b.FStar_Tactics_NamedView.ppname);
      FStar_Tactics_NamedView.sort = (b.FStar_Tactics_NamedView.sort);
      FStar_Tactics_NamedView.qual = q;
      FStar_Tactics_NamedView.attrs = (b.FStar_Tactics_NamedView.attrs)
    }
let (binder_to_term :
  FStar_Tactics_NamedView.binder -> FStar_Tactics_NamedView.term) =
  fun b ->
    FStar_Tactics_NamedView.pack
      (FStar_Tactics_NamedView.Tv_Var
         (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv b))
let (binder_argv :
  FStar_Tactics_NamedView.binder -> FStar_Reflection_V2_Data.argv) =
  fun b ->
    let q =
      match b.FStar_Tactics_NamedView.qual with
      | FStar_Reflection_V2_Data.Q_Meta uu___ ->
          FStar_Reflection_V2_Data.Q_Implicit
      | q1 -> q1 in
    ((binder_to_term b), q)
let rec list_last :
  'a . 'a Prims.list -> ('a, unit) FStar_Tactics_Effect.tac_repr =
  fun uu___ ->
    (fun xs ->
       match xs with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_V2_Derived.fail "list_last: empty"))
       | x::[] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> x)))
       | uu___::xs1 -> Obj.magic (Obj.repr (list_last xs1))) uu___
let (embed_int : Prims.int -> FStar_Tactics_NamedView.term) =
  fun i ->
    FStar_Reflection_V2_Builtins.pack_ln
      (FStar_Reflection_V2_Data.Tv_Const (FStar_Reflection_V2_Data.C_Int i))
let (embed_string : Prims.string -> FStar_Tactics_NamedView.term) =
  fun s ->
    FStar_Reflection_V2_Builtins.pack_ln
      (FStar_Reflection_V2_Data.Tv_Const
         (FStar_Reflection_V2_Data.C_String s))
let (mk_proj_decl :
  Prims.bool ->
    FStar_Reflection_Types.name ->
      Prims.string Prims.list ->
        FStar_Tactics_NamedView.univ_name Prims.list ->
          FStar_Tactics_NamedView.binder Prims.list ->
            Prims.nat ->
              FStar_Tactics_NamedView.binder ->
                FStar_Tactics_NamedView.term ->
                  (FStar_Tactics_NamedView.namedv *
                    FStar_Reflection_Types.fv) Prims.list ->
                    ((FStar_Reflection_Types.sigelt Prims.list *
                       FStar_Reflection_Types.fv),
                      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun is_method ->
    fun tyqn ->
      fun ctorname ->
        fun univs ->
          fun params ->
            fun idx ->
              fun field ->
                fun unfold_names_tm ->
                  fun smap ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.MkProjectors.fst"
                               (Prims.of_int (107)) (Prims.of_int (2))
                               (Prims.of_int (107)) (Prims.of_int (61)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.MkProjectors.fst"
                               (Prims.of_int (108)) (Prims.of_int (2))
                               (Prims.of_int (190)) (Prims.of_int (35)))))
                      (Obj.magic
                         (debug
                            (fun uu___ ->
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.MkProjectors.fst"
                                          (Prims.of_int (107))
                                          (Prims.of_int (41))
                                          (Prims.of_int (107))
                                          (Prims.of_int (60)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "prims.fst"
                                          (Prims.of_int (595))
                                          (Prims.of_int (19))
                                          (Prims.of_int (595))
                                          (Prims.of_int (31)))))
                                 (Obj.magic
                                    (FStar_Tactics_Unseal.unseal
                                       field.FStar_Tactics_NamedView.ppname))
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         Prims.strcat "Processing field "
                                           uu___1)))))
                      (fun uu___ ->
                         (fun uu___ ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.MkProjectors.fst"
                                          (Prims.of_int (108))
                                          (Prims.of_int (2))
                                          (Prims.of_int (108))
                                          (Prims.of_int (62)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.MkProjectors.fst"
                                          (Prims.of_int (108))
                                          (Prims.of_int (63))
                                          (Prims.of_int (190))
                                          (Prims.of_int (35)))))
                                 (Obj.magic
                                    (debug
                                       (fun uu___1 ->
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.MkProjectors.fst"
                                                     (Prims.of_int (108))
                                                     (Prims.of_int (36))
                                                     (Prims.of_int (108))
                                                     (Prims.of_int (61)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "prims.fst"
                                                     (Prims.of_int (595))
                                                     (Prims.of_int (19))
                                                     (Prims.of_int (595))
                                                     (Prims.of_int (31)))))
                                            (Obj.magic
                                               (FStar_Tactics_V2_Builtins.term_to_string
                                                  field.FStar_Tactics_NamedView.sort))
                                            (fun uu___2 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___3 ->
                                                    Prims.strcat
                                                      "Field typ = " uu___2)))))
                                 (fun uu___1 ->
                                    (fun uu___1 ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.MkProjectors.fst"
                                                     (Prims.of_int (109))
                                                     (Prims.of_int (11))
                                                     (Prims.of_int (109))
                                                     (Prims.of_int (24)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.MkProjectors.fst"
                                                     (Prims.of_int (109))
                                                     (Prims.of_int (27))
                                                     (Prims.of_int (190))
                                                     (Prims.of_int (35)))))
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  FStar_List_Tot_Base.length
                                                    params))
                                            (fun uu___2 ->
                                               (fun np ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.MkProjectors.fst"
                                                                (Prims.of_int (110))
                                                                (Prims.of_int (13))
                                                                (Prims.of_int (110))
                                                                (Prims.of_int (25)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.MkProjectors.fst"
                                                                (Prims.of_int (110))
                                                                (Prims.of_int (28))
                                                                (Prims.of_int (190))
                                                                (Prims.of_int (35)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___2 ->
                                                             FStar_Reflection_V2_Builtins.pack_fv
                                                               tyqn))
                                                       (fun uu___2 ->
                                                          (fun tyfv ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (102)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (35)))))
                                                                  (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (102)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.cur_module
                                                                    ()))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (102)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (102)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (101)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (102)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (101)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (101)))))
                                                                    (Obj.magic
                                                                    (list_last
                                                                    ctorname))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (101)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (101)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Unseal.unseal
                                                                    field.FStar_Tactics_NamedView.ppname))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "__item__"
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    uu___3
                                                                    uu___4))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "__proj__"
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    [uu___3]))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    uu___2
                                                                    uu___3))))
                                                                    uu___2)))
                                                                  (fun uu___2
                                                                    ->
                                                                    (fun nm
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Reflection_V2_Builtins.pack_fv
                                                                    nm))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun fv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Reflection_V2_Derived.mk_app
                                                                    (FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_UInst
                                                                    (tyfv,
                                                                    (FStar_List_Tot_Base.map
                                                                    (fun un
                                                                    ->
                                                                    FStar_Tactics_NamedView.pack_universe
                                                                    (FStar_Tactics_NamedView.Uv_Name
                                                                    un))
                                                                    univs))))
                                                                    (FStar_List_Tot_Base.map
                                                                    binder_argv
                                                                    params)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun rty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.fresh_binder
                                                                    rty))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun rb
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (73)))))
                                                                    (Obj.magic
                                                                    (subst_map
                                                                    smap
                                                                    (binder_to_term
                                                                    rb)
                                                                    field.FStar_Tactics_NamedView.sort))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
                                                                    (FStar_List_Tot_Base.op_At
                                                                    (FStar_List_Tot_Base.map
                                                                    binder_mk_implicit
                                                                    params)
                                                                    [rb])
                                                                    uu___2))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    projty ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (debug
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    projty))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "Proj typ = "
                                                                    uu___3)))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_NamedView.pack_sigelt
                                                                    (FStar_Tactics_NamedView.Sg_Let
                                                                    {
                                                                    FStar_Tactics_NamedView.isrec
                                                                    = false;
                                                                    FStar_Tactics_NamedView.lbs
                                                                    =
                                                                    [
                                                                    {
                                                                    FStar_Tactics_NamedView.lb_fv
                                                                    = fv;
                                                                    FStar_Tactics_NamedView.lb_us
                                                                    = univs;
                                                                    FStar_Tactics_NamedView.lb_typ
                                                                    = projty;
                                                                    FStar_Tactics_NamedView.lb_def
                                                                    =
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Effect";
                                                                    "synth_by_tactic"]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Abs
                                                                    ((FStar_Reflection_V2_Builtins.pack_binder
                                                                    {
                                                                    FStar_Reflection_V2_Data.sort2
                                                                    =
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    FStar_Reflection_V2_Data.Tv_Unknown);
                                                                    FStar_Reflection_V2_Data.qual
                                                                    =
                                                                    FStar_Reflection_V2_Data.Q_Explicit;
                                                                    FStar_Reflection_V2_Data.attrs
                                                                    = [];
                                                                    FStar_Reflection_V2_Data.ppname2
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "uu___")
                                                                    }),
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "MkProjectors";
                                                                    "mk_one_projector"]))),
                                                                    (unfold_names_tm,
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((embed_int
                                                                    np),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((embed_int
                                                                    idx),
                                                                    FStar_Reflection_V2_Data.Q_Explicit))))))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit))))
                                                                    }]
                                                                    })))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    se_proj
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (8)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (35)))))
                                                                    (if
                                                                    Prims.op_Negation
                                                                    is_method
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    [])))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    FStar_List_Tot_Base.existsb
                                                                    (FStar_Reflection_TermEq_Simple.term_eq
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Typeclasses";
                                                                    "no_method"]))))
                                                                    field.FStar_Tactics_NamedView.attrs
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    []))
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.cur_module
                                                                    ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (64)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Unseal.unseal
                                                                    field.FStar_Tactics_NamedView.ppname))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    [uu___6]))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    uu___5
                                                                    uu___6))))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Reflection_V2_Builtins.pack_fv
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    meth_fv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (8)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    {
                                                                    FStar_Tactics_NamedView.uniq
                                                                    =
                                                                    (rb.FStar_Tactics_NamedView.uniq);
                                                                    FStar_Tactics_NamedView.ppname
                                                                    =
                                                                    (rb.FStar_Tactics_NamedView.ppname);
                                                                    FStar_Tactics_NamedView.sort
                                                                    =
                                                                    (rb.FStar_Tactics_NamedView.sort);
                                                                    FStar_Tactics_NamedView.qual
                                                                    =
                                                                    (FStar_Reflection_V2_Data.Q_Meta
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Typeclasses";
                                                                    "tcresolve"]))));
                                                                    FStar_Tactics_NamedView.attrs
                                                                    =
                                                                    (rb.FStar_Tactics_NamedView.attrs)
                                                                    }))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun rb1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    (subst_map
                                                                    smap
                                                                    (binder_to_term
                                                                    rb1)
                                                                    field.FStar_Tactics_NamedView.sort))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
                                                                    (FStar_List_Tot_Base.op_At
                                                                    (FStar_List_Tot_Base.map
                                                                    binder_mk_implicit
                                                                    params)
                                                                    [rb1])
                                                                    uu___5))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    projty1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (8)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Effect";
                                                                    "synth_by_tactic"]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Abs
                                                                    ((FStar_Reflection_V2_Builtins.pack_binder
                                                                    {
                                                                    FStar_Reflection_V2_Data.sort2
                                                                    =
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    FStar_Reflection_V2_Data.Tv_Unknown);
                                                                    FStar_Reflection_V2_Data.qual
                                                                    =
                                                                    FStar_Reflection_V2_Data.Q_Explicit;
                                                                    FStar_Reflection_V2_Data.attrs
                                                                    = [];
                                                                    FStar_Reflection_V2_Data.ppname2
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "uu___")
                                                                    }),
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "MkProjectors";
                                                                    "mk_one_method"]))),
                                                                    ((embed_string
                                                                    (FStar_Reflection_V2_Builtins.implode_qn
                                                                    nm)),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((embed_int
                                                                    np),
                                                                    FStar_Reflection_V2_Data.Q_Explicit))))))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    lb_def ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_NamedView.pack_sigelt
                                                                    (FStar_Tactics_NamedView.Sg_Let
                                                                    {
                                                                    FStar_Tactics_NamedView.isrec
                                                                    = false;
                                                                    FStar_Tactics_NamedView.lbs
                                                                    =
                                                                    [
                                                                    {
                                                                    FStar_Tactics_NamedView.lb_fv
                                                                    = meth_fv;
                                                                    FStar_Tactics_NamedView.lb_us
                                                                    = univs;
                                                                    FStar_Tactics_NamedView.lb_typ
                                                                    = projty1;
                                                                    FStar_Tactics_NamedView.lb_def
                                                                    = lb_def
                                                                    }]
                                                                    })))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    [uu___5]))))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))))
                                                                    (fun
                                                                    maybe_se_method
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (((
                                                                    FStar_Reflection_V2_Builtins.set_sigelt_attrs
                                                                    (FStar_List_Tot_Base.op_At
                                                                    field.FStar_Tactics_NamedView.attrs
                                                                    (FStar_Reflection_V2_Builtins.sigelt_attrs
                                                                    se_proj))
                                                                    se_proj)
                                                                    ::
                                                                    maybe_se_method),
                                                                    fv)))))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                            uu___2))) uu___2)))
                                      uu___1))) uu___)
let (mk_projs :
  Prims.bool ->
    Prims.string ->
      (FStar_Reflection_Types.sigelt Prims.list, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun is_class ->
    fun tyname ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
                 (Prims.of_int (194)) (Prims.of_int (2)) (Prims.of_int (194))
                 (Prims.of_int (51)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
                 (Prims.of_int (194)) (Prims.of_int (52))
                 (Prims.of_int (224)) (Prims.of_int (29)))))
        (Obj.magic
           (FStar_Tactics_V2_Builtins.print
              (Prims.strcat "!! mk_projs tactic called on: " tyname)))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.MkProjectors.fst"
                            (Prims.of_int (195)) (Prims.of_int (13))
                            (Prims.of_int (195)) (Prims.of_int (30)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.MkProjectors.fst"
                            (Prims.of_int (196)) (Prims.of_int (2))
                            (Prims.of_int (224)) (Prims.of_int (29)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___1 ->
                         FStar_Reflection_V2_Builtins.explode_qn tyname))
                   (fun uu___1 ->
                      (fun tyqn ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.MkProjectors.fst"
                                       (Prims.of_int (196))
                                       (Prims.of_int (8))
                                       (Prims.of_int (196))
                                       (Prims.of_int (36)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.MkProjectors.fst"
                                       (Prims.of_int (196))
                                       (Prims.of_int (2))
                                       (Prims.of_int (224))
                                       (Prims.of_int (29)))))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.MkProjectors.fst"
                                             (Prims.of_int (196))
                                             (Prims.of_int (19))
                                             (Prims.of_int (196))
                                             (Prims.of_int (31)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.MkProjectors.fst"
                                             (Prims.of_int (196))
                                             (Prims.of_int (8))
                                             (Prims.of_int (196))
                                             (Prims.of_int (36)))))
                                    (Obj.magic
                                       (FStar_Tactics_V2_Builtins.top_env ()))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            FStar_Reflection_V2_Builtins.lookup_typ
                                              uu___1 tyqn))))
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    match uu___1 with
                                    | FStar_Pervasives_Native.None ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.raise
                                                NotFound))
                                    | FStar_Pervasives_Native.Some se ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.MkProjectors.fst"
                                                         (Prims.of_int (200))
                                                         (Prims.of_int (10))
                                                         (Prims.of_int (200))
                                                         (Prims.of_int (27)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.MkProjectors.fst"
                                                         (Prims.of_int (200))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (224))
                                                         (Prims.of_int (29)))))
                                                (Obj.magic
                                                   (FStar_Tactics_NamedView.inspect_sigelt
                                                      se))
                                                (fun uu___2 ->
                                                   (fun uu___2 ->
                                                      match uu___2 with
                                                      | FStar_Tactics_NamedView.Sg_Inductive
                                                          {
                                                            FStar_Tactics_NamedView.nm
                                                              = nm;
                                                            FStar_Tactics_NamedView.univs1
                                                              = univs;
                                                            FStar_Tactics_NamedView.params
                                                              = params;
                                                            FStar_Tactics_NamedView.typ
                                                              = typ;
                                                            FStar_Tactics_NamedView.ctors
                                                              = ctors;_}
                                                          ->
                                                          Obj.magic
                                                            (Obj.repr
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (57)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (11)))))
                                                                  (if
                                                                    (FStar_List_Tot_Base.length
                                                                    ctors) <>
                                                                    Prims.int_one
                                                                   then
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    "Expected an inductive with one constructor"
                                                                   else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ()))
                                                                  (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_SyntaxHelpers.collect_arr_bs
                                                                    typ))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.fst
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    indices
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (11)))))
                                                                    (if
                                                                    Prims.uu___is_Cons
                                                                    indices
                                                                    then
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    "Inductive indices nonempty?"
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ctors))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (ctorname,
                                                                    ctor_t)::[]
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_SyntaxHelpers.collect_arr_bs
                                                                    ctor_t))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (fields,
                                                                    uu___7)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "Nil"]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "string"]))),
                                                                    FStar_Reflection_V2_Data.Q_Implicit)))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    unfold_names_tm
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (14)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.fold_left
                                                                    (fun
                                                                    uu___8 ->
                                                                    fun field
                                                                    ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (decls,
                                                                    smap,
                                                                    unfold_names_tm1,
                                                                    idx) ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (104)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    (mk_proj_decl
                                                                    is_class
                                                                    tyqn
                                                                    ctorname
                                                                    univs
                                                                    params
                                                                    idx field
                                                                    unfold_names_tm1
                                                                    smap))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (ds, fv)
                                                                    ->
                                                                    ((FStar_List_Tot_Base.op_At
                                                                    decls ds),
                                                                    (((FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                                    field),
                                                                    fv) ::
                                                                    smap),
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "Cons"]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "string"]))),
                                                                    FStar_Reflection_V2_Data.Q_Implicit)))),
                                                                    ((embed_string
                                                                    (FStar_Reflection_V2_Builtins.implode_qn
                                                                    (FStar_Reflection_V2_Builtins.inspect_fv
                                                                    fv))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    (unfold_names_tm1,
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    (idx +
                                                                    Prims.int_one)))))
                                                                    ([], [],
                                                                    unfold_names_tm,
                                                                    Prims.int_zero)
                                                                    fields))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (decls,
                                                                    uu___10,
                                                                    uu___11,
                                                                    uu___12)
                                                                    -> decls))))
                                                                    uu___8)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                      | uu___3 ->
                                                          Obj.magic
                                                            (Obj.repr
                                                               (FStar_Tactics_V2_Derived.fail
                                                                  "not an inductive")))
                                                     uu___2)))) uu___1)))
                        uu___1))) uu___)
let _ =
  FStar_Tactics_Native.register_tactic "FStar.Tactics.MkProjectors.mk_projs"
    (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.MkProjectors.mk_projs (plugin)"
               (FStar_Tactics_Native.from_tactic_2 mk_projs)
               FStar_Syntax_Embeddings.e_bool
               FStar_Syntax_Embeddings.e_string
               (FStar_Syntax_Embeddings.e_list
                  FStar_Reflection_V2_Embeddings.e_sigelt) psc ncb us args)