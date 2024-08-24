open Prims
let (empty_elim : Prims.empty -> unit -> Obj.t) =
  fun uu___1 ->
    fun uu___ ->
      (fun e -> fun a -> Obj.magic (failwith "unreachable")) uu___1 uu___
let (add_suffix :
  Prims.string -> FStar_Reflection_Types.name -> FStar_Reflection_Types.name)
  =
  fun s ->
    fun nm ->
      FStar_Reflection_V2_Builtins.explode_qn
        (Prims.strcat (FStar_Reflection_V2_Builtins.implode_qn nm) s)
let (unitv_ : FStar_Tactics_NamedView.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_Const FStar_Reflection_V2_Data.C_Unit)
let (unitt_ : FStar_Tactics_NamedView.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_FVar
       (FStar_Reflection_V2_Builtins.pack_fv ["Prims"; "unit"]))
let (empty_ : FStar_Tactics_NamedView.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_FVar
       (FStar_Reflection_V2_Builtins.pack_fv ["Prims"; "empty"]))
let (either_ :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term -> FStar_Tactics_NamedView.term)
  =
  fun a ->
    fun b ->
      FStar_Reflection_V2_Builtins.pack_ln
        (FStar_Reflection_V2_Data.Tv_App
           ((FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_App
                  ((FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_FVar
                         (FStar_Reflection_V2_Builtins.pack_fv
                            ["FStar"; "Pervasives"; "either"]))),
                    (a, FStar_Reflection_V2_Data.Q_Explicit)))),
             (b, FStar_Reflection_V2_Data.Q_Explicit)))
let (tuple2_ :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term -> FStar_Tactics_NamedView.term)
  =
  fun a ->
    fun b ->
      FStar_Reflection_V2_Builtins.pack_ln
        (FStar_Reflection_V2_Data.Tv_App
           ((FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_App
                  ((FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_FVar
                         (FStar_Reflection_V2_Builtins.pack_fv
                            ["FStar"; "Pervasives"; "Native"; "tuple2"]))),
                    (a, FStar_Reflection_V2_Data.Q_Explicit)))),
             (b, FStar_Reflection_V2_Data.Q_Explicit)))
let (mktuple2_ :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term -> FStar_Tactics_NamedView.term)
  =
  fun a ->
    fun b ->
      FStar_Reflection_V2_Builtins.pack_ln
        (FStar_Reflection_V2_Data.Tv_App
           ((FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_App
                  ((FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_FVar
                         (FStar_Reflection_V2_Builtins.pack_fv
                            ["FStar"; "Pervasives"; "Native"; "Mktuple2"]))),
                    (a, FStar_Reflection_V2_Data.Q_Explicit)))),
             (b, FStar_Reflection_V2_Data.Q_Explicit)))
let (get_inductive_typ :
  Prims.string ->
    (FStar_Tactics_NamedView.sigelt_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (18)) (Prims.of_int (10)) (Prims.of_int (18))
               (Prims.of_int (20)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (18)) (Prims.of_int (23)) (Prims.of_int (27))
               (Prims.of_int (48)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.top_env ()))
      (fun uu___ ->
         (fun e ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                          (Prims.of_int (19)) (Prims.of_int (11))
                          (Prims.of_int (19)) (Prims.of_int (39)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                          (Prims.of_int (20)) (Prims.of_int (2))
                          (Prims.of_int (27)) (Prims.of_int (48)))))
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       FStar_Reflection_V2_Builtins.lookup_typ e
                         (FStar_Reflection_V2_Builtins.explode_qn nm)))
                 (fun uu___ ->
                    (fun se ->
                       match se with
                       | FStar_Pervasives_Native.None ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_V2_Derived.fail
                                   "ctors_of_typ: type not found"))
                       | FStar_Pervasives_Native.Some se1 ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.TypeRepr.fst"
                                            (Prims.of_int (23))
                                            (Prims.of_int (14))
                                            (Prims.of_int (23))
                                            (Prims.of_int (31)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.TypeRepr.fst"
                                            (Prims.of_int (24))
                                            (Prims.of_int (4))
                                            (Prims.of_int (27))
                                            (Prims.of_int (48)))))
                                   (Obj.magic
                                      (FStar_Tactics_NamedView.inspect_sigelt
                                         se1))
                                   (fun sev ->
                                      if
                                        FStar_Tactics_NamedView.uu___is_Sg_Inductive
                                          sev
                                      then
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___ -> sev)
                                      else
                                        FStar_Tactics_V2_Derived.fail
                                          "ctors_of_typ: not an inductive type"))))
                      uu___))) uu___)
let (alg_ctor :
  FStar_Reflection_Types.typ ->
    (FStar_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ty ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (30)) (Prims.of_int (15)) (Prims.of_int (30))
               (Prims.of_int (29)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (29)) (Prims.of_int (35)) (Prims.of_int (31))
               (Prims.of_int (67)))))
      (Obj.magic (FStar_Tactics_V2_SyntaxHelpers.collect_arr ty))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | (tys, c) ->
                Obj.magic
                  (FStar_Tactics_Util.fold_right
                     (fun uu___2 ->
                        fun uu___1 ->
                          (fun ty1 ->
                             fun acc ->
                               Obj.magic
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 -> tuple2_ ty1 acc))) uu___2
                            uu___1) tys unitt_)) uu___)
let (generate_repr_typ :
  FStar_Tactics_NamedView.binders ->
    FStar_Reflection_V2_Data.ctor Prims.list ->
      (FStar_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun params ->
    fun ctors ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                 (Prims.of_int (35)) (Prims.of_int (18)) (Prims.of_int (35))
                 (Prims.of_int (61)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                 (Prims.of_int (35)) (Prims.of_int (64)) (Prims.of_int (38))
                 (Prims.of_int (17)))))
        (Obj.magic
           (FStar_Tactics_Util.map
              (fun uu___ -> match uu___ with | (uu___1, ty) -> alg_ctor ty)
              ctors))
        (fun uu___ ->
           (fun ctor_typs ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                            (Prims.of_int (37)) (Prims.of_int (4))
                            (Prims.of_int (37)) (Prims.of_int (67)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                            (Prims.of_int (36)) (Prims.of_int (6))
                            (Prims.of_int (36)) (Prims.of_int (21)))))
                   (Obj.magic
                      (FStar_Tactics_Util.fold_right
                         (fun uu___1 ->
                            fun uu___ ->
                              (fun ty ->
                                 fun acc ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___ -> either_ ty acc)))
                                uu___1 uu___) ctor_typs empty_))
                   (fun alternative_typ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ -> alternative_typ)))) uu___)
let _ =
  FStar_Tactics_Native.register_tactic
    "FStar.Tactics.TypeRepr.generate_repr_typ" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.TypeRepr.generate_repr_typ (plugin)"
               (FStar_Tactics_Native.from_tactic_2 generate_repr_typ)
               (FStar_Syntax_Embeddings.e_list
                  FStar_Tactics_NamedView.e_binder)
               (FStar_Syntax_Embeddings.e_list
                  (FStar_Syntax_Embeddings.e_tuple2
                     (FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string)
                     FStar_Reflection_V2_Embeddings.e_term))
               FStar_Reflection_V2_Embeddings.e_term psc ncb us args)
let (generate_down : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (43)) (Prims.of_int (10)) (Prims.of_int (43))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (43)) (Prims.of_int (21)) (Prims.of_int (52))
               (Prims.of_int (3)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.intro ()))
      (fun uu___1 ->
         (fun b ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                          (Prims.of_int (44)) (Prims.of_int (14))
                          (Prims.of_int (44)) (Prims.of_int (26)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                          (Prims.of_int (45)) (Prims.of_int (2))
                          (Prims.of_int (52)) (Prims.of_int (3)))))
                 (Obj.magic
                    (FStar_Tactics_V2_Builtins.t_destruct
                       (FStar_Tactics_V2_SyntaxCoercions.binding_to_term b)))
                 (fun uu___1 ->
                    (fun cases ->
                       Obj.magic
                         (FStar_Tactics_Util.iteri
                            (fun i ->
                               fun uu___1 ->
                                 match uu___1 with
                                 | (c, n) ->
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.TypeRepr.fst"
                                                (Prims.of_int (46))
                                                (Prims.of_int (13))
                                                (Prims.of_int (46))
                                                (Prims.of_int (42)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.TypeRepr.fst"
                                                (Prims.of_int (46))
                                                (Prims.of_int (45))
                                                (Prims.of_int (51))
                                                (Prims.of_int (13)))))
                                       (Obj.magic
                                          (FStar_Tactics_Util.repeatn n
                                             (fun uu___2 ->
                                                FStar_Tactics_V2_Builtins.intro
                                                  ())))
                                       (fun uu___2 ->
                                          (fun bs ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.TypeRepr.fst"
                                                           (Prims.of_int (47))
                                                           (Prims.of_int (16))
                                                           (Prims.of_int (47))
                                                           (Prims.of_int (24)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.TypeRepr.fst"
                                                           (Prims.of_int (47))
                                                           (Prims.of_int (27))
                                                           (Prims.of_int (51))
                                                           (Prims.of_int (13)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_V2_Builtins.intro
                                                        ()))
                                                  (fun uu___2 ->
                                                     (fun _b_eq ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (80)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (13)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Util.fold_right
                                                                   (fun
                                                                    uu___3 ->
                                                                    fun
                                                                    uu___2 ->
                                                                    (fun b1
                                                                    ->
                                                                    fun acc
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    mktuple2_
                                                                    (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                                    b1) acc)))
                                                                    uu___3
                                                                    uu___2)
                                                                   bs unitv_))
                                                             (fun uu___2 ->
                                                                (fun sol ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.repeatn
                                                                    i
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_V2_Derived.apply
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Inr"]))))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Inl"])))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.exact
                                                                    sol))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                  uu___2)))
                                                       uu___2))) uu___2))
                            cases)) uu___1))) uu___1)
let _ =
  FStar_Tactics_Native.register_tactic "FStar.Tactics.TypeRepr.generate_down"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.TypeRepr.generate_down (plugin)"
               (FStar_Tactics_Native.from_tactic_1 generate_down)
               FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
               psc ncb us args)
let rec (get_apply_tuple :
  FStar_Tactics_NamedView.binding ->
    (FStar_Tactics_NamedView.binding Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (55)) (Prims.of_int (17)) (Prims.of_int (55))
               (Prims.of_int (35)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (54)) (Prims.of_int (58)) (Prims.of_int (74))
               (Prims.of_int (69)))))
      (Obj.magic
         (FStar_Tactics_V2_SyntaxHelpers.collect_app
            b.FStar_Reflection_V2_Data.sort3))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | (hd, args) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                              (Prims.of_int (56)) (Prims.of_int (8))
                              (Prims.of_int (56)) (Prims.of_int (24)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                              (Prims.of_int (56)) (Prims.of_int (2))
                              (Prims.of_int (74)) (Prims.of_int (69)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.TypeRepr.fst"
                                    (Prims.of_int (56)) (Prims.of_int (8))
                                    (Prims.of_int (56)) (Prims.of_int (18)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.TypeRepr.fst"
                                    (Prims.of_int (56)) (Prims.of_int (8))
                                    (Prims.of_int (56)) (Prims.of_int (24)))))
                           (Obj.magic (FStar_Tactics_NamedView.inspect hd))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 -> (uu___1, args)))))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           match uu___1 with
                           | (FStar_Tactics_NamedView.Tv_UInst (fv, uu___2),
                              b1::b2::[]) ->
                               Obj.magic
                                 (Obj.repr
                                    (if
                                       (FStar_Reflection_V2_Builtins.inspect_fv
                                          fv)
                                         =
                                         ["FStar";
                                         "Pervasives";
                                         "Native";
                                         "tuple2"]
                                     then
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.TypeRepr.fst"
                                                  (Prims.of_int (60))
                                                  (Prims.of_int (18))
                                                  (Prims.of_int (60))
                                                  (Prims.of_int (30)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.TypeRepr.fst"
                                                  (Prims.of_int (61))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (65))
                                                  (Prims.of_int (30)))))
                                         (Obj.magic
                                            (FStar_Tactics_V2_Builtins.t_destruct
                                               (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                  b)))
                                         (fun uu___3 ->
                                            (fun cases ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.TypeRepr.fst"
                                                             (Prims.of_int (61))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (61))
                                                             (Prims.of_int (136)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.TypeRepr.fst"
                                                             (Prims.of_int (61))
                                                             (Prims.of_int (137))
                                                             (Prims.of_int (65))
                                                             (Prims.of_int (30)))))
                                                    (Obj.magic
                                                       (FStar_Tactics_V2_Derived.guard
                                                          ((((FStar_List_Tot_Base.length
                                                                cases)
                                                               =
                                                               Prims.int_one)
                                                              &&
                                                              ((FStar_Reflection_V2_Builtins.inspect_fv
                                                                  (FStar_Pervasives_Native.fst
                                                                    (FStar_List_Tot_Base.hd
                                                                    cases)))
                                                                 =
                                                                 ["FStar";
                                                                 "Pervasives";
                                                                 "Native";
                                                                 "Mktuple2"]))
                                                             &&
                                                             ((FStar_Pervasives_Native.snd
                                                                 (FStar_List_Tot_Base.hd
                                                                    cases))
                                                                =
                                                                (Prims.of_int (2))))))
                                                    (fun uu___3 ->
                                                       (fun uu___3 ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (23)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                               (Obj.magic
                                                                  (FStar_Tactics_V2_Builtins.intro
                                                                    ()))
                                                               (fun uu___4 ->
                                                                  (fun b11 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.intro
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun b21
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.intro
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun _eq
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (get_apply_tuple
                                                                    b21))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    b11 ::
                                                                    uu___4))))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                         uu___3))) uu___3)
                                     else
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.TypeRepr.fst"
                                                  (Prims.of_int (67))
                                                  (Prims.of_int (11))
                                                  (Prims.of_int (67))
                                                  (Prims.of_int (71)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.TypeRepr.fst"
                                                  (Prims.of_int (67))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (67))
                                                  (Prims.of_int (71)))))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.TypeRepr.fst"
                                                        (Prims.of_int (67))
                                                        (Prims.of_int (49))
                                                        (Prims.of_int (67))
                                                        (Prims.of_int (70)))))
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
                                                     b.FStar_Reflection_V2_Data.sort3))
                                               (fun uu___4 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___5 ->
                                                       Prims.strcat
                                                         "unexpected term in apply_tuple: "
                                                         uu___4))))
                                         (fun uu___4 ->
                                            FStar_Tactics_V2_Derived.fail
                                              uu___4)))
                           | (FStar_Tactics_NamedView.Tv_FVar fv, b1::b2::[])
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (if
                                       (FStar_Reflection_V2_Builtins.inspect_fv
                                          fv)
                                         =
                                         ["FStar";
                                         "Pervasives";
                                         "Native";
                                         "tuple2"]
                                     then
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.TypeRepr.fst"
                                                  (Prims.of_int (60))
                                                  (Prims.of_int (18))
                                                  (Prims.of_int (60))
                                                  (Prims.of_int (30)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.TypeRepr.fst"
                                                  (Prims.of_int (61))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (65))
                                                  (Prims.of_int (30)))))
                                         (Obj.magic
                                            (FStar_Tactics_V2_Builtins.t_destruct
                                               (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                  b)))
                                         (fun uu___2 ->
                                            (fun cases ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.TypeRepr.fst"
                                                             (Prims.of_int (61))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (61))
                                                             (Prims.of_int (136)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.TypeRepr.fst"
                                                             (Prims.of_int (61))
                                                             (Prims.of_int (137))
                                                             (Prims.of_int (65))
                                                             (Prims.of_int (30)))))
                                                    (Obj.magic
                                                       (FStar_Tactics_V2_Derived.guard
                                                          ((((FStar_List_Tot_Base.length
                                                                cases)
                                                               =
                                                               Prims.int_one)
                                                              &&
                                                              ((FStar_Reflection_V2_Builtins.inspect_fv
                                                                  (FStar_Pervasives_Native.fst
                                                                    (FStar_List_Tot_Base.hd
                                                                    cases)))
                                                                 =
                                                                 ["FStar";
                                                                 "Pervasives";
                                                                 "Native";
                                                                 "Mktuple2"]))
                                                             &&
                                                             ((FStar_Pervasives_Native.snd
                                                                 (FStar_List_Tot_Base.hd
                                                                    cases))
                                                                =
                                                                (Prims.of_int (2))))))
                                                    (fun uu___2 ->
                                                       (fun uu___2 ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (23)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                               (Obj.magic
                                                                  (FStar_Tactics_V2_Builtins.intro
                                                                    ()))
                                                               (fun uu___3 ->
                                                                  (fun b11 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.intro
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun b21
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.intro
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun _eq
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (get_apply_tuple
                                                                    b21))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    b11 ::
                                                                    uu___3))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                         uu___2))) uu___2)
                                     else
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.TypeRepr.fst"
                                                  (Prims.of_int (67))
                                                  (Prims.of_int (11))
                                                  (Prims.of_int (67))
                                                  (Prims.of_int (71)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.TypeRepr.fst"
                                                  (Prims.of_int (67))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (67))
                                                  (Prims.of_int (71)))))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.TypeRepr.fst"
                                                        (Prims.of_int (67))
                                                        (Prims.of_int (49))
                                                        (Prims.of_int (67))
                                                        (Prims.of_int (70)))))
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
                                                     b.FStar_Reflection_V2_Data.sort3))
                                               (fun uu___3 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___4 ->
                                                       Prims.strcat
                                                         "unexpected term in apply_tuple: "
                                                         uu___3))))
                                         (fun uu___3 ->
                                            FStar_Tactics_V2_Derived.fail
                                              uu___3)))
                           | (FStar_Tactics_NamedView.Tv_FVar fv, []) ->
                               Obj.magic
                                 (Obj.repr
                                    (if
                                       (FStar_Reflection_V2_Builtins.inspect_fv
                                          fv)
                                         = ["Prims"; "unit"]
                                     then
                                       Obj.repr
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 -> []))
                                     else
                                       Obj.repr
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.TypeRepr.fst"
                                                     (Prims.of_int (72))
                                                     (Prims.of_int (11))
                                                     (Prims.of_int (72))
                                                     (Prims.of_int (71)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.TypeRepr.fst"
                                                     (Prims.of_int (72))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (72))
                                                     (Prims.of_int (71)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.TypeRepr.fst"
                                                           (Prims.of_int (72))
                                                           (Prims.of_int (49))
                                                           (Prims.of_int (72))
                                                           (Prims.of_int (70)))))
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
                                                        b.FStar_Reflection_V2_Data.sort3))
                                                  (fun uu___3 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___4 ->
                                                          Prims.strcat
                                                            "unexpected term in apply_tuple: "
                                                            uu___3))))
                                            (fun uu___3 ->
                                               FStar_Tactics_V2_Derived.fail
                                                 uu___3))))
                           | uu___2 ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.TypeRepr.fst"
                                                (Prims.of_int (74))
                                                (Prims.of_int (9))
                                                (Prims.of_int (74))
                                                (Prims.of_int (69)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.TypeRepr.fst"
                                                (Prims.of_int (74))
                                                (Prims.of_int (4))
                                                (Prims.of_int (74))
                                                (Prims.of_int (69)))))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.TypeRepr.fst"
                                                      (Prims.of_int (74))
                                                      (Prims.of_int (47))
                                                      (Prims.of_int (74))
                                                      (Prims.of_int (68)))))
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
                                                   b.FStar_Reflection_V2_Data.sort3))
                                             (fun uu___3 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___4 ->
                                                     Prims.strcat
                                                       "unexpected term in apply_tuple: "
                                                       uu___3))))
                                       (fun uu___3 ->
                                          FStar_Tactics_V2_Derived.fail
                                            uu___3)))) uu___1))) uu___)
let rec (generate_up_aux :
  FStar_Reflection_V2_Data.ctor Prims.list ->
    FStar_Tactics_NamedView.binding ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ctors ->
    fun b ->
      match ctors with
      | [] ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                     (Prims.of_int (82)) (Prims.of_int (4))
                     (Prims.of_int (82)) (Prims.of_int (23)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                     (Prims.of_int (83)) (Prims.of_int (4))
                     (Prims.of_int (83)) (Prims.of_int (11)))))
            (Obj.magic
               (FStar_Tactics_V2_Derived.apply
                  (FStar_Reflection_V2_Builtins.pack_ln
                     (FStar_Reflection_V2_Data.Tv_FVar
                        (FStar_Reflection_V2_Builtins.pack_fv
                           ["FStar"; "Tactics"; "TypeRepr"; "empty_elim"])))))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_V2_Derived.exact
                       (FStar_Tactics_V2_SyntaxCoercions.binding_to_term b)))
                 uu___)
      | c::cs ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                     (Prims.of_int (85)) (Prims.of_int (16))
                     (Prims.of_int (85)) (Prims.of_int (28)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                     (Prims.of_int (86)) (Prims.of_int (4))
                     (Prims.of_int (99)) (Prims.of_int (24)))))
            (Obj.magic
               (FStar_Tactics_V2_Builtins.t_destruct
                  (FStar_Tactics_V2_SyntaxCoercions.binding_to_term b)))
            (fun uu___ ->
               (fun cases ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.TypeRepr.fst"
                                (Prims.of_int (86)) (Prims.of_int (4))
                                (Prims.of_int (87)) (Prims.of_int (49)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.TypeRepr.fst"
                                (Prims.of_int (88)) (Prims.of_int (4))
                                (Prims.of_int (99)) (Prims.of_int (24)))))
                       (if
                          (FStar_List_Tot_Base.length cases) <>
                            (Prims.of_int (2))
                        then
                          FStar_Tactics_V2_Derived.fail
                            "generate_up_aux: expected Inl/Inr???"
                        else
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> ()))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.TypeRepr.fst"
                                           (Prims.of_int (88))
                                           (Prims.of_int (4))
                                           (Prims.of_int (96))
                                           (Prims.of_int (5)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.TypeRepr.fst"
                                           (Prims.of_int (96))
                                           (Prims.of_int (6))
                                           (Prims.of_int (99))
                                           (Prims.of_int (24)))))
                                  (Obj.magic
                                     (FStar_Tactics_V2_Derived.focus
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.TypeRepr.fst"
                                                      (Prims.of_int (89))
                                                      (Prims.of_int (15))
                                                      (Prims.of_int (89))
                                                      (Prims.of_int (23)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.TypeRepr.fst"
                                                      (Prims.of_int (89))
                                                      (Prims.of_int (26))
                                                      (Prims.of_int (95))
                                                      (Prims.of_int (11)))))
                                             (Obj.magic
                                                (FStar_Tactics_V2_Builtins.intro
                                                   ()))
                                             (fun uu___2 ->
                                                (fun b' ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.TypeRepr.fst"
                                                                 (Prims.of_int (90))
                                                                 (Prims.of_int (16))
                                                                 (Prims.of_int (90))
                                                                 (Prims.of_int (24)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.TypeRepr.fst"
                                                                 (Prims.of_int (90))
                                                                 (Prims.of_int (27))
                                                                 (Prims.of_int (95))
                                                                 (Prims.of_int (11)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_V2_Builtins.intro
                                                              ()))
                                                        (fun uu___2 ->
                                                           (fun _eq ->
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (24)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (11)))))
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives_Native.fst
                                                                    c))
                                                                   (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    c_name ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (get_apply_tuple
                                                                    b'))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun args
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply
                                                                    (FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    c_name)))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.iter
                                                                    (fun b1
                                                                    ->
                                                                    FStar_Tactics_V2_Derived.exact
                                                                    (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                                    b1)) args))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.qed
                                                                    ()))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                             uu___2))) uu___2))))
                                  (fun uu___1 ->
                                     (fun uu___1 ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.TypeRepr.fst"
                                                      (Prims.of_int (97))
                                                      (Prims.of_int (12))
                                                      (Prims.of_int (97))
                                                      (Prims.of_int (20)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.TypeRepr.fst"
                                                      (Prims.of_int (97))
                                                      (Prims.of_int (23))
                                                      (Prims.of_int (99))
                                                      (Prims.of_int (24)))))
                                             (Obj.magic
                                                (FStar_Tactics_V2_Builtins.intro
                                                   ()))
                                             (fun uu___2 ->
                                                (fun b1 ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.TypeRepr.fst"
                                                                 (Prims.of_int (98))
                                                                 (Prims.of_int (14))
                                                                 (Prims.of_int (98))
                                                                 (Prims.of_int (22)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.TypeRepr.fst"
                                                                 (Prims.of_int (99))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (99))
                                                                 (Prims.of_int (24)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_V2_Builtins.intro
                                                              ()))
                                                        (fun uu___2 ->
                                                           (fun _eq ->
                                                              Obj.magic
                                                                (generate_up_aux
                                                                   cs b1))
                                                             uu___2))) uu___2)))
                                       uu___1))) uu___))) uu___)
let (generate_up :
  Prims.string -> unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun nm ->
    fun uu___ ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                 (Prims.of_int (104)) (Prims.of_int (29))
                 (Prims.of_int (104)) (Prims.of_int (49)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                 (Prims.of_int (103)) (Prims.of_int (43))
                 (Prims.of_int (106)) (Prims.of_int (25)))))
        (Obj.magic (get_inductive_typ nm))
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | FStar_Tactics_NamedView.Sg_Inductive
                  { FStar_Tactics_NamedView.nm = uu___2;
                    FStar_Tactics_NamedView.univs1 = uu___3;
                    FStar_Tactics_NamedView.params = uu___4;
                    FStar_Tactics_NamedView.typ = uu___5;
                    FStar_Tactics_NamedView.ctors = ctors;_}
                  ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.TypeRepr.fst"
                                (Prims.of_int (105)) (Prims.of_int (10))
                                (Prims.of_int (105)) (Prims.of_int (18)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.TypeRepr.fst"
                                (Prims.of_int (106)) (Prims.of_int (2))
                                (Prims.of_int (106)) (Prims.of_int (25)))))
                       (Obj.magic (FStar_Tactics_V2_Builtins.intro ()))
                       (fun uu___6 ->
                          (fun b -> Obj.magic (generate_up_aux ctors b))
                            uu___6))) uu___1)
let _ =
  FStar_Tactics_Native.register_tactic "FStar.Tactics.TypeRepr.generate_up"
    (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.TypeRepr.generate_up (plugin)"
               (FStar_Tactics_Native.from_tactic_2 generate_up)
               FStar_Syntax_Embeddings.e_string
               FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
               psc ncb us args)
let (make_implicits :
  FStar_Tactics_NamedView.binders -> FStar_Tactics_NamedView.binders) =
  fun bs ->
    FStar_List_Tot_Base.map
      (fun b ->
         match b.FStar_Tactics_NamedView.qual with
         | FStar_Reflection_V2_Data.Q_Explicit ->
             {
               FStar_Tactics_NamedView.uniq =
                 (b.FStar_Tactics_NamedView.uniq);
               FStar_Tactics_NamedView.ppname =
                 (b.FStar_Tactics_NamedView.ppname);
               FStar_Tactics_NamedView.sort =
                 (b.FStar_Tactics_NamedView.sort);
               FStar_Tactics_NamedView.qual =
                 FStar_Reflection_V2_Data.Q_Implicit;
               FStar_Tactics_NamedView.attrs =
                 (b.FStar_Tactics_NamedView.attrs)
             }
         | uu___ -> b) bs
let (binder_to_argv :
  FStar_Tactics_NamedView.binder -> FStar_Reflection_V2_Data.argv) =
  fun b ->
    ((FStar_Tactics_V2_SyntaxCoercions.binder_to_term b),
      (b.FStar_Tactics_NamedView.qual))
let (generate_all :
  FStar_Reflection_Types.name ->
    FStar_Tactics_NamedView.binders ->
      FStar_Reflection_V2_Data.ctor Prims.list ->
        (FStar_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    fun params ->
      fun ctors ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                   (Prims.of_int (119)) (Prims.of_int (17))
                   (Prims.of_int (119)) (Prims.of_int (38)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                   (Prims.of_int (119)) (Prims.of_int (41))
                   (Prims.of_int (165)) (Prims.of_int (27)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> make_implicits params))
          (fun uu___ ->
             (fun params_i ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                              (Prims.of_int (120)) (Prims.of_int (15))
                              (Prims.of_int (120)) (Prims.of_int (88)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                              (Prims.of_int (120)) (Prims.of_int (91))
                              (Prims.of_int (165)) (Prims.of_int (27)))))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           FStar_Reflection_V2_Derived.mk_app
                             (FStar_Tactics_NamedView.pack
                                (FStar_Tactics_NamedView.Tv_FVar
                                   (FStar_Reflection_V2_Builtins.pack_fv nm)))
                             (FStar_List_Tot_Base.map binder_to_argv params)))
                     (fun uu___ ->
                        (fun t ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.TypeRepr.fst"
                                         (Prims.of_int (121))
                                         (Prims.of_int (15))
                                         (Prims.of_int (121))
                                         (Prims.of_int (45)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.TypeRepr.fst"
                                         (Prims.of_int (121))
                                         (Prims.of_int (48))
                                         (Prims.of_int (165))
                                         (Prims.of_int (27)))))
                                (Obj.magic (generate_repr_typ params ctors))
                                (fun uu___ ->
                                   (fun t_repr ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.TypeRepr.fst"
                                                    (Prims.of_int (122))
                                                    (Prims.of_int (16))
                                                    (Prims.of_int (130))
                                                    (Prims.of_int (3)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.TypeRepr.fst"
                                                    (Prims.of_int (131))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (165))
                                                    (Prims.of_int (27)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.TypeRepr.fst"
                                                          (Prims.of_int (122))
                                                          (Prims.of_int (31))
                                                          (Prims.of_int (130))
                                                          (Prims.of_int (3)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.TypeRepr.fst"
                                                          (Prims.of_int (122))
                                                          (Prims.of_int (16))
                                                          (Prims.of_int (130))
                                                          (Prims.of_int (3)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.TypeRepr.fst"
                                                                (Prims.of_int (123))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (129))
                                                                (Prims.of_int (6)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.TypeRepr.fst"
                                                                (Prims.of_int (122))
                                                                (Prims.of_int (31))
                                                                (Prims.of_int (130))
                                                                (Prims.of_int (3)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (6)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (6)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (36)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (6)))))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_SyntaxHelpers.mk_arr
                                                                    params
                                                                    (FStar_Reflection_V2_Data.C_Total
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Type
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    FStar_Reflection_V2_Data.Uv_Unk))))))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun
                                                                    uu___ ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.mk_abs
                                                                    params
                                                                    t_repr))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    {
                                                                    FStar_Tactics_NamedView.lb_fv
                                                                    =
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    (add_suffix
                                                                    "_repr"
                                                                    nm));
                                                                    FStar_Tactics_NamedView.lb_us
                                                                    = [];
                                                                    FStar_Tactics_NamedView.lb_typ
                                                                    = uu___;
                                                                    FStar_Tactics_NamedView.lb_def
                                                                    = uu___1
                                                                    }))))
                                                                    uu___)))
                                                                   (fun uu___
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    [uu___]))))
                                                             (fun uu___ ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___1
                                                                    ->
                                                                    {
                                                                    FStar_Tactics_NamedView.isrec
                                                                    = false;
                                                                    FStar_Tactics_NamedView.lbs
                                                                    = uu___
                                                                    }))))
                                                       (fun uu___ ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___1 ->
                                                               FStar_Tactics_NamedView.Sg_Let
                                                                 uu___))))
                                                 (fun uu___ ->
                                                    (fun uu___ ->
                                                       Obj.magic
                                                         (FStar_Tactics_NamedView.pack_sigelt
                                                            uu___)) uu___)))
                                           (fun uu___ ->
                                              (fun se_repr ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.TypeRepr.fst"
                                                               (Prims.of_int (134))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (134))
                                                               (Prims.of_int (30)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.TypeRepr.fst"
                                                               (Prims.of_int (135))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (165))
                                                               (Prims.of_int (27)))))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___ ->
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
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "TypeRepr";
                                                                    "generate_down"]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    FStar_Reflection_V2_Data.C_Unit)),
                                                                    FStar_Reflection_V2_Data.Q_Explicit))))))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))))
                                                      (fun uu___ ->
                                                         (fun down_def ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (41)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (27)))))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_V2_Derived.mk_abs
                                                                    params_i
                                                                    down_def))
                                                                 (fun uu___
                                                                    ->
                                                                    (fun
                                                                    down_def1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.fresh_binder
                                                                    t))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun b ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (8)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (8)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
                                                                    params_i
                                                                    (FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_Arrow
                                                                    (b,
                                                                    (FStar_Reflection_V2_Data.C_Total
                                                                    t_repr))))))
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    {
                                                                    FStar_Tactics_NamedView.lb_fv
                                                                    =
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    (add_suffix
                                                                    "_down"
                                                                    nm));
                                                                    FStar_Tactics_NamedView.lb_us
                                                                    = [];
                                                                    FStar_Tactics_NamedView.lb_typ
                                                                    = uu___;
                                                                    FStar_Tactics_NamedView.lb_def
                                                                    =
                                                                    down_def1
                                                                    }))))
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    [uu___]))))
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    {
                                                                    FStar_Tactics_NamedView.isrec
                                                                    = false;
                                                                    FStar_Tactics_NamedView.lbs
                                                                    = uu___
                                                                    }))))
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_NamedView.Sg_Let
                                                                    uu___))))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun
                                                                    uu___ ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_NamedView.pack_sigelt
                                                                    uu___))
                                                                    uu___)))
                                                                    uu___)))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun
                                                                    se_down
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
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
                                                                    "TypeRepr";
                                                                    "generate_up"]))),
                                                                    ((FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_Const
                                                                    (FStar_Reflection_V2_Data.C_String
                                                                    (FStar_Reflection_V2_Builtins.implode_qn
                                                                    nm)))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    FStar_Reflection_V2_Data.C_Unit)),
                                                                    FStar_Reflection_V2_Data.Q_Explicit))))))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun
                                                                    up_def ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.mk_abs
                                                                    params_i
                                                                    up_def))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun
                                                                    up_def1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.fresh_binder
                                                                    t_repr))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun b ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (8)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (8)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
                                                                    params_i
                                                                    (FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_Arrow
                                                                    (b,
                                                                    (FStar_Reflection_V2_Data.C_Total
                                                                    t))))))
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    {
                                                                    FStar_Tactics_NamedView.lb_fv
                                                                    =
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    (add_suffix
                                                                    "_up" nm));
                                                                    FStar_Tactics_NamedView.lb_us
                                                                    = [];
                                                                    FStar_Tactics_NamedView.lb_typ
                                                                    = uu___;
                                                                    FStar_Tactics_NamedView.lb_def
                                                                    = up_def1
                                                                    }))))
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    [uu___]))))
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    {
                                                                    FStar_Tactics_NamedView.isrec
                                                                    = false;
                                                                    FStar_Tactics_NamedView.lbs
                                                                    = uu___
                                                                    }))))
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_NamedView.Sg_Let
                                                                    uu___))))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun
                                                                    uu___ ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_NamedView.pack_sigelt
                                                                    uu___))
                                                                    uu___)))
                                                                    uu___)))
                                                                    (fun
                                                                    se_up ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    [se_repr;
                                                                    se_down;
                                                                    se_up]))))
                                                                    uu___)))
                                                                    uu___)))
                                                                    uu___)))
                                                                    uu___)))
                                                           uu___))) uu___)))
                                     uu___))) uu___))) uu___)
let (entry :
  Prims.string ->
    (FStar_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (169)) (Prims.of_int (41)) (Prims.of_int (169))
               (Prims.of_int (61)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (168)) (Prims.of_int (37)) (Prims.of_int (170))
               (Prims.of_int (30))))) (Obj.magic (get_inductive_typ nm))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Tactics_NamedView.Sg_Inductive
                { FStar_Tactics_NamedView.nm = nm1;
                  FStar_Tactics_NamedView.univs1 = uu___1;
                  FStar_Tactics_NamedView.params = params;
                  FStar_Tactics_NamedView.typ = uu___2;
                  FStar_Tactics_NamedView.ctors = ctors;_}
                -> Obj.magic (generate_all nm1 params ctors)) uu___)
let _ =
  FStar_Tactics_Native.register_tactic "FStar.Tactics.TypeRepr.entry"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.TypeRepr.entry (plugin)"
               (FStar_Tactics_Native.from_tactic_1 entry)
               FStar_Syntax_Embeddings.e_string
               (FStar_Syntax_Embeddings.e_list
                  FStar_Reflection_V2_Embeddings.e_sigelt) psc ncb us args)