open Prims
let rec (collect_arr' :
  FStar_Tactics_NamedView.binder Prims.list ->
    FStar_Tactics_NamedView.comp ->
      ((FStar_Tactics_NamedView.binder Prims.list *
         FStar_Tactics_NamedView.comp),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun bs ->
         fun c ->
           match c with
           | FStarC_Reflection_V2_Data.C_Total t ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = FStar_Tactics_NamedView.inspect t in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.SyntaxHelpers.fst"
                                (Prims.of_int (15)) (Prims.of_int (20))
                                (Prims.of_int (15)) (Prims.of_int (29)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.SyntaxHelpers.fst"
                                (Prims.of_int (15)) (Prims.of_int (14))
                                (Prims.of_int (19)) (Prims.of_int (19)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             match uu___1 with
                             | FStar_Tactics_NamedView.Tv_Arrow (b, c1) ->
                                 Obj.magic
                                   (Obj.repr (collect_arr' (b :: bs) c1))
                             | uu___2 ->
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 -> (bs, c))))) uu___1)))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 -> (bs, c))))) uu___1 uu___
let (collect_arr_bs :
  FStarC_Reflection_Types.typ ->
    ((FStar_Tactics_NamedView.binder Prims.list *
       FStar_Tactics_NamedView.comp),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = collect_arr' [] (FStarC_Reflection_V2_Data.C_Total t) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
               (Prims.of_int (25)) (Prims.of_int (18)) (Prims.of_int (25))
               (Prims.of_int (45)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
               (Prims.of_int (24)) (Prims.of_int (22)) (Prims.of_int (26))
               (Prims.of_int (29))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              match uu___1 with
              | (bs, c) -> ((FStar_List_Tot_Base.rev bs), c)))
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.collect_arr_bs" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.SyntaxHelpers.collect_arr_bs (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 collect_arr_bs)
               FStarC_Reflection_V2_Embeddings.e_term
               (FStarC_Syntax_Embeddings.e_tuple2
                  (FStarC_Syntax_Embeddings.e_list
                     FStar_Tactics_NamedView.e_binder)
                  FStarC_Reflection_V2_Embeddings.e_comp_view) psc ncb us
               args)
let (collect_arr :
  FStarC_Reflection_Types.typ ->
    ((FStarC_Reflection_Types.typ Prims.list * FStar_Tactics_NamedView.comp),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = collect_arr' [] (FStarC_Reflection_V2_Data.C_Total t) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
               (Prims.of_int (29)) (Prims.of_int (18)) (Prims.of_int (29))
               (Prims.of_int (45)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
               (Prims.of_int (28)) (Prims.of_int (19)) (Prims.of_int (31))
               (Prims.of_int (29))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              match uu___1 with
              | (bs, c) ->
                  ((FStar_List_Tot_Base.rev
                      (FStar_List_Tot_Base.map
                         (fun b -> b.FStar_Tactics_NamedView.sort) bs)), c)))
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.collect_arr" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.SyntaxHelpers.collect_arr (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 collect_arr)
               FStarC_Reflection_V2_Embeddings.e_term
               (FStarC_Syntax_Embeddings.e_tuple2
                  (FStarC_Syntax_Embeddings.e_list
                     FStarC_Reflection_V2_Embeddings.e_term)
                  FStarC_Reflection_V2_Embeddings.e_comp_view) psc ncb us
               args)
let rec (collect_abs' :
  FStar_Tactics_NamedView.binder Prims.list ->
    FStar_Tactics_NamedView.term ->
      ((FStar_Tactics_NamedView.binder Prims.list *
         FStar_Tactics_NamedView.term),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bs ->
    fun t ->
      let uu___ = FStar_Tactics_NamedView.inspect t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
                 (Prims.of_int (35)) (Prims.of_int (10)) (Prims.of_int (35))
                 (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
                 (Prims.of_int (35)) (Prims.of_int (4)) (Prims.of_int (38))
                 (Prims.of_int (18))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | FStar_Tactics_NamedView.Tv_Abs (b, t') ->
                  Obj.magic (Obj.repr (collect_abs' (b :: bs) t'))
              | uu___2 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> (bs, t))))) uu___1)
let (collect_abs :
  FStar_Tactics_NamedView.term ->
    ((FStar_Tactics_NamedView.binder Prims.list *
       FStar_Tactics_NamedView.term),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = collect_abs' [] t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
               (Prims.of_int (41)) (Prims.of_int (19)) (Prims.of_int (41))
               (Prims.of_int (36)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
               (Prims.of_int (40)) (Prims.of_int (19)) (Prims.of_int (42))
               (Prims.of_int (30))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              match uu___1 with
              | (bs, t') -> ((FStar_List_Tot_Base.rev bs), t')))
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.collect_abs" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.SyntaxHelpers.collect_abs (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 collect_abs)
               FStarC_Reflection_V2_Embeddings.e_term
               (FStarC_Syntax_Embeddings.e_tuple2
                  (FStarC_Syntax_Embeddings.e_list
                     FStar_Tactics_NamedView.e_binder)
                  FStarC_Reflection_V2_Embeddings.e_term) psc ncb us args)
let fail : 'a . Prims.string -> ('a, unit) FStar_Tactics_Effect.tac_repr =
  fun uu___ ->
    (fun m ->
       Obj.magic
         (FStar_Tactics_Effect.raise
            (FStarC_Tactics_Common.TacticFailure
               ((FStarC_Errors_Msg.mkmsg m), FStar_Pervasives_Native.None))))
      uu___
let rec (mk_arr :
  FStar_Tactics_NamedView.binder Prims.list ->
    FStar_Tactics_NamedView.comp ->
      (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun bs ->
         fun cod ->
           match bs with
           | [] -> Obj.magic (Obj.repr (fail "mk_arr, empty binders"))
           | b::[] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          FStar_Tactics_NamedView.pack
                            (FStar_Tactics_NamedView.Tv_Arrow (b, cod)))))
           | b::bs1 ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       let uu___1 =
                         let uu___2 = mk_arr bs1 cod in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V2.SyntaxHelpers.fst"
                                    (Prims.of_int (53)) (Prims.of_int (32))
                                    (Prims.of_int (53)) (Prims.of_int (47)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V2.SyntaxHelpers.fst"
                                    (Prims.of_int (53)) (Prims.of_int (23))
                                    (Prims.of_int (53)) (Prims.of_int (48)))))
                           (Obj.magic uu___2)
                           (fun uu___3 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___4 ->
                                   FStarC_Reflection_V2_Data.C_Total uu___3)) in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.V2.SyntaxHelpers.fst"
                                  (Prims.of_int (53)) (Prims.of_int (23))
                                  (Prims.of_int (53)) (Prims.of_int (48)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.V2.SyntaxHelpers.fst"
                                  (Prims.of_int (53)) (Prims.of_int (11))
                                  (Prims.of_int (53)) (Prims.of_int (49)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___3 ->
                                 FStar_Tactics_NamedView.Tv_Arrow (b, uu___2))) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.SyntaxHelpers.fst"
                                (Prims.of_int (53)) (Prims.of_int (11))
                                (Prims.of_int (53)) (Prims.of_int (49)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "dummy" Prims.int_zero
                                Prims.int_zero Prims.int_zero Prims.int_zero)))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               FStar_Tactics_NamedView.pack uu___1)))))
        uu___1 uu___
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.mk_arr" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.V2.SyntaxHelpers.mk_arr (plugin)"
               (FStarC_Tactics_Native.from_tactic_2 mk_arr)
               (FStarC_Syntax_Embeddings.e_list
                  FStar_Tactics_NamedView.e_binder)
               FStarC_Reflection_V2_Embeddings.e_comp_view
               FStarC_Reflection_V2_Embeddings.e_term psc ncb us args)
let rec (mk_tot_arr :
  FStar_Tactics_NamedView.binder Prims.list ->
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun bs ->
         fun cod ->
           match bs with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> cod)))
           | b::bs1 ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       let uu___1 =
                         let uu___2 = mk_tot_arr bs1 cod in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V2.SyntaxHelpers.fst"
                                    (Prims.of_int (59)) (Prims.of_int (32))
                                    (Prims.of_int (59)) (Prims.of_int (51)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V2.SyntaxHelpers.fst"
                                    (Prims.of_int (59)) (Prims.of_int (23))
                                    (Prims.of_int (59)) (Prims.of_int (52)))))
                           (Obj.magic uu___2)
                           (fun uu___3 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___4 ->
                                   FStarC_Reflection_V2_Data.C_Total uu___3)) in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.V2.SyntaxHelpers.fst"
                                  (Prims.of_int (59)) (Prims.of_int (23))
                                  (Prims.of_int (59)) (Prims.of_int (52)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.V2.SyntaxHelpers.fst"
                                  (Prims.of_int (59)) (Prims.of_int (11))
                                  (Prims.of_int (59)) (Prims.of_int (53)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___3 ->
                                 FStar_Tactics_NamedView.Tv_Arrow (b, uu___2))) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.SyntaxHelpers.fst"
                                (Prims.of_int (59)) (Prims.of_int (11))
                                (Prims.of_int (59)) (Prims.of_int (53)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "dummy" Prims.int_zero
                                Prims.int_zero Prims.int_zero Prims.int_zero)))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               FStar_Tactics_NamedView.pack uu___1)))))
        uu___1 uu___
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.mk_tot_arr" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.V2.SyntaxHelpers.mk_tot_arr (plugin)"
               (FStarC_Tactics_Native.from_tactic_2 mk_tot_arr)
               (FStarC_Syntax_Embeddings.e_list
                  FStar_Tactics_NamedView.e_binder)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Reflection_V2_Embeddings.e_term psc ncb us args)
let (lookup_lb :
  FStar_Tactics_NamedView.letbinding Prims.list ->
    FStarC_Reflection_Types.name ->
      (FStar_Tactics_NamedView.letbinding, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun lbs ->
    fun nm ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                FStar_List_Tot_Base.find
                  (fun lb ->
                     (FStarC_Reflection_V2_Builtins.inspect_fv
                        lb.FStar_Tactics_NamedView.lb_fv)
                       = nm) lbs)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
                 (Prims.of_int (62)) (Prims.of_int (10)) (Prims.of_int (64))
                 (Prims.of_int (16)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
                 (Prims.of_int (66)) (Prims.of_int (2)) (Prims.of_int (68))
                 (Prims.of_int (59))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun o ->
              match o with
              | FStar_Pervasives_Native.Some lb ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> lb)))
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (Obj.repr
                       (fail "lookup_letbinding: Name not in let group")))
             uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.lookup_lb" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.V2.SyntaxHelpers.lookup_lb (plugin)"
               (FStarC_Tactics_Native.from_tactic_2 lookup_lb)
               (FStarC_Syntax_Embeddings.e_list
                  FStar_Tactics_NamedView.e_letbinding)
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Syntax_Embeddings.e_string)
               FStar_Tactics_NamedView.e_letbinding psc ncb us args)
let rec (inspect_unascribe :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.term_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Tactics_NamedView.inspect t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
               (Prims.of_int (71)) (Prims.of_int (8)) (Prims.of_int (71))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
               (Prims.of_int (71)) (Prims.of_int (2)) (Prims.of_int (75))
               (Prims.of_int (12))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Tactics_NamedView.Tv_AscribedT
                (t1, uu___2, uu___3, uu___4) ->
                Obj.magic (Obj.repr (inspect_unascribe t1))
            | FStar_Tactics_NamedView.Tv_AscribedC
                (t1, uu___2, uu___3, uu___4) ->
                Obj.magic (Obj.repr (inspect_unascribe t1))
            | tv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> tv))))
           uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.inspect_unascribe" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.SyntaxHelpers.inspect_unascribe (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 inspect_unascribe)
               FStarC_Reflection_V2_Embeddings.e_term
               FStar_Tactics_NamedView.e_named_term_view psc ncb us args)
let rec (collect_app' :
  FStarC_Reflection_V2_Data.argv Prims.list ->
    FStar_Tactics_NamedView.term ->
      ((FStar_Tactics_NamedView.term * FStarC_Reflection_V2_Data.argv
         Prims.list),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun args ->
    fun t ->
      let uu___ = inspect_unascribe t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
                 (Prims.of_int (80)) (Prims.of_int (10)) (Prims.of_int (80))
                 (Prims.of_int (29)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
                 (Prims.of_int (80)) (Prims.of_int (4)) (Prims.of_int (83))
                 (Prims.of_int (20))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | FStar_Tactics_NamedView.Tv_App (l, r) ->
                  Obj.magic (Obj.repr (collect_app' (r :: args) l))
              | uu___2 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> (t, args))))) uu___1)
let (collect_app :
  FStar_Tactics_NamedView.term ->
    ((FStar_Tactics_NamedView.term * FStarC_Reflection_V2_Data.argv
       Prims.list),
      unit) FStar_Tactics_Effect.tac_repr)
  = collect_app' []
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.collect_app" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.SyntaxHelpers.collect_app (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 collect_app)
               FStarC_Reflection_V2_Embeddings.e_term
               (FStarC_Syntax_Embeddings.e_tuple2
                  FStarC_Reflection_V2_Embeddings.e_term
                  (FStarC_Syntax_Embeddings.e_list
                     (FStarC_Syntax_Embeddings.e_tuple2
                        FStarC_Reflection_V2_Embeddings.e_term
                        FStarC_Reflection_V2_Embeddings.e_aqualv))) psc ncb
               us args)
let (hua :
  FStar_Tactics_NamedView.term ->
    ((FStarC_Reflection_Types.fv * FStarC_Reflection_V2_Data.universes *
       FStarC_Reflection_V2_Data.argv Prims.list)
       FStar_Pervasives_Native.option,
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = collect_app t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
               (Prims.of_int (89)) (Prims.of_int (17)) (Prims.of_int (89))
               (Prims.of_int (30)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
               (Prims.of_int (88)) (Prims.of_int (62)) (Prims.of_int (93))
               (Prims.of_int (13))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | (hd, args) ->
                let uu___2 = FStar_Tactics_NamedView.inspect hd in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.SyntaxHelpers.fst"
                              (Prims.of_int (90)) (Prims.of_int (8))
                              (Prims.of_int (90)) (Prims.of_int (18)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.V2.SyntaxHelpers.fst"
                              (Prims.of_int (90)) (Prims.of_int (2))
                              (Prims.of_int (93)) (Prims.of_int (13)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___4 ->
                             match uu___3 with
                             | FStar_Tactics_NamedView.Tv_FVar fv ->
                                 FStar_Pervasives_Native.Some (fv, [], args)
                             | FStar_Tactics_NamedView.Tv_UInst (fv, us) ->
                                 FStar_Pervasives_Native.Some (fv, us, args)
                             | uu___5 -> FStar_Pervasives_Native.None))))
           uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.SyntaxHelpers.hua"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.SyntaxHelpers.hua (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 hua)
               FStarC_Reflection_V2_Embeddings.e_term
               (FStarC_Syntax_Embeddings.e_option
                  (FStarC_Syntax_Embeddings.e_tuple3
                     FStarC_Reflection_V2_Embeddings.e_fv
                     (FStarC_Syntax_Embeddings.e_list
                        FStarC_Reflection_V2_Embeddings.e_universe)
                     (FStarC_Syntax_Embeddings.e_list
                        (FStarC_Syntax_Embeddings.e_tuple2
                           FStarC_Reflection_V2_Embeddings.e_term
                           FStarC_Reflection_V2_Embeddings.e_aqualv)))) psc
               ncb us args)