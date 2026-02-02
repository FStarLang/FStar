open Fstarcompiler
open Prims
let rec collect_arr' (uu___1 : FStar_Tactics_NamedView.binder Prims.list)
  (uu___ : FStar_Tactics_NamedView.comp) :
  ((FStar_Tactics_NamedView.binder Prims.list * FStar_Tactics_NamedView.comp),
    unit) FStar_Tactics_Effect.tac_repr=
  (fun bs c ->
     match c with
     | FStarC_Reflection_V2_Data.C_Total t ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic (FStar_Tactics_NamedView.inspect t))
                 (fun uu___ ->
                    (fun uu___ ->
                       match uu___ with
                       | FStar_Tactics_NamedView.Tv_Arrow (b, c1) ->
                           Obj.magic (Obj.repr (collect_arr' (b :: bs) c1))
                       | uu___1 ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> (bs, c))))) uu___)))
     | uu___ ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> (bs, c)))))
    uu___1 uu___
let collect_arr_bs (t : FStarC_Reflection_Types.typ) :
  ((FStar_Tactics_NamedView.binder Prims.list * FStar_Tactics_NamedView.comp),
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = collect_arr' [] (FStarC_Reflection_V2_Data.C_Total t) ps in
    match x with | (bs, c) -> ((FStar_List_Tot_Base.rev bs), c)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.collect_arr_bs" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.SyntaxHelpers.collect_arr_bs (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  collect_arr_bs)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                  (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                     FStar_Tactics_NamedView.e_binder)
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_comp_view)
               psc ncb us args)
let collect_arr (t : FStarC_Reflection_Types.typ) :
  ((FStarC_Reflection_Types.typ Prims.list * FStar_Tactics_NamedView.comp),
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = collect_arr' [] (FStarC_Reflection_V2_Data.C_Total t) ps in
    match x with
    | (bs, c) ->
        ((FStar_List_Tot_Base.rev
            (FStar_List_Tot_Base.map
               (fun b -> b.FStar_Tactics_NamedView.sort) bs)), c)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.collect_arr" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.SyntaxHelpers.collect_arr (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 collect_arr)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                  (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_comp_view)
               psc ncb us args)
let rec collect_abs' (bs : FStar_Tactics_NamedView.binder Prims.list)
  (t : FStar_Tactics_NamedView.term) :
  ((FStar_Tactics_NamedView.binder Prims.list * FStar_Tactics_NamedView.term),
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_NamedView.inspect t ps in
    match x with
    | FStar_Tactics_NamedView.Tv_Abs (b, t') -> collect_abs' (b :: bs) t' ps
    | uu___ -> (bs, t)
let collect_abs (t : FStar_Tactics_NamedView.term) :
  ((FStar_Tactics_NamedView.binder Prims.list * FStar_Tactics_NamedView.term),
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = collect_abs' [] t ps in
    match x with | (bs, t') -> ((FStar_List_Tot_Base.rev bs), t')
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.collect_abs" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.SyntaxHelpers.collect_abs (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 collect_abs)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                  (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                     FStar_Tactics_NamedView.e_binder)
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term) psc
               ncb us args)
let fail (m : Prims.string) : ('a, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    Obj.magic
      (FStarC_Tactics_V2_Builtins.raise_core
         (FStarC_Tactics_Common.TacticFailure
            ((FStarC_Errors_Msg.mkmsg m), FStar_Pervasives_Native.None)) ps)
let rec mk_arr (uu___1 : FStar_Tactics_NamedView.binder Prims.list)
  (uu___ : FStar_Tactics_NamedView.comp) :
  (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr=
  (fun bs cod ->
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
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (Obj.magic (mk_arr bs1 cod))
                             (fun uu___ uu___1 ->
                                FStarC_Reflection_V2_Data.C_Total uu___)))
                       (fun uu___ uu___1 ->
                          FStar_Tactics_NamedView.Tv_Arrow (b, uu___))))
                 (fun uu___ uu___1 -> FStar_Tactics_NamedView.pack uu___))))
    uu___1 uu___
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.mk_arr" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.V2.SyntaxHelpers.mk_arr (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_2 mk_arr)
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  FStar_Tactics_NamedView.e_binder)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_comp_view
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term psc ncb
               us args)
let rec mk_tot_arr (uu___1 : FStar_Tactics_NamedView.binder Prims.list)
  (uu___ : FStar_Tactics_NamedView.term) :
  (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr=
  (fun bs cod ->
     match bs with
     | [] -> Obj.magic (Obj.repr (fun uu___ -> cod))
     | b::bs1 ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (Obj.magic (mk_tot_arr bs1 cod))
                             (fun uu___ uu___1 ->
                                FStarC_Reflection_V2_Data.C_Total uu___)))
                       (fun uu___ uu___1 ->
                          FStar_Tactics_NamedView.Tv_Arrow (b, uu___))))
                 (fun uu___ uu___1 -> FStar_Tactics_NamedView.pack uu___))))
    uu___1 uu___
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.mk_tot_arr" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.V2.SyntaxHelpers.mk_tot_arr (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_2 mk_tot_arr)
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  FStar_Tactics_NamedView.e_binder)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term psc ncb
               us args)
let lookup_lb (lbs : FStar_Tactics_NamedView.letbinding Prims.list)
  (nm : FStarC_Reflection_Types.name) :
  (FStar_Tactics_NamedView.letbinding, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      FStar_List_Tot_Base.find
        (fun lb ->
           (FStarC_Reflection_V2_Builtins.inspect_fv
              lb.FStar_Tactics_NamedView.lb_fv)
             = nm) lbs in
    match x with
    | FStar_Pervasives_Native.Some lb -> lb
    | FStar_Pervasives_Native.None ->
        fail "lookup_letbinding: Name not in let group" ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.lookup_lb" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.V2.SyntaxHelpers.lookup_lb (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_2 lookup_lb)
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  FStar_Tactics_NamedView.e_letbinding)
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  Fstarcompiler.FStarC_Syntax_Embeddings.e_string)
               FStar_Tactics_NamedView.e_letbinding psc ncb us args)
let rec inspect_unascribe (t : FStar_Tactics_NamedView.term) :
  (FStar_Tactics_NamedView.term_view, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_NamedView.inspect t ps in
    match x with
    | FStar_Tactics_NamedView.Tv_AscribedT (t1, uu___, uu___1, uu___2) ->
        inspect_unascribe t1 ps
    | FStar_Tactics_NamedView.Tv_AscribedC (t1, uu___, uu___1, uu___2) ->
        inspect_unascribe t1 ps
    | tv -> tv
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.inspect_unascribe" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.SyntaxHelpers.inspect_unascribe (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  inspect_unascribe)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               FStar_Tactics_NamedView.e_named_term_view psc ncb us args)
let rec collect_app' (args : FStarC_Reflection_V2_Data.argv Prims.list)
  (t : FStar_Tactics_NamedView.term) :
  ((FStar_Tactics_NamedView.term * FStarC_Reflection_V2_Data.argv Prims.list),
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = inspect_unascribe t ps in
    match x with
    | FStar_Tactics_NamedView.Tv_App (l, r) -> collect_app' (r :: args) l ps
    | uu___ -> (t, args)
let collect_app :
  FStar_Tactics_NamedView.term ->
    ((FStar_Tactics_NamedView.term * FStarC_Reflection_V2_Data.argv
       Prims.list),
      unit) FStar_Tactics_Effect.tac_repr=
  collect_app' []
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.collect_app" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.SyntaxHelpers.collect_app (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 collect_app)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                  (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                        Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                        Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_aqualv)))
               psc ncb us args)
let hua (t : FStar_Tactics_NamedView.term) :
  ((FStarC_Reflection_Types.fv * FStarC_Reflection_V2_Data.universes *
     FStarC_Reflection_V2_Data.argv Prims.list)
     FStar_Pervasives_Native.option,
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = collect_app t ps in
    match x with
    | (hd, args) ->
        let x1 = FStar_Tactics_NamedView.inspect hd ps in
        (match x1 with
         | FStar_Tactics_NamedView.Tv_FVar fv ->
             FStar_Pervasives_Native.Some (fv, [], args)
         | FStar_Tactics_NamedView.Tv_UInst (fv, us) ->
             FStar_Pervasives_Native.Some (fv, us, args)
         | uu___ -> FStar_Pervasives_Native.None)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.hua" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.SyntaxHelpers.hua (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 hua)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                  (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple3
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_fv
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                        Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe)
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                        (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                           Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                           Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_aqualv))))
               psc ncb us args)
