open Prims
let rec collect_arr' (bs : FStar_Tactics_NamedView.binder Prims.list)
  (c : FStar_Tactics_NamedView.comp) :
  FStarC_Tactics_Types.ref_proofstate ->
    (FStar_Tactics_NamedView.binder Prims.list *
      FStar_Tactics_NamedView.comp)=
  match c with
  | FStarC_Reflection_V2_Data.C_Total t ->
      (fun ps ->
         let x = FStar_Tactics_NamedView.inspect t ps in
         match x with
         | FStar_Tactics_NamedView.Tv_Arrow (b, c1) ->
             collect_arr' (b :: bs) c1 ps
         | uu___ -> (bs, c))
  | uu___ -> (fun uu___1 -> (bs, c))
let collect_arr_bs (t : FStarC_Reflection_Types.typ)
  (ps : FStarC_Tactics_Types.ref_proofstate) :
  (FStar_Tactics_NamedView.binder Prims.list * FStar_Tactics_NamedView.comp)=
  let x = collect_arr' [] (FStarC_Reflection_V2_Data.C_Total t) ps in
  match x with | (bs, c) -> ((FStar_List_Tot_Base.rev bs), c)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.collect_arr_bs" (Prims.of_int 2)
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
let collect_arr (t : FStarC_Reflection_Types.typ)
  (ps : FStarC_Tactics_Types.ref_proofstate) :
  (FStarC_Reflection_Types.typ Prims.list * FStar_Tactics_NamedView.comp)=
  let x = collect_arr' [] (FStarC_Reflection_V2_Data.C_Total t) ps in
  match x with
  | (bs, c) ->
      ((FStar_List_Tot_Base.rev
          (FStar_List_Tot_Base.map (fun b -> b.FStar_Tactics_NamedView.sort)
             bs)), c)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.collect_arr" (Prims.of_int 2)
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
let rec collect_abs' (bs : FStar_Tactics_NamedView.binder Prims.list)
  (t : FStar_Tactics_NamedView.term)
  (ps : FStarC_Tactics_Types.ref_proofstate) :
  (FStar_Tactics_NamedView.binder Prims.list * FStar_Tactics_NamedView.term)=
  let x = FStar_Tactics_NamedView.inspect t ps in
  match x with
  | FStar_Tactics_NamedView.Tv_Abs (b, t') -> collect_abs' (b :: bs) t' ps
  | uu___ -> (bs, t)
let collect_abs (t : FStar_Tactics_NamedView.term)
  (ps : FStarC_Tactics_Types.ref_proofstate) :
  (FStar_Tactics_NamedView.binder Prims.list * FStar_Tactics_NamedView.term)=
  let x = collect_abs' [] t ps in
  match x with | (bs, t') -> ((FStar_List_Tot_Base.rev bs), t')
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.collect_abs" (Prims.of_int 2)
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
let fail (uu___1 : Prims.string)
  (uu___ : FStarC_Tactics_Types.ref_proofstate) : 'a=
  (fun m ps ->
     Obj.magic
       (FStarC_Tactics_V2_Builtins.raise_core
          (FStarC_Tactics_Common.TacticFailure
             ((FStar_Errors_Msg.mkmsg m), FStar_Pervasives_Native.None)) ps))
    uu___1 uu___
let rec mk_arr (bs : FStar_Tactics_NamedView.binder Prims.list)
  (cod : FStar_Tactics_NamedView.comp) :
  FStarC_Tactics_Types.ref_proofstate -> FStar_Tactics_NamedView.term=
  match bs with
  | [] -> fail "mk_arr, empty binders"
  | b::[] ->
      (fun uu___ ->
         FStar_Tactics_NamedView.pack
           (FStar_Tactics_NamedView.Tv_Arrow (b, cod)))
  | b::bs1 ->
      (fun ps ->
         let x =
           let x1 =
             let x2 = mk_arr bs1 cod ps in
             FStarC_Reflection_V2_Data.C_Total x2 in
           FStar_Tactics_NamedView.Tv_Arrow (b, x1) in
         FStar_Tactics_NamedView.pack x)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.mk_arr" (Prims.of_int 3)
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
let rec mk_tot_arr (bs : FStar_Tactics_NamedView.binder Prims.list)
  (cod : FStar_Tactics_NamedView.term) :
  FStarC_Tactics_Types.ref_proofstate -> FStar_Tactics_NamedView.term=
  match bs with
  | [] -> (fun uu___ -> cod)
  | b::bs1 ->
      (fun ps ->
         let x =
           let x1 =
             let x2 = mk_tot_arr bs1 cod ps in
             FStarC_Reflection_V2_Data.C_Total x2 in
           FStar_Tactics_NamedView.Tv_Arrow (b, x1) in
         FStar_Tactics_NamedView.pack x)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.mk_tot_arr" (Prims.of_int 3)
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
let lookup_lb (lbs : FStar_Tactics_NamedView.letbinding Prims.list)
  (nm : FStarC_Reflection_Types.name)
  (ps : FStarC_Tactics_Types.ref_proofstate) :
  FStar_Tactics_NamedView.letbinding=
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
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.lookup_lb" (Prims.of_int 3)
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
let rec inspect_unascribe (t : FStar_Tactics_NamedView.term)
  (ps : FStarC_Tactics_Types.ref_proofstate) :
  FStar_Tactics_NamedView.term_view=
  let x = FStar_Tactics_NamedView.inspect t ps in
  match x with
  | FStar_Tactics_NamedView.Tv_AscribedT (t1, uu___, uu___1, uu___2) ->
      inspect_unascribe t1 ps
  | FStar_Tactics_NamedView.Tv_AscribedC (t1, uu___, uu___1, uu___2) ->
      inspect_unascribe t1 ps
  | tv -> tv
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.inspect_unascribe" (Prims.of_int 2)
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.SyntaxHelpers.inspect_unascribe (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 inspect_unascribe)
               FStarC_Reflection_V2_Embeddings.e_term
               FStar_Tactics_NamedView.e_named_term_view psc ncb us args)
let rec collect_app' (args : FStarC_Reflection_V2_Data.argv Prims.list)
  (t : FStar_Tactics_NamedView.term)
  (ps : FStarC_Tactics_Types.ref_proofstate) :
  (FStar_Tactics_NamedView.term * FStarC_Reflection_V2_Data.argv Prims.list)=
  let x = inspect_unascribe t ps in
  match x with
  | FStar_Tactics_NamedView.Tv_App (l, r) -> collect_app' (r :: args) l ps
  | uu___ -> (t, args)
let collect_app :
  FStar_Tactics_NamedView.term ->
    FStarC_Tactics_Types.ref_proofstate ->
      (FStar_Tactics_NamedView.term * FStarC_Reflection_V2_Data.argv
        Prims.list)=
  collect_app' []
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.SyntaxHelpers.collect_app" (Prims.of_int 2)
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
let hua (t : FStar_Tactics_NamedView.term)
  (ps : FStarC_Tactics_Types.ref_proofstate) :
  (FStarC_Reflection_Types.fv * FStarC_Reflection_V2_Data.universes *
    FStarC_Reflection_V2_Data.argv Prims.list) FStar_Pervasives_Native.option=
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
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.SyntaxHelpers.hua"
    (Prims.of_int 2)
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
