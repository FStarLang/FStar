open Fstarcompiler
open Prims
let rec (collect_arr' :
  FStarC_Reflection_Types.binder Prims.list ->
    FStarC_Reflection_Types.comp ->
      ((FStarC_Reflection_Types.binder Prims.list *
         FStarC_Reflection_Types.comp),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun bs ->
         fun c ->
           match FStarC_Reflection_V1_Builtins.inspect_comp c with
           | FStarC_Reflection_V1_Data.C_Total t ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x = FStarC_Tactics_V1_Builtins.inspect t ps in
                       match x with
                       | FStarC_Reflection_V1_Data.Tv_Arrow (b, c1) ->
                           collect_arr' (b :: bs) c1 ps
                       | uu___ -> (bs, c)))
           | uu___ -> Obj.magic (Obj.repr (fun uu___1 -> (bs, c)))) uu___1
        uu___
let (collect_arr_bs :
  FStarC_Reflection_Types.typ ->
    ((FStarC_Reflection_Types.binder Prims.list *
       FStarC_Reflection_Types.comp),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun ps ->
      let x =
        collect_arr' []
          (FStarC_Reflection_V1_Builtins.pack_comp
             (FStarC_Reflection_V1_Data.C_Total t)) ps in
      match x with | (bs, c) -> ((FStar_List_Tot_Base.rev bs), c)
let (collect_arr :
  FStarC_Reflection_Types.typ ->
    ((FStarC_Reflection_Types.typ Prims.list * FStarC_Reflection_Types.comp),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun ps ->
      let x =
        collect_arr' []
          (FStarC_Reflection_V1_Builtins.pack_comp
             (FStarC_Reflection_V1_Data.C_Total t)) ps in
      match x with
      | (bs, c) ->
          ((FStar_List_Tot_Base.rev
              (FStar_List_Tot_Base.map
                 FStar_Reflection_V1_Derived.type_of_binder bs)), c)
let rec (collect_abs' :
  FStarC_Reflection_Types.binder Prims.list ->
    FStarC_Reflection_Types.term ->
      ((FStarC_Reflection_Types.binder Prims.list *
         FStarC_Reflection_Types.term),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bs ->
    fun t ->
      fun ps ->
        let x = FStarC_Tactics_V1_Builtins.inspect t ps in
        match x with
        | FStarC_Reflection_V1_Data.Tv_Abs (b, t') ->
            collect_abs' (b :: bs) t' ps
        | uu___ -> (bs, t)
let (collect_abs :
  FStarC_Reflection_Types.term ->
    ((FStarC_Reflection_Types.binder Prims.list *
       FStarC_Reflection_Types.term),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun ps ->
      let x = collect_abs' [] t ps in
      match x with | (bs, t') -> ((FStar_List_Tot_Base.rev bs), t')
let fail : 'a . Prims.string -> ('a, unit) FStar_Tactics_Effect.tac_repr =
  fun m ->
    fun ps ->
      Obj.magic
        (FStarC_Tactics_V1_Builtins.raise_core
           (FStarC_Tactics_Common.TacticFailure
              ((FStarC_Errors_Msg.mkmsg m), FStar_Pervasives_Native.None)) ps)
let rec (mk_arr :
  FStarC_Reflection_Types.binder Prims.list ->
    FStarC_Reflection_Types.comp ->
      (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bs ->
    fun cod ->
      match bs with
      | [] -> fail "mk_arr, empty binders"
      | b::[] ->
          FStarC_Tactics_V1_Builtins.pack
            (FStarC_Reflection_V1_Data.Tv_Arrow (b, cod))
      | b::bs1 ->
          (fun ps ->
             let x =
               let x1 =
                 let x2 =
                   let x3 = mk_arr bs1 cod ps in
                   FStarC_Reflection_V1_Data.C_Total x3 in
                 FStarC_Reflection_V1_Builtins.pack_comp x2 in
               FStarC_Reflection_V1_Data.Tv_Arrow (b, x1) in
             FStarC_Tactics_V1_Builtins.pack x ps)
let rec (mk_arr_curried :
  FStarC_Reflection_Types.binder Prims.list ->
    FStarC_Reflection_Types.comp ->
      (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bs ->
    fun cod ->
      match bs with
      | [] -> fail "mk_arr, empty binders"
      | b::[] ->
          FStarC_Tactics_V1_Builtins.pack_curried
            (FStarC_Reflection_V1_Data.Tv_Arrow (b, cod))
      | b::bs1 ->
          (fun ps ->
             let x =
               let x1 =
                 let x2 =
                   let x3 = mk_arr_curried bs1 cod ps in
                   FStarC_Reflection_V1_Data.C_Total x3 in
                 FStarC_Reflection_V1_Builtins.pack_comp x2 in
               FStarC_Reflection_V1_Data.Tv_Arrow (b, x1) in
             FStarC_Tactics_V1_Builtins.pack_curried x ps)
let rec (mk_tot_arr :
  FStarC_Reflection_Types.binder Prims.list ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun bs ->
         fun cod ->
           match bs with
           | [] -> Obj.magic (Obj.repr (fun uu___ -> cod))
           | b::bs1 ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x =
                         let x1 =
                           let x2 =
                             let x3 = mk_tot_arr bs1 cod ps in
                             FStarC_Reflection_V1_Data.C_Total x3 in
                           FStarC_Reflection_V1_Builtins.pack_comp x2 in
                         FStarC_Reflection_V1_Data.Tv_Arrow (b, x1) in
                       FStarC_Tactics_V1_Builtins.pack x ps))) uu___1 uu___
let (lookup_lb_view :
  FStarC_Reflection_Types.letbinding Prims.list ->
    FStarC_Reflection_Types.name ->
      (FStarC_Reflection_V1_Data.lb_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun lbs ->
    fun nm ->
      fun ps ->
        let x =
          FStar_List_Tot_Base.find
            (fun lb ->
               (FStarC_Reflection_V1_Builtins.inspect_fv
                  (FStarC_Reflection_V1_Builtins.inspect_lb lb).FStarC_Reflection_V1_Data.lb_fv)
                 = nm) lbs in
        match x with
        | FStar_Pervasives_Native.Some lb ->
            FStarC_Reflection_V1_Builtins.inspect_lb lb
        | FStar_Pervasives_Native.None ->
            fail "lookup_lb_view: Name not in let group" ps
let rec (inspect_unascribe :
  FStarC_Reflection_Types.term ->
    (FStarC_Reflection_V1_Data.term_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun ps ->
      let x = FStarC_Tactics_V1_Builtins.inspect t ps in
      match x with
      | FStarC_Reflection_V1_Data.Tv_AscribedT (t1, uu___, uu___1, uu___2) ->
          inspect_unascribe t1 ps
      | FStarC_Reflection_V1_Data.Tv_AscribedC (t1, uu___, uu___1, uu___2) ->
          inspect_unascribe t1 ps
      | tv -> tv
let rec (collect_app' :
  FStarC_Reflection_V1_Data.argv Prims.list ->
    FStarC_Reflection_Types.term ->
      ((FStarC_Reflection_Types.term * FStarC_Reflection_V1_Data.argv
         Prims.list),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun args ->
    fun t ->
      fun ps ->
        let x = inspect_unascribe t ps in
        match x with
        | FStarC_Reflection_V1_Data.Tv_App (l, r) ->
            collect_app' (r :: args) l ps
        | uu___ -> (t, args)
let (collect_app :
  FStarC_Reflection_Types.term ->
    ((FStarC_Reflection_Types.term * FStarC_Reflection_V1_Data.argv
       Prims.list),
      unit) FStar_Tactics_Effect.tac_repr)
  = collect_app' []
