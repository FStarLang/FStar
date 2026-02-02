open Fstarcompiler
open Prims
let rec collect_arr' (uu___1 : FStarC_Reflection_Types.binder Prims.list)
  (uu___ : FStarC_Reflection_Types.comp) :
  ((FStarC_Reflection_Types.binder Prims.list * FStarC_Reflection_Types.comp),
    unit) FStar_Tactics_Effect.tac_repr=
  (fun bs c ->
     match FStarC_Reflection_V1_Builtins.inspect_comp c with
     | FStarC_Reflection_V1_Data.C_Total t ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic (FStarC_Tactics_V1_Builtins.inspect t))
                 (fun uu___ ->
                    (fun uu___ ->
                       match uu___ with
                       | FStarC_Reflection_V1_Data.Tv_Arrow (b, c1) ->
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
  ((FStarC_Reflection_Types.binder Prims.list * FStarC_Reflection_Types.comp),
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      collect_arr' []
        (FStarC_Reflection_V1_Builtins.pack_comp
           (FStarC_Reflection_V1_Data.C_Total t)) ps in
    match x with | (bs, c) -> ((FStar_List_Tot_Base.rev bs), c)
let collect_arr (t : FStarC_Reflection_Types.typ) :
  ((FStarC_Reflection_Types.typ Prims.list * FStarC_Reflection_Types.comp),
    unit) FStar_Tactics_Effect.tac_repr=
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
let rec collect_abs' (bs : FStarC_Reflection_Types.binder Prims.list)
  (t : FStarC_Reflection_Types.term) :
  ((FStarC_Reflection_Types.binder Prims.list * FStarC_Reflection_Types.term),
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V1_Builtins.inspect t ps in
    match x with
    | FStarC_Reflection_V1_Data.Tv_Abs (b, t') ->
        collect_abs' (b :: bs) t' ps
    | uu___ -> (bs, t)
let collect_abs (t : FStarC_Reflection_Types.term) :
  ((FStarC_Reflection_Types.binder Prims.list * FStarC_Reflection_Types.term),
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = collect_abs' [] t ps in
    match x with | (bs, t') -> ((FStar_List_Tot_Base.rev bs), t')
let fail (m : Prims.string) : ('a, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    Obj.magic
      (FStarC_Tactics_V1_Builtins.raise_core
         (FStarC_Tactics_Common.TacticFailure
            ((FStarC_Errors_Msg.mkmsg m), FStar_Pervasives_Native.None)) ps)
let rec mk_arr (bs : FStarC_Reflection_Types.binder Prims.list)
  (cod : FStarC_Reflection_Types.comp) :
  (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr=
  match bs with
  | [] -> fail "mk_arr, empty binders"
  | b::[] ->
      FStarC_Tactics_V1_Builtins.pack
        (FStarC_Reflection_V1_Data.Tv_Arrow (b, cod))
  | b::bs1 ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (Obj.magic (mk_arr bs1 cod))
                          (fun uu___ uu___1 ->
                             FStarC_Reflection_V1_Data.C_Total uu___)))
                    (fun uu___ uu___1 ->
                       FStarC_Reflection_V1_Builtins.pack_comp uu___)))
              (fun uu___ uu___1 ->
                 FStarC_Reflection_V1_Data.Tv_Arrow (b, uu___))))
        (fun uu___ ->
           (fun uu___ -> Obj.magic (FStarC_Tactics_V1_Builtins.pack uu___))
             uu___)
let rec mk_arr_curried (bs : FStarC_Reflection_Types.binder Prims.list)
  (cod : FStarC_Reflection_Types.comp) :
  (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr=
  match bs with
  | [] -> fail "mk_arr, empty binders"
  | b::[] ->
      FStarC_Tactics_V1_Builtins.pack_curried
        (FStarC_Reflection_V1_Data.Tv_Arrow (b, cod))
  | b::bs1 ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (Obj.magic (mk_arr_curried bs1 cod))
                          (fun uu___ uu___1 ->
                             FStarC_Reflection_V1_Data.C_Total uu___)))
                    (fun uu___ uu___1 ->
                       FStarC_Reflection_V1_Builtins.pack_comp uu___)))
              (fun uu___ uu___1 ->
                 FStarC_Reflection_V1_Data.Tv_Arrow (b, uu___))))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic (FStarC_Tactics_V1_Builtins.pack_curried uu___))
             uu___)
let rec mk_tot_arr (uu___1 : FStarC_Reflection_Types.binder Prims.list)
  (uu___ : FStarC_Reflection_Types.term) :
  (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr=
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
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (Obj.magic (mk_tot_arr bs1 cod))
                                   (fun uu___ uu___1 ->
                                      FStarC_Reflection_V1_Data.C_Total uu___)))
                             (fun uu___ uu___1 ->
                                FStarC_Reflection_V1_Builtins.pack_comp uu___)))
                       (fun uu___ uu___1 ->
                          FStarC_Reflection_V1_Data.Tv_Arrow (b, uu___))))
                 (fun uu___ ->
                    (fun uu___ ->
                       Obj.magic (FStarC_Tactics_V1_Builtins.pack uu___))
                      uu___)))) uu___1 uu___
let lookup_lb_view (lbs : FStarC_Reflection_Types.letbinding Prims.list)
  (nm : FStarC_Reflection_Types.name) :
  (FStarC_Reflection_V1_Data.lb_view, unit) FStar_Tactics_Effect.tac_repr=
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
let rec inspect_unascribe (t : FStarC_Reflection_Types.term) :
  (FStarC_Reflection_V1_Data.term_view, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V1_Builtins.inspect t ps in
    match x with
    | FStarC_Reflection_V1_Data.Tv_AscribedT (t1, uu___, uu___1, uu___2) ->
        inspect_unascribe t1 ps
    | FStarC_Reflection_V1_Data.Tv_AscribedC (t1, uu___, uu___1, uu___2) ->
        inspect_unascribe t1 ps
    | tv -> tv
let rec collect_app' (args : FStarC_Reflection_V1_Data.argv Prims.list)
  (t : FStarC_Reflection_Types.term) :
  ((FStarC_Reflection_Types.term * FStarC_Reflection_V1_Data.argv Prims.list),
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = inspect_unascribe t ps in
    match x with
    | FStarC_Reflection_V1_Data.Tv_App (l, r) ->
        collect_app' (r :: args) l ps
    | uu___ -> (t, args)
let collect_app :
  FStarC_Reflection_Types.term ->
    ((FStarC_Reflection_Types.term * FStarC_Reflection_V1_Data.argv
       Prims.list),
      unit) FStar_Tactics_Effect.tac_repr=
  collect_app' []
