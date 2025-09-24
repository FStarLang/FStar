open Fstarcompiler
open Prims
let (on_sort_binder :
  (FStarC_Reflection_Types.term ->
     (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStarC_Reflection_Types.binder ->
      (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun b ->
      fun ps ->
        let x = FStarC_Reflection_V2_Builtins.inspect_binder b in
        let x1 =
          let x2 = f x.FStarC_Reflection_V2_Data.sort2 ps in
          {
            FStarC_Reflection_V2_Data.sort2 = x2;
            FStarC_Reflection_V2_Data.qual =
              (x.FStarC_Reflection_V2_Data.qual);
            FStarC_Reflection_V2_Data.attrs =
              (x.FStarC_Reflection_V2_Data.attrs);
            FStarC_Reflection_V2_Data.ppname2 =
              (x.FStarC_Reflection_V2_Data.ppname2)
          } in
        FStarC_Reflection_V2_Builtins.pack_binder x1
let (on_sort_simple_binder :
  (FStarC_Reflection_Types.term ->
     (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStarC_Reflection_V2_Data.simple_binder ->
      (FStarC_Reflection_V2_Data.simple_binder, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun b ->
      fun ps ->
        let x = FStarC_Reflection_V2_Builtins.inspect_binder b in
        let x1 =
          let x2 = f x.FStarC_Reflection_V2_Data.sort2 ps in
          {
            FStarC_Reflection_V2_Data.sort2 = x2;
            FStarC_Reflection_V2_Data.qual =
              (x.FStarC_Reflection_V2_Data.qual);
            FStarC_Reflection_V2_Data.attrs =
              (x.FStarC_Reflection_V2_Data.attrs);
            FStarC_Reflection_V2_Data.ppname2 =
              (x.FStarC_Reflection_V2_Data.ppname2)
          } in
        FStarC_Reflection_V2_Builtins.pack_binder x1
let rec (visit_tm :
  (FStarC_Reflection_Types.term ->
     (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ff ->
    fun t ->
      fun ps ->
        let x = FStarC_Reflection_V2_Builtins.inspect_ln t in
        let x1 =
          match x with
          | FStarC_Reflection_V2_Data.Tv_FVar uu___ -> x
          | FStarC_Reflection_V2_Data.Tv_Var uu___ -> x
          | FStarC_Reflection_V2_Data.Tv_BVar uu___ -> x
          | FStarC_Reflection_V2_Data.Tv_UInst (uu___, uu___1) -> x
          | FStarC_Reflection_V2_Data.Tv_Type u ->
              FStarC_Reflection_V2_Data.Tv_Type u
          | FStarC_Reflection_V2_Data.Tv_Const c ->
              FStarC_Reflection_V2_Data.Tv_Const c
          | FStarC_Reflection_V2_Data.Tv_Uvar (i, u) ->
              FStarC_Reflection_V2_Data.Tv_Uvar (i, u)
          | FStarC_Reflection_V2_Data.Tv_Unknown ->
              FStarC_Reflection_V2_Data.Tv_Unknown
          | FStarC_Reflection_V2_Data.Tv_Unsupp ->
              FStarC_Reflection_V2_Data.Tv_Unsupp
          | FStarC_Reflection_V2_Data.Tv_Arrow (b, c) ->
              let x2 = on_sort_binder (visit_tm ff) b ps in
              let x3 = visit_comp ff c ps in
              FStarC_Reflection_V2_Data.Tv_Arrow (x2, x3)
          | FStarC_Reflection_V2_Data.Tv_Abs (b, t1) ->
              let x2 = on_sort_binder (visit_tm ff) b ps in
              let x3 = visit_tm ff t1 ps in
              FStarC_Reflection_V2_Data.Tv_Abs (x2, x3)
          | FStarC_Reflection_V2_Data.Tv_App (l, (r, q)) ->
              let x2 = visit_tm ff l ps in
              let x3 = visit_tm ff r ps in
              FStarC_Reflection_V2_Data.Tv_App (x2, (x3, q))
          | FStarC_Reflection_V2_Data.Tv_Refine (b, r) ->
              let x2 = on_sort_simple_binder (visit_tm ff) b ps in
              let x3 = visit_tm ff r ps in
              FStarC_Reflection_V2_Data.Tv_Refine (x2, x3)
          | FStarC_Reflection_V2_Data.Tv_Let (r, attrs, b, def, t1) ->
              let x2 = on_sort_simple_binder (visit_tm ff) b ps in
              let x3 = visit_tm ff def ps in
              let x4 = visit_tm ff t1 ps in
              FStarC_Reflection_V2_Data.Tv_Let (r, attrs, x2, x3, x4)
          | FStarC_Reflection_V2_Data.Tv_Match (sc, ret_opt, brs) ->
              let x2 = visit_tm ff sc ps in
              let x3 =
                FStar_Tactics_Util.map_opt
                  (fun uu___ ->
                     match uu___ with
                     | (b, asc) ->
                         (fun ps1 ->
                            let x4 = on_sort_binder (visit_tm ff) b ps1 in
                            let x5 =
                              match asc with
                              | (Fstarcompiler.FStar_Pervasives.Inl t1,
                                 tacopt, use_eq) ->
                                  let x6 =
                                    let x7 = visit_tm ff t1 ps1 in
                                    Fstarcompiler.FStar_Pervasives.Inl x7 in
                                  let x7 =
                                    FStar_Tactics_Util.map_opt (visit_tm ff)
                                      tacopt ps1 in
                                  (x6, x7, use_eq)
                              | (Fstarcompiler.FStar_Pervasives.Inr c,
                                 tacopt, use_eq) ->
                                  let x6 =
                                    let x7 = visit_comp ff c ps1 in
                                    Fstarcompiler.FStar_Pervasives.Inr x7 in
                                  let x7 =
                                    FStar_Tactics_Util.map_opt (visit_tm ff)
                                      tacopt ps1 in
                                  (x6, x7, use_eq) in
                            (x4, x5))) ret_opt ps in
              let x4 = FStar_Tactics_Util.map (visit_br ff) brs ps in
              FStarC_Reflection_V2_Data.Tv_Match (x2, x3, x4)
          | FStarC_Reflection_V2_Data.Tv_AscribedT (e, t1, topt, use_eq) ->
              let x2 = visit_tm ff e ps in
              let x3 = visit_tm ff t1 ps in
              FStarC_Reflection_V2_Data.Tv_AscribedT (x2, x3, topt, use_eq)
          | FStarC_Reflection_V2_Data.Tv_AscribedC (e, c, topt, use_eq) ->
              let x2 = visit_tm ff e ps in
              let x3 = visit_comp ff c ps in
              FStarC_Reflection_V2_Data.Tv_AscribedC (x2, x3, topt, use_eq) in
        ff (FStarC_Reflection_V2_Builtins.pack_ln x1) ps
and (visit_br :
  (FStarC_Reflection_Types.term ->
     (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStarC_Reflection_V2_Data.branch ->
      (FStarC_Reflection_V2_Data.branch, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ff ->
    fun b ->
      fun ps ->
        let x = b in
        match x with
        | (p, t) ->
            let x1 = visit_pat ff p ps in
            let x2 = visit_tm ff t ps in (x1, x2)
and (visit_pat :
  (FStarC_Reflection_Types.term ->
     (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStarC_Reflection_V2_Data.pattern ->
      (FStarC_Reflection_V2_Data.pattern, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun ff ->
         fun p ->
           match p with
           | FStarC_Reflection_V2_Data.Pat_Constant uu___ ->
               Obj.magic (Obj.repr (fun uu___1 -> p))
           | FStarC_Reflection_V2_Data.Pat_Var (v, s) ->
               Obj.magic
                 (Obj.repr
                    (fun uu___ -> FStarC_Reflection_V2_Data.Pat_Var (v, s)))
           | FStarC_Reflection_V2_Data.Pat_Cons (head, univs, subpats) ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x =
                         FStar_Tactics_Util.map
                           (fun uu___ ->
                              match uu___ with
                              | (p1, b) ->
                                  (fun ps1 ->
                                     let x1 = visit_pat ff p1 ps1 in (x1, b)))
                           subpats ps in
                       FStarC_Reflection_V2_Data.Pat_Cons (head, univs, x)))
           | FStarC_Reflection_V2_Data.Pat_Dot_Term t ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x = FStar_Tactics_Util.map_opt (visit_tm ff) t ps in
                       FStarC_Reflection_V2_Data.Pat_Dot_Term x))) uu___1
        uu___
and (visit_comp :
  (FStarC_Reflection_Types.term ->
     (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStarC_Reflection_Types.comp ->
      (FStarC_Reflection_Types.comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ff ->
    fun c ->
      fun ps ->
        let x = FStarC_Reflection_V2_Builtins.inspect_comp c in
        let x1 =
          match x with
          | FStarC_Reflection_V2_Data.C_Total ret ->
              let x2 = visit_tm ff ret ps in
              FStarC_Reflection_V2_Data.C_Total x2
          | FStarC_Reflection_V2_Data.C_GTotal ret ->
              let x2 = visit_tm ff ret ps in
              FStarC_Reflection_V2_Data.C_GTotal x2
          | FStarC_Reflection_V2_Data.C_Lemma (pre, post, pats) ->
              let x2 = visit_tm ff pre ps in
              let x3 = visit_tm ff post ps in
              let x4 = visit_tm ff pats ps in
              FStarC_Reflection_V2_Data.C_Lemma (x2, x3, x4)
          | FStarC_Reflection_V2_Data.C_Eff (us, eff, res, args, decrs) ->
              let x2 = visit_tm ff res ps in
              let x3 =
                FStar_Tactics_Util.map
                  (fun uu___ ->
                     match uu___ with
                     | (a, q) ->
                         (fun ps1 -> let x4 = visit_tm ff a ps1 in (x4, q)))
                  args ps in
              let x4 = FStar_Tactics_Util.map (visit_tm ff) decrs ps in
              FStarC_Reflection_V2_Data.C_Eff (us, eff, x2, x3, x4) in
        FStarC_Reflection_V2_Builtins.pack_comp x1
