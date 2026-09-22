open Prims
let on_sort_binder
  (f :
    FStarC_Reflection_Types.term ->
      FStarC_Tactics_Types.ref_proofstate -> FStarC_Reflection_Types.term)
  (b : FStarC_Reflection_Types.binder)
  (ps : FStarC_Tactics_Types.ref_proofstate) :
  FStarC_Reflection_Types.binder=
  let x = FStarC_Reflection_V2_Builtins.inspect_binder b in
  let x1 =
    let x2 = f x.FStarC_Reflection_V2_Data.sort2 ps in
    {
      FStarC_Reflection_V2_Data.sort2 = x2;
      FStarC_Reflection_V2_Data.qual = (x.FStarC_Reflection_V2_Data.qual);
      FStarC_Reflection_V2_Data.attrs = (x.FStarC_Reflection_V2_Data.attrs);
      FStarC_Reflection_V2_Data.ppname2 =
        (x.FStarC_Reflection_V2_Data.ppname2)
    } in
  FStarC_Reflection_V2_Builtins.pack_binder x1
let on_sort_simple_binder
  (f :
    FStarC_Reflection_Types.term ->
      FStarC_Tactics_Types.ref_proofstate -> FStarC_Reflection_Types.term)
  (b : FStarC_Reflection_V2_Data.simple_binder)
  (ps : FStarC_Tactics_Types.ref_proofstate) :
  FStarC_Reflection_V2_Data.simple_binder=
  let x = FStarC_Reflection_V2_Builtins.inspect_binder b in
  let x1 =
    let x2 = f x.FStarC_Reflection_V2_Data.sort2 ps in
    {
      FStarC_Reflection_V2_Data.sort2 = x2;
      FStarC_Reflection_V2_Data.qual = (x.FStarC_Reflection_V2_Data.qual);
      FStarC_Reflection_V2_Data.attrs = (x.FStarC_Reflection_V2_Data.attrs);
      FStarC_Reflection_V2_Data.ppname2 =
        (x.FStarC_Reflection_V2_Data.ppname2)
    } in
  FStarC_Reflection_V2_Builtins.pack_binder x1
let rec visit_tm
  (ff :
    FStarC_Reflection_Types.term ->
      FStarC_Tactics_Types.ref_proofstate -> FStarC_Reflection_Types.term)
  (t : FStarC_Reflection_Types.term)
  (ps : FStarC_Tactics_Types.ref_proofstate) : FStarC_Reflection_Types.term=
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
                        | (FStar_Pervasives.Inl t1, tacopt, use_eq) ->
                            let x6 =
                              let x7 = visit_tm ff t1 ps1 in
                              FStar_Pervasives.Inl x7 in
                            let x7 =
                              FStar_Tactics_Util.map_opt (visit_tm ff) tacopt
                                ps1 in
                            (x6, x7, use_eq)
                        | (FStar_Pervasives.Inr c, tacopt, use_eq) ->
                            let x6 =
                              let x7 = visit_comp ff c ps1 in
                              FStar_Pervasives.Inr x7 in
                            let x7 =
                              FStar_Tactics_Util.map_opt (visit_tm ff) tacopt
                                ps1 in
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
and visit_br
  (ff :
    FStarC_Reflection_Types.term ->
      FStarC_Tactics_Types.ref_proofstate -> FStarC_Reflection_Types.term)
  (b : FStarC_Reflection_V2_Data.branch)
  (ps : FStarC_Tactics_Types.ref_proofstate) :
  FStarC_Reflection_V2_Data.branch=
  let x = b in
  match x with
  | (p, t) ->
      let x1 = visit_pat ff p ps in let x2 = visit_tm ff t ps in (x1, x2)
and visit_pat
  (ff :
    FStarC_Reflection_Types.term ->
      FStarC_Tactics_Types.ref_proofstate -> FStarC_Reflection_Types.term)
  (p : FStarC_Reflection_V2_Data.pattern) :
  FStarC_Tactics_Types.ref_proofstate -> FStarC_Reflection_V2_Data.pattern=
  match p with
  | FStarC_Reflection_V2_Data.Pat_Constant uu___ -> (fun uu___1 -> p)
  | FStarC_Reflection_V2_Data.Pat_Var (v, s) ->
      (fun uu___ -> FStarC_Reflection_V2_Data.Pat_Var (v, s))
  | FStarC_Reflection_V2_Data.Pat_Cons (head, univs, subpats) ->
      (fun ps ->
         let x =
           FStar_Tactics_Util.map
             (fun uu___ ->
                match uu___ with
                | (p1, b) ->
                    (fun ps1 -> let x1 = visit_pat ff p1 ps1 in (x1, b)))
             subpats ps in
         FStarC_Reflection_V2_Data.Pat_Cons (head, univs, x))
  | FStarC_Reflection_V2_Data.Pat_Dot_Term t ->
      (fun ps ->
         let x = FStar_Tactics_Util.map_opt (visit_tm ff) t ps in
         FStarC_Reflection_V2_Data.Pat_Dot_Term x)
and visit_comp
  (ff :
    FStarC_Reflection_Types.term ->
      FStarC_Tactics_Types.ref_proofstate -> FStarC_Reflection_Types.term)
  (c : FStarC_Reflection_Types.comp)
  (ps : FStarC_Tactics_Types.ref_proofstate) : FStarC_Reflection_Types.comp=
  let x = FStarC_Reflection_V2_Builtins.inspect_comp c in
  let x1 =
    let x2 = visit_tm ff x.FStarC_Reflection_V2_Data.result_typ ps in
    let x3 =
      FStar_Tactics_Util.map (visit_flag ff)
        x.FStarC_Reflection_V2_Data.flags ps in
    {
      FStarC_Reflection_V2_Data.effect_name =
        (x.FStarC_Reflection_V2_Data.effect_name);
      FStarC_Reflection_V2_Data.result_typ = x2;
      FStarC_Reflection_V2_Data.flags = x3;
      FStarC_Reflection_V2_Data.source_effect_name =
        (x.FStarC_Reflection_V2_Data.source_effect_name)
    } in
  FStarC_Reflection_V2_Builtins.pack_comp x1
and visit_flag
  (ff :
    FStarC_Reflection_Types.term ->
      FStarC_Tactics_Types.ref_proofstate -> FStarC_Reflection_Types.term)
  (f : FStarC_Reflection_V2_Data.cflag) :
  FStarC_Tactics_Types.ref_proofstate -> FStarC_Reflection_V2_Data.cflag=
  match f with
  | FStarC_Reflection_V2_Data.SMTPAT t ->
      (fun ps ->
         let x = visit_tm ff t ps in FStarC_Reflection_V2_Data.SMTPAT x)
  | FStarC_Reflection_V2_Data.DECREASES
      (FStarC_Reflection_V2_Data.Decreases_lex ts) ->
      (fun ps ->
         let x =
           let x1 = FStar_Tactics_Util.map (visit_tm ff) ts ps in
           FStarC_Reflection_V2_Data.Decreases_lex x1 in
         FStarC_Reflection_V2_Data.DECREASES x)
  | FStarC_Reflection_V2_Data.DECREASES
      (FStarC_Reflection_V2_Data.Decreases_wf (rel, e)) ->
      (fun ps ->
         let x = visit_tm ff rel ps in
         let x1 = visit_tm ff e ps in
         FStarC_Reflection_V2_Data.DECREASES
           (FStarC_Reflection_V2_Data.Decreases_wf (x, x1)))
