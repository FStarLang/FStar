open Prims
let rec for_all :
  'a .
    ('a -> (Prims.bool, Obj.t) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.bool, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun p l ->
    match l with
    | [] -> (fun uu___ -> true)
    | x::xs ->
        FStar_Tactics_Effect.tac_bind () () (p x)
          (fun uu___ ->
             if uu___
             then for_all p xs
             else FStar_Tactics_Effect.lift_div_tac () (fun uu___1 -> false))
let rec check (t : FStar_Tactics_NamedView.term) :
  (Prims.bool, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_NamedView.inspect t ps in
    match x with
    | FStar_Tactics_NamedView.Tv_BVar bv -> false
    | FStar_Tactics_NamedView.Tv_Const uu___ -> true
    | FStar_Tactics_NamedView.Tv_Uvar (uu___, uu___1) -> false
    | FStar_Tactics_NamedView.Tv_Var uu___ -> true
    | FStar_Tactics_NamedView.Tv_FVar uu___ -> true
    | FStar_Tactics_NamedView.Tv_UInst (uu___, us) -> for_all check_u us ps
    | FStar_Tactics_NamedView.Tv_App (hd, (a, q)) ->
        let x1 = check hd ps in if x1 then check a ps else false
    | FStar_Tactics_NamedView.Tv_Abs (b, body) ->
        let x1 = check b.FStar_Tactics_NamedView.sort ps in
        if x1 then check body ps else false
    | FStar_Tactics_NamedView.Tv_Arrow (b, c) ->
        let x1 = check b.FStar_Tactics_NamedView.sort ps in
        if x1 then check_comp c ps else false
    | FStar_Tactics_NamedView.Tv_Type u -> check_u u ps
    | FStar_Tactics_NamedView.Tv_Refine (b, ref) ->
        let x1 = check b.FStar_Tactics_NamedView.sort ps in
        if x1 then check ref ps else false
    | FStar_Tactics_NamedView.Tv_Let (recf, attrs, b, def, body) ->
        let x1 = let x2 = for_all check attrs ps in Prims.op_Negation x2 in
        if x1
        then false
        else
          (let x2 = let x3 = check def ps in Prims.op_Negation x3 in
           if x2 then false else check body ps)
    | FStar_Tactics_NamedView.Tv_Match (sc, uu___, brs) ->
        let x1 = check sc ps in if x1 then for_all check_br brs ps else false
    | FStar_Tactics_NamedView.Tv_AscribedT (e, t1, uu___, uu___1) ->
        let x1 = check e ps in if x1 then check t1 ps else false
    | FStar_Tactics_NamedView.Tv_AscribedC (e, c, uu___, uu___1) ->
        let x1 = check e ps in if x1 then check_comp c ps else false
    | FStar_Tactics_NamedView.Tv_Unknown -> true
    | FStar_Tactics_NamedView.Tv_Unsupp -> true
and check_u (u : FStar_Tactics_NamedView.universe) :
  (Prims.bool, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_NamedView.inspect_universe u ps in
    match x with
    | FStar_Tactics_NamedView.Uv_BVar uu___ -> false
    | FStar_Tactics_NamedView.Uv_Name uu___ -> true
    | FStar_Tactics_NamedView.Uv_Unif uu___ -> false
    | FStar_Tactics_NamedView.Uv_Zero -> true
    | FStar_Tactics_NamedView.Uv_Succ u1 -> check_u u1 ps
    | FStar_Tactics_NamedView.Uv_Max us -> for_all check_u us ps
    | FStar_Tactics_NamedView.Uv_Unk -> true
and check_comp (c : FStar_Tactics_NamedView.comp) :
  (Prims.bool, Obj.t) FStar_Tactics_Effect.tac_repr=
  match c with
  | FStarC_Reflection_V2_Data.C_Total typ -> check typ
  | FStarC_Reflection_V2_Data.C_GTotal typ -> check typ
  | FStarC_Reflection_V2_Data.C_Lemma (pre, post, pats) ->
      FStar_Tactics_Effect.tac_bind () ()
        (FStar_Tactics_Effect.tac_bind () () (check pre)
           (fun uu___ uu___1 -> Prims.op_Negation uu___))
        (fun uu___ ->
           if uu___
           then fun uu___1 -> false
           else
             FStar_Tactics_Effect.tac_bind () ()
               (FStar_Tactics_Effect.tac_bind () () (check post)
                  (fun uu___1 uu___2 -> Prims.op_Negation uu___1))
               (fun uu___1 ->
                  if uu___1 then fun uu___2 -> false else check pats))
  | FStarC_Reflection_V2_Data.C_Eff (us, nm, res, args, decrs) ->
      FStar_Tactics_Effect.tac_bind () ()
        (FStar_Tactics_Effect.tac_bind () () (for_all check_u us)
           (fun uu___ uu___1 -> Prims.op_Negation uu___))
        (fun uu___ ->
           if uu___
           then fun uu___1 -> false
           else
             FStar_Tactics_Effect.tac_bind () ()
               (FStar_Tactics_Effect.tac_bind () () (check res)
                  (fun uu___1 uu___2 -> Prims.op_Negation uu___1))
               (fun uu___1 ->
                  if uu___1
                  then fun uu___2 -> false
                  else
                    FStar_Tactics_Effect.tac_bind () ()
                      (FStar_Tactics_Effect.tac_bind () ()
                         (for_all
                            (fun uu___2 ->
                               match uu___2 with | (a, q) -> check a) args)
                         (fun uu___2 uu___3 -> Prims.op_Negation uu___2))
                      (fun uu___2 ->
                         if uu___2
                         then fun uu___3 -> false
                         else
                           FStar_Tactics_Effect.tac_bind () ()
                             (FStar_Tactics_Effect.tac_bind () ()
                                (for_all check decrs)
                                (fun uu___3 uu___4 ->
                                   Prims.op_Negation uu___3))
                             (fun uu___3 uu___4 ->
                                if uu___3 then false else true))))
and check_br (b : FStar_Tactics_NamedView.branch) :
  (Prims.bool, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = b in match x with | (p, t) -> check t ps
let check_ln (t : FStar_Tactics_NamedView.term) :
  (Prims.bool, Obj.t) FStar_Tactics_Effect.tac_repr= check t
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.CheckLN.check_ln"
    (Prims.of_int 2)
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.CheckLN.check_ln (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 check_ln)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Syntax_Embeddings.e_bool psc ncb us args)
