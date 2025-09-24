open Fstarcompiler
open Prims
let rec for_all :
  'a .
    ('a -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun p ->
         fun l ->
           match l with
           | [] -> Obj.magic (Obj.repr (fun uu___ -> true))
           | x::xs ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x1 = p x ps in
                       if x1 then for_all p xs ps else false))) uu___1 uu___
let rec (check :
  FStar_Tactics_NamedView.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
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
          let x1 = check sc ps in
          if x1 then for_all check_br brs ps else false
      | FStar_Tactics_NamedView.Tv_AscribedT (e, t1, uu___, uu___1) ->
          let x1 = check e ps in if x1 then check t1 ps else false
      | FStar_Tactics_NamedView.Tv_AscribedC (e, c, uu___, uu___1) ->
          let x1 = check e ps in if x1 then check_comp c ps else false
      | FStar_Tactics_NamedView.Tv_Unknown -> true
      | FStar_Tactics_NamedView.Tv_Unsupp -> true
and (check_u :
  FStar_Tactics_NamedView.universe ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun u ->
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
and (check_comp :
  FStar_Tactics_NamedView.comp ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun c ->
    match c with
    | FStarC_Reflection_V2_Data.C_Total typ -> check typ
    | FStarC_Reflection_V2_Data.C_GTotal typ -> check typ
    | FStarC_Reflection_V2_Data.C_Lemma (pre, post, pats) ->
        (fun ps ->
           let x = let x1 = check pre ps in Prims.op_Negation x1 in
           if x
           then false
           else
             (let x1 = let x2 = check post ps in Prims.op_Negation x2 in
              if x1 then false else check pats ps))
    | FStarC_Reflection_V2_Data.C_Eff (us, nm, res, args, decrs) ->
        (fun ps ->
           let x = let x1 = for_all check_u us ps in Prims.op_Negation x1 in
           if x
           then false
           else
             (let x1 = let x2 = check res ps in Prims.op_Negation x2 in
              if x1
              then false
              else
                (let x2 =
                   let x3 =
                     for_all
                       (fun uu___2 -> match uu___2 with | (a, q) -> check a)
                       args ps in
                   Prims.op_Negation x3 in
                 if x2
                 then false
                 else
                   (let x3 =
                      let x4 = for_all check decrs ps in Prims.op_Negation x4 in
                    if x3 then false else true))))
and (check_br :
  FStar_Tactics_NamedView.branch ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  = fun b -> fun ps -> let x = b in match x with | (p, t) -> check t ps
let (check_ln :
  FStar_Tactics_NamedView.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> check t
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.CheckLN.check_ln" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.CheckLN.check_ln (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 check_ln)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Syntax_Embeddings.e_bool psc ncb us args)
