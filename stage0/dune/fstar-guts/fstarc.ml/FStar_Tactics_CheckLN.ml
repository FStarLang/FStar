open Prims
let rec for_all :
  'a .
    ('a -> FStarC_Tactics_Types.ref_proofstate -> Prims.bool) ->
      'a Prims.list -> FStarC_Tactics_Types.ref_proofstate -> Prims.bool
  =
  fun p l ->
    match l with
    | [] -> (fun uu___ -> true)
    | x::xs ->
        (fun ps -> let x1 = p x ps in if x1 then for_all p xs ps else false)
let rec check (t : FStar_Tactics_NamedView.term)
  (ps : FStarC_Tactics_Types.ref_proofstate) : Prims.bool=
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
      let x1 = let x2 = for_all check attrs ps in Prims.not x2 in
      if x1
      then false
      else
        (let x2 = let x3 = check def ps in Prims.not x3 in
         if x2 then false else check body ps)
  | FStar_Tactics_NamedView.Tv_Match (sc, uu___, brs) ->
      let x1 = check sc ps in if x1 then for_all check_br brs ps else false
  | FStar_Tactics_NamedView.Tv_AscribedT (e, t1, uu___, uu___1) ->
      let x1 = check e ps in if x1 then check t1 ps else false
  | FStar_Tactics_NamedView.Tv_AscribedC (e, c, uu___, uu___1) ->
      let x1 = check e ps in if x1 then check_comp c ps else false
  | FStar_Tactics_NamedView.Tv_Unknown -> true
  | FStar_Tactics_NamedView.Tv_Unsupp -> true
and check_u (u : FStar_Tactics_NamedView.universe)
  (ps : FStarC_Tactics_Types.ref_proofstate) : Prims.bool=
  let x = FStar_Tactics_NamedView.inspect_universe u ps in
  match x with
  | FStar_Tactics_NamedView.Uv_BVar uu___ -> false
  | FStar_Tactics_NamedView.Uv_Name uu___ -> true
  | FStar_Tactics_NamedView.Uv_Unif uu___ -> false
  | FStar_Tactics_NamedView.Uv_Zero -> true
  | FStar_Tactics_NamedView.Uv_Succ u1 -> check_u u1 ps
  | FStar_Tactics_NamedView.Uv_Max us -> for_all check_u us ps
  | FStar_Tactics_NamedView.Uv_Unk -> true
and check_comp (c : FStar_Tactics_NamedView.comp)
  (ps : FStarC_Tactics_Types.ref_proofstate) : Prims.bool=
  let x =
    let x1 = check c.FStarC_Reflection_V2_Data.result_typ ps in Prims.not x1 in
  if x
  then false
  else for_all check_flag c.FStarC_Reflection_V2_Data.flags ps
and check_flag (f : FStarC_Reflection_V2_Data.cflag) :
  FStarC_Tactics_Types.ref_proofstate -> Prims.bool=
  match f with
  | FStarC_Reflection_V2_Data.SMTPAT t -> check t
  | FStarC_Reflection_V2_Data.DECREASES
      (FStarC_Reflection_V2_Data.Decreases_lex ts) -> for_all check ts
  | FStarC_Reflection_V2_Data.DECREASES
      (FStarC_Reflection_V2_Data.Decreases_wf (rel, e)) ->
      (fun ps ->
         let x = let x1 = check rel ps in Prims.not x1 in
         if x then false else check e ps)
and check_br (b : FStar_Tactics_NamedView.branch)
  (ps : FStarC_Tactics_Types.ref_proofstate) : Prims.bool=
  let x = b in match x with | (p, t) -> check t ps
let check_ln (t : FStar_Tactics_NamedView.term) :
  FStarC_Tactics_Types.ref_proofstate -> Prims.bool= check t
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
