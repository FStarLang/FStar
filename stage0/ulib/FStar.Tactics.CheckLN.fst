module FStar.Tactics.CheckLN

open FStar.Tactics.V2.Bare
open FStar.Tactics.Util

let rec for_all (p : 'a -> Tac bool) (l : list 'a)  : Tac bool =
  match l with
  | [] -> true
  | x::xs -> if p x then for_all p xs else false

let rec check (t:term) : Tac bool =
  match inspect t with
  (* We are using the named view, which opens terms
  as needed on every node. If we reach a bvar, the original
  term is not LN. *)
  | Tv_BVar bv -> false

  | Tv_Const _ -> true
  | Tv_Uvar _ _ -> false (* conservative *)

  | Tv_Var _ -> true
  | Tv_FVar _ -> true
  | Tv_UInst _ us -> for_all check_u us
  | Tv_App hd (a, q) -> if check hd then check a else false
  | Tv_Abs b body -> if check b.sort then check body else false
  | Tv_Arrow b c -> if check b.sort then check_comp c else false
  | Tv_Type u -> check_u u
  | Tv_Refine b ref -> if check b.sort then check ref else false
  | Tv_Let recf attrs b def body ->
    if not (for_all check attrs) then false else
    if not (check def) then false else
    check body
  | Tv_Match sc _ brs -> 
    if check sc then for_all check_br brs else false
  | Tv_AscribedT e t _ _ ->
    if check e then check t else false
  | Tv_AscribedC e c _ _ ->
    if check e then check_comp c else false

  | Tv_Unknown -> true
  | Tv_Unsupp -> true // hm..
and check_u (u:universe) : Tac bool =
  match inspect_universe u with
  | Uv_BVar _ -> false
  | Uv_Name _ -> true
  | Uv_Unif _ -> false (* conservative *)
  | Uv_Zero -> true
  | Uv_Succ u -> check_u u
  | Uv_Max us -> for_all check_u us
  | Uv_Unk -> true
and check_comp (c:comp) : Tac bool =
  match c with
  | C_Total typ -> check typ
  | C_GTotal typ -> check typ
  | C_Lemma pre post pats -> 
    if not (check pre) then false else
    if not (check post) then false else
    check pats
  | C_Eff us nm res args decrs ->
     if not (for_all check_u us) then false else
     if not (check res) then false else
     if not (for_all (fun (a,q) -> check a) args) then false else
     if not (for_all check decrs) then false else
     true
 
and check_br (b:branch) : Tac bool =
  (* Could check the pattern's ascriptions too. *)
  let (p, t) = b in
  check t

[@@plugin]
let check_ln (t:term) : Tac bool = check t
