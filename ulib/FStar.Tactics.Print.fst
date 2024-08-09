module FStar.Tactics.Print

open FStar.Reflection.V2
open FStar.Tactics.Effect
open FStar.Stubs.Tactics.V2.Builtins
open FStar.Tactics.V2.Derived
open FStar.Tactics.NamedView

let namedv_to_string (x:namedv) : Tac string=
  unseal x.ppname ^ "#" ^ string_of_int x.uniq

private
let paren (s:string) : string = "(" ^ s ^ ")"

(* TODO: making this a local definition in print_list fails to extract. *)
private
let rec print_list_aux (f:'a -> Tac string) (xs:list 'a) : Tac string =
  match xs with
  | [] -> ""
  | [x] -> f x
  | x::xs -> f x ^ "; " ^ print_list_aux f xs

private
let print_list (f:'a -> Tac string) (l:list 'a) : Tac string =
   "[" ^ print_list_aux f l ^ "]"

let rec universe_to_ast_string (u:universe) : Tac string =
  match inspect_universe u with
  | Uv_Zero -> "Uv_Zero"
  | Uv_Succ u -> "Uv_Succ" ^ paren (universe_to_ast_string u)
  | Uv_Max us -> "Uv_Max" ^ print_list universe_to_ast_string us
  | Uv_BVar n -> "Uv_BVar" ^ paren (string_of_int n)
  | Uv_Name i -> "Uv_Name" ^ paren (fst i)
  | Uv_Unif _ -> "Uv_Unif"
  | Uv_Unk -> "Uv_Unk"

let universes_to_ast_string (us:universes) : Tac string =
  print_list universe_to_ast_string us

let rec term_to_ast_string (t:term) : Tac string =
  match inspect t with
  | Tv_Var bv -> "Tv_Var " ^ namedv_to_string bv
  | Tv_BVar bv -> "Tv_BVar " ^ bv_to_string bv
  | Tv_FVar fv -> "Tv_FVar " ^ fv_to_string fv
  | Tv_UInst fv us ->
    "Tv_UInst" ^ paren (fv_to_string fv ^ ", " ^ universes_to_ast_string us)
  | Tv_App hd (a, _) -> "Tv_App " ^ paren (term_to_ast_string hd ^ ", " ^ term_to_ast_string a)
  | Tv_Abs x e -> "Tv_Abs " ^ paren (binder_to_string x ^ ", " ^ term_to_ast_string e)
  | Tv_Arrow x c -> "Tv_Arrow " ^ paren (binder_to_string x ^ ", " ^ comp_to_ast_string c)
  | Tv_Type u -> "Type" ^ paren (universe_to_ast_string u)
  | Tv_Refine x e -> "Tv_Refine " ^ paren (binder_to_string x ^ ", " ^ term_to_ast_string e)
  | Tv_Const c -> const_to_ast_string c
  | Tv_Uvar i _ -> "Tv_Uvar " ^ string_of_int i
  | Tv_Let recf _ x e1 e2 ->
           "Tv_Let " ^ paren (string_of_bool recf ^ ", " ^
                              binder_to_string x ^ ", " ^
                              term_to_ast_string e1 ^ ", " ^
                              term_to_ast_string e2)
  | Tv_Match e ret_opt brs ->
    "Tv_Match " ^
      paren (
        term_to_ast_string e ^
        ", " ^
        match_returns_to_string ret_opt ^
        ", " ^
        branches_to_ast_string brs)
  | Tv_AscribedT e t _ use_eq -> "Tv_AscribedT " ^ paren (term_to_ast_string e ^ ", " ^ term_to_ast_string t ^ ", " ^ string_of_bool use_eq)
  | Tv_AscribedC e c _ use_eq -> "Tv_AscribedC " ^ paren (term_to_ast_string e ^ ", " ^ comp_to_ast_string c ^ ", " ^ string_of_bool use_eq)
  | Tv_Unknown -> "_"
  | Tv_Unsupp -> "<Tv_Unsupp>"

and match_returns_to_string (ret_opt:option match_returns_ascription) : Tac string =
  let tacopt_to_string tacopt : Tac string =
    match tacopt with
    | None -> ""
    | Some tac -> " by " ^ (term_to_ast_string tac) in
  match ret_opt with
  | None -> ""
  | Some (b, asc) ->
    (binder_to_string b ^ " ")
      ^
    (match asc with
     | Inl t, tacopt, _ -> (term_to_ast_string t) ^ (tacopt_to_string tacopt)
     | Inr c, tacopt, _ -> (comp_to_ast_string c) ^ (tacopt_to_string tacopt))

and branches_to_ast_string (brs:list branch) : Tac string =
  print_list branch_to_ast_string brs

and branch_to_ast_string (b:branch) : Tac string =
  let p, e = b in
  paren ("_pat, " ^ term_to_ast_string e)

and comp_to_ast_string (c:comp) : Tac string =
  match inspect_comp c with
  | C_Total t -> "Tot " ^ term_to_ast_string t
  | C_GTotal t -> "GTot " ^ term_to_ast_string t
  | C_Lemma pre post _ -> "Lemma " ^ term_to_ast_string pre ^ " " ^ term_to_ast_string post
  | C_Eff us eff res _ _ ->
    "Effect" ^ "<" ^ universes_to_ast_string us ^ "> " ^ paren (implode_qn eff ^ ", " ^ term_to_ast_string res)

and const_to_ast_string (c:vconst) : Tac string =
  match c with
  | C_Unit -> "C_Unit"
  | C_Int i -> "C_Int " ^ string_of_int i
  | C_True -> "C_True"
  | C_False -> "C_False"
  | C_String s -> "C_String " ^ s
  | C_Range _ -> "C_Range _"
  | C_Reify -> "C_Reify"
  | C_Reflect name -> "C_Reflect " ^ implode_qn name
  | C_Real r -> "C_Real \"" ^ r ^ "\""
