module FStar.Tactics.Print

open FStar.Reflection
open FStar.Tactics.Effect
open FStar.Tactics.Builtins

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

let rec term_to_ast_string (t:term) : Tac string =
  match inspect t with
  | Tv_Var bv -> "Tv_Var " ^ bv_to_string bv
  | Tv_BVar bv -> "Tv_BVar " ^ bv_to_string bv
  | Tv_FVar fv -> "Tv_FVar " ^ fv_to_string fv
  | Tv_App hd (a, _) -> "Tv_App " ^ paren (term_to_ast_string hd ^ ", " ^ term_to_ast_string a)
  | Tv_Abs x e -> "Tv_Abs " ^ paren (binder_to_string x ^ ", " ^ term_to_ast_string e)
  | Tv_Arrow x c -> "Tv_Arrow " ^ paren (binder_to_string x ^ ", " ^ comp_to_ast_string c)
  | Tv_Type _ -> "Type"
  | Tv_Refine x e -> "Tv_Refine " ^ paren (bv_to_string x ^ ", " ^ term_to_ast_string e)
  | Tv_Const c -> const_to_ast_string c
  | Tv_Uvar i _ -> "Tv_Uvar " ^ string_of_int i
  | Tv_Let recf _ x e1 e2 ->
           "Tv_Let " ^ paren (string_of_bool recf ^ ", " ^
                              bv_to_string x ^ ", " ^
                              term_to_ast_string e1 ^ ", " ^
                              term_to_ast_string e2)
  | Tv_Match e ret_opt brs ->
    let tacopt_to_string tacopt : Tac string =
      match tacopt with
      | None -> ""
      | Some tac -> " by " ^ (term_to_ast_string tac) in
    "Tv_Match " ^
      paren (
        term_to_ast_string e ^
        ", " ^
        (match ret_opt with
         | None -> "None"
         | Some (Inl t, tacopt) -> (term_to_ast_string t) ^ (tacopt_to_string tacopt)
         | Some (Inr c, tacopt) -> (comp_to_ast_string c) ^ (tacopt_to_string tacopt)) ^
        ", " ^
        branches_to_ast_string brs)
  | Tv_AscribedT e t _ -> "Tv_AscribedT " ^ paren (term_to_ast_string e ^ ", " ^ term_to_ast_string t)
  | Tv_AscribedC e c _ -> "Tv_AscribedC " ^ paren (term_to_ast_string e ^ ", " ^ comp_to_ast_string c)
  | Tv_Unknown -> "_"

and branches_to_ast_string (brs:list branch) : Tac string =
  print_list branch_to_ast_string brs

and branch_to_ast_string (b:branch) : Tac string =
  let p, e = b in
  paren ("_pat, " ^ term_to_ast_string e)

and comp_to_ast_string (c:comp) : Tac string =
  match inspect_comp c with
  | C_Total t _ -> "Tot " ^ term_to_ast_string t
  | C_GTotal t _ -> "GTot " ^ term_to_ast_string t
  | C_Lemma pre post _ -> "Lemma " ^ term_to_ast_string pre ^ " " ^ term_to_ast_string post
  | C_Eff _ eff res _ -> "Effect " ^ paren (implode_qn eff ^ ", " ^ term_to_ast_string res)

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
