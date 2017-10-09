/// =========
/// Pattern-Matching utilities
/// =========

module PatternMatching.Utils

open FStar.Tactics
open PatternMatching.Types

let string_of_qn qn = String.concat "." qn

let term_head t : string =
  match inspect t with
  | Tv_Var bv -> "Tv_Var"
  | Tv_FVar fv -> "Tv_FVar"
  | Tv_App f x -> "Tv_App"
  | Tv_Abs x t -> "Tv_Abs"
  | Tv_Arrow x t -> "Tv_Arrow"
  | Tv_Type () -> "Tv_Type"
  | Tv_Refine x t -> "Tv_Refine"
  | Tv_Const cst -> "Tv_Const"
  | Tv_Uvar i t -> "Tv_Uvar"
  | Tv_Let b t t -> "Tv_Let"
  | Tv_Match t branches -> "Tv_Match"
  | Tv_Unknown -> "Tv_Unknown"

let desc_of_pattern = function
| PAny -> "anything"
| PVar _ -> "a variable"
| PQn qn -> "a constant (" ^ string_of_qn qn ^ ")"
| PApp _ _ -> "a function application"

let rec string_of_pattern = function
| PAny -> "__"
| PVar x -> "?" ^ x
| PQn qn -> string_of_qn qn
| PApp l r -> "(" ^ string_of_pattern l ^ " "
              ^ string_of_pattern r ^ ")"

let print_term t = print (term_to_string t)

let rec tacmap (f: 'a -> Tac 'b) (ls: list 'a) : Tac (list 'b) =
  match ls with
  | [] -> []
  | hd :: tl -> f hd :: tacmap f tl

let rec tacfold_left (f: 'a -> 'b -> Tac 'a) (x: 'a) (l:list 'b) : Tac 'a (decreases l) =
  match l with
  | [] -> x
  | hd :: tl -> tacfold_left f (f x hd) tl
