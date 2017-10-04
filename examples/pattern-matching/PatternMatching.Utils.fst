/// =========
/// Pattern-Matching utilities
/// =========

module PatternMatching.Utils

open FStar.Tactics
open PatternMatching.Types

let string_of_qn qn = String.concat "." qn

let term_head t : string =
  match inspect t with
  | Tv_Var bv -> "Var"
  | Tv_FVar fv -> "FVar"
  | Tv_App f x -> "App"
  | Tv_Abs x t -> "Abs"
  | Tv_Arrow x t -> "Arrow"
  | Tv_Type () -> "Type"
  | Tv_Refine x t -> "Refine"
  | Tv_Const cst -> "Const"
  | Tv_Uvar i t -> "Uvar"
  | Tv_Let b t t -> "Let"
  | Tv_Match t branches -> "Match"
  | Tv_Unknown -> "Unknown"

let desc_of_pattern = function
| SPAny -> "anything"
| SPVar _ -> "a variable"
| SPQn qn -> "a constant (" ^ string_of_qn qn ^ ")"
| SPApp _ _ -> "a function application"

let rec string_of_pattern = function
| SPAny -> "__"
| SPVar x -> "?" ^ x
| SPQn qn -> string_of_qn qn
| SPApp l r -> "(" ^ string_of_pattern l ^ " "
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
