(************************
***       Types       ***
*************************)

module Term

type symbol_cat = 
  | Tuple : symbol_cat
  | Constructor : list term -> term -> symbol_cat
  | Destructor : list term -> term -> symbol_cat

and symbol = 
  {
    name : string;
    arity : nat;
    cat : symbol_cat 
  }

and term = 
  | Func : (symbol * list term) -> term 
  | Name : string -> term

(******* List ******)

val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _::q -> 1 + (length q)

(*********************************
***        Predicates          ***
**********************************) 

(** Arity and arguments **)

type good_symbol = s:symbol{ match s.cat with 
  | Tuple  -> true
  | Constructor list_arg _ -> length list_arg = s.arity
  | Destructor list_arg _ -> length list_arg = s.arity
  }

let n:term = Name "n"

(* Does type check *)
let a:good_symbol = 
  let x = { name = "enc" ; arity = 2; cat = Constructor [n;n] n } in
  x

(** Does not type check *)
let a':good_symbol = { name = "enc" ; arity = 2; cat = Constructor [n;n] n }
(* *)
