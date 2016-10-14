module SimplePrintf

open FStar.Char
open FStar.String

// arguments to printf
type arg =
| Bool | Int | Char | String

// directives to printf
type dir =
| Lit : char -> dir
| Arg : arg  -> dir

let arg_type (a:arg) : Tot Type0 =
  match a with
  | Bool   -> bool
  | Int    -> int
  | Char   -> char
  | String -> string

let rec dir_type (ds:list dir) : Tot Type0 =
  match ds with
  | [] -> string
  | Lit c :: ds' -> dir_type ds'
  | Arg a :: ds' -> arg_type a -> Tot (dir_type ds')

let dir_type' ds = dir_type ds

let rec string_of_dirs ds (k:string -> Tot string) : Tot (dir_type ds) =
  match ds with
  | [] -> k ""
  | Lit c :: ds' -> 
    (string_of_dirs ds' (fun res -> k (string_of_char c ^ res))
     <: dir_type' ds' //this is an ugly workaround for #606
    )
  | Arg a :: ds' -> fun (x : arg_type a) ->
      string_of_dirs ds' (fun res -> k (match a with
                                        | Bool -> string_of_bool x
                                        | Int -> string_of_int x
                                        | Char -> string_of_char x
                                        | String -> x) ^ res)

let example1 : string =
  string_of_dirs [Arg Int; Arg String] (fun s -> s) 42 " answer"

(* TODO: This fails to extract:
./SimplePrintf.fst(45,2-45,64): Ill-typed application: application is (SimplePrintf.string_of_dirs (Prims.Cons (SimplePrintf.Arg SimplePrintf.Int) (Prims.Cons (SimplePrintf.Arg SimplePrintf.String) (Prims.Nil ))) (fun s -> s@0) 42 " answer") 
 remaining args are 42 " answer"
ml type of head is Prims.unit dir_type
*)

exception InvalidFormatString

let rec parse_format (s:list char) : Ex (list dir) =
  match s with
  | [] -> []
  | '%' :: c :: s' ->
    let d = match c with
            | '%' -> Lit '%'
            | 'b' -> Arg Bool
            | 'd' -> Arg Int
            | 'c' -> Arg Char
            | 's' -> Arg String
            | _   -> raise InvalidFormatString
    in d :: parse_format s'
  | '%' :: [] -> raise InvalidFormatString
  | c :: s' -> Lit c :: parse_format s'

(* let parse_format_pure (s:list char) : option (list dir) = *)
(*   match reify (parse_format s) with *)
(* Effect Prims.EXN cannot be reified [3 times] *)

(* Need some serious effect hiding to be able to call parse_format in
   a type! Could try to use reify but only after we switch EXN to dm4free

   Below we change parse_format to return option *)

let add_dir (d:dir) (ods : option (list dir)) : Tot (option (list dir)) =
  match ods with
  | None -> None
  | Some ds -> Some (d::ds)

let rec parse_format_pure (s:list char) : Tot (option (list dir)) =
  match s with
  | [] -> Some []
  | '%' :: c :: s' -> (match c with
                      | '%' -> add_dir (Lit '%') (parse_format_pure s')
                      | 'b' -> add_dir (Arg Bool) (parse_format_pure s')
                      | 'd' -> add_dir (Arg Int) (parse_format_pure s')
                      | 'c' -> add_dir (Arg Char) (parse_format_pure s')
                      | 's' -> add_dir (Arg String) (parse_format_pure s')
                      | _   -> None)
  | '%' :: [] -> None
  | c :: s' -> add_dir (Lit c) (parse_format_pure s')

let rec parse_format_string (s:string) : Tot (option (list dir)) =
  parse_format_pure (list_of_string s)

let sprintf (s:string{is_Some (parse_format_string s)})
  : Tot (dir_type (Some.v (parse_format_string s))) =
  string_of_dirs (Some.v (parse_format_string s)) (fun s -> s)

let example2 () =
  assert_norm (list_of_string "%d=%s" == ['%'; 'd'; '='; '%'; 's'])

(* assert_norm above works, but this if I make it a lemma it doesn't
   (could not prove post-condition)*)
(* let example2_lemma () : *)
(*   Lemma (list_of_string "%d=%s" == ['%'; 'd'; '='; '%'; 's']) = () *)


(* TODO: it seems that only the assert_norm above trigger reduce_primops,
         without reduce_primops example 4 and 5 will fail *)

(* TODO: in example 3, could it be that F* is not unfolding fixpoints, or what? *)

(* let example3 () = *)
(*   assert_norm (parse_format_pure ['%'; 'd'; '='; '%'; 's'] *)
(*     == Some [Arg Int; Arg String]) *)

(* let example3_lemma () : *)
(*   Lemma (parse_format_pure ['%'; 'd'; '='; '%'; 's'] *)
(*          == Some [Arg Int; Arg String]) = () *)

(* let example4 () = *)
(*   assert_norm (parse_format_string "%d=%s" == Some [Arg Int; Arg String]) *)


(* let example5 : string = (sprintf "%d=%s" <: int -> string -> Tot string) 42 " answer" *)

(* This requires a pesky annotation, otherwise it doesn't work *)
(* ./SimplePrintf.fst(95,59-95,61) : Error Too many arguments to function of type *)
(* (s:(s#16858:(Prims.list FStar.String.char){(Prims.b2t (Prims.is_Some (SimplePrintf.parse_format_pure s@0)))}) -> Tot (SimplePrintf.dir_type (Prims.Some.v (SimplePrintf.parse_format_pure s@0)))); got 3 arguments *)
