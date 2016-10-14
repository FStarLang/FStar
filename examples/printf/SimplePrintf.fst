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

(* Can use assert_norm above to prove a lemma that F* cannot prove on its own *)
let example2_lemma () :
  Lemma (list_of_string "%d=%s" == ['%'; 'd'; '='; '%'; 's']) =
    assert_norm (list_of_string "%d=%s" == ['%'; 'd'; '='; '%'; 's'])

(* It might seem nicer to just call normalize in the lemma statement,
   but that doesn't allow using the lemma later on; so we're stuck with the duplication *)
private let example2_lemma_looks_nicer_but_not_usable () :
  Lemma (normalize (list_of_string "%d=%s" == ['%'; 'd'; '='; '%'; 's'])) = ()
(* This also needs the private qualifier, otherwise getting this:
Interface of SimplePrintf violates its abstraction (add a 'private'
qualifier to
'SimplePrintf.example2_lemma_looks_nicer_but_not_usable'?): Expected
expression of type "(Prims.list (?50858 uu___))"; got expression "%"
of type "FStar.Char.char" *)

let example3_lemma () :
  Lemma (parse_format_pure ['%'; 'd'; '='; '%'; 's']
         == Some [Arg Int; Lit '='; Arg String]) =
  assert_norm (parse_format_pure ['%'; 'd'; '='; '%'; 's']
               == Some [Arg Int; Lit '='; Arg String])

let example4_lemma () :
  Lemma (parse_format_string "%d=%s" == Some [Arg Int; Lit '='; Arg String]) =
  assert_norm (parse_format_string "%d=%s" == Some [Arg Int; Lit '='; Arg String])

let example5 : string =
  (* Requiring such an assert_norm on each usage seems quite bad for usability *)
  assert_norm (parse_format_string "%d=%s" == Some [Arg Int; Lit '='; Arg String]);
  (sprintf "%d=%s" <: int -> string -> Tot string) 42 " answer"
  (* We also requires a pesky type annotation, but that seems more acceptable *)
