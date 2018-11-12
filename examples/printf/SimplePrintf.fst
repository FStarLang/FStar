(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module SimplePrintf

open FStar.Char
open FStar.String

// arguments to printf
type arg =
  | Bool
  | Int
  | Char
  | String

// directives to printf
type dir =
  | Lit of char
  | Arg of arg

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

let (^) x y = Prims.strcat x y

let rec string_of_dirs ds (k:string -> Tot string)
  : dir_type ds
  = match ds with
    | [] -> k ""
    | Lit c :: ds' ->
      string_of_dirs ds' (fun res -> k (string_of_char c ^ res))
      <: normalize_term (dir_type ds')
    | Arg a :: ds' ->
      fun (x : arg_type a) ->
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

(* Below we write parse_format returning option
   (see SimplePrintfReify for more interesting version) *)

// type hoption (a:Type) : Type = | Nothing : hoption a | Just : v:a -> hoption a

// unfold
// let just (#a:Type) (x:hoption a{Just? x}) = match x with Just y -> y

let add_dir (d:dir) (ods : option (list dir))
    : option (list dir)
    = match ods with
      | None -> None
      | Some ds -> Some (d::ds)

let rec parse_format_pure (s:list char)
    : option (list dir)
    = match s with
      | [] -> Some []
      | ['%'] -> None
      | '%' :: c :: s' -> begin
        match c with
        | '%' -> add_dir (Lit '%') (parse_format_pure s')
        | 'b' -> add_dir (Arg Bool) (parse_format_pure s')
        | 'd' -> add_dir (Arg Int) (parse_format_pure s')
        | 'c' -> add_dir (Arg Char) (parse_format_pure s')
        | 's' -> add_dir (Arg String) (parse_format_pure s')
        | _   -> None
        end
      | c :: s' ->
        add_dir (Lit c) (parse_format_pure s')

let parse_format_string (s:string) : option (list dir) =
    parse_format_pure (list_of_string s)

let valid_format_string = s:string{Some? (parse_format_string s)}

let sprintf
    (s:string{normalize_term (b2t (Some? (parse_format_string s)))})
    : normalize_term (dir_type (Some?.v (parse_format_string s)))
    = string_of_dirs (Some?.v (parse_format_string s)) (fun s -> s)

#set-options "--max_fuel 0" //no SMT reasoning about recursive functions
let test () = sprintf "%d: Hello %s, sprintf %s" 0 "#fstar-hackery" "works!"
// let test2 () = sprintf "%d: Hello %s, sprintf %s" "huh?" "#fstar-hackery" "works!"
