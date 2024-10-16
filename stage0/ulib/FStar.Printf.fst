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
module FStar.Printf

(*
 * A variable arity C-style printf
 * See tests/micro-benchmarks/Test.Printf.fst for example usage
 *)

open FStar.Char
open FStar.String
module I = FStar.Integers

noeq
type extension =
  | MkExtension : #a:Type0 -> $f:(a -> Tot string) -> extension

/// `arg`: The format specifiers supported
///      %b : bool
///      %d : int
///      %c : char
///      %s : string
///      %uy : U8.t
///      %us : U16.t
///      %ul : U32.t
///      %uL : U64.t
///      %y  : Int8.t
///      %i  : Int16.t
///      %l  : Int32.t
///      %L  : Int64.t
noeq
type arg =
  | Bool
  | Int
  | Char
  | String
  | U8
  | U16
  | U32
  | U64
  | I8
  | I16
  | I32
  | I64
  | Extension of extension

/// `arg_type`: Interpreting a `arg` tag as a type
let arg_type (a:arg) : Tot Type0 =
  match a with
  | Bool   -> bool
  | Int    -> int
  | Char   -> char
  | String -> string
  | U8     -> FStar.UInt8.t
  | U16    -> FStar.UInt16.t
  | U32    -> FStar.UInt32.t
  | U64    -> FStar.UInt64.t
  | I8     -> FStar.Int8.t
  | I16    -> FStar.Int16.t
  | I32    -> FStar.Int32.t
  | I64    -> FStar.Int64.t
  | Extension (MkExtension #t _)  -> t

let string_of_arg (#a:arg) (x:arg_type a) : string =
    match a with
    | Bool   -> string_of_bool x
    | Int    -> string_of_int x
    | Char   -> string_of_char x
    | String -> x
    | U8     -> FStar.UInt8.to_string x
    | U16    -> FStar.UInt16.to_string x
    | U32    -> FStar.UInt32.to_string x
    | U64    -> FStar.UInt64.to_string x
    | I8     -> FStar.Int8.to_string x
    | I16    -> FStar.Int16.to_string x
    | I32    -> FStar.Int32.to_string x
    | I64    -> FStar.Int64.to_string x
    | Extension (MkExtension f) -> f x

/// `dir`: Internal to this module
///        A 'directive"; used when parsing a format specifier
noeq
type dir =
  | Lit of char
  | Arg of arg

/// `dir_type ds`: Interpreting a list directives as a pure function type
let rec dir_type (ds:list dir) : Tot Type0 =
  match ds with
  | [] -> string
  | Lit c :: ds' -> dir_type ds'
  | Arg a :: ds' -> arg_type a -> dir_type ds'

/// `string_of_dirs ds`:
///       Interpreting a list of directives as its function,
///       in a continuation-passing style
let rec string_of_dirs
        (ds:list dir)
        (k:string -> string)
  : dir_type ds
  = match ds with
    | [] -> k ""
    | Lit c :: ds' ->
      coerce_eq () (
      string_of_dirs ds' (fun res -> k (string_of_char c ^ res))
      )
    | Arg a :: ds' ->
      fun (x : arg_type a) ->
        string_of_dirs ds' (fun res -> ((k "")
                                     ^ string_of_arg x
                                     ^ res))

type extension_parser = i:list char -> option (extension & o:list char{o << i})

/// `parse_format s`:
///     Parses a list of characters into a list of directives
///     Or None, in case the format string is invalid
let rec parse_format
      (s:list char)
      (parse_ext: extension_parser)
    : option (list dir)
    = let add_dir (d:dir) (ods : option (list dir))
        : option (list dir)
        = match ods with
          | None -> None
          | Some ds -> Some (d::ds)
      in
      match s with
      | [] -> Some []
      | ['%'] -> None

      //Unsigned integers beging with '%u'
      | '%' :: 'u' :: s' -> begin
        match s' with
        | 'y' :: s'' -> add_dir (Arg U8) (parse_format s'' parse_ext)
        | 's' :: s'' -> add_dir (Arg U16) (parse_format s'' parse_ext)
        | 'l' :: s'' -> add_dir (Arg U32) (parse_format s'' parse_ext)
        | 'L' :: s'' -> add_dir (Arg U64) (parse_format s'' parse_ext)
        | _ -> None
        end

      //User extensions begin with '%X'
      | '%' :: 'X' :: s' -> begin
        match parse_ext s' with
        | Some (ext, rest) -> add_dir (Arg (Extension ext)) (parse_format rest parse_ext)
        | _ -> None
       end

      | '%' :: c :: s' -> begin
        match c with
        | '%' -> add_dir (Lit '%')    (parse_format s' parse_ext)
        | 'b' -> add_dir (Arg Bool)   (parse_format s' parse_ext)
        | 'd' -> add_dir (Arg Int)    (parse_format s' parse_ext)
        | 'c' -> add_dir (Arg Char)   (parse_format s' parse_ext)
        | 's' -> add_dir (Arg String) (parse_format s' parse_ext)
        | 'y' -> add_dir (Arg I8)     (parse_format s' parse_ext)
        | 'i' -> add_dir (Arg I16)    (parse_format s' parse_ext)
        | 'l' -> add_dir (Arg I32)    (parse_format s' parse_ext)
        | 'L' -> add_dir (Arg I64)    (parse_format s' parse_ext)
        | _   -> None
        end
      | c :: s' ->
        add_dir (Lit c) (parse_format s' parse_ext)

/// `parse_format_string`: parses a format `string` into a list of directives
let parse_format_string
    (s:string)
    (parse_ext:extension_parser)
  : option (list dir)
  = parse_format (list_of_string s) parse_ext

let no_extensions : extension_parser = fun s -> None

/// `sprintf`: The main function of this module
///     A variable arity string formatter
///     Used as: `sprintf "format string" v1 ... vn`
///
///     It's marked `inline_for_extraction`, meaning that we don't need
///     any special support in our compilation targets to support sprintf
///
///     `sprintf "Hello %s" "world"`
///      will just extract to `"Hello " ^ "world"`
inline_for_extraction
let sprintf
    (s:string{normalize_term (b2t (Some? (parse_format_string s no_extensions)))})
    : norm [unascribe; delta; iota; zeta; primops] (dir_type (Some?.v (parse_format_string s no_extensions)))
    = norm [unascribe; delta; iota; zeta; primops] (string_of_dirs (Some?.v (parse_format_string s no_extensions)) (fun s -> s))


/// `ext_sprintf`: An extensible version of sprintf
inline_for_extraction
let ext_sprintf
    (parse_ext: extension_parser)
    (s:string{normalize_term (b2t (Some? (parse_format_string s parse_ext)))})
    : norm [unascribe; delta; iota; zeta; primops] (dir_type (Some?.v (parse_format_string s parse_ext)))
    = norm [unascribe; delta; iota; zeta; primops] (string_of_dirs (Some?.v (parse_format_string s parse_ext)) (fun s -> s))
