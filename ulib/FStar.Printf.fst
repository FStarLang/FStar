module FStar.Printf
(** A variable arity C-style printf **)
open FStar.Char
open FStar.String
module I = FStar.Integers

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

/// `dir`: Internal to this module
///        A 'directive"; used when parsing a format specifier
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
      string_of_dirs ds' (fun res -> k (string_of_char c ^ res))
      <: normalize_term (dir_type ds')
    | Arg a :: ds' ->
      fun (x : arg_type a) ->
        string_of_dirs ds' (fun res -> ((k "")
                                     ^ string_of_arg x
                                     ^ res))

/// `parse_format s`:
///     Parses a list of characters into a list of directives
///     Or None, in case the format string is invalid
let rec parse_format
      (s:list char)
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
      | '%' :: 'u' :: s' -> begin
        match s' with
        | 'y' :: s'' -> add_dir (Arg U8) (parse_format s'')
        | 's' :: s'' -> add_dir (Arg U16) (parse_format s'')
        | 'l' :: s'' -> add_dir (Arg U32) (parse_format s'')
        | 'L' :: s'' -> add_dir (Arg U64) (parse_format s'')
        | _ -> None
        end
      | '%' :: c :: s' -> begin
        match c with
        | '%' -> add_dir (Lit '%')    (parse_format s')
        | 'b' -> add_dir (Arg Bool)   (parse_format s')
        | 'd' -> add_dir (Arg Int)    (parse_format s')
        | 'c' -> add_dir (Arg Char)   (parse_format s')
        | 's' -> add_dir (Arg String) (parse_format s')
        | 'y' -> add_dir (Arg I8)     (parse_format s')
        | 'i' -> add_dir (Arg I16)    (parse_format s')
        | 'l' -> add_dir (Arg I32)    (parse_format s')
        | 'L' -> add_dir (Arg I64)    (parse_format s')
        | _   -> None
        end
      | c :: s' ->
        add_dir (Lit c) (parse_format s')

/// `parse_format_string`: parses a format `string` into a list of directives
let parse_format_string
    (s:string)
  : option (list dir)
  = parse_format (list_of_string s)

//THIS DOESN'T WORK WITH '--use_two_phase_tc true'; disable it locally
#set-options "--use_two_phase_tc false"
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
    (s:string{normalize_term (b2t (Some? (parse_format_string s)))})
    : normalize_term (dir_type (Some?.v (parse_format_string s)))
    = normalize_term (string_of_dirs (Some?.v (parse_format_string s)) (fun s -> s))

let test () = sprintf "%d: Hello %s, sprintf %s %ul" 0 "#fstar-hackery" "works!" 0ul
