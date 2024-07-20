module U = FStar_Compiler_Util
open FStar_Errors
open FStar_Syntax_Syntax
open Lexing
open FStar_Sedlexing
module Codes = FStar_Errors_Codes
module Msg = FStar_Errors_Msg

type filename = string

type input_frag = {
    frag_fname:filename;
    frag_text:string;
    frag_line:Prims.int;
    frag_col:Prims.int
}

val read_vfs_entry : string -> (U.time * string) option
val add_vfs_entry: string -> string -> unit
val get_file_last_modification_time: string -> U.time

type parse_frag =
    | Filename of filename
    | Toplevel of input_frag
    | Incremental of input_frag
    | Fragment of input_frag

type parse_error = (Codes.raw_error * Msg.error_message * FStar_Compiler_Range.range)

type code_fragment = {
   range : FStar_Compiler_Range.range;
   code: string;
}

type parse_result =
    | ASTFragment of (FStar_Parser_AST.inputFragment * (string * FStar_Compiler_Range.range) list)
    | IncrementalFragment of ((FStar_Parser_AST.decl * code_fragment) list * (string * FStar_Compiler_Range.range) list * parse_error option)
    | Term of FStar_Parser_AST.term
    | ParseError of parse_error

val parse_incremental_decls :
    (*filename*)string ->
    (*contents*)string ->
    FStar_Sedlexing.lexbuf ->
    (unit -> 'token * Lexing.position * Lexing.position) ->
    ('semantic_value -> FStar_Compiler_Range.range) ->
    ((Lexing.lexbuf -> 'token) -> Lexing.lexbuf ->
         ('semantic_value list * FStar_Sedlexing.snap option) option) ->
'semantic_value list * parse_error option

type lang_opts = (string * FStar_Parser_AST_Util.open_namespaces_and_abbreviations option) option
val parse: lang_opts -> parse_frag -> parse_result

val find_file: string -> string

val parse_warn_error: string -> Codes.error_setting list 

val parse_string_incrementally:
     string -> ((FStar_Parser_AST.decl list * parse_error option), (string * FStar_Compiler_Range.range) option) FStar_Pervasives.either