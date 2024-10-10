module U = FStarC_Compiler_Util
open FStarC_Errors
open FStarC_Syntax_Syntax
open Lexing
open FStarC_Sedlexing
module Codes = FStarC_Errors_Codes
module Msg = FStarC_Errors_Msg

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

type parse_error = (Codes.error_code * Msg.error_message * FStarC_Compiler_Range.range)

type code_fragment = {
   range : FStarC_Compiler_Range.range;
   code: string;
}

type parse_result =
    | ASTFragment of (FStarC_Parser_AST.inputFragment * (string * FStarC_Compiler_Range.range) list)
    | IncrementalFragment of ((FStarC_Parser_AST.decl * code_fragment) list * (string * FStarC_Compiler_Range.range) list * parse_error option)
    | Term of FStarC_Parser_AST.term
    | ParseError of parse_error

val parse_incremental_decls :
    (*filename*)string ->
    (*contents*)string ->
    FStarC_Sedlexing.lexbuf ->
    (unit -> 'token * Lexing.position * Lexing.position) ->
    ('semantic_value -> FStarC_Compiler_Range.range) ->
    ((Lexing.lexbuf -> 'token) -> Lexing.lexbuf ->
         ('semantic_value list * FStarC_Sedlexing.snap option) option) ->
'semantic_value list * parse_error option

type lang_opts = string option
val parse: lang_opts -> parse_frag -> parse_result

val find_file: string -> string

val parse_warn_error: string -> Codes.error_setting list 

val parse_fstar_incrementally: FStarC_Parser_AST_Util.extension_lang_parser
