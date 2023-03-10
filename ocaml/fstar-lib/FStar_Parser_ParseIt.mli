module U = FStar_Compiler_Util
open FStar_Errors
open FStar_Syntax_Syntax
open Lexing
open FStar_Sedlexing

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

type parse_error = (FStar_Errors.raw_error * string * FStar_Compiler_Range.range)

type parse_result =
    | ASTFragment of (FStar_Parser_AST.inputFragment * (string * FStar_Compiler_Range.range) list)
    | IncrementalFragment of (FStar_Parser_AST.decl list * (string * FStar_Compiler_Range.range) list * parse_error option)
    | Term of FStar_Parser_AST.term
    | ParseError of parse_error

val parse: parse_frag -> parse_result

val find_file: string -> string

val parse_warn_error: string -> FStar_Errors.error_setting list 
