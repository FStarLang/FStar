(* This is just a simple lexer to parse the arguments
to --warn_error. *)

open FStarC_Parser_WarnError

module Sedlexing = FStarC_Sedlexing (* KEEP: somehow needed if even unused? *)
module L     = FStarC_Sedlexing
module E     = FStarC_Errors
module Codes = FStarC_Errors_Codes

let digit   = [%sedlex.regexp? '0'..'9']
let integer = [%sedlex.regexp? Plus digit]

let current_range lexbuf =
  FStarC_Parser_Util.mksyn_range (fst (L.range lexbuf)) (snd (L.range lexbuf))

let fail lexbuf (e, msg) =
  let m = current_range lexbuf in
  E.raise_error_text m e msg

let rec token lexbuf =
  match%sedlex lexbuf with
  | zs -> token lexbuf (* ignore whitespace *)
  | integer -> INT (Z.of_int (int_of_string (L.lexeme lexbuf)))
  | "-"  -> MINUS
  | "+"  -> PLUS
  | "@"  -> AT
  | ".." -> DOT_DOT
  | eof  -> EOF
  | _ -> fail lexbuf (Codes.Fatal_SyntaxError, "unexpected char")
