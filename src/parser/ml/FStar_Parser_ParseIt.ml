module U = FStar_Util
open FStar_Errors
open FStar_Syntax_Syntax
open Lexing

type filename = string

type input_frag = {
    frag_text:string;
    frag_line:Prims.int;
    frag_col:Prims.int
}

let resetLexbufPos filename lexbuf =
  lexbuf.lex_curr_p <- {
    pos_fname= FStar_Range.encode_file filename;
    pos_cnum = 0; pos_bol = 0;
    pos_lnum=1 }

let setLexbufPos filename lexbuf line col =
  lexbuf.lex_curr_p <- {
    pos_fname= FStar_Range.encode_file filename;
    pos_cnum = col;
    pos_bol  = 0;
    pos_lnum = line }

module Path = BatPathGen.OfString

let find_file filename =
  match FStar_Options.find_file filename with
    | Some s ->
      s
    | None ->
      raise(Err (FStar_Util.format1 "Unable to open file: %s\n" filename))

let read_file (filename:string) =
  try
    BatFile.with_file_in filename BatIO.read_all
  with e -> raise (Err (FStar_Util.format1 "Unable to open file: %s\n" filename))

let fs_extensions = [".fs"; ".fsi"]
let fst_extensions = [".fst"; ".fsti"]
let interface_extensions = [".fsti"; ".fsi"]

let valid_extensions () =
  fst_extensions @ if FStar_Options.ml_ish () then fs_extensions else []

let has_extension file extensions =
  FStar_List.existsb (FStar_Util.ends_with file) extensions

let check_extension fn =
  if (not (has_extension fn (valid_extensions ()))) then
    let message = FStar_Util.format1 "Unrecognized extension '%s'" fn in
    raise (Err (if has_extension fn fs_extensions then
                  message ^ " (pass --MLish to process .fs and .fsi files)"
                else message))

let parse fn =
  FStar_Parser_Util.warningHandler := (function
    | e -> Printf.printf "There was some warning (TODO)\n");

  let filename,lexbuf,line,col = match fn with
    | U.Inl(f) ->
        check_extension f;
        let f' = find_file f in
        (try f', Lexing.from_string (read_file f'), 1, 0
         with _ -> raise (Err(FStar_Util.format1 "Unable to open file: %s\n" f')))
    | U.Inr s ->
      "<input>", Lexing.from_string s.frag_text, Z.to_int s.frag_line, Z.to_int s.frag_col in

  setLexbufPos filename lexbuf line col;

  let lexer = FStar_Parser_LexFStar.token in

  try
      let fileOrFragment = FStar_Parser_Parse.inputFragment lexer lexbuf in
      let frags = match fileOrFragment with
          | U.Inl modul ->
             if has_extension filename interface_extensions
             then match modul with
                  | FStar_Parser_AST.Module(l,d) ->
                    U.Inl (FStar_Parser_AST.Interface(l, d, true))
                  | _ -> failwith "Impossible"
             else U.Inl modul
          | _ -> fileOrFragment
      in
      U.Inl (frags, FStar_Parser_LexFStar.flush_comments ())
  with
    | FStar_Errors.Empty_frag ->
      U.Inl (U.Inr [], [])

    | FStar_Errors.Error(msg, r) ->
      U.Inr (msg, r)

    | e ->
      let pos = FStar_Parser_Util.pos_of_lexpos lexbuf.lex_curr_p in
      let r = FStar_Range.mk_range filename pos pos in
      U.Inr ("Syntax error: " ^ (Printexc.to_string e), r)
