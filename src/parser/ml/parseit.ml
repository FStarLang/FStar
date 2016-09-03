open FStar_Util
open FStar_Absyn_Syntax
open Lexing

let resetLexbufPos filename lexbuf =
  lexbuf.lex_curr_p <- {
    pos_fname= FStar_Range.encode_file filename;
    pos_cnum = 0; pos_bol = 0;
    pos_lnum=1 }

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


let check_extension fn =
    if not (FStar_Util.ends_with fn ".fst")
    && not (FStar_Util.ends_with fn ".fsti")
    then raise (FStar_Syntax_Syntax.Err("Unrecognized file extension: " ^fn))

let parse fn =
  FStar_Parser_Util.warningHandler := (function
    | e -> Printf.printf "There was some warning (TODO)\n");

  let filename,lexbuf = match fn with
    | Inl(f) ->
        check_extension f;
	let f' = find_file f in
        (try f', Lexing.from_string (read_file f')
         with _ -> raise (Err(FStar_Util.format1 "Unable to open file: %s\n" f')))
    | Inr(s) ->
      "<input>", Lexing.from_string s in

  resetLexbufPos filename lexbuf;

  let lexer = FStar_Parser_LexFStar.token in
  let tokenize = FStar_Parser_LexFilter.tokenizer lexer lexbuf in
  try
      let fileOrFragment = FStar_Parser_Parse.inputFragment tokenize lexbuf in
      let frags = match fileOrFragment with
          | Inl mods ->
             if FStar_Util.ends_with filename ".fsti"
             then Inl (mods |> FStar_List.map (function
                  | FStar_Parser_AST.Module(l,d) ->
                    FStar_Parser_AST.Interface(l, d, true)
                  | _ -> failwith "Impossible"))
             else Inl mods
          | _ -> fileOrFragment in
      Inl frags
  with
    | FStar_Syntax_Syntax.Error(msg, r)
    | FStar_Absyn_Syntax.Error(msg, r) ->
      Inr (msg, r)

    | e ->
      let pos = lexbuf.lex_curr_p in
      let p = FStar_Range.mk_pos pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1) in
      let r = FStar_Range.mk_range filename (Z.of_int p) (Z.of_int p) in
      Inr ("Syntax error: " ^ (Printexc.to_string e), r)
