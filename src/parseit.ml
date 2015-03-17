open Support.Microsoft.FStar
open Support.Microsoft.FStar.Util
open Microsoft_FStar_Absyn_Syntax
open Lexing

let resetLexbufPos filename lexbuf = 
  lexbuf.lex_curr_p <- { 
    pos_fname= Range.encode_file filename; 
    pos_cnum = 0; pos_bol = 0;
    pos_lnum=1 }

let parse_file fn = 
  Parser.Util.warningHandler := (function
    | Microsoft_FStar_Parser_Lexhelp.ReservedKeyword(m,s) -> Printf.printf "%s:%s" (Range.string_of_range s) m
    | e -> Printf.printf "There was some warning (TODO)\n");

  let filename,channel = match fn with
    | Inl(f) -> f,open_in f
    | Inr(s) -> failwith "not supported" in
  
  let lexbuf = Lexing.from_channel channel in
  resetLexbufPos filename lexbuf;
  let lexer = Microsoft_FStar_Parser_LexFStar.token in
  try
    let file = Microsoft_FStar_Parser_Parse.file lexer lexbuf in
    let mods = if Util.ends_with filename ".fsi" 
               then file |> List.map (function
                | Microsoft_FStar_Parser_AST.Module(l,d) -> 
                  Microsoft_FStar_Parser_AST.Interface(l,d,Util.for_some (fun m -> m=l.str) (!Microsoft_FStar_Options.admit_fsi))
                | _ -> failwith "Impossible") 
               else file in
     Inl mods
  with 
    | Microsoft_FStar_Absyn_Syntax.Error(msg, r) -> 
      let msg = Util.format2 "ERROR %s: %s\n" (Range.string_of_range r) msg in
      Inr msg
    | e ->
      let pos = lexbuf.lex_curr_p in
      Inr  (Util.format3 "ERROR: Syntax error near line %s, character %s in file %s\n" 
              (Util.string_of_int pos.pos_lnum) 
              (Util.string_of_int (pos.pos_cnum - pos.pos_bol))
              filename)
