module U = FStar_Compiler_Util
open FStar_Errors
open FStar_Syntax_Syntax
open Lexing
open FStar_Sedlexing
open FStar_Errors_Codes
module Codes = FStar_Errors_Codes

type filename = string

type input_frag = {
    frag_fname:filename;
    frag_text:string;
    frag_line:Prims.int;
    frag_col:Prims.int
}

let resetLexbufPos filename lexbuf =
  lexbuf.cur_p <- {
    pos_fname= filename;
    pos_cnum = 0;
    pos_bol = 0;
    pos_lnum = 1 }

let setLexbufPos filename lexbuf line col =
  lexbuf.cur_p <- {
    pos_fname= filename;
    pos_cnum = col;
    pos_bol  = 0;
    pos_lnum = line }

module Path = BatPathGen.OfString

let find_file filename =
  match FStar_Options.find_file filename with
    | Some s ->
      s
    | None ->
      raise_err (Fatal_ModuleOrFileNotFound, U.format1 "Unable to find file: %s\n" filename)

let vfs_entries : (U.time * string) U.smap = U.smap_create (Z.of_int 1)

let read_vfs_entry fname =
  U.smap_try_find vfs_entries (U.normalize_file_path fname)

let add_vfs_entry fname contents =
  U.smap_add vfs_entries (U.normalize_file_path fname) (U.now (), contents)

let get_file_last_modification_time filename =
  match read_vfs_entry filename with
  | Some (mtime, _contents) -> mtime
  | None -> U.get_file_last_modification_time filename

let read_physical_file (filename: string) =
  (* BatFile.with_file_in uses Unix.openfile (which isn't available in
     js_of_ocaml) instead of Pervasives.open_in, so we don't use it here. *)
  try
    let channel = open_in_bin filename in
    BatPervasives.finally
      (fun () -> close_in channel)
      (fun channel -> really_input_string channel (in_channel_length channel))
      channel
  with e ->
    raise_err (Fatal_UnableToReadFile, U.format1 "Unable to read file %s\n" filename)

let read_file (filename:string) =
  let debug = FStar_Options.debug_any () in
  match read_vfs_entry filename with
  | Some (_mtime, contents) ->
    if debug then U.print1 "Reading in-memory file %s\n" filename;
    filename, contents
  | None ->
    let filename = find_file filename in
    if debug then U.print1 "Opening file %s\n" filename;
    filename, read_physical_file filename

let fs_extensions = [".fs"; ".fsi"]
let fst_extensions = [".fst"; ".fsti"]
let interface_extensions = [".fsti"; ".fsi"]

let valid_extensions () =
  fst_extensions @ if FStar_Options.ml_ish () then fs_extensions else []

let has_extension file extensions =
  FStar_List.existsb (U.ends_with file) extensions

let check_extension fn =
  if (not (has_extension fn (valid_extensions ()))) then
    let message = U.format1 "Unrecognized extension '%s'" fn in
    raise_err (Fatal_UnrecognizedExtension, if has_extension fn fs_extensions then
                  message ^ " (pass --MLish to process .fs and .fsi files)"
                else message)

type parse_frag =
    | Filename of filename
    | Toplevel of input_frag
    | Incremental of input_frag
    | Fragment of input_frag

type parse_error = (Codes.raw_error * string * FStar_Compiler_Range.range)


type code_fragment = {
   range: FStar_Compiler_Range.range;
   code: string;
}

type parse_result =
    | ASTFragment of (FStar_Parser_AST.inputFragment * (string * FStar_Compiler_Range.range) list)
    | IncrementalFragment of ((FStar_Parser_AST.decl * code_fragment) list * (string * FStar_Compiler_Range.range) list * parse_error option)
    | Term of FStar_Parser_AST.term
    | ParseError of parse_error

module BU = FStar_Compiler_Util
module Range = FStar_Compiler_Range

let parse fn =
  FStar_Parser_Util.warningHandler := (function
    | e -> Printf.printf "There was some warning (TODO)\n");

  let lexbuf, filename, contents = match fn with
    | Filename f ->
        check_extension f;
        let f', contents = read_file f in
        (try create contents f' 1 0, f', contents
         with _ -> raise_err (Fatal_InvalidUTF8Encoding, U.format1 "File %s has invalid UTF-8 encoding.\n" f'))
    | Incremental s
    | Toplevel s
    | Fragment s ->
      create s.frag_text s.frag_fname (Z.to_int s.frag_line) (Z.to_int s.frag_col), "<input>", s.frag_text
  in

  let lexer () =
    let tok = FStar_Parser_LexFStar.token lexbuf in
    (tok, lexbuf.start_p, lexbuf.cur_p)
  in
  let range_of_positions start fin = 
    let start_pos = FStar_Parser_Util.pos_of_lexpos start in
    let end_pos = FStar_Parser_Util.pos_of_lexpos fin in
    FStar_Compiler_Range.mk_range filename start_pos end_pos
  in
  let err_of_parse_error () =
      let pos = lexbuf.cur_p in
      Fatal_SyntaxError,
      "Syntax error",
      range_of_positions pos pos
  in
  let parse_incremental_decls () =
      let parse_one_decl = MenhirLib.Convert.Simplified.traditional2revised FStar_Parser_Parse.oneDeclOrEOF in
      let contents_at =
        let lines = U.splitlines contents in
        let split_line_at_col line col =
            if col > 0
            then (
                (* Don't index directly into the string, since this is a UTF-8 string.
                   Convert first to a list of charaters, index into that, and then convert
                   back to a string *)
                let chars = FStar_String.list_of_string line in
                if col <= List.length chars
                then (
                  let prefix, suffix = FStar_Compiler_Util.first_N (Z.of_int col) chars in
                  Some (FStar_String.string_of_list prefix, 
                        FStar_String.string_of_list suffix)
                )
                else (
                  None
                )
            )
            else None
        in
        let line_from_col line pos =
          match split_line_at_col line pos with
          | None -> None
          | Some (_, p) -> Some p
        in
        let line_to_col line pos =
          match split_line_at_col line pos with
          | None -> None
          | Some (p, _) -> Some p
        in
        (* Find the raw content of the input from the line of the start_pos to the end_pos.
           This is used by Interactive.Incremental to record exactly the raw content of the
           fragment that was checked *) 
        fun (range:Range.range) ->
          (* discard all lines until the start line *)
          let start_pos = Range.start_of_range range in
          let end_pos = Range.end_of_range range in
          let start_line = Z.to_int (Range.line_of_pos start_pos) in
          let start_col = Z.to_int (Range.col_of_pos start_pos) in
          let end_line = Z.to_int (Range.line_of_pos end_pos) in
          let end_col = Z.to_int (Range.col_of_pos end_pos) in          
          let suffix = 
            FStar_Compiler_Util.nth_tail 
              (Z.of_int (if start_line > 0 then start_line - 1 else 0))
              lines
          in
          (* Take all the lines between the start and end lines *)
          let text, rest =
            FStar_Compiler_Util.first_N
              (Z.of_int (end_line - start_line))
              suffix
          in
          let text =
            match text with
            | first_line::rest -> (
              match line_from_col first_line start_col with
              | Some s -> s :: rest
              | _ -> text
            )
            | _ -> text
          in
          let text = 
          (* For the last line itself, take the prefix of it up to the character of the end_pos *)
            match rest with
            | last::_ -> (
              match line_to_col last end_col with
              | None -> text
              | Some last ->
                (* The last line is also the first line *)
                match text with
                | [] -> (
                  match line_from_col last start_col with
                  | None -> [last]
                  | Some l -> [l]
                )
                | _ -> text @ [last]
            )
            | _ -> text
          in
          { range;
            code = FStar_String.concat "\n" text }
      in
      let open FStar_Pervasives in
      let rec parse decls =
        let start_pos = current_pos lexbuf in
        let d =
          try
            (* Reset the gensym between decls, to ensure determinism, 
               otherwise, every _ is parsed as different name *)
            FStar_GenSym.reset_gensym();
            Inl (parse_one_decl lexer)
          with 
          | FStar_Errors.Error(e, msg, r, _ctx) ->
            Inr (e, msg, r)

          | Parsing.Parse_error as _e -> 
            Inr (err_of_parse_error ())
        in
        match d with
        | Inl None -> List.rev decls, None
        | Inl (Some d) -> 
          (* The parser may advance the lexer beyond the decls last token.
             E.g., in `let f x = 0 let g = 1`, we will have parsed the decl for `f`
                   but the lexer will have advanced to `let ^ g ...` since the
                   parser will have looked ahead.
                   Rollback the lexer one token for declarations whose syntax
                   requires such lookahead to complete a production.
          *)
          let end_pos =
            if not (FStar_Parser_AST.decl_syntax_is_delimited d)
            then (
              rollback lexbuf;
              current_pos lexbuf
            )
            else (
              current_pos lexbuf
            )
          in
          let raw_contents = contents_at d.drange in
          (*
          if FStar_Options.debug_any()
          then (
            FStar_Compiler_Util.print4 "Parsed decl@%s=%s\nRaw contents@%s=%s\n"
              (FStar_Compiler_Range.string_of_def_range d.drange)
              (FStar_Parser_AST.decl_to_string d)
              (FStar_Compiler_Range.string_of_def_range raw_contents.range)
              raw_contents.code
          );
          *)
          parse ((d, raw_contents)::decls)
        | Inr err -> List.rev decls, Some err
      in
      parse []
  in
  let parse_incremental_fragment () =
      let decls, err_opt = parse_incremental_decls () in
      match err_opt with
      | None ->
        FStar_Parser_AST.as_frag (List.map fst decls)
      | Some (e, msg, r) ->
        raise (FStar_Errors.Error(e, msg, r, []))
  in

  try
    match fn with
    | Filename _
    | Toplevel _ -> begin
      let fileOrFragment =
          MenhirLib.Convert.Simplified.traditional2revised FStar_Parser_Parse.inputFragment lexer
      in
      let frags = match fileOrFragment with
          | FStar_Pervasives.Inl modul ->
             if has_extension filename interface_extensions
             then match modul with
                  | FStar_Parser_AST.Module(l,d) ->
                    FStar_Pervasives.Inl (FStar_Parser_AST.Interface(l, d, true))
                  | _ -> failwith "Impossible"
             else FStar_Pervasives.Inl modul
          | _ -> fileOrFragment
      in ASTFragment (frags, FStar_Parser_Util.flush_comments ())
      end
      
    | Incremental _ ->
      let decls, err_opt = parse_incremental_decls () in
      IncrementalFragment(decls, FStar_Parser_Util.flush_comments(), err_opt)
    
    | Fragment _ ->
      Term (MenhirLib.Convert.Simplified.traditional2revised FStar_Parser_Parse.term lexer)
  with
    | FStar_Errors.Empty_frag ->
      ASTFragment (FStar_Pervasives.Inr [], [])

    | FStar_Errors.Error(e, msg, r, _ctx) ->
      ParseError (e, msg, r)

    | Parsing.Parse_error as _e ->
      ParseError (err_of_parse_error())

(** Parsing of command-line error/warning/silent flags. *)
let parse_warn_error s =
  let user_flags =
    if s = ""
    then []
    else
      let lexbuf = FStar_Sedlexing.create s "" 0 (String.length s) in
      let lexer() = let tok = FStar_Parser_LexFStar.token lexbuf in
        (tok, lexbuf.start_p, lexbuf.cur_p)
      in
      try
        MenhirLib.Convert.Simplified.traditional2revised FStar_Parser_Parse.warn_error_list lexer
      with e ->
        failwith (U.format1 "Malformed warn-error list: %s" s)
  in
  FStar_Errors.update_flags user_flags
