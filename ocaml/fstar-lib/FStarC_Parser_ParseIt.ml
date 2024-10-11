module U = FStarC_Compiler_Util
open FStarC_Errors
open FStarC_Syntax_Syntax
open Lexing
open FStarC_Sedlexing
open FStarC_Errors_Codes
module Codes = FStarC_Errors_Codes
module Msg = FStarC_Errors_Msg

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
  match FStarC_Find.find_file filename with
    | Some s ->
      s
    | None ->
      raise_error_text FStarC_Compiler_Range.dummyRange Fatal_ModuleOrFileNotFound (U.format1 "Unable to find file: %s\n" filename)

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
    raise_error_text FStarC_Compiler_Range.dummyRange Fatal_UnableToReadFile (U.format1 "Unable to read file %s\n" filename)

let read_file (filename:string) =
  let debug = FStarC_Compiler_Debug.any () in
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
  fst_extensions @ if FStarC_Options.ml_ish () then fs_extensions else []

let has_extension file extensions =
  FStar_List.existsb (U.ends_with file) extensions

let check_extension fn =
  if (not (has_extension fn (valid_extensions ()))) then
    let message = U.format1 "Unrecognized extension '%s'" fn in
    raise_error_text FStarC_Compiler_Range.dummyRange Fatal_UnrecognizedExtension
      (if has_extension fn fs_extensions
       then message ^ " (pass --MLish to process .fs and .fsi files)"
       else message)

type parse_frag =
    | Filename of filename
    | Toplevel of input_frag
    | Incremental of input_frag
    | Fragment of input_frag

type parse_error = (Codes.error_code * Msg.error_message * FStarC_Compiler_Range.range)


type code_fragment = {
   range: FStarC_Compiler_Range.range;
   code: string;
}

type 'a incremental_result = 
    ('a * code_fragment) list * (string * FStarC_Compiler_Range.range) list * parse_error option

type parse_result =
    | ASTFragment of (FStarC_Parser_AST.inputFragment * (string * FStarC_Compiler_Range.range) list)
    | IncrementalFragment of FStarC_Parser_AST.decl incremental_result
    | Term of FStarC_Parser_AST.term
    | ParseError of parse_error

module BU = FStarC_Compiler_Util
module Range = FStarC_Compiler_Range
module MHL = MenhirLib.Convert

let range_of_positions filename start fin = 
  let start_pos = FStarC_Parser_Util.pos_of_lexpos start in
  let end_pos = FStarC_Parser_Util.pos_of_lexpos fin in
  FStarC_Compiler_Range.mk_range filename start_pos end_pos

let err_of_parse_error filename lexbuf tag =
    let pos = lexbuf.cur_p in
    let tag =
      match tag with
      | None -> "Syntax error"
      | Some tag -> tag
    in
    Fatal_SyntaxError,
    Msg.mkmsg tag,
    range_of_positions filename pos pos

let string_of_lexpos lp = 
    let r = range_of_positions "<input>" lp lp in
    FStarC_Compiler_Range.string_of_range r

let parse_incremental_decls
    filename
    (contents:string)
    lexbuf
    (lexer:unit -> 'token * Lexing.position * Lexing.position)
    (range_of: 'semantic_value -> FStarC_Compiler_Range.range)
    (parse_one:
     (Lexing.lexbuf -> 'token) ->
         Lexing.lexbuf ->
         ('semantic_value list * FStarC_Sedlexing.snap option) option)
: 'semantic_value list * parse_error option
= let parse_one = MenhirLib.Convert.Simplified.traditional2revised parse_one in
  let err_of_parse_error tag = err_of_parse_error filename lexbuf tag in
  let open FStar_Pervasives in
  let push_decls ds decls = List.fold_left (fun decls d -> d::decls) decls ds in
  let rec parse decls =
    let start_pos = current_pos lexbuf in
    let d =
      try
        (* Reset the gensym between decls, to ensure determinism, 
            otherwise, every _ is parsed as different name *)
        FStarC_GenSym.reset_gensym();
        Inl (parse_one lexer)
      with 
      | FStarC_Errors.Error(e, msg, r, ctx) ->
        Inr (e, msg, r)

      | e -> 
        Inr (err_of_parse_error None)
    in
    match d with
    | Inl None -> 
      List.rev decls, None
    | Inl (Some (ds, snap_opt)) -> 
      (* The parser may advance the lexer beyond the decls last token. 
          E.g., in `let f x = 0 let g = 1`, we will have parsed the decl for `f`
                but the lexer will have advanced to `let ^ g ...` since the
                parser will have looked ahead.
                Rollback the lexer one token for declarations whose syntax
                requires such lookahead to complete a production.
      *)
      let _ = 
        match snap_opt with
        | None -> 
          rollback lexbuf
        | Some p -> 
          restore_snapshot lexbuf p
      in
      parse (push_decls ds decls)
    | Inr err ->
      List.rev decls, Some err
  in
  parse []

let contents_at contents =
    let lines = U.splitlines contents in
    let split_line_at_col line col =
        if col > 0
        then (
            (* Don't index directly into the string, since this is a UTF-8 string.
                Convert first to a list of characters, index into that, and then convert
                back to a string *)
            let chars = FStar_String.list_of_string line in
            if col <= List.length chars
            then (
              let prefix, suffix = FStarC_Compiler_Util.first_N (Z.of_int col) chars in
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
        FStarC_Compiler_Util.nth_tail 
          (Z.of_int (if start_line > 0 then start_line - 1 else 0))
          lines
      in
      (* Take all the lines between the start and end lines *)
      let text, rest =
        FStarC_Compiler_Util.first_N
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


let parse_incremental_fragment
    filename
    (contents:string)
    lexbuf
    (lexer:unit -> 'token * Lexing.position * Lexing.position)
    (range_of: 'semantic_value -> FStarC_Compiler_Range.range)
    (parse_one:
     (Lexing.lexbuf -> 'token) ->
         Lexing.lexbuf ->
         ('semantic_value list * FStarC_Sedlexing.snap option) option)
: 'semantic_value incremental_result
= let res = parse_incremental_decls filename contents lexbuf lexer range_of parse_one in
  let comments = FStarC_Parser_Util.flush_comments () in
  let contents_at = contents_at contents in
  let decls, err_opt = res in
  let decls = List.map (fun d -> d, contents_at (range_of d)) decls in
  decls, comments, err_opt

let parse_fstar_incrementally
: FStarC_Parser_AST_Util.extension_lang_parser 
= let f =
    fun (s:string) (r:FStarC_Compiler_Range.range) ->
      let open FStar_Pervasives in
      let open FStarC_Compiler_Range in
      let lexbuf =
        create s
             (file_of_range r)
             (Z.to_int (line_of_pos (start_of_range r)))
             (Z.to_int (col_of_pos (start_of_range r)))
      in
      let filename = file_of_range r in 
      let contents = s in
      let lexer () =
        let tok = FStarC_Parser_LexFStar.token lexbuf in
        (tok, lexbuf.start_p, lexbuf.cur_p)
      in
      try 
        let decls, err_opt = 
          parse_incremental_decls
            filename
            contents
            lexbuf
            lexer
            (fun (d:FStarC_Parser_AST.decl) -> d.drange)
            FStarC_Parser_Parse.oneDeclOrEOF
        in
        match err_opt with
        | None -> Inr decls
        | Some (_, msg, r) -> 
          let open FStarC_Parser_AST in
          let err_decl = mk_decl Unparseable r [] in
          Inr (decls @ [err_decl])
      with
      | FStarC_Errors.Error(e, msg, r, _ctx) ->
        let msg = FStarC_Errors_Msg.rendermsg msg in
        let err : FStarC_Parser_AST_Util.error_message = { message = msg; range = r } in
        Inl err
      | e ->
        let pos = FStarC_Parser_Util.pos_of_lexpos (lexbuf.cur_p) in
        let r = FStarC_Compiler_Range.mk_range filename pos pos in
        let err : FStarC_Parser_AST_Util.error_message = { message = "Syntax error parsing #lang-fstar block: "; range = r } in
        Inl err
  in
  { parse_decls = f }
let _ = FStarC_Parser_AST_Util.register_extension_lang_parser "fstar" parse_fstar_incrementally

type lang_opts = string option

let parse_lang lang fn =
  match fn with
  | Filename _ ->
    failwith "parse_lang: only in incremental mode"
  | Incremental s
  | Toplevel s
  | Fragment s ->
    try
      let frag_pos = FStarC_Compiler_Range.mk_pos s.frag_line s.frag_col in
      let rng = FStarC_Compiler_Range.mk_range s.frag_fname frag_pos frag_pos in
      let decls = FStarC_Parser_AST_Util.parse_extension_lang lang s.frag_text rng in
      let comments = FStarC_Parser_Util.flush_comments () in
      ASTFragment (Inr decls, comments)
    with
    | FStarC_Errors.Error(e, msg, r, _ctx) ->
      ParseError (e, msg, r)

let parse (lang_opt:lang_opts) fn =
  FStarC_Parser_Util.warningHandler := (function
    | e -> Printf.printf "There was some warning (TODO)\n");
  match lang_opt with
  | Some lang -> parse_lang lang fn
  | _ -> 
    let lexbuf, filename, contents =
      match fn with
      | Filename f ->
          check_extension f;
          let f', contents = read_file f in
          (try create contents f' 1 0, f', contents
          with _ -> raise_error_text FStarC_Compiler_Range.dummyRange Fatal_InvalidUTF8Encoding (U.format1 "File %s has invalid UTF-8 encoding." f'))
      | Incremental s
      | Toplevel s
      | Fragment s ->
        create s.frag_text s.frag_fname (Z.to_int s.frag_line) (Z.to_int s.frag_col), "<input>", s.frag_text
    in

    let lexer () =
      let tok = FStarC_Parser_LexFStar.token lexbuf in
      (tok, lexbuf.start_p, lexbuf.cur_p)
    in
    try
      match fn with
      | Filename _
      | Toplevel _ -> begin
        let fileOrFragment =
            MenhirLib.Convert.Simplified.traditional2revised FStarC_Parser_Parse.inputFragment lexer
        in
        let frags = match fileOrFragment with
            | FStar_Pervasives.Inl modul ->
              if has_extension filename interface_extensions
              then match modul with
                    | FStarC_Parser_AST.Module(l,d) ->
                      FStar_Pervasives.Inl (FStarC_Parser_AST.Interface(l, d, true))
                    | _ -> failwith "Impossible"
              else FStar_Pervasives.Inl modul
            | _ -> fileOrFragment
        in ASTFragment (frags, FStarC_Parser_Util.flush_comments ())
        end
        
      | Incremental i ->
        let decls, comments, err_opt = 
          parse_incremental_fragment 
            filename
            i.frag_text
            lexbuf
            lexer
            (fun (d:FStarC_Parser_AST.decl) -> d.drange)
            FStarC_Parser_Parse.oneDeclOrEOF
        in
        IncrementalFragment(decls, comments, err_opt)
      
      | Fragment _ ->
        Term (MenhirLib.Convert.Simplified.traditional2revised FStarC_Parser_Parse.term lexer)
    with
      | FStarC_Errors.Empty_frag ->
        ASTFragment (FStar_Pervasives.Inr [], [])

      | FStarC_Errors.Error(e, msg, r, _ctx) ->
        ParseError (e, msg, r)

      | e ->
  (*
      | Parsing.Parse_error as _e
      | FStarC_Parser_Parse.MenhirBasics.Error as _e  ->
  *)
        ParseError (err_of_parse_error filename lexbuf None)


(** Parsing of command-line error/warning/silent flags. *)
let parse_warn_error s =
  let user_flags =
    if s = ""
    then []
    else
      let lexbuf = FStarC_Sedlexing.create s "" 0 (String.length s) in
      let lexer() = let tok = FStarC_Parser_LexFStar.token lexbuf in
        (tok, lexbuf.start_p, lexbuf.cur_p)
      in
      try
        MenhirLib.Convert.Simplified.traditional2revised FStarC_Parser_Parse.warn_error_list lexer
      with e ->
        failwith (U.format1 "Malformed warn-error list: %s" s)
  in
  FStarC_Errors.update_flags user_flags
