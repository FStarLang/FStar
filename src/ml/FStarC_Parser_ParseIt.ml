module U = FStarC_Util
open FStarC_SMap
open FStarC_Errors
open FStarC_Syntax_Syntax
open Lexing
open FStarC_Sedlexing
open FStarC_Errors_Codes
module Codes = FStarC_Errors_Codes
module Msg = FStarC_Errors_Msg
module Filepath = FStarC_Filepath
module SMap = FStarC_SMap

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

let find_file filename =
  match FStarC_Find.find_file filename with
    | Some s ->
      s
    | None ->
      raise_error_text FStarC_Range.dummyRange Fatal_ModuleOrFileNotFound (FStarC_Format.fmt1 "Unable to find file: %s\n" filename)

let vfs_entries : (FStarC_Time.time_of_day * string) SMap.t = SMap.create (Z.of_int 1)

let read_vfs_entry fname =
  SMap.try_find vfs_entries (Filepath.normalize_file_path fname)

let add_vfs_entry fname contents =
  SMap.add vfs_entries (Filepath.normalize_file_path fname) (FStarC_Time.get_time_of_day (), contents)

let get_file_last_modification_time filename =
  match read_vfs_entry filename with
  | Some (mtime, _contents) -> mtime
  | None -> FStarC_Time.get_file_last_modification_time filename

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
    raise_error_text FStarC_Range.dummyRange Fatal_UnableToReadFile (FStarC_Format.fmt1 "Unable to read file %s\n" filename)

let read_file (filename:string) =
  let debug = FStarC_Debug.any () in
  match read_vfs_entry filename with
  | Some (_mtime, contents) ->
    if debug then FStarC_Format.print1 "Reading in-memory file %s\n" filename;
    filename, contents
  | None ->
    let filename = find_file filename in
    if debug then FStarC_Format.print1 "Opening file %s\n" filename;
    filename, read_physical_file filename

let extra_extensions () = List.concat_map (fun x -> ["." ^ x; "." ^ x ^ "i"]) (FStarC_Options.lang_extensions ())
let fst_extensions () = [".fst"; ".fsti"] @ extra_extensions ()
let extra_extensions_interface () = List.map (fun x -> "." ^ x ^ "i") (FStarC_Options.lang_extensions ())
let interface_extensions () = [".fsti"] @ extra_extensions_interface ()

let has_extension file extensions =
  FStar_List.existsb (U.ends_with file) extensions

let take_lang_extension file =
  FStar_List.tryFind (fun x -> U.ends_with file ("."^x)) (FStarC_Options.lang_extensions ())

let check_extension fn =
  if (not (has_extension fn (fst_extensions ()))) then
    let message = FStarC_Format.fmt1 "Unrecognized extension '%s'" fn in
    raise_error_text FStarC_Range.dummyRange Fatal_UnrecognizedExtension message

type parse_frag =
    | Filename of filename
    | Toplevel of input_frag
    | Incremental of input_frag
    | Fragment of input_frag

type parse_error = (Codes.error_code * Msg.error_message * FStarC_Range.t)


type code_fragment = {
   range: FStarC_Range.t;
   code: string;
}

type 'a incremental_result = 
    ('a * code_fragment) list * (string * FStarC_Range.t) list * parse_error option

type parse_result =
    | ASTFragment of (FStarC_Parser_AST.inputFragment * (string * FStarC_Range.t) list)
    | IncrementalFragment of FStarC_Parser_AST.decl incremental_result
    | Term of FStarC_Parser_AST.term
    | ParseError of parse_error

module Range = FStarC_Range

let range_of_positions filename start fin = 
  let start_pos = FStarC_Parser_Util.pos_of_lexpos start in
  let end_pos = FStarC_Parser_Util.pos_of_lexpos fin in
  FStarC_Range.mk_range filename start_pos end_pos

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

let parse_incremental_decls
    filename
    (contents:string)
    lexbuf
    (lexer:unit -> 'token * Lexing.position * Lexing.position)
    (range_of: 'semantic_value -> FStarC_Range.t)
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
              let prefix, suffix = FStarC_Util.first_N (Z.of_int col) chars in
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
    fun (range:Range.t) ->
      (* discard all lines until the start line *)
      let start_pos = Range.start_of_range range in
      let end_pos = Range.end_of_range range in
      let start_line = Z.to_int (Range.line_of_pos start_pos) in
      let start_col = Z.to_int (Range.col_of_pos start_pos) in
      let end_line = Z.to_int (Range.line_of_pos end_pos) in
      let end_col = Z.to_int (Range.col_of_pos end_pos) in          
      let suffix = 
        FStarC_Util.nth_tail 
          (Z.of_int (if start_line > 0 then start_line - 1 else 0))
          lines
      in
      (* Take all the lines between the start and end lines *)
      let text, rest =
        FStarC_Util.first_N
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
    (range_of: 'semantic_value -> FStarC_Range.t)
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

let dbg_Tokens = FStarC_Debug.get_toggle "Tokens"

let string_of_token =
  let open FStarC_Parser_Parse in
  function
  | STRING s -> "STRING " ^ s
  | IDENT s -> "IDENT " ^ s
  | NAME s -> "NAME " ^ s
  | TILDE s -> "TILDE " ^ s
  | INT8 s   -> "INT8 " ^ s
  | INT16 s  -> "INT16 " ^ s
  | INT32 s  -> "INT32 " ^ s
  | INT64 s  -> "INT64 " ^ s
  | INT s    -> "INT " ^ s
  | UINT8 s  -> "UINT8 " ^ s
  | UINT16 s -> "UINT16 " ^ s
  | UINT32 s -> "UINT32 " ^ s
  | UINT64 s -> "UINT64 " ^ s
  | SIZET s  -> "SIZET " ^ s
  | REAL s   -> "REAL " ^ s
  | CHAR c   -> "CHAR c"
  | LET -> "LET"
  | LET_OP s -> "LET_OP " ^ s
  | AND_OP s -> "AND_OP " ^ s
  | MATCH_OP s -> "MATCH_OP " ^ s
  | IF_OP s -> "IF_OP " ^ s
  | EXISTS -> "EXISTS"
  | EXISTS_OP s -> "EXISTS_OP " ^ s
  | FORALL -> "FORALL"
  | FORALL_OP s -> "FORALL_OP " ^ s
  | SEMICOLON_OP op -> "SEMICOLON_OP " ^ (match op with None -> "None" | Some s -> "(Some " ^ s ^ ")")
  | ASSUME -> "ASSUME"
  | NEW -> "NEW"
  | LOGIC -> "LOGIC"
  | ATTRIBUTES -> "ATTRIBUTES"
  | IRREDUCIBLE -> "IRREDUCIBLE"
  | UNFOLDABLE -> "UNFOLDABLE"
  | INLINE -> "INLINE"
  | OPAQUE -> "OPAQUE"
  | UNFOLD -> "UNFOLD"
  | INLINE_FOR_EXTRACTION -> "INLINE_FOR_EXTRACTION"
  | NOEXTRACT -> "NOEXTRACT"
  | NOEQUALITY -> "NOEQUALITY"
  | UNOPTEQUALITY -> "UNOPTEQUALITY"
  | PRAGMA_SHOW_OPTIONS -> "PRAGMA_SHOW_OPTIONS"
  | PRAGMA_SET_OPTIONS -> "PRAGMA_SET_OPTIONS"
  | PRAGMA_RESET_OPTIONS -> "PRAGMA_RESET_OPTIONS"
  | PRAGMA_PUSH_OPTIONS -> "PRAGMA_PUSH_OPTIONS"
  | PRAGMA_POP_OPTIONS -> "PRAGMA_POP_OPTIONS"
  | PRAGMA_RESTART_SOLVER -> "PRAGMA_RESTART_SOLVER"
  | PRAGMA_PRINT_EFFECTS_GRAPH -> "PRAGMA_PRINT_EFFECTS_GRAPH"
  | SUBTYPE -> "SUBTYPE"
  | EQUALTYPE -> "EQUALTYPE"
  | SUBKIND -> "SUBKIND"
  | BY -> "BY"
  | AND -> "AND"
  | ASSERT -> "ASSERT"
  | SYNTH -> "SYNTH"
  | BEGIN -> "BEGIN"
  | ELSE -> "ELSE"
  | END -> "END"
  | EXCEPTION -> "EXCEPTION"
  | FALSE -> "FALSE"
  | FUN -> "FUN"
  | FUNCTION -> "FUNCTION"
  | IF -> "IF"
  | IN -> "IN"
  | MODULE -> "MODULE"
  | MATCH -> "MATCH"
  | OF -> "OF"
  | FRIEND -> "FRIEND"
  | OPEN -> "OPEN"
  | REC -> "REC"
  | THEN -> "THEN"
  | TRUE -> "TRUE"
  | TRY -> "TRY"
  | TYPE -> "TYPE"
  | CALC -> "CALC"
  | CLASS -> "CLASS"
  | INSTANCE -> "INSTANCE"
  | EFFECT -> "EFFECT"
  | VAL -> "VAL"
  | INTRO -> "INTRO"
  | ELIM -> "ELIM"
  | INCLUDE -> "INCLUDE"
  | WHEN -> "WHEN"
  | AS -> "AS"
  | RETURNS -> "RETURNS"
  | RETURNS_EQ -> "RETURNS_EQ"
  | WITH -> "WITH"
  | HASH -> "HASH"
  | AMP -> "AMP"
  | LPAREN -> "LPAREN"
  | RPAREN -> "RPAREN"
  | LPAREN_RPAREN -> "LPAREN_RPAREN"
  | COMMA -> "COMMA"
  | LONG_LEFT_ARROW -> "LONG_LEFT_ARROW"
  | LARROW -> "LARROW"
  | RARROW -> "RARROW"
  | IFF -> "IFF"
  | IMPLIES -> "IMPLIES"
  | CONJUNCTION -> "CONJUNCTION"
  | DISJUNCTION -> "DISJUNCTION"
  | DOT -> "DOT"
  | COLON -> "COLON"
  | COLON_COLON -> "COLON_COLON"
  | SEMICOLON -> "SEMICOLON"
  | QMARK_DOT -> "QMARK_DOT"
  | QMARK -> "QMARK"
  | EQUALS -> "EQUALS"
  | PERCENT_LBRACK -> "PERCENT_LBRACK"
  | LBRACK_AT -> "LBRACK_AT"
  | LBRACK_AT_AT -> "LBRACK_AT_AT"
  | LBRACK_AT_AT_AT -> "LBRACK_AT_AT_AT"
  | DOT_LBRACK -> "DOT_LBRACK"
  | DOT_LENS_PAREN_LEFT -> "DOT_LENS_PAREN_LEFT"
  | DOT_LPAREN -> "DOT_LPAREN"
  | DOT_LBRACK_BAR -> "DOT_LBRACK_BAR"
  | LBRACK -> "LBRACK"
  | LBRACK_BAR -> "LBRACK_BAR"
  | LBRACE_BAR -> "LBRACE_BAR"
  | LBRACE -> "LBRACE"
  | BANG_LBRACE -> "BANG_LBRACE"
  | BAR_RBRACK -> "BAR_RBRACK"
  | BAR_RBRACE -> "BAR_RBRACE"
  | UNDERSCORE -> "UNDERSCORE"
  | LENS_PAREN_LEFT -> "LENS_PAREN_LEFT"
  | LENS_PAREN_RIGHT -> "LENS_PAREN_RIGHT"
  | SEQ_BANG_LBRACK -> "SEQ_BANG_LBRACK"
  | BAR -> "BAR"
  | RBRACK -> "RBRACK"
  | RBRACE -> "RBRACE"
  | DOLLAR -> "DOLLAR"
  | PRIVATE -> "PRIVATE"
  | REIFIABLE -> "REIFIABLE"
  | REFLECTABLE -> "REFLECTABLE"
  | REIFY -> "REIFY"
  | RANGE_OF -> "RANGE_OF"
  | SET_RANGE_OF -> "SET_RANGE_OF"
  | LBRACE_COLON_PATTERN -> "LBRACE_COLON_PATTERN"
  | PIPE_LEFT -> "PIPE_LEFT"
  | PIPE_RIGHT -> "PIPE_RIGHT"
  | NEW_EFFECT -> "NEW_EFFECT"
  | SUB_EFFECT -> "SUB_EFFECT"
  | LAYERED_EFFECT -> "LAYERED_EFFECT"
  | POLYMONADIC_BIND -> "POLYMONADIC_BIND"
  | POLYMONADIC_SUBCOMP -> "POLYMONADIC_SUBCOMP"
  | SPLICE -> "SPLICE"
  | SPLICET -> "SPLICET"
  | SQUIGGLY_RARROW -> "SQUIGGLY_RARROW"
  | TOTAL -> "TOTAL"
  | REQUIRES -> "REQUIRES"
  | ENSURES -> "ENSURES"
  | DECREASES -> "DECREASES"
  | LBRACE_COLON_WELL_FOUNDED -> "LBRACE_COLON_WELL_FOUNDED"
  | MINUS -> "MINUS"
  | COLON_EQUALS -> "COLON_EQUALS"
  | QUOTE -> "QUOTE"
  | BACKTICK_AT -> "BACKTICK_AT"
  | BACKTICK_HASH -> "BACKTICK_HASH"
  | BACKTICK -> "BACKTICK"
  | UNIV_HASH -> "UNIV_HASH"
  | BACKTICK_PERC -> "BACKTICK_PERC"
  | OPPREFIX s -> "OPPREFIX " ^ s
  | OPINFIX0a s -> "OPINFIX0a " ^ s
  | OPINFIX0b s -> "OPINFIX0b " ^ s
  | OPINFIX0c s -> "OPINFIX0c " ^ s
  | OPINFIX0d s -> "OPINFIX0d " ^ s
  | OPINFIX1 s -> "OPINFIX1 " ^ s
  | OPINFIX2 s -> "OPINFIX2 " ^ s
  | OPINFIX3L s -> "OPINFIX3L " ^ s
  | OPINFIX3R s -> "OPINFIX3R " ^ s
  | OPINFIX4 s -> "OPINFIX4 " ^ s
  | OP_MIXFIX_ASSIGNMENT s -> "OP_MIXFIX_ASSIGNMENT " ^ s
  | OP_MIXFIX_ACCESS s -> "OP_MIXFIX_ACCESS " ^ s
  | BLOB _ -> "BLOB _"
  | USE_LANG_BLOB _ -> "USE_LANG_BLOB _"
  | EOF -> "EOF"
  | DOT_DOT -> "DOT_DOT"
  | _ -> "(unknown token)"

let parse_fstar_incrementally
: FStarC_Parser_AST_Util.extension_lang_parser 
= let f =
    fun (s:string) (r:FStarC_Range.t) ->
      let open FStar_Pervasives in
      let open FStarC_Range in
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
        if !dbg_Tokens then
          print_string ("TOKEN: " ^ (string_of_token tok) ^ "\n");
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
        let err : FStarC_Parser_AST_Util.error_message = { message = msg; range = r } in
        Inl err
      | e ->
        let pos = FStarC_Parser_Util.pos_of_lexpos (lexbuf.cur_p) in
        let r = FStarC_Range.mk_range filename pos pos in
        let err : FStarC_Parser_AST_Util.error_message = { message = FStarC_Errors_Msg.mkmsg "Syntax error parsing #lang-fstar block: "; range = r } in
        Inl err
  in
  { parse_decls = f }
let _ = FStarC_Parser_AST_Util.register_extension_lang_parser "fstar" parse_fstar_incrementally

type lang_opts = string option

let parse_lang lang fn =
  let frag =
    match fn with
    | Filename f ->
      check_extension f;
      let f', contents = read_file f in
      {
        frag_fname = f';
        frag_text = contents;
        frag_line = Z.one;
        frag_col = Z.zero;
      }
    | Incremental frag
    | Toplevel frag
    | Fragment frag -> frag
  in
  try
    let frag_pos = FStarC_Range.mk_pos frag.frag_line frag.frag_col in
    let rng = FStarC_Range.mk_range frag.frag_fname frag_pos frag_pos in
    let contents_at = contents_at frag.frag_text in
    let decls = FStarC_Parser_AST_Util.parse_extension_lang lang frag.frag_text rng in
    let comments = FStarC_Parser_Util.flush_comments () in
    match fn with
      | Filename _ | Toplevel _ ->
        ASTFragment (FStarC_Parser_AST.as_frag decls, comments)
      | Incremental _ ->
        let decls = List.map (fun d -> d, contents_at d.FStarC_Parser_AST.drange) decls in
        IncrementalFragment (decls, comments, None)
      | Fragment _ ->
        (* parse_no_lang returns `Term` for Fragment, but we don't have a term parser for language extensions *)
        ASTFragment (FStar_Pervasives.Inr decls, comments)
  with
  | FStarC_Errors.Error(e, msg, r, _ctx) ->
    ParseError (e, msg, r)

let parse_no_lang fn =
  let lexbuf, filename, contents =
    match fn with
    | Filename f ->
        check_extension f;
        let f', contents = read_file f in
        (try create contents f' 1 0, f', contents
        with _ -> raise_error_text FStarC_Range.dummyRange Fatal_InvalidUTF8Encoding (FStarC_Format.fmt1 "File %s has invalid UTF-8 encoding." f'))
    | Incremental s
    | Toplevel s
    | Fragment s ->
      create s.frag_text s.frag_fname (Z.to_int s.frag_line) (Z.to_int s.frag_col), s.frag_fname, s.frag_text
  in

  let lexer () =
    let tok = FStarC_Parser_LexFStar.token lexbuf in
      if !dbg_Tokens then
        print_string ("TOKEN: " ^ (string_of_token tok) ^ "\n");
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
            if has_extension filename (interface_extensions ())
            then FStar_Pervasives.Inl (FStarC_Parser_AST.as_interface modul)
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


let parse (lang_opt:lang_opts) fn =
  FStarC_Stats.record "parse" @@ fun () ->
  FStarC_Parser_Util.warningHandler := (function
    | e -> Printf.printf "There was some warning (TODO)\n");

  match lang_opt with
  | Some lang -> parse_lang lang fn
  | None ->
    let filename =
        match fn with
        | Filename fn -> fn
        | Toplevel frag -> frag.frag_fname
        | Incremental frag -> frag.frag_fname
        | Fragment frag -> frag.frag_fname
    in
    match take_lang_extension filename with
    | Some lang -> parse_lang lang fn
    | None -> parse_no_lang fn


(** Parsing of command-line error/warning/silent flags. *)
let parse_warn_error s =
  let user_flags =
    let lexbuf = FStarC_Sedlexing.create s "" 0 (String.length s) in
    let lexer () =
      let tok = FStarC_Parser_WarnError_Lex.token lexbuf in
      (tok, lexbuf.start_p, lexbuf.cur_p)
    in
    try
      Some (MenhirLib.Convert.Simplified.traditional2revised FStarC_Parser_WarnError.warn_error_list lexer)
    with e ->
      None
  in
  let map_opt f = function
    | None -> None
    | Some x -> Some (f x)
  in
  map_opt FStarC_Errors.update_flags user_flags
