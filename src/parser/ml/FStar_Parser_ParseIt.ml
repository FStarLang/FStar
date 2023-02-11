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
    | Fragment of input_frag

type parse_result =
    | ASTFragment of (FStar_Parser_AST.inputFragment * (string * FStar_Compiler_Range.range) list)
    | Term of FStar_Parser_AST.term
    | ParseError of (FStar_Errors.raw_error * string * FStar_Compiler_Range.range)

let parse fn =
  FStar_Parser_Util.warningHandler := (function
    | e -> Printf.printf "There was some warning (TODO)\n");

  let lexbuf, filename = match fn with
    | Filename f ->
        check_extension f;
        let f', contents = read_file f in
        (try create contents f' 1 0, f'
         with _ -> raise_err (Fatal_InvalidUTF8Encoding, U.format1 "File %s has invalid UTF-8 encoding.\n" f'))
    | Toplevel s
    | Fragment s ->
      create s.frag_text s.frag_fname (Z.to_int s.frag_line) (Z.to_int s.frag_col), "<input>"
  in

  let lexer () =
    let tok = FStar_Parser_LexFStar.token lexbuf in
    (tok, lexbuf.start_p, lexbuf.cur_p)
  in

  try
    match fn with
    | Filename _
    | Toplevel _ -> begin
      let fileOrFragment = MenhirLib.Convert.Simplified.traditional2revised FStar_Parser_Parse.inputFragment lexer in
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
    | Fragment _ ->
      Term (MenhirLib.Convert.Simplified.traditional2revised FStar_Parser_Parse.term lexer)
  with
    | FStar_Errors.Empty_frag ->
      ASTFragment (FStar_Pervasives.Inr [], [])

    | FStar_Errors.Error(e, msg, r, _ctx) ->
      ParseError (e, msg, r)

    | Parsing.Parse_error as _e ->
      let pos = FStar_Parser_Util.pos_of_lexpos lexbuf.cur_p in
      let r = FStar_Compiler_Range.mk_range filename pos pos in
      ParseError (Fatal_SyntaxError, "Syntax error", r)

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

module A = FStar_Parser_AST
  
let modul_to_json_string (m:A.modul)
  : string
  = Yojson.Safe.to_string (A.modul_to_yojson m)
  
let modul_of_json_string (s:string)
  : (A.modul, string) FStar_Pervasives.either
  = try
      match A.modul_of_yojson (Yojson.Safe.from_string s) with
      | Result.Ok m -> FStar_Pervasives.Inl m
      | Result.Error s -> FStar_Pervasives.Inr s
    with Yojson.Json_error msg -> FStar_Pervasives.Inr msg
  
