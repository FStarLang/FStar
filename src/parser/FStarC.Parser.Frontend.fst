(*
   Copyright 2008-2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.Parser.Frontend

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Parser
open FStarC.Errors
open FStarC.Time
open FStarC.Class.Show

module AST = FStarC.Parser.AST
module AU = FStarC.Parser.AST.Util
module G = FStarC.Parser.Grammar
module L = FStarC.Parser.Lexer
module R = FStarC.Range
module U = FStarC.Util
module Codes = FStarC.Errors.Codes
module GS = FStarC.GenSym
module HT = FStarC.HashTable

let find_file (filename:string) : ML string =
  match FStarC.Find.find_file filename with
  | Some s -> s
  | None ->
    raise_error_text R.dummyRange Codes.Fatal_ModuleOrFileNotFound
      (Format.fmt1 "Unable to find file: %s\n" filename)

(* The virtual file system: contents of files given by the IDE, which take
   precedence over the files on disk *)
let vfs_entries : HT.t string (time_of_day & string) = HT.create 1

let read_vfs_entry (fname:string) : ML (option (time_of_day & string)) =
  HT.try_find vfs_entries (Filepath.normalize_file_path fname)

let add_vfs_entry (fname:string) (contents:string) : ML unit =
  HT.add vfs_entries (Filepath.normalize_file_path fname) (get_time_of_day (), contents)

let get_file_last_modification_time (fname:string) : ML time_of_day =
  match read_vfs_entry fname with
  | Some (mtime, _contents) -> mtime
  | None -> FStarC.Time.get_file_last_modification_time fname

let read_physical_file (filename:string) : ML string =
  try U.file_get_contents filename
  with _ ->
    raise_error_text R.dummyRange Codes.Fatal_UnableToReadFile
      (Format.fmt1 "Unable to read file %s\n" filename)

let read_file (filename:string) : ML (string & string) =
  let debug = Debug.any () in
  match read_vfs_entry filename with
  | Some (_mtime, contents) ->
    if debug then Format.print1 "Reading in-memory file %s\n" filename;
    (filename, contents)
  | None ->
    let filename = find_file filename in
    if debug then Format.print1 "Opening file %s\n" filename;
    (filename, read_physical_file filename)

let fst_extensions () : ML (list string) =
  [".fst"; ".fsti"] @ List.collect (fun x -> ["." ^ x; "." ^ x ^ "i"]) (Options.lang_extensions ())

let interface_extensions () : ML (list string) =
  ".fsti" :: List.map (fun x -> "." ^ x ^ "i") (Options.lang_extensions ())

let has_extension (file:string) (extensions:list string) : ML bool =
  List.existsb (U.ends_with file) extensions

let take_lang_extension (file:string) : ML (option string) =
  List.tryFind (fun x -> U.ends_with file ("." ^ x)) (Options.lang_extensions ())

let check_extension (fn:string) : ML unit =
  if not (has_extension fn (fst_extensions ())) then
    raise_error_text R.dummyRange Codes.Fatal_UnrecognizedExtension
      (Format.fmt1 "Unrecognized extension ‘%s’" fn)

(* [contents_at contents rng] is the text of [contents] covered by [rng]. It is
   used by FStarC.Interactive.Incremental to record exactly the raw content
   of the fragment that was checked. Columns count characters, not bytes. *)
let contents_at (contents:string) : ML (R.range -> ML code_fragment) =
  let lines = U.splitlines contents in
  let split_line_at_col (line:string) (col:int) : option (string & string) =
    if col > 0 then
      let chars = String.list_of_string line in
      if col <= List.length chars then
        let prefix, suffix = U.first_N col chars in
        Some (String.string_of_list prefix, String.string_of_list suffix)
      else None
    else None
  in
  let line_from_col line pos = match split_line_at_col line pos with
    | None -> None
    | Some (_, p) -> Some p
  in
  let line_to_col line pos = match split_line_at_col line pos with
    | None -> None
    | Some (p, _) -> Some p
  in
  fun (range:R.range) ->
    let start_pos = R.start_of_range range in
    let end_pos = R.end_of_range range in
    let start_line = R.line_of_pos start_pos in
    let start_col = R.col_of_pos start_pos in
    let end_line = R.line_of_pos end_pos in
    let end_col = R.col_of_pos end_pos in
    (* discard all lines until the start line *)
    let suffix = U.nth_tail (if start_line > 0 then start_line - 1 else 0) lines in
    (* take all the lines between the start and end lines *)
    let text, rest = U.first_N (end_line - start_line) suffix in
    let text =
      match text with
      | first_line :: rest ->
        (match line_from_col first_line start_col with
         | Some s -> s :: rest
         | None -> text)
      | _ -> text
    in
    (* for the last line, take its prefix up to the end column *)
    let text =
      match rest with
      | last :: _ ->
        (match line_to_col last end_col with
         | None -> text
         | Some last ->
           (match text with
            | [] ->
              (* the last line is also the first line *)
              (match line_from_col last start_col with
               | None -> [last]
               | Some l -> [l])
            | _ -> text @ [last]))
      | _ -> text
    in
    { range; code = String.concat "\n" text }

let parse_fstar_incrementally_aux (s:string) (r:R.range)
  : ML (either AU.error_message (list AST.decl))
= let filename = R.file_of_range r in
  try
    let decls, comments, err_opt =
      G.parse_incremental filename s
        (R.line_of_pos (R.start_of_range r)) (R.col_of_pos (R.start_of_range r))
    in
    (* Frontend.parse_lang collects the comments from the buffer *)
    AU.add_comments comments;
    match err_opt with
    | None -> Inr decls
    | Some (_, _, r) -> Inr (decls @ [AST.mk_decl AST.Unparseable r []])
  with
  | Error (_, msg, r, _) -> Inl { AU.message = msg; AU.range = r }

let parse_fstar_incrementally : AU.extension_lang_parser =
  { AU.parse_decls = parse_fstar_incrementally_aux }

let _ = AU.register_extension_lang_parser "fstar" parse_fstar_incrementally

let frag_of (fn:parse_frag) : ML input_frag =
  match fn with
  | Filename f ->
    check_extension f;
    let f', contents = read_file f in
    { frag_fname = f'; frag_text = contents; frag_line = 1; frag_col = 0 }
  | Incremental frag
  | Toplevel frag
  | Fragment frag -> frag

let parse_lang (lang:string) (fn:parse_frag) : ML parse_result =
  let frag = frag_of fn in
  try
    let frag_pos = R.mk_pos frag.frag_line frag.frag_col in
    let rng = R.mk_range frag.frag_fname frag_pos frag_pos in
    let contents_at = contents_at frag.frag_text in
    let decls = AU.parse_extension_lang lang frag.frag_text rng in
    let comments = AU.flush_comments () in
    match fn with
    | Filename _ | Toplevel _ ->
      ASTFragment (AST.as_frag decls, comments)
    | Incremental _ ->
      let decls = List.map (fun (d:AST.decl) -> (d, contents_at d.drange)) decls in
      IncrementalFragment (decls, comments, None)
    | Fragment _ ->
      (* there is no term parser for language extensions *)
      ASTFragment (Inr decls, comments)
  with
  | Error (e, msg, r, _) -> ParseError (e, msg, r)

let parse_no_lang (fn:parse_frag) : ML parse_result =
  let frag = frag_of fn in
  let filename = frag.frag_fname in
  let contents = frag.frag_text in
  let line = frag.frag_line in
  let col = frag.frag_col in
  try
    match fn with
    | Filename _
    | Toplevel _ ->
      let frag, comments = G.parse_file filename contents line col in
      let frag =
        match frag with
        | Inl modul ->
          if has_extension filename (interface_extensions ())
          then Inl (AST.as_interface modul)
          else frag
        | _ -> frag
      in
      (* the comments of extension-language blocks are in the buffer *)
      ASTFragment (frag, AU.flush_comments () @ comments)
    | Incremental _ ->
      let decls, comments, err_opt = G.parse_incremental filename contents line col in
      let contents_at = contents_at contents in
      let decls = List.map (fun (d:AST.decl) -> (d, contents_at d.drange)) decls in
      IncrementalFragment (decls, AU.flush_comments () @ comments, err_opt)
    | Fragment _ ->
      Term (G.parse_term filename contents line col)
  with
  | Empty_frag -> ASTFragment (Inr [], [])
  | Error (e, msg, r, _) -> ParseError (e, msg, r)

(* [--ext parser=bench]: time the lexer alone ("lex"), the parser alone on
   the lexed tokens ("parse"), and both ("new") on each file, averaging over
   [--ext parser_bench_iters] runs (default 10); [--ext parser_bench_only]
   selects one of them. *)
let show_ms (ns:int) : ML string =
  let us = ns / 1000 in
  let frac = us % 1000 in
  show (us / 1000) ^ "." ^ (if frac < 10 then "00" else if frac < 100 then "0" else "") ^ show frac

let bench (fn:parse_frag) : ML parse_result =
  match fn with
  | Filename f ->
    let iters =
      match U.safe_int_of_string (Options.Ext.get "parser_bench_iters") with
      | Some n -> if n > 0 then n else 10
      | None -> 10
    in
    let f', contents = read_file f in
    let only = Options.Ext.get "parser_bench_only" in
    let time (name:string) (k:unit -> ML unit) : ML unit =
      if only = "" || only = name then begin
        let g0 = GS.get_gensym_state () in
        let t0 = Timing.now_ns () in
        let rec go (n:int) : ML unit =
          if n > 0 then begin
            GS.set_gensym_state g0;
            ignore (AU.flush_comments ());
            k ();
            go (n - 1)
          end
        in
        go iters;
        let t = Timing.diff_ns t0 (Timing.now_ns ()) / iters in
        Format.print3_error "PARSER-BENCH %s %s %s ms\n" f name (show_ms t)
      end
    in
    time "lex" (fun () -> ignore (L.lex_all f' contents 1 0));
    (let toks, _ = L.lex_all f' contents 1 0 in
     time "parse" (fun () -> try ignore (G.parse_tokens f' toks) with _ -> ()));
    time "new" (fun () -> ignore (parse_no_lang fn));
    parse_no_lang fn
  | _ -> parse_no_lang fn

let parse (lang_opt:lang_opts) (fn:parse_frag) : ML parse_result =
  Stats.record "parse" (fun () ->
  match lang_opt with
  | Some lang -> parse_lang lang fn
  | None ->
    let filename =
      match fn with
      | Filename fn -> fn
      | Toplevel frag
      | Incremental frag
      | Fragment frag -> frag.frag_fname
    in
    match take_lang_extension filename with
    | Some lang -> parse_lang lang fn
    | None ->
      if Options.Ext.get "parser" = "bench"
      then bench fn
      else parse_no_lang fn)

(* Parsing of the arguments of --warn_error, e.g. "@1..10-5+42". The grammar
   is (flag range)* with flag one of @ (error), + (warning) and - (silent),
   and range either INT or INT..INT. Unicode space separators are ignored. *)
type warn_error_token =
  | WE_INT of int
  | WE_MINUS
  | WE_PLUS
  | WE_AT
  | WE_DOT_DOT

let is_space_separator (n:int) : bool =
  n = 0x20 || n = 0xA0 || n = 0x1680 || (0x2000 <= n && n <= 0x200A)
  || n = 0x202F || n = 0x205F || n = 0x3000

let is_digit (n:int) : bool = 0x30 <= n && n <= 0x39

let rec lex_warn_error (cs:list int) : option (list warn_error_token) =
  match cs with
  | [] -> Some []
  | c :: cs ->
    if is_space_separator c then lex_warn_error cs
    else if is_digit c then
      let rec digits (acc:int) (cs:list int) : int & list int =
        match cs with
        | c :: cs' -> if is_digit c then digits (10 * acc + (c - 0x30)) cs' else (acc, cs)
        | [] -> (acc, cs)
      in
      let n, cs = digits (c - 0x30) cs in
      cons_opt (WE_INT n) (lex_warn_error cs)
    else if c = 0x2D then cons_opt WE_MINUS (lex_warn_error cs)
    else if c = 0x2B then cons_opt WE_PLUS (lex_warn_error cs)
    else if c = 0x40 then cons_opt WE_AT (lex_warn_error cs)
    else if c = 0x2E then
      match cs with
      | 0x2E :: cs -> cons_opt WE_DOT_DOT (lex_warn_error cs)
      | _ -> None
    else None
and cons_opt (t:warn_error_token) (ts:option (list warn_error_token)) : option (list warn_error_token) =
  match ts with
  | Some ts -> Some (t :: ts)
  | None -> None

let rec parse_warn_error_tokens (ts:list warn_error_token)
  : option (list (Codes.error_flag & (int & int)))
= let flag_and_range (f:Codes.error_flag) (ts:list warn_error_token) =
    match ts with
    | WE_INT i :: WE_DOT_DOT :: WE_INT j :: ts ->
      (match parse_warn_error_tokens ts with
       | Some l -> Some ((f, (i, j)) :: l)
       | None -> None)
    | WE_INT i :: ts ->
      (match parse_warn_error_tokens ts with
       | Some l -> Some ((f, (i, i)) :: l)
       | None -> None)
    | _ -> None
  in
  match ts with
  | [] -> Some []
  | WE_AT :: ts -> flag_and_range Codes.CAlwaysError ts
  | WE_PLUS :: ts -> flag_and_range Codes.CWarning ts
  | WE_MINUS :: ts -> flag_and_range Codes.CSilent ts
  | _ -> None

let parse_warn_error (s:string) : ML (option (list error_setting)) =
  let cs = List.map Util.int_of_char (String.list_of_string s) in
  match lex_warn_error cs with
  | None -> None
  | Some ts ->
    match parse_warn_error_tokens ts with
    | None -> None
    | Some l -> Some (update_flags l)
