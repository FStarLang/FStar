
(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
#light "off"
module FStar.Parser.ParseIt
open FStar
open FStar.Util
open FStar.Errors

type filename = string

type input_frag = {
    frag_fname:filename;
    frag_text:string;
    frag_line:int;
    frag_col:int
}



let resetLexbufPos filename (lexbuf: Microsoft.FSharp.Text.Lexing.LexBuffer<char>) =
  lexbuf.EndPos <- {lexbuf.EndPos with
    pos_fname=filename;
    pos_cnum=0;
    pos_lnum=1 }

let setLexbufPos filename (lexbuf: Microsoft.FSharp.Text.Lexing.LexBuffer<char>) line col =
  lexbuf.EndPos <- {lexbuf.EndPos with
    pos_fname=filename;
    pos_cnum=col;
    pos_lnum=line }

let find_file filename =
  match Options.find_file filename with
    | Some s ->
      s
    | None ->
      raise_err (Errors.Fatal_ModuleOrFileNotFound, (Util.format1 "Unable to find file: %s\n" filename))

let vfs_entries : Util.smap<(time * string)> = Util.smap_create 1

let read_vfs_entry fname =
  Util.smap_try_find vfs_entries (Util.normalize_file_path fname)

let add_vfs_entry fname contents =
  Util.smap_add vfs_entries (Util.normalize_file_path fname) (Util.now (), contents)

let get_file_last_modification_time filename =
  match read_vfs_entry filename with
  | Some (mtime, _contents) -> mtime
  | None -> Util.get_file_last_modification_time filename

let read_file (filename:string) =
  let debug = Options.debug_any () in
  match read_vfs_entry filename with
  | Some (_mtime, contents) ->
    if debug then Util.print1 "Reading in-memory file %s\n" filename;
    filename, contents
  | None ->
    let filename = find_file filename in
    try
      if debug then Util.print1 "Opening file %s\n" filename;
      let fs = new System.IO.StreamReader(filename) in
      filename, fs.ReadToEnd ()
    with _ ->
      raise_err (Errors.Fatal_UnableToReadFile, (Util.format1 "Unable to read file %s" filename))

let fs_extensions = [".fs"; ".fsi"]
let fst_extensions = [".fst"; ".fsti"]
let interface_extensions = [".fsti"; ".fsi"]

let valid_extensions () =
  fst_extensions @ if Options.ml_ish () then fs_extensions else []

let has_extension file extensions =
  List.existsb (ends_with file) extensions

let check_extension fn =
  if (not (has_extension fn (valid_extensions ()))) then
    let message = format1 "Unrecognized extension '%s'" fn in
    raise_err (Errors.Fatal_UnrecognizedExtension, (if has_extension fn fs_extensions then
                  message ^ " (pass --MLish to process .fs and .fsi files)"
                else message))

type parse_frag =
    | Filename of filename
    | Toplevel of input_frag
    | Fragment of input_frag

type parse_result =
    | ASTFragment of (AST.inputFragment * list<(string * Range.range)>)
    | Term of AST.term
    | ParseError of (Errors.raw_error * string * Range.range)

let parse fn =
  let filename,sr,fs,line,col = match fn with
    | Filename (filename:string) ->
        check_extension filename;
        let filename', contents = read_file filename in
        filename',
        new System.IO.StringReader(contents) :> System.IO.TextReader,
        contents,
        1,
        0
    | Toplevel frag
    | Fragment frag ->
        frag.frag_fname,
        new System.IO.StringReader(frag.frag_text) :> System.IO.TextReader,
        frag.frag_text,
        frag.frag_line,
        frag.frag_col  in

  let lexbuf = Microsoft.FSharp.Text.Lexing.LexBuffer<char>.FromTextReader(sr) in
  setLexbufPos filename lexbuf line col;
  try
      let lexargs = Lexhelp.mkLexargs ((fun () -> "."), filename,fs) in
      let lexer =
          let lexer0 = LexFStar.token lexargs in
          fun lexbuf ->
              let tok = lexer0 lexbuf in
              // TODO : set up this option (needs to modify dependencies...)
              // if Options.get_debug_level () |> List.contains "Lex"
              // then
              //     printfn "token : %+A\n" tok ;
              tok
      in
      match fn with
      | Toplevel _
      | Filename _ -> begin
          let fileOrFragment = Parse.inputFragment lexer lexbuf in
          let frags = match fileOrFragment with
          | Inl modul ->
              if has_extension filename interface_extensions
              then match modul with
              | AST.Module(l,d) ->
                  Inl (AST.Interface(l, d, true))
              | _ -> failwith "Impossible"
              else Inl modul
           | _ -> fileOrFragment in
           let non_polymorphic_nil : list<string * FStar.Range.range> = [] in
           ASTFragment (frags, non_polymorphic_nil)
           end
      | Fragment _ ->
          Term (Parse.term lexer lexbuf)
  with
    | Empty_frag ->
        ASTFragment (Inr [], [])
    | Error(e, msg, r) ->
        ParseError(e, msg, r)
    | e ->
        let pos_of_lexpos (p: Microsoft.FSharp.Text.Lexing.Position) =
            Range.mk_pos p.pos_lnum (p.pos_cnum - p.pos_bol) in
        let p0 = pos_of_lexpos lexbuf.StartPos in
        let p1 = pos_of_lexpos lexbuf.EndPos in
        let r = Range.mk_range filename p0 p1 in
        ParseError (Errors.Fatal_SyntaxError, (if Options.trace_error ()
                     then sprintf "Syntax error (%A)" e
                     else sprintf "Syntax error (%s)" e.Message), r)

(** Parsing of command-line error/warning/silent flags. *)
let parse_warn_error s =
  let user_flags =
    if s = "" then []
    else
      let lexbuf = Microsoft.FSharp.Text.Lexing.LexBuffer<char>.FromString s in
      let lexer lexbuf = LexFStar.token (Lexhelp.mkLexargs ((fun () -> "."), "","")) lexbuf in
        try
          Parse.warn_error_list lexer lexbuf
        with e ->
          FStar.Errors.log_issue Range.dummyRange (Warning_MalformedWarnErrorList, "Malformed warn-error list, ignored");
          []
   in
   FStar.Errors.update_flags user_flags
