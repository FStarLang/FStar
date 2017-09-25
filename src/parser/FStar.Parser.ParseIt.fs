
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
    frag_text:string;
    frag_line:int;
    frag_col:int
}



let resetLexbufPos filename (lexbuf: Microsoft.FSharp.Text.Lexing.LexBuffer<char>) =
  lexbuf.EndPos <- {lexbuf.EndPos with
    pos_fname= Range.encode_file filename;
    pos_cnum=0;
    pos_lnum=1 }

let setLexbufPos filename (lexbuf: Microsoft.FSharp.Text.Lexing.LexBuffer<char>) line col =
  lexbuf.EndPos <- {lexbuf.EndPos with
    pos_fname= Range.encode_file filename;
    pos_cnum=col;
    pos_lnum=line }

let find_file filename =
  match Options.find_file filename with
    | Some s ->
      s
    | None ->
      raise (Err(Util.format1 "Unable to find file: %s\n" filename))

let vfs_entries : Util.smap<string> = Util.smap_create 1

let read_vfs_entry fname =
  Util.smap_try_find vfs_entries fname

let add_vfs_entry fname contents =
  Util.smap_add vfs_entries fname contents

let read_file (filename:string) =
  let debug = Options.debug_any () in
  match read_vfs_entry filename with
  | Some contents ->
    if debug then Util.print1 "Reading in-memory file %s" filename;
    filename, contents
  | None ->
    let filename = find_file filename in
    try
      if debug then Util.print1 "Opening file %s" filename;
      let fs = new System.IO.StreamReader(filename) in
      filename, fs.ReadToEnd ()
    with _ ->
      raise (Err (Util.format1 "Unable to read file %s" filename))

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
    raise (Err (if has_extension fn fs_extensions then
                  message ^ " (pass --MLish to process .fs and .fsi files)"
                else message))

//val parse: either<filename, input_frag> -> either<(AST.inputFragment * list<(string * Range.range)>) , (string * Range.range)>
let parse fn =
  Parser.Util.warningHandler := (function
    | e -> let msg = Printf.sprintf "Warning: %A\n" e in
           Util.print_warning msg);
  Parser.Util.errorHandler := (function
    | e -> raise e);

  let filename,sr,fs,line,col = match fn with
    | Inl (filename:string) ->
        check_extension filename;
        let filename', contents = read_file filename in
        filename',
        new System.IO.StringReader(contents) :> System.IO.TextReader,
        contents,
        1,
        0
    | Inr frag ->
        "<input>",
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
       Inl (frags, non_polymorphic_nil)
  with
    | Empty_frag ->
      Inl (Inr [], [])
    | Error(msg, r) ->
      Inr (msg, r)
    | e ->
      let pos_of_lexpos (p: Microsoft.FSharp.Text.Lexing.Position) =
        Range.mk_pos p.pos_lnum (p.pos_cnum - p.pos_bol) in
      let p0 = pos_of_lexpos lexbuf.StartPos in
      let p1 = pos_of_lexpos lexbuf.EndPos in
      let r = Range.mk_range filename p0 p1 in
      Inr ((if Options.trace_error ()
            then sprintf "Syntax error (%A)" e
            else sprintf "Syntax error (%s)" e.Message), r)
