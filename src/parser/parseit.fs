
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

let resetLexbufPos filename (lexbuf: Microsoft.FSharp.Text.Lexing.LexBuffer<char>) =
  lexbuf.EndPos <- {lexbuf.EndPos with
    pos_fname= Range.encode_file filename;
    pos_cnum=0;
    pos_lnum=1 }

let find_file filename =
  match Options.find_file filename with
    | Some s ->
      s
    | None ->
      raise (Absyn.Syntax.Err(Util.format1 "Unable to find file: %s\n" filename))

let read_file (filename:string) =
  if !Options.debug <> []
  then Util.print1 "Opening file: %s\n" filename;
  try
  let fs = new System.IO.StreamReader(filename) in
  fs.ReadToEnd()
  with _ -> Util.format1 "Unable to open file: %s" filename

let parse fn =
  Parser.Util.warningHandler := (function
    | Lexhelp.ReservedKeyword(m,s) -> Printf.printf "%s:%s" (Range.string_of_range s) m
    | e -> Printf.printf "Warning: %A\n" e);

  Parser.Util.errorHandler := (function
    | e -> raise e);

  let filename,sr,fs = match fn with
    | Inl (filename:string) ->
      let filename' = find_file filename in
      let contents = read_file filename' in
      filename', new System.IO.StringReader(contents) :> System.IO.TextReader, contents
    | Inr (s:string) -> "<input>", new System.IO.StringReader(s) :> System.IO.TextReader, s  in

  let lexbuf = Microsoft.FSharp.Text.Lexing.LexBuffer<char>.FromTextReader(sr) in
  resetLexbufPos filename lexbuf;
  let lexargs = Lexhelp.mkLexargs ((fun () -> "."), filename,fs) in
  let lexer = LexFStar.token lexargs in
  try
    let fileOrFragment = Parse.inputFragment lexer lexbuf in
    let frags = match fileOrFragment with
        | Inl mods ->
           if Util.ends_with filename ".fsi" || Util.ends_with filename ".fsti"
           then Inl (mods |> List.map (function
                | AST.Module(l,d) ->
                  AST.Interface(l, d, Util.for_some (fun m -> m=l.str) !Options.admit_fsi)
                | _ -> failwith "Impossible"))
           else Inl mods
        | _ -> fileOrFragment in
    Inl frags
  with
    | Absyn.Syntax.Error(msg, r) ->
      Inr (msg, r)
    | e ->
      let pos = lexbuf.EndPos in
      let p = Range.mk_pos pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1) in
      let r = Range.mk_range filename p p in
      Inr ("Syntax error", r)
