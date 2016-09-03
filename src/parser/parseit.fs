
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

// VALS_HACK_HERE

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
  if Options.debug_any()
  then Util.print1 "Opening file: %s\n" filename;
  try
  let fs = new System.IO.StreamReader(filename) in
  fs.ReadToEnd()
  with _ -> Util.format1 "Unable to open file: %s" filename

let check_extension fn =
    if not (Util.ends_with fn ".fst")
    && not (Util.ends_with fn ".fsti")
    then raise (FStar.Syntax.Syntax.Err("Unrecognized file extension: " ^fn))

let parse fn =
  Parser.Util.warningHandler := (function
    | e -> Printf.printf "Warning: %A\n" e);

  Parser.Util.errorHandler := (function
    | e -> raise e);

  let filename,sr,fs = match fn with
    | Inl (filename:string) ->
        check_extension filename;
        let filename' = find_file filename in
        let contents = read_file filename' in
        filename', new System.IO.StringReader(contents) :> System.IO.TextReader, contents
    | Inr (s:string) -> "<input>", new System.IO.StringReader(s) :> System.IO.TextReader, s  in

  let lexbuf = Microsoft.FSharp.Text.Lexing.LexBuffer<char>.FromTextReader(sr) in
  resetLexbufPos filename lexbuf;
  try
      let lexargs = Lexhelp.mkLexargs ((fun () -> "."), filename,fs) in
      let lexer = LexFStar.token lexargs in

      let light = LexFilter.tokenizer lexer lexbuf in

      let debug_print_tokens = false in
      let print_tokens =
          fun _ ->
              let tok = lexer lexbuf in
              printfn "%A" tok;
              tok in

      let tokenize = if filename.Contains("light-syntax") // todo: replace with #light param check
                     then (printfn "Using #light"; light)
                     else (if debug_print_tokens then print_tokens else (fun _ -> lexer lexbuf)) in

      let fileOrFragment = Parse.inputFragment tokenize lexbuf in
      let frags = match fileOrFragment with
        | Inl mods ->
           if Util.ends_with filename ".fsti"
           then Inl (mods |> List.map (function
                | AST.Module(l,d) ->
                  AST.Interface(l, d, true)
                | _ -> failwith "Impossible"))
           else Inl mods
        | _ -> fileOrFragment in
       Inl frags
  with
    | Absyn.Syntax.Error(msg, r)
    | Syntax.Syntax.Error(msg, r) ->
      Inr (msg, r)
    | e ->
      let p0 =
        let p = lexbuf.StartPos in
        Range.mk_pos p.pos_lnum (p.pos_cnum - p.pos_bol + 1) in
      let p1 =
        let p = lexbuf.EndPos in
        Range.mk_pos p.pos_lnum (p.pos_cnum - p.pos_bol + 1) in
      let r = Range.mk_range filename p0 p1 in
      Inr ("Syntax error", r)
