
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
    frag_line:Prims.int;
    frag_col:Prims.int
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
    then raise (Err("Unrecognized file extension: " ^fn))

let parse fn =
  Parser.Util.warningHandler := (function
    | e -> let msg = Printf.sprintf "Warning: %A\n" e in
           Util.print_warning msg);
  Parser.Util.errorHandler := (function
    | e -> raise e);

  let filename,sr,fs,line,col = match fn with
    | Inl (filename:string) ->
        check_extension filename;
        let filename' = find_file filename in
        let contents = read_file filename' in
        filename',
        new System.IO.StringReader(contents) :> System.IO.TextReader,
        contents,
        1,
        0
    | Inr frag ->
        "<input>",
        new System.IO.StringReader(frag.frag_text) :> System.IO.TextReader,
        frag.frag_text,
        Prims.to_int frag.frag_line,
        Prims.to_int frag.frag_col  in

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
        | Inl mods ->
           if Util.ends_with filename ".fsti"
           then Inl (mods |> List.map (function
                | AST.Module(l,d) ->
                  AST.Interface(l, d, true)
                | _ -> failwith "Impossible"))
           else Inl mods
        | _ -> fileOrFragment in
       let non_polymorphic_nil : list<string * FStar.Range.range> = [] in
       Inl (frags, non_polymorphic_nil)
  with
    | Empty_frag ->
        Inl (Inl [], [])
    | Error(msg, r) ->
      Inr (msg, r)
    | e ->
      let pos_of_lexpos (p: Microsoft.FSharp.Text.Lexing.Position) =
        Range.mk_pos p.pos_lnum (p.pos_cnum - p.pos_bol) in
      let p0 = pos_of_lexpos lexbuf.StartPos in
      let p1 = pos_of_lexpos lexbuf.EndPos in
      let r = Range.mk_range filename p0 p1 in
      Inr (sprintf "Syntax error (%A)" e, r)
