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
module Microsoft.FStar.Parser.Driver

open Microsoft.FStar
open Microsoft.FStar.Parser
open Microsoft.FStar.Parser.AST
open Microsoft.FStar.Parser.Lexhelp
open Microsoft.FStar.Parser.Parse
open Util

let print_error msg r = 
  Printf.printf "ERROR %s: %s\n" (Range.string_of_range r) msg

let parse env fn =
  Parse.warningHandler := (function 
    | Lexhelp.ReservedKeyword(m,s) -> Printf.printf "%s:%s" (Range.string_of_range s) m
    | e -> Printf.printf "Warning: %A\n" e);

  let filename,sr = match fn with 
    | Inl (filename:string) -> filename, 
      (try new System.IO.StreamReader(filename) :> System.IO.TextReader
       with _ -> raise (Absyn.Syntax.Err (Util.format1 "Unable to open file: %s" filename)))
    | Inr (s:string) -> "<input>", new System.IO.StringReader(s) :> System.IO.TextReader in

  let lexbuf = Microsoft.FSharp.Text.Lexing.LexBuffer<char>.FromTextReader(sr) in
  resetLexbufPos filename lexbuf;
  let lexargs = mkLexargs ((fun () -> "."), filename) in 
  let lexer = LexFStar.token lexargs in 
    try
      let ast = Parse.file lexer lexbuf in 
      Desugar.desugar_file env ast
    with 
      | Absyn.Syntax.Error(msg, r) -> 
        print_error msg r;
        exit 0 
      | e ->
        let pos = lexbuf.EndPos in
        Printf.printf "ERROR: Syntax error near line %d, character %d in file %s\n" (pos.pos_lnum) (pos.pos_cnum - pos.pos_bol) filename;
        exit 0

let parse_files files = 
  let _, mods = List.fold_left (fun (env,mods) fn -> 
    let env, m = parse env (Inl fn) in 
    (env, m::mods)) (DesugarEnv.empty_env(), []) files in 
  List.rev mods |> List.flatten
  
#if TEST
let _ =
    let files = List.tl <| List.ofArray Sys.argv in 
    parse_files files   
#endif 
