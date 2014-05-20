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
open Microsoft.FStar.Parser.Parse
open Microsoft.FStar.Util

let print_error msg r = 
  Util.print_string (Util.format2 "ERROR %s: %s\n" (Range.string_of_range r) msg)

let parse env fn =
  match ParseIt.parse_file fn with 
    | Inl ast -> Desugar.desugar_file env ast
    | Inr msg -> 
      Util.print_string msg;
      exit 0

let parse_files files = 
  let _, mods = List.fold_left (fun (env,mods) fn -> 
    let env, m = parse env (Inl fn) in 
    (env, m::mods)) (DesugarEnv.empty_env(), []) files in 
  List.rev mods |> List.flatten

(* ;;  *)

(* parse_files ["prims.fst"] *)
  
