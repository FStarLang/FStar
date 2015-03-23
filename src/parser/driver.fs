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

open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax

let print_error msg r = 
  Util.print_string (Util.format2 "ERROR %s: %s\n" (Range.string_of_range r) msg)

let is_cache_file (fn: either<string, string>) :(bool * string) = match fn with
  | Inl(s) -> ((Util.get_file_extension s) = ".cache"), s
  | _ -> false, ""

let parse env fn =
  let (b, s) = is_cache_file fn in
  if b then
    let full_name = Options.get_fstar_home () ^ "/" ^ Options.cache_dir ^ "/" ^ s in
    let m = SSyntax.deserialize_modul (get_oreader full_name) in
    Desugar.add_modul_to_env m env, [m]
  else
    match ParseIt.parse_file fn with 
    | Inl ast -> Desugar.desugar_file env ast
    | Inr msg -> 
      Util.print_string msg;
      exit 1

let parse_files files = 
  let _, mods = List.fold_left (fun (env,mods) fn -> 
    let env, m = parse env (Inl fn) in
    Options.reset_options();
    let _ = match !Options.dump_module with 
      | Some n -> 
        m |> List.iter (fun (m:Absyn.Syntax.modul) -> if n=m.name.str then (Util.format1 "%s\n" <| Absyn.Print.modul_to_string m) |> Util.print_string)
      | _ -> () in
    (env, m::mods)) (DesugarEnv.empty_env(), []) files in 
  List.rev mods |> List.flatten

(* ;;  *)

(* parse_files ["prims.fst"] *)
  
