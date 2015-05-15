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

let is_cache_file (fn: string) = Util.get_file_extension fn = ".cache"

let parse_fragment env frag =
    match ParseIt.parse (Inr frag) with
    | Inl (Inl [modul]) -> //interactive mode: module
      let env, modul = Desugar.desugar_partial_modul env modul in
      Inl (env, modul)
  
    | Inl (Inr decls) -> //interactive mode: more decls
      Inr <| Desugar.desugar_decls env decls
  
    | Inl (Inl _) -> 
      Util.print_string "Refusing to check more than one module at a time incrementally";
      exit 1

    | Inr msg -> 
      Util.print_string msg;
      exit 1

let parse_file env fn =
  if is_cache_file fn then
    let full_name = Options.get_fstar_home () ^ "/" ^ Options.cache_dir ^ "/" ^ fn in
    let m = SSyntax.deserialize_modul (get_oreader full_name) in
    Desugar.add_modul_to_env m env, [m]
  else
    match ParseIt.parse (Inl fn) with
    | Inl (Inl ast) ->
      Desugar.desugar_file env ast
  
    | Inr msg -> 
      Util.print_string msg;
      exit 1

let read_build_config file = ParseIt.read_build_config file
  
