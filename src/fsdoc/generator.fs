(*
   Copyright 2008-2016 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or impliedmk_
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"
module FStar.Fsdoc.Generator
open FStar.Util
open FStar.Parser.AST
open FStar.Ident

module O = FStar.Options
module P = FStar.Parser.Driver
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module SU  = FStar.Syntax.Util
module U  = FStar.Util
module C  = FStar.Syntax.Const

(* We store a forest-like representation of the module namespaces for index generation*)
type mforest =
| Leaf of string * string
| Branch of smap<mforest>

let htree : smap<mforest> = smap_create 50

let parse_file (fn:string) =
  U.write_file (O.prepend_output_dir (".mk"))

let document_decl (w:string->unit) (d:decl) =
  let {d = decl; drange = _; doc = doc} = d in
  (match doc with
  | Some (doc, kw) -> w doc
  | _ -> ());
  (match decl with
  | TopLevelModule _ | Open _ | ModuleAbbrev _ | Main _ | Pragma _ -> ()
  | Fsdoc fsd -> w (fst fsd); w "\n"
  | _ ->
    begin
      w "```fstar";
      w (decl_to_string d);
      w "```\n"
    end)

let document_module (m:modul) =
  let name, decls, mt = match m with
    | Module(n,d) -> n, d, "module"
    | Interface(n,d,_) -> n, d, "interface" in
  let mdoc = List.tryPick (function | {d=TopLevelModule k; doc=d} -> Some (k,d) | _ -> None)  decls in
  let name, com = match mdoc with
    | Some (n, com) ->
      let com = match com with
      | Some (doc, kw) -> (match List.tryFind (fun (k,v)->k = "summary") kw with
         | None -> doc | Some (_, summary) -> summary)
      | None -> "*(no documentation provided)*" in
      (n, com)
    | None -> name, "*(no documentation provided)*" in
  let on = O.prepend_output_dir (name.str^".mk") in
  let fd = open_file_for_writing on in
  let w = append_to_file fd in
  w (format "# module %s\n" [name.str]);
  (match mdoc with | Some(_, Some(doc, _)) -> w doc | _ -> ());
  List.iter (document_decl w) decls;
  close_file fd

let generate (files:list<string>) =
  let modules = List.collect (fun fn -> P.parse_file fn) files in
  List.iter document_module modules

