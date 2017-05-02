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

(*
    fsdoc generator.
    For usage, see https://github.com/FStarLang/FStar/wiki/Generating-documentation-with-fsdoc-comments.
*)
#light "off"
module FStar.Fsdoc.Generator
open FStar.All

open FStar
// open FStar.Util
open FStar.Parser.AST
open FStar.Ident

module O = FStar.Options
module P = FStar.Parser.Driver
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module SU  = FStar.Syntax.Util
module U  = FStar.Util
module C  = FStar.Syntax.Const

module PP = FStar.Pprint
module TD = FStar.Parser.ToDocument

(*
Notes:
- x-ref will come, but not yet. One way to implement x-ref would be do fully-expand
  all names, as if there weren't any "open"s at the top of the file. But dep and tc
  already do this, and we'd be adding another pass, very sim

- Haven't got the hang of what a .md file should look like. # vs ## vs crlf?
- Things to fix are prefixed with "SI:".
*)

///////////////////////////////////////////////////////////////////////////////
// lib
///////////////////////////////////////////////////////////////////////////////

let str = PP.doc_of_string

// This is how we TD.brackets. 
let fd_brackets = { TD.decl_openb = str "```"; TD.decl_closeb = str "```";
                    TD.fdoc_openb = PP.empty; TD.fdoc_closeb = PP.empty }

// Test for a single TopLevelModule \in decls.
let one_toplevel (decls:list<decl>) =
    let top,nontops = List.partition
                        (fun d -> match d.d with | TopLevelModule _ -> true | _ -> false)
                        decls in
    match top with
    | t :: [] -> Some (t,nontops)
    | _ -> None

// A decl is documented if either:
// - it's got a fsdoc attached to it (either at top-level or in it's subtree); or
// - it itself is a Fsdoc
let decl_documented (d:decl) =
    let tycon_documented (tt:list<(tycon * option<fsdoc>)>) =
        let tyconvars_documented tycon =
            match tycon with
            | TyconAbstract _ | TyconAbbrev _ -> false
            | TyconRecord(_,_,_,fields) ->
                List.existsb (fun (_id,_t,doco) -> U.is_some doco) fields
            | TyconVariant(_,_,_,vars) ->
                List.existsb (fun (_id,_t,doco,_u) -> U.is_some doco) vars in
        List.existsb
            (fun (tycon,doco) -> (tyconvars_documented tycon) || U.is_some doco)
            tt
    in
    // either d.doc attached at the top-level decl
    match d.doc with
    | Some  _ -> true
    | _ ->
        begin match d.d with
        // or it's an fsdoc
        | Fsdoc _ -> true
        // or the tycon is documented
        | Tycon(_,ty) -> tycon_documented ty
        // no other way to document a decl right now
        | _ -> false
        end

let document_of_ofsdoc ofsdoc = 
    match ofsdoc with
    | Some(doc,kw) -> TD.doc_of_fsdoc fd_brackets (doc,kw)
    | _ -> PP.empty

let document_of_decl (d:decl) = 
  if decl_documented d then // SI: or do we want to drop this gate? See #861.
    TD.decl_to_document fd_brackets d
  else PP.empty 

// return (opt_summary, opt_doc) pair
let fsdoc_of_toplevel name topdecl =
  match topdecl.d with
  | TopLevelModule _ ->
    // summary, or doc, or nodoc.
    (match topdecl.doc with
    | Some (doc, kw) ->
        (match List.tryFind (fun (k,v)->k = "summary") kw with
        | None -> None, Some(doc)
        | Some (_, summary) -> Some(summary), Some(doc))
    | None -> None, None)
  | _ -> raise(FStar.Errors.Err("Not a TopLevelModule"))


///////////////////////////////////////////////////////////////////////////////
// modul
///////////////////////////////////////////////////////////////////////////////
let module_to_document (m:modul) : (lid * PP.document) = 
  // Get m's name and decls.
  let name, decls, _mt = match m with // SI: don't forget mt!
    | Module(n,d) -> n, d, "module"
    | Interface(n,d,_) -> n, d, "interface" in
  // Run document_toplevel against the toplevel,
  // then run document_decl against all the other decls.
  match one_toplevel decls with
  | Some (top_decl,other_decls) ->
        begin
            // Keep TopLevelModule special
            let no_summary = "fsdoc: no-summary-found" in
            let no_comment = "fsdoc: no-comment-found" in
            let summary, comment = fsdoc_of_toplevel name top_decl in
            let summary = (match summary with Some(s) -> s | _ -> no_summary) in
            let comment = (match comment with Some(s) -> s | _ -> no_comment) in
            let toplevel_doc = 
                PP.concat [
                PP.group (PP.(^^) (str "# module ") (str name.str)); PP.hardline;
                PP.group (str summary); PP.hardline; 
                PP.group (str comment); PP.hardline ] in
            // non-TopLevelModule decls.
            let otherdecl_docs = List.map document_of_decl other_decls in
            let docs = PP.concat (toplevel_doc :: otherdecl_docs) in 
            (name, docs)
        end
    | None -> raise(FStar.Errors.Err(Util.format1 "No singleton toplevel in module %s" name.str))


///////////////////////////////////////////////////////////////////////////////
// entry point
///////////////////////////////////////////////////////////////////////////////
let generate (files:list<string>) =
  // Parse modules 
  let modules = List.collect (fun fn -> fst (P.parse_file fn)) files in
  // PP each module into a PP.doc.  
  let id_and_docs = List.map module_to_document modules in 
  let m_ids = List.map fst id_and_docs in 
  // Write mod_names into index.md
  let on = O.prepend_output_dir "index.md" in
  let fd = U.open_file_for_writing on in
  List.iter (fun m -> U.append_to_file fd (U.format "%s\n" [m.str])) m_ids;
  U.close_file fd;
  // Write each (id,doc) \in id_and_docs into id.md. 
  List.iter
    (fun (id,doc) -> 
      let on = O.prepend_output_dir (id.str^".md") in
      let fd = FStar.Util.open_file_for_writing on in
      PP.pretty_out_channel (U.float_of_string "1.0") 100 doc fd;
      U.close_file fd)
    id_and_docs 





