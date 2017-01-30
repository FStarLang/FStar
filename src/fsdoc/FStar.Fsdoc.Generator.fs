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

open FStar
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

(*
Notes:
- a lot of the string_of functions and their concatenation should go away with
  a better pretty-printer.
- there are too many strings being passed around/returned. Need to wrap up the F#
  and OCaml Buffer libraries in a buffer.fsti one.
- x-ref will come, but not yet. One way to implement x-ref would be do fully-expand
  all names, as if there weren't any "open"s at the top of the file. But dep and tc
  already do this, and we'd be adding another pass, very sim

- Haven't got the hang of what a .md file should look like. # vs ## vs crlf?
- Things to fix are prefixed with "SI:".
*)

///////////////////////////////////////////////////////////////////////////////
// lib
///////////////////////////////////////////////////////////////////////////////

// Test for a single TopLevelModule \in decls.
let one_toplevel (decls:list<decl>) =
let top,nontops = List.partition
                    (fun d -> match d.d with | TopLevelModule _ -> true | _ -> false)
                    decls in
match top with
| t :: [] -> Some (t,nontops)
| _ -> None

// We store a forest-like representation of the module namespaces for index generation.
// SI: not used yet.
type mforest =
| Leaf of string * string
| Branch of smap<mforest>

let htree : smap<mforest> = smap_create 50

// if xo=Some(x) then f x else y
// SI: use the one in FStar.Option -- there must be one there!
let string_of_optiont f y xo =
    match xo with
    | Some x -> f x
    | None -> y

let string_of_fsdoco d = string_of_optiont (fun x -> "(*" ^ string_of_fsdoc x ^ "*)") "" d
let string_of_termo t = string_of_optiont term_to_string "" t

// wrap-up s in MD code block.
// SI: we pretend to be F# so that pandoc can produce prettier html.
let code_wrap s = "```fsharp\n" ^ s ^ "\n```\n"

///////////////////////////////////////////////////////////////////////////////
// tycon
///////////////////////////////////////////////////////////////////////////////

let string_of_tycon tycon =
    match tycon with
    | TyconAbstract _ -> "abstract"
    | TyconAbbrev _ -> "abbrev"
    | TyconRecord(id,_bb,_ko,fields) ->
        id.idText ^ " = { " ^
        ( fields
          |> List.map
                    (fun (id,t,doco) -> (string_of_fsdoco doco) ^
                                        id.idText ^ ":" ^ (term_to_string t))
          |> String.concat "; " ) ^
        " }"
    | TyconVariant(id,_bb,_ko,vars) ->
        id.idText ^ " = " ^
        ( vars
            |> List.map
                    (fun (id,trmo,doco,u) ->
                        (string_of_fsdoco doco) ^
                        id.idText ^ ":" ^ (string_of_optiont term_to_string "" trmo))
            |> String.concat " | " )

///////////////////////////////////////////////////////////////////////////////
// decl
///////////////////////////////////////////////////////////////////////////////

// SI: really only expecting non-TopLevelModule's.
let string_of_decl' d =
  match d with
  | TopLevelModule l -> "module " ^ l.str // SI: should never get here
  | Open l -> "open " ^ l.str
  | Include l -> "include " ^ l.str
  | ModuleAbbrev (i, l) -> "module " ^ i.idText ^ " = " ^ l.str
  | KindAbbrev(i, _, _) -> "kind " ^ i.idText
  | TopLevelLet(_, pats) ->
        let termty = List.map (fun (p,t) -> (pat_to_string p, term_to_string t)) pats in
        let termty' = List.map (fun (p,t) -> p ^ ":" ^ t) termty in
        "let " ^ (String.concat ", " termty')
  | Main _ -> "main ..."
  | Assume(i, t) -> "assume " ^ i.idText ^ ":" ^ (term_to_string t)
  | Tycon(_, tys) ->
            "type " ^
             (tys |> List.map (fun (t,d)-> (string_of_tycon t) ^ " " ^ (string_of_fsdoco d))
                 |> String.concat " and ") (* SI: sep will be "," for Record but "and" for Variant *)
  | Val(i, t) -> "val " ^ i.idText ^ ":" ^ (term_to_string t)
  | Exception(i, _) -> "exception " ^ i.idText
  | NewEffect(DefineEffect(i, _, _, _, _))
  | NewEffect(RedefineEffect(i, _, _)) -> "new_effect " ^ i.idText
  | NewEffectForFree(DefineEffect(i, _, _, _, _))
  | NewEffectForFree(RedefineEffect(i, _, _)) -> "new_effect_for_free " ^ i.idText
  | SubEffect _ -> "sub_effect"
  | Pragma _ -> "pragma"
  | Fsdoc (comm,_) -> comm

// A decl is documented if either:
// - it's got a fsdoc attached to it (either at top-level or in it's subtree); or
// - it itself is a Fsdoc
let decl_documented (d:decl) =
    let tycon_documented (tt:list<(tycon * option<fsdoc>)>) =
        let tyconvars_documented tycon =
            match tycon with
            | TyconAbstract _ | TyconAbbrev _ -> false
            | TyconRecord(_,_,_,fields) ->
                List.existsb (fun (_id,_t,doco) -> is_some doco) fields
            | TyconVariant(_,_,_,vars) ->
                List.existsb (fun (_id,_t,doco,_u) -> is_some doco) vars in
        List.existsb
            (fun (tycon,doco) -> (tyconvars_documented tycon) || is_some doco)
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

let document_decl (w:string->unit) (d:decl) =
  if decl_documented d then
    // This expr is OK F# code, but we need a few {begin, '('}s to make it OCaml as well.
        // print the decl
        let {d = decl; drange = _; doc = fsdoc} = d in
        w (code_wrap (string_of_decl' d.d));
        // print the doc, if there's one
        begin match fsdoc with
        | Some(doc,_kw) -> w ("\n" ^ doc) // SI: do something with kw
        | _ -> ()
        end ;
        w "" // EOL
  else ()

// return (opt_summary, opt_doc) pair
let document_toplevel name topdecl =
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
let document_module (m:modul) =
  //Util.print "doc_module: %s\n" [(modul_to_string m)] ;
  // Get m's name and decls.
  let name, decls, _mt = match m with // SI: don't forget mt!
    | Module(n,d) -> n, d, "module"
    | Interface(n,d,_) -> n, d, "interface" in
  // Run document_toplevel against the toplevel,
  // then run document_decl against all the other decls.
  match one_toplevel decls with
  | Some (top_decl,other_decls) ->
        begin
          let on = O.prepend_output_dir (name.str^".md") in
          let fd = open_file_for_writing on in
          let w = append_to_file fd in
          // SI: keep TopLevelModule special?
          let no_summary = "fsdoc: no-summary-found" in
          let no_comment = "fsdoc: no-comment-found" in
          let summary, comment = document_toplevel name top_decl in
          let summary = (match summary with | Some(s) -> s | None -> no_summary) in
          let comment = (match comment with | Some(s) -> s | None -> no_comment) in
          w (format "# module %s" [name.str]);
          w (format "%s\n" [summary]);
          w (format "%s\n" [comment]);
          // non-TopLevelModule decls.
          List.iter (document_decl w) other_decls;
          close_file fd;
          name
        end
    | None -> raise(FStar.Errors.Err(Util.format1 "No singleton toplevel in module %s" name.str))

///////////////////////////////////////////////////////////////////////////////
// entry point
///////////////////////////////////////////////////////////////////////////////
let generate (files:list<string>) =
  // fsdoc each module into it's own module.md.
  let modules = List.collect (fun fn -> fst (P.parse_file fn)) files in
  let mods = List.map document_module modules in
  // write mod_names into index.md
  let on = O.prepend_output_dir "index.md" in
  let fd = open_file_for_writing on in
  List.iter (fun m -> append_to_file fd (format "%s\n" [m.str])) mods;
  close_file fd





