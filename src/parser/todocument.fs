(*
   Copyright 2016 Microsoft Research

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

(** Convert Parser.Ast to Pprint.document for prettyprinting. *)
module FStar.Parser.ToDocument

open FStar
open FStar.Parser.AST
open FStar.Ident
open FStar.Const
open FStar.Pprint

// VALS_HACK_HERE

// abbrev 
let str s = document_of_string s

// lib
let doc_of_option n f x = 
    match x with 
    | None -> n
    | Some x' -> f x'


// doc_of_* begins
let doc_of_fsdoc (comment,keywords) = 
    group (concat [(str comment); space; 
                   (separate_map (str ",") 
                        (fun (k,v) -> (concat [(str k); (str "->"); (str v)])) keywords)])

let doc_of_let_qualifier = function
  | NoLetQualifier -> empty
  | Rec -> (str "rec")
  | Mutable -> (str "mutable")

let to_string_l sep f l =
  String.concat sep (List.map f l)

let doc_of_imp = function
    | Hash -> str "#"
    | _ -> empty 

let doc_of_const x = match x with
  | Const_effect -> str "eff"
  | Const_unit -> str "()"
  | Const_bool b -> str (if b then "true" else "false")
  | Const_float x ->  str (Util.string_of_float x)
  | Const_char x ->   squotes (document_of_char x )
  | Const_string(bytes, _) -> dquotes (str (Util.string_of_bytes bytes))
  | Const_bytearray _  ->  str "<bytearray>"
  | Const_int (x, _) -> str x
  | Const_range r -> str (Range.string_of_range r)
  | Const_reify
  | Const_reflect _ -> str "unsupported constant"

// SI: maybe do nesting for terms with args? 
let rec doc_of_term (x:term) = match x.tm with
  | Wild -> underscore 
  | Requires (t, _) -> 
        group (brackets (concat [(str "requires"); space; (doc_of_term t)]))
  | Ensures (t, _) ->          
        group (brackets (concat [(str "ensures"); space; (doc_of_term t)]))
  | Labeled (t, l, _) -> 
        group (brackets (concat [(str "labeled"); space; (str l); (doc_of_term t)]))
  | Const c -> group (doc_of_const c)
  | Op(s, xs) -> 
        group (concat [(str s); (brackets (separate_map (str ", ") doc_of_term xs))])
  | Tvar id -> group (str id.idText)
  | Var l
  | Name l -> group (str l.str)
  | Construct (l, args) ->
        group (brackets (
                concat [(str l.str); space; 
                        (separate_map space (fun (a,imp) -> concat [(doc_of_imp imp); (doc_of_term a)]) args)]))
  | Abs(pats, t) ->
        group (brackets (
                concat [(str "fun"); space; 
                        (separate_map space doc_of_pat pats);
                        space; (str "->"); space; 
                        (doc_of_term t)]))
  | App(t1, t2, imp) -> 
        group (concat [
                    (doc_of_term t1); space;
                    (doc_of_imp imp); (doc_of_term t2)])
  | Let (Rec, lbs, body) ->
        group (concat [(str "let rec"); space;
                        (separate_map (str " and ") (fun (p,b) -> concat [(doc_of_pat p); equals; (doc_of_term b)]) lbs);
                        space; (str "in"); space;
                        (doc_of_term body)])
  | Let (q, [(pat,tm)], body) ->
        group (concat [(str "let"); space;
                       (doc_of_let_qualifier q); space;
                       (doc_of_pat pat); space;
                       equals; space;
                       (doc_of_term tm); 
                       space; (str "in"); space;
                       (doc_of_term body)])
  | Seq(t1, t2) ->
        group (concat [doc_of_term t1; semi; space; doc_of_term t2])
  | If(t1, t2, t3) ->
        group (concat [(str "if"); space; (doc_of_term t1); space; (str "then"); space; 
                       (nest 2 (doc_of_term t2)); 
                       (str "else"); space;
                       (nest 2 (doc_of_term t3))])
  | Match(t, branches) ->
       group (concat 
                [(str "match"); space; (doc_of_term t); space; (str "with"); space;
                 (separate_map hardline 
                     (fun (p,w,e) -> concat [(str " | ");
                                             (doc_of_pat p); space; 
                                             (match w with | None -> empty | Some e -> concat [str "when "; (doc_of_term e)]);
                                             space; (str "->"); space;
                                             (doc_of_term e)])
                     branches)])
  | Ascribed(t1, t2) ->
        group (concat [doc_of_term t1; space; colon; space; doc_of_term t2])
  | Record(Some e, fields) ->
        group (concat [
                    lbrace; (doc_of_term e); space; str "with"; space;
                    separate_map space 
                        (fun (l,e) -> concat [str l.str; equals; doc_of_term e])
                        fields;
                    rbrace])
  | Record(None, fields) ->
        group (concat [
                    lbrace; 
                    separate_map space
                        (fun (l,e) -> concat [(str l.str); equals; (doc_of_term e)])
                        fields;
                    rbrace
                    ])
  | Project(e,l) ->
        group (concat [doc_of_term e; dot; str l.str])
  | Product([], t) ->
        group (doc_of_term t)
  | Product(b::hd::tl, t) ->
        group (doc_of_term (mk_term (Product([b], mk_term (Product(hd::tl, t)) x.range x.level)) x.range x.level))
  | Product([b], t) when (x.level = Type) ->
        group (concat [(doc_of_binder b); space; str "->"; space; (doc_of_term t)])
  | Product([b], t) when (x.level = Kind) ->
        group (concat [(doc_of_binder b); space; str "=>"; space; (doc_of_term t)])
  | Sum(binders, t) ->
        group (concat [(separate_map (str " * ") doc_of_binder binders);
                       space; str "*"; space;
                       doc_of_term t])
  | QForall(bs, pats, t) ->
        group (concat [
                    str "forall"; space;
                    separate_map space doc_of_binder bs; 
                    dot; lbrace; colon; str "pattern"; space;
                    // TODO: should the separator be /\ here? 
                    separate_map (str " \/ ") (separate_map (concat [semi; space]) doc_of_term) pats;
                    rbrace; space;
                    doc_of_term t])
  | QExists(bs, pats, t) ->
        group (concat [
                    str "exists"; space;
                    separate_map space doc_of_binder bs; 
                    dot; lbrace; colon; str "pattern"; space;
                    separate_map (str " \/ ") (separate_map (concat [semi; space]) doc_of_term) pats;
                    rbrace; space;
                    doc_of_term t])


  | Refine(b, t) ->
        group (concat [
                    doc_of_binder b;
                    colon;
                    lbrace; doc_of_term t; rbrace])
  | NamedTyp(x, t) ->
        group (concat [str x.idText; colon; doc_of_term t])
  | Paren t -> group (parens (doc_of_term t))
  | Product(bs, t) ->
        group (concat [
                    str "Unidentified product: [";
                    separate_map comma doc_of_binder bs; 
                    str "]"; space;
                    doc_of_term t])
  | t -> underscore 

and doc_of_binder x =
  let s = match x.b with
  | Variable i -> str i.idText
  | TVariable i -> concat [str i.idText; colon; underscore] 
  | TAnnotated(i,t)
  | Annotated(i,t) -> concat [str i.idText; colon; doc_of_term t]
  | NoName t -> doc_of_term t in
  concat [doc_of_aqual x.aqual;  s]

and doc_of_aqual = function
   | Some Equality -> str "$"
   | Some Implicit -> str "#"
   | _ -> empty 

and doc_of_pat x = match x.pat with
  | PatWild -> underscore 
  | PatConst c -> doc_of_const c
  | PatApp(p, ps) ->
        group (parens (concat [(doc_of_pat p); space; (separate_map space doc_of_pat ps)]))
  | PatTvar (i, aq)
  | PatVar (i,  aq) -> 
        group (concat [(doc_of_aqual aq); (str i.idText)])
  | PatName l -> str l.str
  | PatList l -> group (brackets (separate_map (concat [semi; space]) doc_of_pat l))
  | PatTuple (l, false) -> group (parens (separate_map (concat [semi; space]) doc_of_pat l))
  | PatTuple (l, true) -> group (parens (concat [bar; (separate_map (concat [comma; space]) doc_of_pat l); bar]))
  | PatRecord l -> 
        group (braces (separate_map (concat [semi; space]) (fun (f,e) -> concat [(str f.str); equals; (doc_of_pat e)]) l))
  | PatOr l ->  separate_map (concat [bar; hardline; space]) doc_of_pat l
  | PatOp op ->  parens (str op)
  | PatAscribed(p,t) -> group (parens (concat [doc_of_pat p; colon; doc_of_term t]))

let rec head_id_of_pat p = match p.pat with
        | PatName l -> [l]
        | PatVar (i, _) -> [Ident.lid_of_ids [i]]
        | PatApp(p, _) -> head_id_of_pat p
        | PatAscribed(p, _) -> head_id_of_pat p
        | _ -> []

let lids_of_let defs =  defs |> List.collect (fun (p, _) -> head_id_of_pat p)

// TODO: check with parser re how these are printed.
let doc_of_tycon = function
  | TyconAbstract(i, bb, k) ->
        group (concat [str "abstract"; space;
                       (separate_map space doc_of_binder bb); space;
                       doc_of_option empty doc_of_term k; space;
                       hardline
                       ])
// TODO bb, k, t, flds, vars
  | TyconAbbrev(i, bb, k, t) -> group (str i.idText)
  | TyconRecord(i, bb, k, flds) -> 
        group (concat [str i.idText; space; equals; space;
                       (separate_map space doc_of_binder bb); space;
                       doc_of_option empty doc_of_term k; space; 
                       braces ((separate_map (concat [space; semi; space])
                                    (fun (i,t,d) -> concat [str i.idText; space; colon; space; doc_of_term t])
                                    flds))])
  | TyconVariant(i, bb, k, vars) -> group (str i.idText)

let doc_of_decl (d:decl) = match d.d with
  | TopLevelModule l -> 
        group (concat [(str "module"); space; (str l.str); hardline])
  | Open l -> 
        group (concat [(str "open"); space; equals; space; (str l.str); hardline])
  | ModuleAbbrev (i, l) ->         
        group (concat [(str "module"); space; (str i.idText);space; equals; space; (str l.str); hardline] )
  | KindAbbrev(i, bb, k) -> 
        group (concat [(str "kind"); space; (str i.idText);
                        (separate_map space
                            (fun b -> doc_of_binder b)
                            bb);
                        space; equals; space; (doc_of_term k);  hardline])
  | TopLevelLet(qq, lq, pats_terms) ->  
        // TODO: qq, lq. 
        let head_ids = List.collect (fun (p,_) -> head_id_of_pat p) pats_terms in 
        group (concat [(str "let"); space;
                       (separate_map (str ", ")
                            (fun l -> str l.str)
                            head_ids); 
                       hardline] )
  | Main e -> group (concat [str "main"; space; doc_of_term e])
  | Assume(q, i, t) -> 
    // TODO: q, i.
        group (concat [ (str "assume"); space; (str i.idText); hardline])
  | Tycon(q, tys) -> 
    // TODO: q. Also, print "type" here, or in doc_of_tycon?
        group (concat [(str "type"); space; 
                        (separate_map (str ", ")
                            // TODO: d
                            (fun (x,d) -> doc_of_tycon x)
                            tys);
                        hardline ])
  | Val(_, i, _) -> concat [(str "val "); (str i.idText); hardline]
  | Exception(i, _) -> concat [(str "exception "); (str i.idText); hardline]
  | NewEffect(_, DefineEffect(i, _, _, _, _))
  | NewEffect(_, RedefineEffect(i, _, _)) -> concat [(str "new_effect) "); (str i.idText); hardline]
  | NewEffectForFree(_, DefineEffect(i, _, _, _, _))
  | NewEffectForFree(_, RedefineEffect(i, _, _)) -> concat [(str "new_effect_for_free "); (str i.idText); hardline]
  | SubEffect l -> str "sub_effect"
  | Pragma p -> str "pragma"
  | Fsdoc d -> group (concat [doc_of_fsdoc d; hardline]) 

// SI: go straight to decls (might have to change if TopLevel is not the first decl). 
let doc_of_modul (m:modul) = match m with
    | Module (_, decls) 
    | Interface (_, decls, _) ->
      decls |> List.map doc_of_decl |> concat

//
let term_to_document t = doc_of_term t
let decl_to_document d = doc_of_decl d
let modul_to_document m = doc_of_modul m
