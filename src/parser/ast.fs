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
module FStar.Parser.AST
//open FStar.Absyn
module C = FStar.Absyn.Const
module U = FStar.Absyn.Util
module P = FStar.Absyn.Print
module S = FStar.Absyn.Syntax
//open FStar.Absyn.Syntax
open FStar.Range
open FStar.Ident
open FStar
open FStar.Util
open FStar.Const

(* AST produced by the parser, before desugaring
   It is not stratified: a single type called "term" containing
   expressions, formulas, types, and so on
 *)
type level = | Un | Expr | Type | Kind | Formula
type imp =
    | FsTypApp
    | Hash
    | Nothing
type arg_qualifier =
    | Implicit
    | Equality
type aqual = option<arg_qualifier>

// let rec mutable makes no sense, so just don't do it
type let_qualifier =
  | NoLetQualifier
  | Rec
  | Mutable

type term' =
  | Wild
  | Const     of sconst
  | Op        of string * list<term>
  | Tvar      of ident
  | Var       of lid // a qualified identifier that starts with a lowercase (Foo.Bar.baz)
  | Name      of lid // a qualified identifier that starts with an uppercase (Foo.Bar.Baz)
  | Construct of lid * list<(term*imp)>               (* data, type: bool in each arg records an implicit *)
  | Abs       of list<pattern> * term
  | App       of term * term * imp                    (* aqual marks an explicitly provided implicit parameter *)
  | Let       of let_qualifier * list<(pattern * term)> * term
  | LetOpen   of lid * term
  | Seq       of term * term
  | If        of term * term * term
  | Match     of term * list<branch>
  | TryWith   of term * list<branch>
  | Ascribed  of term * term
  | Record    of option<term> * list<(lid * term)>
  | Project   of term * lid
  | Product   of list<binder> * term (* function space *)
  | Sum       of list<binder> * term (* dependent tuple *)
  | QForall   of list<binder> * list<list<term>> * term
  | QExists   of list<binder> * list<list<term>> * term
  | Refine    of binder * term
  | NamedTyp  of ident * term
  | Paren     of term
  | Requires  of term * option<string>
  | Ensures   of term * option<string>
  | Labeled   of term * string * bool
  | Assign    of ident * term

and term = {tm:term'; range:range; level:level}

and binder' =
  | Variable of ident
  | TVariable of ident
  | Annotated of ident * term
  | TAnnotated of ident * term
  | NoName of term
and binder = {b:binder'; brange:range; blevel:level; aqual:aqual}

and pattern' =
  | PatWild
  | PatConst    of sconst
  | PatApp      of pattern * list<pattern>
  | PatVar      of ident * option<arg_qualifier>
  | PatName     of lid
  | PatTvar     of ident * option<arg_qualifier>
  | PatList     of list<pattern>
  | PatTuple    of list<pattern> * bool (* dependent if flag is set *)
  | PatRecord   of list<(lid * pattern)>
  | PatAscribed of pattern * term
  | PatOr       of list<pattern>
  | PatOp       of string
and pattern = {pat:pattern'; prange:range}

and branch = (pattern * option<term> * term)

type knd = term
type typ = term
type expr = term

// Documentation comment. May appear appear as follows:
//  - Immediately before a top-level declaration
//  - Immediately after a type constructor or record field
//  - In the middle of a file, as a standalone documentation declaration
type fsdoc = string * list<(string * string)> // comment + (name,value) keywords

type tycon =
  | TyconAbstract of ident * list<binder> * option<knd>
  | TyconAbbrev   of ident * list<binder> * option<knd> * term
  | TyconRecord   of ident * list<binder> * option<knd> * list<(ident * term * option<fsdoc>)>
  | TyconVariant  of ident * list<binder> * option<knd> * list<(ident * option<term> * option<fsdoc> * bool)> (* using 'of' notion *)

type qualifier =
  | Private
  | Abstract
  | Noeq
  | Unopteq
  | Assumption
  | DefaultEffect
  | TotalEffect
  | Effect
  | New
  | Inline                                 //a definition that *should* always be unfolded by the normalizer
  | Unfoldable                             //a definition that may be unfolded by the normalizer, but only if necessary (default)
  | Irreducible                            //a definition that can never be unfolded by the normalizer
  | Reifiable
  | Reflectable
  //old qualifiers
  | Opaque
  | Logic



type qualifiers = list<qualifier>

type lift_op =
  | NonReifiableLift of term
  | ReifiableLift    of term * term //lift_wp, lift

type lift = {
  msource: lid;
  mdest:   lid;
  lift_op: lift_op;
}

type pragma =
  | SetOptions of string
  | ResetOptions of option<string>

type decl' =
  | TopLevelModule of lid
  | Open of lid
  | ModuleAbbrev of ident * lid
  | KindAbbrev of ident * list<binder> * knd
  | ToplevelLet of qualifiers * let_qualifier * list<(pattern * term)>
  | Main of term
  | Assume of qualifiers * ident * term
  | Tycon of qualifiers * list<(tycon * option<fsdoc>)>
  | Val of qualifiers * ident * term  (* bool is for logic val *)
  | Exception of ident * option<term>
  | NewEffect of qualifiers * effect_decl
  | NewEffectForFree of qualifiers * effect_decl (* always a [DefineEffect] *)
  | SubEffect of lift
  | Pragma of pragma
  | Fsdoc of fsdoc
and decl = {d:decl'; drange:range; doc:option<fsdoc>;}
and effect_decl =
  | DefineEffect   of ident * list<binder> * term * list<decl> * list<decl>
  | RedefineEffect of ident * list<binder> * term

type modul =
  | Module of lid * list<decl>
  | Interface of lid * list<decl> * bool (* flag to mark admitted interfaces *)
type file = list<modul>
type inputFragment = either<file,list<decl>>

(********************************************************************************)
let check_id id =
    if Options.universes()
    then let first_char = String.substring id.idText 0 1 in
         if String.lowercase first_char = first_char
         then ()
         else raise (FStar.Syntax.Syntax.Error(Util.format1 "Invalid identifer '%s'; expected a symbol that begins with a lower-case character" id.idText, id.idRange))
    else ()

let mk_decl d r doc = {d=d; drange=r; doc=doc}
let mk_binder b r l i = {b=b; brange=r; blevel=l; aqual=i}
let mk_term t r l = {tm=t; range=r; level=l}
let mk_uminus t r l =
  let t =
    match t.tm with
    | Const (Const_int (s, Some (Signed, width))) ->
        Const (Const_int ("-" ^ s, Some (Signed, width)))
    | _ ->
        Op("-", [t])
  in
  mk_term t r l

let mk_pattern p r = {pat=p; prange=r}
let un_curry_abs ps body = match body.tm with
    | Abs(p', body') -> Abs(ps@p', body')
    | _ -> Abs(ps, body)
let mk_function branches r1 r2 =
  let x =
    if Options.universes()
    then let i = FStar.Syntax.Syntax.next_id () in
         Ident.gen r1
    else U.genident (Some r1) in
  mk_term (Abs([mk_pattern (PatVar(x,None)) r1],
               mk_term (Match(mk_term (Var(lid_of_ids [x])) r1 Expr, branches)) r2 Expr))
    r2 Expr
let un_function p tm = match p.pat, tm.tm with
    | PatVar _, Abs(pats, body) -> Some (mk_pattern (PatApp(p, pats)) p.prange, body)
    | _ -> None

let lid_with_range lid r = lid_of_path (path_of_lid lid) r

let consPat r hd tl = PatApp(mk_pattern (PatName C.cons_lid) r, [hd;tl])
let consTerm r hd tl = mk_term (Construct(C.cons_lid, [(hd, Nothing);(tl, Nothing)])) r Expr
let lexConsTerm r hd tl = mk_term (Construct(C.lexcons_lid, [(hd, Nothing);(tl, Nothing)])) r Expr

let mkConsList r elts =
  let nil = mk_term (Construct(C.nil_lid, [])) r Expr in
    List.fold_right (fun e tl -> consTerm r e tl) elts nil

let mkLexList r elts =
  let nil = mk_term (Construct(C.lextop_lid, [])) r Expr in
  List.fold_right (fun e tl -> lexConsTerm r e tl) elts nil

let mkApp t args r = match args with
  | [] -> t
  | _ -> match t.tm with
      | Name s -> mk_term (Construct(s, args)) r Un
      | _ -> List.fold_left (fun t (a,imp) -> mk_term (App(t, a, imp)) r Un) t args

let mkRefSet r elts =
  let univs = Options.universes () in
  let empty_lid, singleton_lid, union_lid = if univs then C.tset_empty, C.tset_singleton, C.tset_union else C.set_empty, C.set_singleton, C.set_union in
  let empty = mk_term (Var(set_lid_range empty_lid r)) r Expr in
  let ref_constr = mk_term (Var (set_lid_range C.heap_ref r)) r Expr in
  let singleton = mk_term (Var (set_lid_range singleton_lid r)) r Expr in
  let union = mk_term (Var(set_lid_range union_lid r)) r Expr in
  List.fold_right (fun e tl ->
    let e = mkApp ref_constr [(e, Nothing)] r in
    let single_e = mkApp singleton [(e, Nothing)] r in
    mkApp union [(single_e, Nothing); (tl, Nothing)] r) elts empty

let mkExplicitApp t args r = match args with
  | [] -> t
  | _ -> match t.tm with
      | Name s -> mk_term (Construct(s, (List.map (fun a -> (a, Nothing)) args))) r Un
      | _ -> List.fold_left (fun t a -> mk_term (App(t, a, Nothing)) r Un) t args

let mkAdmitMagic r =
    let unit_const = mk_term(Const Const_unit) r Expr in
    let admit =
        let admit_name = mk_term(Var(set_lid_range C.admit_lid r)) r Expr in
        mkExplicitApp admit_name [unit_const] r in
    let magic =
        let magic_name = mk_term(Var(set_lid_range C.magic_lid r)) r Expr in
        mkExplicitApp magic_name [unit_const] r in
    let admit_magic = mk_term(Seq(admit, magic)) r Expr in
    admit_magic

let mkWildAdmitMagic r = (mk_pattern PatWild r, None, mkAdmitMagic r)

let focusBranches branches r =
    let should_filter = Util.for_some fst branches in
        if should_filter
        then let _ = Tc.Errors.warn r "Focusing on only some cases" in
         let focussed = List.filter fst branches |> List.map snd in
                 focussed@[mkWildAdmitMagic r]
        else branches |> List.map snd

let focusLetBindings lbs r =
    let should_filter = Util.for_some fst lbs in
        if should_filter
        then let _ = Tc.Errors.warn r "Focusing on only some cases in this (mutually) recursive definition" in
         List.map (fun (f, lb) ->
              if f then lb
              else (fst lb, mkAdmitMagic r)) lbs
        else lbs |> List.map snd

let mkFsTypApp t args r =
  mkApp t (List.map (fun a -> (a, FsTypApp)) args) r

let mkTuple args r =
  let cons =
    if Options.universes()
    then FStar.Syntax.Util.mk_tuple_data_lid (List.length args) r
    else U.mk_tuple_data_lid (List.length args) r in
  mkApp (mk_term (Name cons) r Expr) (List.map (fun x -> (x, Nothing)) args) r

let mkDTuple args r =
  let cons =
        if Options.universes()
        then FStar.Syntax.Util.mk_dtuple_data_lid (List.length args) r
        else U.mk_dtuple_data_lid (List.length args) r in
  mkApp (mk_term (Name cons) r Expr) (List.map (fun x -> (x, Nothing)) args) r

let mkRefinedBinder id t refopt m implicit =
  let b = mk_binder (Annotated(id, t)) m Type implicit in
  match refopt with
    | None -> b
    | Some t -> mk_binder (Annotated(id, mk_term (Refine(b, t)) m Type)) m Type implicit

let rec extract_named_refinement t1  =
    match t1.tm with
        | NamedTyp(x, t) -> Some (x, t, None)
        | Refine({b=Annotated(x, t)}, t') ->  Some (x, t, Some t')
    | Paren t -> extract_named_refinement t
        | _ -> None

//////////////////////////////////////////////////////////////////////////////////////////////
// Printing ASTs, mostly for debugging
//////////////////////////////////////////////////////////////////////////////////////////////

let string_of_fsdoc (comment,keywords) = 
    comment ^ (String.concat "," (List.map (fun (k,v) -> k ^ "->" ^ v) keywords))

let string_of_let_qualifier = function
  | NoLetQualifier -> ""
  | Rec -> "rec"
  | Mutable -> "mutable"
let to_string_l sep f l =
  String.concat sep (List.map f l)
let imp_to_string = function
    | Hash -> "#"
    | _ -> ""
let rec term_to_string (x:term) = match x.tm with
  | Wild -> "_"
  | Requires (t, _) -> Util.format1 "(requires %s)" (term_to_string t)
  | Ensures (t, _) -> Util.format1 "(ensures %s)" (term_to_string t)
  | Labeled (t, l, _) -> Util.format2 "(labeled %s %s)" l (term_to_string t)
  | Const c -> P.const_to_string c
  | Op(s, xs) -> Util.format2 "%s(%s)" s (String.concat ", " (List.map (fun x -> x|> term_to_string) xs))
  | Tvar id -> id.idText
  | Var l
  | Name l -> l.str
  | Construct (l, args) ->
    Util.format2 "(%s %s)" l.str (to_string_l " " (fun (a,imp) -> Util.format2 "%s%s" (imp_to_string imp) (term_to_string a)) args)
  | Abs(pats, t) ->
    Util.format2 "(fun %s -> %s)" (to_string_l " " pat_to_string pats) (t|> term_to_string)
  | App(t1, t2, imp) -> Util.format3 "%s %s%s" (t1|> term_to_string) (imp_to_string imp) (t2|> term_to_string)
  | Let (Rec, lbs, body) ->
    Util.format2 "let rec %s in %s" (to_string_l " and " (fun (p,b) -> Util.format2 "%s=%s" (p|> pat_to_string) (b|> term_to_string)) lbs) (body|> term_to_string)
  | Let (q, [(pat,tm)], body) ->
    Util.format4 "let %s %s = %s in %s" (string_of_let_qualifier q) (pat|> pat_to_string) (tm|> term_to_string) (body|> term_to_string)
  | Seq(t1, t2) ->
    Util.format2 "%s; %s" (t1|> term_to_string) (t2|> term_to_string)
  | If(t1, t2, t3) ->
    Util.format3 "if %s then %s else %s" (t1|> term_to_string) (t2|> term_to_string) (t3|> term_to_string)
  | Match(t, branches) ->
    Util.format2 "match %s with %s"
      (t|> term_to_string)
      (to_string_l " | " (fun (p,w,e) -> Util.format3 "%s %s -> %s"
        (p |> pat_to_string)
        (match w with | None -> "" | Some e -> Util.format1 "when %s" (term_to_string e))
        (e |> term_to_string)) branches)
  | Ascribed(t1, t2) ->
    Util.format2 "(%s : %s)" (t1|> term_to_string) (t2|> term_to_string)
  | Record(Some e, fields) ->
    Util.format2 "{%s with %s}" (e|> term_to_string) (to_string_l " " (fun (l,e) -> Util.format2 "%s=%s" (l.str) (e|> term_to_string)) fields)
  | Record(None, fields) ->
    Util.format1 "{%s}" (to_string_l " " (fun (l,e) -> Util.format2 "%s=%s" (l.str) (e|> term_to_string)) fields)
  | Project(e,l) ->
    Util.format2 "%s.%s" (e|> term_to_string) (l.str)
  | Product([], t) ->
    term_to_string t
  | Product(b::hd::tl, t) ->
    term_to_string (mk_term (Product([b], mk_term (Product(hd::tl, t)) x.range x.level)) x.range x.level)
  | Product([b], t) when (x.level = Type) ->
    Util.format2 "%s -> %s" (b|> binder_to_string) (t|> term_to_string)
  | Product([b], t) when (x.level = Kind) ->
    Util.format2 "%s => %s" (b|> binder_to_string) (t|> term_to_string)
  | Sum(binders, t) ->
    Util.format2 "%s * %s" (binders |> (List.map binder_to_string) |> String.concat " * " ) (t|> term_to_string)
  | QForall(bs, pats, t) ->
    Util.format3 "forall %s.{:pattern %s} %s"
      (to_string_l " " binder_to_string bs)
      (to_string_l " \/ " (to_string_l "; " term_to_string) pats)
      (t|> term_to_string)
  | QExists(bs, pats, t) ->
    Util.format3 "exists %s.{:pattern %s} %s"
      (to_string_l " " binder_to_string bs)
      (to_string_l " \/ " (to_string_l "; " term_to_string) pats)
      (t|> term_to_string)
  | Refine(b, t) ->
    Util.format2 "%s:{%s}" (b|> binder_to_string) (t|> term_to_string)
  | NamedTyp(x, t) ->
    Util.format2 "%s:%s" x.idText  (t|> term_to_string)
  | Paren t -> Util.format1 "(%s)" (t|> term_to_string)
  | Product(bs, t) ->
        Util.format2 "Unidentified product: [%s] %s"
          (bs |> List.map binder_to_string |> String.concat ",") (t|> term_to_string)
  | t -> "_"

and binder_to_string x =
  let s = match x.b with
  | Variable i -> i.idText
  | TVariable i -> Util.format1 "%s:_" (i.idText)
  | TAnnotated(i,t)
  | Annotated(i,t) -> Util.format2 "%s:%s" (i.idText) (t |> term_to_string)
  | NoName t -> t |> term_to_string in
  Util.format2 "%s%s" (aqual_to_string x.aqual) s

and aqual_to_string = function
   | Some Equality -> "$"
   | Some Implicit -> "#"
   | _ -> ""

and pat_to_string x = match x.pat with
  | PatWild -> "_"
  | PatConst c -> P.const_to_string c
  | PatApp(p, ps) -> Util.format2 "(%s %s)" (p |> pat_to_string) (to_string_l " " pat_to_string ps)
  | PatTvar (i, aq)
  | PatVar (i,  aq) -> Util.format2 "%s%s" (aqual_to_string aq) i.idText
  | PatName l -> l.str
  | PatList l -> Util.format1 "[%s]" (to_string_l "; " pat_to_string l)
  | PatTuple (l, false) -> Util.format1 "(%s)" (to_string_l ", " pat_to_string l)
  | PatTuple (l, true) -> Util.format1 "(|%s|)" (to_string_l ", " pat_to_string l)
  | PatRecord l -> Util.format1 "{%s}" (to_string_l "; " (fun (f,e) -> Util.format2 "%s=%s" (f.str) (e |> pat_to_string)) l)
  | PatOr l ->  to_string_l "|\n " pat_to_string l
  | PatOp op ->  Util.format1 "(%s)" op
  | PatAscribed(p,t) -> Util.format2 "(%s:%s)" (p |> pat_to_string) (t |> term_to_string)

let rec head_id_of_pat p = match p.pat with
        | PatName l -> [l]
        | PatVar (i, _) -> [FStar.Ident.lid_of_ids [i]]
        | PatApp(p, _) -> head_id_of_pat p
        | PatAscribed(p, _) -> head_id_of_pat p
        | _ -> []

let lids_of_let defs =  defs |> List.collect (fun (p, _) -> head_id_of_pat p)

let id_of_tycon = function
  | TyconAbstract(i, _, _)
  | TyconAbbrev(i, _, _, _)
  | TyconRecord(i, _, _, _)
  | TyconVariant(i, _, _, _) -> i.idText

let decl_to_string (d:decl) = match d.d with
  | TopLevelModule l -> "module " ^ l.str
  | Open l -> "open " ^ l.str
  | ModuleAbbrev (i, l) -> Util.format2 "module %s = %s" i.idText l.str
  | KindAbbrev(i, _, _) -> "kind " ^ i.idText
  | ToplevelLet(_, _, pats) -> "let " ^ (lids_of_let pats |> List.map (fun l -> l.str) |> String.concat ", ")
  | Main _ -> "main ..."
  | Assume(_, i, _) -> "assume " ^ i.idText
  | Tycon(_, tys) -> "type " ^ (tys |> List.map (fun (x,_)->id_of_tycon x) |> String.concat ", ")
  | Val(_, i, _) -> "val " ^ i.idText
  | Exception(i, _) -> "exception " ^ i.idText
  | NewEffect(_, DefineEffect(i, _, _, _, _))
  | NewEffect(_, RedefineEffect(i, _, _)) -> "new_effect " ^ i.idText
  | NewEffectForFree(_, DefineEffect(i, _, _, _, _))
  | NewEffectForFree(_, RedefineEffect(i, _, _)) -> "new_effect_for_free " ^ i.idText
  | SubEffect _ -> "sub_effect"
  | Pragma _ -> "pragma"
  | Fsdoc _ -> "fsdoc"

let modul_to_string (m:modul) = match m with
    | Module (_, decls)
    | Interface (_, decls, _) ->
      decls |> List.map decl_to_string |> String.concat "\n"


//////////////////////////////////////////////////////////////////////////////////////////////
// Error reporting
//////////////////////////////////////////////////////////////////////////////////////////////

let error msg tm r =
 let tm = tm |> term_to_string in
 let tm = if String.length tm >= 80 then Util.substring tm 0 77 ^ "..." else tm in
 if Options.universes()
 then raise (FStar.Syntax.Syntax.Error(msg^"\n"^tm, r))
 else raise (S.Error(msg^"\n"^tm, r))
