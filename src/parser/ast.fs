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
module Microsoft.FStar.Parser.AST
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Range
open Microsoft.FStar
open Microsoft.FStar.Util

(* AST produced by the parser, before desugaring
   It is not stratified: a single type called "term" containing
   expressions, formulas, types, and so on
 *)
type level = | Un | Expr | Type | Kind | Formula
type lid = Syntax.LongIdent
type term' = 
  | Wild      
  | Const     of Syntax.sconst
  | Op        of string * list<term>
  | Tvar      of ident
  | Var       of lid
  | Name      of lid
  | Construct of lid * list<(term*bool)>               (* data, type: bool in each arg records an implicit *)
  | Abs       of list<pattern> * term
  | App       of term * term * bool                    (* aqual marks an explicitly provided implicit parameter *)
  | Let       of bool * list<(pattern * term)> * term  (* bool is for let rec *)
  | Seq       of term * term
  | If        of term * term * term
  | Match     of term * list<branch>
  | TryWith   of term * list<branch>
  | Ascribed  of term * term 
  | Record    of option<term> * list<(lid * term)>
  | Project   of term * lid
  | Product   of list<binder> * term (* function space *)
  | Sum       of list<binder> * term (* dependent tuple *)
  | QForall   of list<binder> * list<term> * term 
  | QExists   of list<binder> * list<term> * term 
  | Refine    of binder * term 
  | Paren     of term
  | Requires  of term * option<string>
  | Ensures   of term * option<string>
  | Labeled   of term * string * bool

and term = {tm:term'; range:range; level:level}

and binder' = 
  | Variable of ident
  | TVariable of ident
  | Annotated of ident * term 
  | TAnnotated of ident * term 
  | NoName of term
and binder = {b:binder'; brange:range; blevel:level; aqual:Syntax.aqual}

and pattern' = 
  | PatWild
  | PatConst    of Syntax.sconst 
  | PatApp      of pattern * list<pattern> 
  | PatVar      of ident * bool         (* flag marks an explicitly provided implicit *)
  | PatName     of lid
  | PatTvar     of ident
  | PatList     of list<pattern>
  | PatTuple    of list<pattern> * bool (* dependent if flag is set *)
  | PatRecord   of list<(lid * pattern)>
  | PatAscribed of pattern * term 
  | PatOr       of list<pattern>
and pattern = {pat:pattern'; prange:range}

and branch = (pattern * option<term> * term)

type knd = term
type typ = term
type expr = term

type tycon =  
  | TyconAbstract of ident * list<binder> * option<knd>
  | TyconAbbrev   of ident * list<binder> * option<knd> * term
  | TyconRecord   of ident * list<binder> * option<knd> * list<(ident * term)>
  | TyconVariant  of ident * list<binder> * option<knd> * list<(ident * option<term> * bool)> (* using 'of' notion *)
   
type qualifiers = list<Syntax.qualifier>

type decl' = 
  | Open of lid 
  | KindAbbrev of ident * list<binder> * knd
  | ToplevelLet of bool * list<(pattern * term)> 
  | Main of term
  | Assume of qualifiers * ident * term
  | Tycon of qualifiers * list<tycon>
  | Val of qualifiers * ident * term  (* bool is for logic val *)
  | Exception of ident * option<term>
  | MonadLat of list<monad_sig> * list<lift>
and decl = {d:decl'; drange:range}
and monad_sig = {
  mon_name:ident;
  mon_total:bool;
  mon_decls:list<decl>;
  mon_abbrevs:list<(bool * ident * list<binder> * typ)>
 }
and lift = {
  msource: ident;
  mdest: ident;
  lift_op: term
 }

type pragma =
  | Monadic of lid * lid * lid
  | Dynamic 
type modul = 
  | Module of LongIdent * list<decl>
  | Interface of LongIdent * list<decl>
type file = list<pragma> * list<modul>

(********************************************************************************)
let mk_decl d r = {d=d; drange=r}
let mk_binder b r l i = {b=b; brange=r; blevel=l; aqual=i}
let mk_term t r l = {tm=t; range=r; level=l}
let mk_pattern p r = {pat=p; prange=r}
let un_curry_abs ps body = match body.tm with 
    | Abs(p', body') -> Abs(ps@p', body')
    | _ -> Abs(ps, body)
let mk_function branches r1 r2 = 
  let x = Util.genident (Some r1) in
  mk_term (Abs([mk_pattern (PatVar(x,false)) r1],
               mk_term (Match(mk_term (Var(lid_of_ids [x])) r1 Expr, branches)) r2 Expr))
    r2 Expr
let un_function p tm = match p.pat, tm.tm with 
    | PatVar _, Abs(pats, body) -> Some (mk_pattern (PatApp(p, pats)) p.prange, body)
    | _ -> None
  
let lid_with_range lid r = lid_of_path (path_of_lid lid) r

let to_string_l sep f l = 
  String.concat sep (List.map f l)

let rec term_to_string (x:term) = match x.tm with 
  | Wild -> "_"
  | Requires (t, _) -> Util.format1 "(requires %s)" (term_to_string t)
  | Ensures (t, _) -> Util.format1 "(ensures %s)" (term_to_string t)
  | Labeled (t, l, _) -> Util.format2 "(labeled %s %s)" l (term_to_string t)
  | Const c -> Print.const_to_string c
  | Op(s, xs) -> Util.format2 "%s(%s)" s (String.concat ", " (List.map (fun x -> x|> term_to_string) xs))
  | Tvar id -> id.idText
  | Var l
  | Name l -> Print.sli l
  | Construct(l, args) -> 
    Util.format2 "(%s %s)" (Print.sli l) (to_string_l " " (fun (a,imp) -> Util.format2 "%s%s" (if imp then "#" else "") (term_to_string a)) args)
  | Abs(pats, t) when (x.level = Expr) -> 
    Util.format2 "(fun %s -> %s)" (to_string_l " " pat_to_string pats) (t|> term_to_string)
  | Abs(pats, t) when (x.level = Type) -> 
    Util.format2 "(fun %s => %s)" (to_string_l " " pat_to_string pats) (t|> term_to_string)
  | App(t1, t2, imp) -> Util.format3 "%s %s%s" (t1|> term_to_string) (if imp then "#" else "") (t2|> term_to_string)
  | Let(false, [(pat,tm)], body) -> 
    Util.format3 "let %s = %s in %s" (pat|> pat_to_string) (tm|> term_to_string) (body|> term_to_string)
  | Let(_, lbs, body) -> 
    Util.format2 "let rec %s in %s" (to_string_l " and " (fun (p,b) -> Util.format2 "%s=%s" (p|> pat_to_string) (b|> term_to_string)) lbs) (body|> term_to_string) 
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
    Util.format2 "{%s with %s}" (e|> term_to_string) (to_string_l " " (fun (l,e) -> Util.format2 "%s=%s" (Print.sli l) (e|> term_to_string)) fields)
  | Record(None, fields) -> 
    Util.format1 "{%s}" (to_string_l " " (fun (l,e) -> Util.format2 "%s=%s" (Print.sli l) (e|> term_to_string)) fields)
  | Project(e,l) -> 
    Util.format2 "%s.%s" (e|> term_to_string) (Print.sli l)
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
      (to_string_l "; " term_to_string pats)
      (t|> term_to_string)
  | QExists(bs, pats, t) ->
    Util.format3 "exists %s.{:pattern %s} %s"
      (to_string_l " " binder_to_string bs)
      (to_string_l "; " term_to_string pats)
      (t|> term_to_string)
  | Refine(b, t) -> 
    Util.format2 "%s:{%s}" (b|> binder_to_string) (t|> term_to_string)      
  | Paren t -> Util.format1 "(%s)" (t|> term_to_string)
  | Product(bs, t) ->
        Util.format2 "Unidentified product: [%s] %s"
          (bs |> List.map binder_to_string |> String.concat ",") (t|> term_to_string)
  | t -> failwith "Missing case in term_to_string"

and binder_to_string x = 
  let s = match x.b with 
  | Variable i -> i.idText
  | TVariable i -> Util.format1 "%s:_" (i.idText) 
  | TAnnotated(i,t)
  | Annotated(i,t) -> Util.format2 "%s:%s" (i.idText) (t |> term_to_string)
  | NoName t -> t |> term_to_string in
  match x.aqual with 
    | Some Implicit -> Util.format1 "#%s" s 
    | Some Equality -> Util.format1 "=%s" s
    | _ -> s

and pat_to_string x = match x.pat with 
  | PatWild -> "_"
  | PatConst c -> Print.const_to_string c
  | PatApp(p, ps) -> Util.format2 "(%s %s)" (p |> pat_to_string) (to_string_l " " pat_to_string ps)
  | PatTvar i 
  | PatVar (i, true) -> Util.format1 "#%s" i.idText
  | PatVar (i, false) -> i.idText
  | PatName l -> Print.sli l
  | PatList l -> Util.format1 "[%s]" (to_string_l "; " pat_to_string l)
  | PatTuple (l, false) -> Util.format1 "(%s)" (to_string_l ", " pat_to_string l)
  | PatTuple (l, true) -> Util.format1 "(|%s|)" (to_string_l ", " pat_to_string l)
  | PatRecord l -> Util.format1 "{%s}" (to_string_l "; " (fun (f,e) -> Util.format2 "%s=%s" (Print.sli f) (e |> pat_to_string)) l)
  | PatOr l ->  to_string_l "|\n " pat_to_string l
  | PatAscribed(p,t) -> Util.format2 "(%s:%s)" (p |> pat_to_string) (t |> term_to_string)
  
let error msg tm r =
 let tm = tm |> term_to_string in
 let tm = if String.length tm >= 80 then Util.substring tm 0 77 ^ "..." else tm in 
 raise (Error(msg^"\n"^tm, r))

let consPat r hd tl = PatApp(mk_pattern (PatName Const.cons_lid) r, [hd;tl])
let consTerm r hd tl = mk_term (Construct(Const.cons_lid, [(hd, false);(tl, false)])) r Expr
let lexConsTerm r hd tl = mk_term (Construct(Const.lexcons_lid, [(hd, false);(tl, false)])) r Expr

let mkConsList r elts =  
  let nil = mk_term (Construct(Const.nil_lid, [])) r Expr in
    List.fold_right (fun e tl -> consTerm r e tl) elts nil

let mkLexList r elts = 
  let nil = mk_term (Construct(Const.lextop_lid, [])) r Expr in
  List.fold_right (fun e tl -> lexConsTerm r e tl) elts nil

let mkApp t args r = match args with 
  | [] -> t 
  | _ -> match t.tm with 
      | Name s -> mk_term (Construct(s, args)) r Un
      | _ -> List.fold_left (fun t (a,imp) -> mk_term (App(t, a, imp)) r Un) t args

let mkExplicitApp t args r = match args with 
  | [] -> t 
  | _ -> match t.tm with 
      | Name s -> mk_term (Construct(s, (List.map (fun a -> (a, false)) args))) r Un
      | _ -> List.fold_left (fun t a -> mk_term (App(t, a, false)) r Un) t args
          
let mkTuple args r = 
  let cons = Util.mk_tuple_data_lid (List.length args) r in 
  mkExplicitApp (mk_term (Name cons) r Expr) args r

let mkDTuple args r = 
  let cons = Util.mk_dtuple_data_lid (List.length args) r in 
  mkExplicitApp (mk_term (Name cons) r Expr) args r
    
let mkRefinedBinder id t refopt m implicit = 
  let b = mk_binder (Annotated(id, t)) m Type implicit in
  match refopt with 
    | None -> b 
    | Some t -> mk_binder (Annotated(id, mk_term (Refine(b, t)) m Type)) m Type implicit