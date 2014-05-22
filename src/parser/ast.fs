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

type level = | Un | Expr | Type | Kind | Formula
type lid = Syntax.LongIdent
type term' = 
  | Wild      
  | Const     of Syntax.sconst
  | Op        of string * list<term>
  | Tvar      of ident
  | Var       of lid
  | Name      of lid
  |   Construct of lid * list<(term*bool)>               (* data, type: bool in each arg records an implicit *)
  | Abs       of list<pattern> * term
  | App       of term * term * bool                    (* bool marks an explicitly provided implicit parameter *)
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
  | Affine    of term

and term = {term:term'; range:range; level:level}

and binder' = 
  | Variable of ident
  | TVariable of ident
  | Annotated of ident * term 
  | TAnnotated of ident * term 
  | NoName of term
and binder = {binder:binder'; brange:range; blevel:level; implicit:bool}

and pattern' = 
  | PatWild
  | PatConst    of Syntax.sconst 
  | PatApp      of pattern * list<pattern> 
  | PatVar      of ident
  | PatName     of lid
  | PatTvar     of ident
  | PatList     of list<pattern>
  | PatTuple    of list<pattern>
  | PatRecord   of list<(lid * pattern)>
  | PatAscribed of pattern * term 
  | PatOr       of list<pattern>
and pattern = {pattern:pattern'; prange:range}

and branch = (pattern * option<term> * term)

type knd = term
type typ = term
type expr = term
type atag = | AssumeTag | QueryTag | DefinitionTag

type tycon =  
  | TyconAbstract of ident * list<binder> * option<knd>
  | TyconAbbrev   of ident * list<binder> * option<knd> * term
  | TyconRecord   of ident * list<binder> * option<knd> * list<(ident * term)>
  | TyconVariant  of ident * list<binder> * option<knd> * list<(ident * option<term> * bool)> (* using 'of' notion *)

type tyvalQual = 
  | NoQual
  | LogicTag  of logic_tag
  | Extern    of ident
  | TupleType of int
  | Assumption
 
type decl' = 
  | Open of lid 
  | KindAbbrev of ident * list<binder> * knd
  | Tycon of tyvalQual * list<tycon>
  | ToplevelLet of bool * list<(pattern * term)> 
  | Main of term
  | Assume of atag * ident * term
  | Val of tyvalQual * ident * term  (* bool is for logic val *)
  | Exception of ident * option<term>
  | MonadLat of list<monad_sig> * list<lift>
and decl = {decl:decl'; drange:range}
and monad_sig = {
  mon_name:ident;
  mon_total:bool;
  mon_decls:list<decl>;
  mon_abbrevs:list<(ident * list<binder> * typ)>
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
type file = list<pragma> * list<modul>

(********************************************************************************)
let mk_decl d r = {decl=d; drange=r}
let mk_binder b r l i = {binder=b; brange=r; blevel=l; implicit=i}
let mk_term t r l = {term=t; range=r; level=l}
let mk_pattern p r = {pattern=p; prange=r}
let mk_function branches r1 r2 = 
  let x = Util.genident (Some r1) in
  mk_term (Abs([mk_pattern (PatVar x) r1],
               mk_term (Match(mk_term (Var(lid_of_ids [x])) r1 Expr, branches)) r2 Expr))
    r2 Expr
    
  
let lid_with_range lid r = lid_of_path (path_of_lid lid) r

let to_string_l sep f l = 
  String.concat sep (List.map f l)

let rec term_to_string (x:term) = match x.term with 
  | Wild -> "_"
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
  | Affine t -> Util.format1 "!%s" (t|> term_to_string)
  | t -> failwith "Missing case in term_to_string"

and binder_to_string x = 
  let s = match x.binder with 
  | Variable i -> i.idText
  | TVariable i -> Util.format1 "%s:_" (i.idText) 
  | TAnnotated(i,t)
  | Annotated(i,t) -> Util.format2 "%s:%s" (i.idText) (t |> term_to_string)
  | NoName t -> t |> term_to_string in
  if x.implicit then Util.format1 "#%s" s else s

and pat_to_string x = match x.pattern with 
  | PatWild -> "_"
  | PatConst c -> Print.const_to_string c
  | PatApp(p, ps) -> Util.format2 "(%s %s)" (p |> pat_to_string) (to_string_l " " pat_to_string ps)
  | PatTvar i 
  | PatVar i -> i.idText
  | PatName l -> Print.sli l
  | PatList l -> Util.format1 "[%s]" (to_string_l "; " pat_to_string l)
  | PatTuple l -> Util.format1 "[%s]" (to_string_l ", " pat_to_string l)
  | PatRecord l -> Util.format1 "{%s}" (to_string_l "; " (fun (f,e) -> Util.format2 "%s=%s" (Print.sli f) (e |> pat_to_string)) l)
  | PatOr l ->  to_string_l "|\n " pat_to_string l
  | PatAscribed(p,t) -> Util.format2 "(%s:%s)" (p |> pat_to_string) (t |> term_to_string)
  
let error msg tm r =
 let tm = tm |> term_to_string in
  let tm = if String.length tm >= 80 then Util.substring tm 0 77 ^ "..." else tm in 
  raise (Error(msg^"\n"^tm, r))
    
