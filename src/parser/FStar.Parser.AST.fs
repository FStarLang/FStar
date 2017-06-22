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
open FStar.All
open FStar.Errors
module C = FStar.Parser.Const
open FStar.Range
open FStar.Ident
open FStar
open FStar.Util
open FStar.Const

(* AST produced by the parser, before desugaring
   It is not stratified: a single type called "term" containing
   expressions, formulas, types, and so on
 *)
type level = | Un | Expr | Type_level | Kind | Formula
type imp =
    | FsTypApp
    | Hash
    | UnivApp
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
  | Op        of ident * list<term>
  | Tvar      of ident
  | Uvar      of ident                                (* universe variable *)
  | Var       of lid // a qualified identifier that starts with a lowercase (Foo.Bar.baz)
  | Name      of lid // a qualified identifier that starts with an uppercase (Foo.Bar.Baz)
  | Projector of lid * ident (* a data constructor followed by one of
                                its formal parameters, or an effect
                                followed by one  of its actions or
                                "fields" *)
  | Construct of lid * list<(term*imp)>               (* data, type: bool in each arg records an implicit *)
  | Abs       of list<pattern> * term
  | App       of term * term * imp                    (* aqual marks an explicitly provided implicit parameter *)
  | Let       of let_qualifier * list<(pattern * term)> * term
  | LetOpen   of lid * term
  | Seq       of term * term
  | Bind      of ident * term * term
  | If        of term * term * term
  | Match     of term * list<branch>
  | TryWith   of term * list<branch>
  | Ascribed  of term * term * option<term>
  | Record    of option<term> * list<(lid * term)>
  | Project   of term * lid
  | Product   of list<binder> * term                 (* function space *)
  | Sum       of list<binder> * term                 (* dependent tuple *)
  | QForall   of list<binder> * list<list<term>> * term
  | QExists   of list<binder> * list<list<term>> * term
  | Refine    of binder * term
  | NamedTyp  of ident * term
  | Paren     of term
  | Requires  of term * option<string>
  | Ensures   of term * option<string>
  | Labeled   of term * string * bool
  | Assign    of ident * term
  | Discrim   of lid   (* Some?  (formerly is_Some) *)
  | Attributes of list<term>   (* attributes decorating a term *)

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
  | PatOp       of ident
and pattern = {pat:pattern'; prange:range}

and branch = (pattern * option<term> * term)

type knd = term
type typ = term
type expr = term

// Documentation comment. May appear appear as follows:
//  - Immediately before a top-level declaration
//  - Immediately after a type constructor or record field
//  - In the middle of a file, as a standalone documentation declaration
(* KM : Would need some range information on fsdocs to be able to print them correctly *)
type fsdoc = string * list<(string * string)> // comment + (name,value) keywords

(* TODO (KM) : it would be useful for the printer to have range information for those *)
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
  | Effect_qual
  | New
  | Inline                                 //a definition that *should* always be unfolded by the normalizer
  | Visible                                //a definition that may be unfolded by the normalizer, but only if necessary (default)
  | Unfold_for_unification_and_vcgen       //a definition that will be unfolded by the normalizer, during unification and for SMT queries
  | Inline_for_extraction                  //a definition that will be inlined only during compilation
  | Irreducible                            //a definition that can never be unfolded by the normalizer
  | NoExtract                              // a definition whose contents won't be extracted (currently, by KreMLin only)
  | Reifiable
  | Reflectable
  //old qualifiers
  | Opaque
  | Logic

type qualifiers = list<qualifier>

type attributes_ = list<term>
type decoration =
  | Qualifier of qualifier
  | DeclAttributes of list<term>
  | Doc of fsdoc

type lift_op =
  | NonReifiableLift of term
  | ReifiableLift    of term * term //lift_wp, lift
  | LiftForFree      of term

type lift = {
  msource: lid;
  mdest:   lid;
  lift_op: lift_op;
}

type pragma =
  | SetOptions of string
  | ResetOptions of option<string>
  | LightOff

type decl' =
  | TopLevelModule of lid
  | Open of lid
  | Include of lid
  | ModuleAbbrev of ident * lid
  | TopLevelLet of let_qualifier * list<(pattern * term)>
  | Main of term
  | Tycon of bool * list<(tycon * option<fsdoc>)>
    (* bool is for effect *)
  | Val of ident * term  (* bool is for logic val *)
  | Exception of ident * option<term>
  | NewEffect of effect_decl
  | SubEffect of lift
  | Pragma of pragma
  | Fsdoc of fsdoc
  | Assume of ident * term

and decl = {
  d:decl';
  drange:range;
  doc:option<fsdoc>;
  quals: qualifiers;
  attrs: attributes_
}
and effect_decl =
  (* KM : Is there really need of the generality of decl here instead of e.g. lid * term ? *)
  | DefineEffect   of ident * list<binder> * term * list<decl>
  | RedefineEffect of ident * list<binder> * term

type modul =
  | Module of lid * list<decl>
  | Interface of lid * list<decl> * bool (* flag to mark admitted interfaces *)
type file = list<modul>
type inputFragment = either<file,list<decl>>

(********************************************************************************)
let check_id id =
    let first_char = String.substring id.idText 0 1 in
    if String.lowercase first_char = first_char
    then ()
    else raise (Error(Util.format1 "Invalid identifer '%s'; expected a symbol that begins with a lower-case character" id.idText, id.idRange))

let at_most_one s r l = match l with
  | [ x ] -> Some x
  | [] -> None
  | _ -> raise (Error (Util.format1 "At most one %s is allowed on declarations" s, r))

let mk_decl d r decorations =
  let doc = at_most_one "fsdoc" r (List.choose (function Doc d -> Some d | _ -> None) decorations) in
  let attributes_ = at_most_one "attribute set" r (
    List.choose (function DeclAttributes a -> Some a | _ -> None) decorations
  ) in
  let attributes_ = Util.dflt [] attributes_ in
  let qualifiers = List.choose (function Qualifier q -> Some q | _ -> None) decorations in
  { d=d; drange=r; doc=doc; quals=qualifiers; attrs=attributes_ }

let mk_binder b r l i = {b=b; brange=r; blevel=l; aqual=i}
let mk_term t r l = {tm=t; range=r; level=l}
let mk_uminus t rminus r l =
  let t =
    match t.tm with
    | Const (Const_int (s, Some (Signed, width))) ->
        Const (Const_int ("-" ^ s, Some (Signed, width)))
    | _ ->
        Op(mk_ident ("-", rminus), [t])
  in
  mk_term t r l

let mk_pattern p r = {pat=p; prange=r}
let un_curry_abs ps body = match body.tm with
    | Abs(p', body') -> Abs(ps@p', body')
    | _ -> Abs(ps, body)
let mk_function branches r1 r2 =
  let x =
    let i = C.next_id () in
    Ident.gen r1 in
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

let ml_comp t =
    let ml = mk_term (Name C.effect_ML_lid) t.range Expr in
    let t = mk_term (App(ml, t, Nothing)) t.range Expr in
    t

let tot_comp t =
    let ml = mk_term (Name C.effect_Tot_lid) t.range Expr in
    let t = mk_term (App(ml, t, Nothing)) t.range Expr in
    t

let mkApp t args r = match args with
  | [] -> t
  | _ -> match t.tm with
      | Name s -> mk_term (Construct(s, args)) r Un
      | _ -> List.fold_left (fun t (a,imp) -> mk_term (App(t, a, imp)) r Un) t args

let mkRefSet r elts =
  let empty_lid, singleton_lid, union_lid =
      C.tset_empty, C.tset_singleton, C.tset_union in
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
        then let _ = Errors.warn r "Focusing on only some cases" in
         let focussed = List.filter fst branches |> List.map snd in
                 focussed@[mkWildAdmitMagic r]
        else branches |> List.map snd

let focusLetBindings lbs r =
    let should_filter = Util.for_some fst lbs in
        if should_filter
        then let _ = Errors.warn r "Focusing on only some cases in this (mutually) recursive definition" in
         List.map (fun (f, lb) ->
              if f then lb
              else (fst lb, mkAdmitMagic r)) lbs
        else lbs |> List.map snd

let mkFsTypApp t args r =
  mkApp t (List.map (fun a -> (a, FsTypApp)) args) r

  (* TODO : is this valid or should it use Construct ? *)
let mkTuple args r =
  let cons = C.mk_tuple_data_lid (List.length args) r in
  mkApp (mk_term (Name cons) r Expr) (List.map (fun x -> (x, Nothing)) args) r

let mkDTuple args r =
  let cons = C.mk_dtuple_data_lid (List.length args) r in
  mkApp (mk_term (Name cons) r Expr) (List.map (fun x -> (x, Nothing)) args) r

let mkRefinedBinder id t should_bind_var refopt m implicit =
  let b = mk_binder (Annotated(id, t)) m Type_level implicit in
  match refopt with
    | None -> b
    | Some phi ->
        if should_bind_var
        then mk_binder (Annotated(id, mk_term (Refine(b, phi)) m Type_level)) m Type_level implicit
        else
            let x = gen t.range in
            let b = mk_binder (Annotated (x, t)) m Type_level implicit in
            mk_binder (Annotated(id, mk_term (Refine(b, phi)) m Type_level)) m Type_level implicit

let mkRefinedPattern pat t should_bind_pat phi_opt t_range range =
    let t = match phi_opt with
        | None     -> t
        | Some phi ->
            if should_bind_pat
            then
                begin match pat.pat with
                | PatVar (x,_) ->
                    mk_term (Refine(mk_binder (Annotated(x, t)) t_range Type_level None, phi)) range Type_level
                | _ ->
                    let x = gen t_range in
                    let phi =
                        (* match x with | pat -> phi | _ -> False *)
                        let x_var = mk_term (Var (lid_of_ids [x])) phi.range Formula in
                        let pat_branch = (pat, None, phi)in
                        let otherwise_branch =
                            (mk_pattern PatWild phi.range, None,
                             mk_term (Name (lid_of_path ["False"] phi.range)) phi.range Formula)
                        in
                        mk_term (Match (x_var, [pat_branch ; otherwise_branch])) phi.range Formula
                    in
                    mk_term (Refine(mk_binder (Annotated(x, t)) t_range Type_level None, phi)) range Type_level
                end
            else
                let x = gen t.range in
                mk_term (Refine(mk_binder (Annotated (x, t)) t_range Type_level None, phi)) range Type_level
     in
     mk_pattern (PatAscribed(pat, t)) range

let rec extract_named_refinement t1  =
    match t1.tm with
        | NamedTyp(x, t) -> Some (x, t, None)
        | Refine({b=Annotated(x, t)}, t') ->  Some (x, t, Some t')
    | Paren t -> extract_named_refinement t
        | _ -> None

(* Some helpers that parse.mly and parse.fsy will want too *)

(* JP: what does this function do? A comment would be welcome, or at the very
   least a type annotation...
   JP: ok, here's my understanding.
   This function peeks at the first top-level declaration;
   - if this is NOT a TopLevelModule, then we're in interactive mode and return
     [Inr list-of-declarations]
   - if this IS a TopLevelModule, then we do a forward search and group
     declarations together with the preceding [TopLevelModule] and return a [Inl
     list-of-modules] where each "module" [Module (lid, list-of-declarations)], with the
     unspecified invariant that the first declaration is a [TopLevelModule]
   JP: TODO actually forbid multiple modules and remove all of this. *)

//NS: needed to hoist this to workaround a bootstrapping bug
//    leaving it within as_frag causes the type-checker to take a very long time, perhaps looping
let rec as_mlist (out:list<modul>) (cur: (lid * decl) * list<decl>) (ds:list<decl>) : list<modul> =
    let ((m_name, m_decl), cur) = cur in
    match ds with
    | [] -> List.rev (Module(m_name, m_decl :: List.rev cur)::out)
    | d :: ds ->
        begin match d.d with
        | TopLevelModule m' ->
            as_mlist (Module(m_name, m_decl :: List.rev cur)::out) ((m', d), []) ds
        | _ ->
            as_mlist out ((m_name, m_decl), d::cur) ds
        end

let as_frag is_light (light_range:Range.range) (ds:list<decl>) : either<(list<modul>),(list<decl>)> =
  let d, ds = match ds with
    | d :: ds -> d, ds
    | [] -> raise Empty_frag
  in
  match d.d with
  | TopLevelModule m ->
      let ds = if is_light then mk_decl (Pragma LightOff) light_range [] :: ds else ds in
      let ms = as_mlist [] ((m,d), []) ds in
      begin match List.tl ms with
      | Module (m', _) :: _ ->
          (* This check is coded to hard-fail in dep.num_of_toplevelmods. *)
          let msg = "Support for more than one module in a file is deprecated" in
          print2_warning "%s (Warning): %s\n" (string_of_range (range_of_lid m')) msg
      | _ ->
          ()
      end;
      Inl ms
  | _ ->
      let ds = d::ds in
      List.iter (function
        | {d=TopLevelModule _; drange=r} -> raise (Error("Unexpected module declaration", r))
        | _ -> ()
      ) ds;
      Inr ds

let compile_op arity s =
    let name_of_char = function
      |'&' -> "Amp"
      |'@'  -> "At"
      |'+' -> "Plus"
      |'-' when (arity=1) -> "Minus"
      |'-' -> "Subtraction"
      |'/' -> "Slash"
      |'<' -> "Less"
      |'=' -> "Equals"
      |'>' -> "Greater"
      |'_' -> "Underscore"
      |'|' -> "Bar"
      |'!' -> "Bang"
      |'^' -> "Hat"
      |'%' -> "Percent"
      |'*' -> "Star"
      |'?' -> "Question"
      |':' -> "Colon"
      | _ -> "UNKNOWN" in
    match s with
    | ".[]<-" -> "op_String_Assignment"
    | ".()<-" -> "op_Array_Assignment"
    | ".[]" -> "op_String_Access"
    | ".()" -> "op_Array_Access"
    | _ -> "op_"^ (String.concat "_" (List.map name_of_char (String.list_of_string s)))

let compile_op' s =
  compile_op (-1) s

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
  | Const c -> C.const_to_string c
  | Op(s, xs) ->
      Util.format2 "%s(%s)" (text_of_id s) (String.concat ", " (List.map (fun x -> x|> term_to_string) xs))
  | Tvar id
  | Uvar id -> id.idText
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
  | Ascribed(t1, t2, None) ->
    Util.format2 "(%s : %s)" (t1|> term_to_string) (t2|> term_to_string)
  | Ascribed(t1, t2, Some tac) ->
    Util.format3 "(%s : %s by %s)" (t1|> term_to_string) (t2|> term_to_string) (tac |> term_to_string)
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
  | Product([b], t) when (x.level = Type_level) ->
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
  | PatConst c -> C.const_to_string c
  | PatApp(p, ps) -> Util.format2 "(%s %s)" (p |> pat_to_string) (to_string_l " " pat_to_string ps)
  | PatTvar (i, aq)
  | PatVar (i,  aq) -> Util.format2 "%s%s" (aqual_to_string aq) i.idText
  | PatName l -> l.str
  | PatList l -> Util.format1 "[%s]" (to_string_l "; " pat_to_string l)
  | PatTuple (l, false) -> Util.format1 "(%s)" (to_string_l ", " pat_to_string l)
  | PatTuple (l, true) -> Util.format1 "(|%s|)" (to_string_l ", " pat_to_string l)
  | PatRecord l -> Util.format1 "{%s}" (to_string_l "; " (fun (f,e) -> Util.format2 "%s=%s" (f.str) (e |> pat_to_string)) l)
  | PatOr l ->  to_string_l "|\n " pat_to_string l
  | PatOp op ->  Util.format1 "(%s)" (Ident.text_of_id op)
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
  | Include l -> "include " ^ l.str
  | ModuleAbbrev (i, l) -> Util.format2 "module %s = %s" i.idText l.str
  | TopLevelLet(_, pats) -> "let " ^ (lids_of_let pats |> List.map (fun l -> l.str) |> String.concat ", ")
  | Main _ -> "main ..."
  | Assume(i, _) -> "assume " ^ i.idText
  | Tycon(_, tys) -> "type " ^ (tys |> List.map (fun (x,_)->id_of_tycon x) |> String.concat ", ")
  | Val(i, _) -> "val " ^ i.idText
  | Exception(i, _) -> "exception " ^ i.idText
  | NewEffect(DefineEffect(i, _, _, _))
  | NewEffect(RedefineEffect(i, _, _)) -> "new_effect " ^ i.idText
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
 raise (Error(msg^"\n"^tm, r))
