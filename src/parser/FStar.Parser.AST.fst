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
module FStar.Parser.AST
open FStar.Pervasives
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Errors
module C = FStar.Parser.Const
open FStar.Compiler.Range
open FStar.Ident
open FStar
open FStar.Compiler
open FStar.Compiler.Util
open FStar.Const

(* AST produced by the parser, before desugaring
   It is not stratified: a single type called "term" containing
   expressions, formulas, types, and so on
 *)
type level = | Un | Expr | Type_level | Kind | Formula

type let_qualifier =
  | NoLetQualifier
  | Rec

type quote_kind =
  | Static
  | Dynamic

type term' =
  | Wild
  | Const     of sconst
  | Op        of ident * list term
  | Tvar      of ident
  | Uvar      of ident                                (* universe variable *)
  | Var       of lid // a qualified identifier that starts with a lowercase (Foo.Bar.baz)
  | Name      of lid // a qualified identifier that starts with an uppercase (Foo.Bar.Baz)
  | Projector of lid * ident (* a data constructor followed by one of
                                its formal parameters, or an effect
                                followed by one  of its actions or
                                "fields" *)
  | Construct of lid * list (term*imp)               (* data, type: bool in each arg records an implicit *)
  | Abs       of list pattern * term
  | App       of term * term * imp                    (* aqual marks an explicitly provided implicit parameter *)
  | Let       of let_qualifier * list (option attributes_ * (pattern * term)) * term
  | LetOperator   of list (ident * pattern * term) * term
  | LetOpen   of lid * term
  | LetOpenRecord of term * term * term
  | Seq       of term * term
  | Bind      of ident * term * term
  | If        of term * option ident (* is this a regular if or a if operator (i.e. [if*]) *)
                      * option match_returns_annotation * term * term
  | Match     of term * option ident (* is this a regular match or a match operator (i.e. [match*]) *)
                      * option match_returns_annotation * list branch
  | TryWith   of term * list branch
  | Ascribed  of term * term * option term * bool  (* bool says whether equality ascription $: *)
  | Record    of option term * list (lid * term)
  | Project   of term * lid
  | Product   of list binder * term                (* function space *)
  | Sum       of list (either binder term) * term (* dependent tuple *)
  | QForall   of list binder * patterns * term
  | QExists   of list binder * patterns * term
  | Refine    of binder * term
  | NamedTyp  of ident * term
  | Paren     of term
  | Requires  of term * option string
  | Ensures   of term * option string
  | LexList   of list term  (* a decreases clause mentions either a lexicographically ordered list, *)
  | WFOrder   of term * term  (* or a well-founded relation or some type and an expression of the same type *)
  | Decreases of term * option string
  | Labeled   of term * string * bool
  | Discrim   of lid   (* Some?  (formerly is_Some) *)
  | Attributes of list term   (* attributes decorating a term *)
  | Antiquote of term  (* Antiquotation within a quoted term *)
  | Quote     of term * quote_kind
  | VQuote    of term        (* Quoting an lid, this gets removed by the desugarer *)
  | CalcProof of term * term * list calc_step (* A calculational proof with relation, initial expression, and steps *)
  | IntroForall of list binder * term * term                     (* intro_forall x1..xn. P with e *)
  | IntroExists of list binder * term * list term * term        (* intro_exists x1...xn.P using v1..vn with e *)
  | IntroImplies of term * term * binder * term                   (* intro_implies P Q with x. e *)
  | IntroOr of bool * term * term * term                          (* intro_or_{left ,right} P Q with e *)
  | IntroAnd of term * term * term * term                         (* intro_and P Q with e1 and e2 *)
  | ElimForall  of list binder * term * list term               (* elim_forall x1..xn. P using v1..vn *)
  | ElimExists  of list binder * term * term * binder * term     (* elim_exists x1...xn.P to Q with e *)
  | ElimImplies of term * term * term                             (* elim_implies P Q with e *)
  | ElimOr of term * term * term * binder * term * binder * term  (* elim_or P Q to R with x.e1 and y.e2 *)
  | ElimAnd of term * term * term * binder * binder * term        (* elim_and P Q to R with x y. e *)
and term = {tm:term'; range:range; level:level}

(* (as y)? returns t *)
and match_returns_annotation = option ident * term * bool

and patterns = list ident * list (list term)

and calc_step =
  | CalcStep of term * term * term (* Relation, justification and next expression *)

and attributes_ = list term

and binder' =
  | Variable of ident
  | TVariable of ident
  | Annotated of ident * term
  | TAnnotated of ident * term
  | NoName of term

and binder = {b:binder'; brange:range; blevel:level; aqual:aqual; battributes:attributes_}

and pattern' =
  | PatWild     of aqual * attributes_
  | PatConst    of sconst
  | PatApp      of pattern * list pattern
  | PatVar      of ident * aqual * attributes_
  | PatName     of lid
  | PatTvar     of ident * aqual * attributes_
  | PatList     of list pattern
  | PatTuple    of list pattern * bool (* dependent if flag is set *)
  | PatRecord   of list (lid * pattern)
  | PatAscribed of pattern * (term * option term)
  | PatOr       of list pattern
  | PatOp       of ident
  | PatVQuote   of term (* [`%foo], transformed into "X.Y.Z.foo" by the desugarer *)
and pattern = {pat:pattern'; prange:range}

and branch = (pattern * option term * term)
and arg_qualifier =
    | Implicit
    | Equality
    | Meta of term
    | TypeClassArg
and aqual = option arg_qualifier
and imp =
    | FsTypApp
    | Hash
    | UnivApp
    | HashBrace of term
    | Infix
    | Nothing

type knd = term
type typ = term
type expr = term

type tycon_record = list (ident * aqual * attributes_ * term)

(** The different kinds of payload a constructor can carry *)
type constructor_payload
  = (** constructor of arity 1 for a type of kind [Type] (e.g. [C of int]) *)
    | VpOfNotation of typ
    (** constructor of any arity & kind (e.g. [C:int->ind] or [C:'a->'b->ind 'c]) *)
    | VpArbitrary of typ
    (** constructor whose payload is a record (e.g. [C {a: int}] or [C {x: Type} -> ind x]) *)
    | VpRecord of (tycon_record * opt_kind:option typ)

(* TODO (KM) : it would be useful for the printer to have range information for those *)
type tycon =
  | TyconAbstract of ident * list binder * option knd
  | TyconAbbrev   of ident * list binder * option knd * term
  | TyconRecord   of ident * list binder * option knd * attributes_ * tycon_record
  | TyconVariant  of ident * list binder * option knd * list (ident * option constructor_payload * attributes_)

type qualifier =
  | Private
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
  | NoExtract                              // a definition whose contents won't be extracted (currently, by KaRaMeL only)
  | Reifiable
  | Reflectable
  //old qualifiers
  | Opaque
  | Logic

type qualifiers = list qualifier

type decoration =
  | Qualifier of qualifier
  | DeclAttributes of list term

type lift_op =
  | NonReifiableLift of term
  | ReifiableLift    of term * term //lift_wp, lift
  | LiftForFree      of term

type lift = {
  msource: lid;
  mdest:   lid;
  lift_op: lift_op;
  braced: bool; //a detail: for incremental parsing, we need to know if it is delimited by bracces  
}

type pragma =
  | SetOptions of string
  | ResetOptions of option string
  | PushOptions of option string
  | PopOptions
  | RestartSolver
  | PrintEffectsGraph

type decl' =
  | TopLevelModule of lid
  | Open of lid
  | Friend of lid
  | Include of lid
  | ModuleAbbrev of ident * lid
  | TopLevelLet of let_qualifier * list (pattern * term)
  | Tycon of bool * bool * list tycon
    (* first bool is for effect *)
    (* second bool is for typeclass *)
  | Val of ident * term  (* bool is for logic val *)
  | Exception of ident * option term
  | NewEffect of effect_decl
  | LayeredEffect of effect_decl
  | SubEffect of lift
  | Polymonadic_bind of lid * lid * lid * term
  | Polymonadic_subcomp of lid * lid * term
  | Pragma of pragma
  | Assume of ident * term
  | Splice of list ident * term

and decl = {
  d:decl';
  drange:range;
  quals: qualifiers;
  attrs: attributes_
}
and effect_decl =
  (* KM : Is there really need of the generality of decl here instead of e.g. lid * term ? *)
  | DefineEffect   of ident * list binder * term * list decl
  | RedefineEffect of ident * list binder * term

type modul =
  | Module of lid * list decl
  | Interface of lid * list decl * bool (* flag to mark admitted interfaces *)
type file = modul
type inputFragment = either file (list decl)

let decl_drange decl = decl.drange

(********************************************************************************)
let check_id id =
    let first_char = String.substring (string_of_id id) 0 1 in
    if String.lowercase first_char = first_char
    then ()
    else raise_error (Fatal_InvalidIdentifier, Util.format1 "Invalid identifer '%s'; expected a symbol that begins with a lower-case character" (string_of_id id))  (range_of_id id)

let at_most_one s r l = match l with
  | [ x ] -> Some x
  | [] -> None
  | _ -> raise_error (Fatal_MoreThanOneDeclaration, (Util.format1 "At most one %s is allowed on declarations" s)) r

let mk_decl d r decorations =
  let attributes_ = at_most_one "attribute set" r (
    List.choose (function DeclAttributes a -> Some a | _ -> None) decorations
  ) in
  let attributes_ = Util.dflt [] attributes_ in
  let qualifiers = List.choose (function Qualifier q -> Some q | _ -> None) decorations in
  { d=d; drange=r; quals=qualifiers; attrs=attributes_ }

let mk_binder_with_attrs b r l i attrs = {b=b; brange=r; blevel=l; aqual=i; battributes=attrs}
let mk_binder b r l i = mk_binder_with_attrs b r l i []
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
  let x = Ident.gen r1 in
  mk_term (Abs([mk_pattern (PatVar(x,None,[])) r1],
               mk_term (Match(mk_term (Var(lid_of_ids [x])) r1 Expr, None, None, branches)) r2 Expr))
    r2 Expr
let un_function p tm = match p.pat, tm.tm with
    | PatVar _, Abs(pats, body) -> Some (mk_pattern (PatApp(p, pats)) p.prange, body)
    | _ -> None

let lid_with_range lid r = lid_of_path (path_of_lid lid) r

let consPat r hd tl = PatApp(mk_pattern (PatName C.cons_lid) r, [hd;tl])
let consTerm r hd tl = mk_term (Construct(C.cons_lid, [(hd, Nothing);(tl, Nothing)])) r Expr

let mkConsList r elts =
  let nil = mk_term (Construct(C.nil_lid, [])) r Expr in
    List.fold_right (fun e tl -> consTerm r e tl) elts nil

let unit_const r = mk_term(Const Const_unit) r Expr

let ml_comp t =
    let lid = C.effect_ML_lid () in
    let ml = mk_term (Name lid) t.range Expr in
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
  let empty_lid, singleton_lid, union_lid, addr_of_lid =
      C.set_empty, C.set_singleton, C.set_union, C.heap_addr_of_lid in
  let empty = mk_term (Var(set_lid_range empty_lid r)) r Expr in
  let addr_of = mk_term (Var (set_lid_range addr_of_lid r)) r Expr in
  let singleton = mk_term (Var (set_lid_range singleton_lid r)) r Expr in
  let union = mk_term (Var(set_lid_range union_lid r)) r Expr in
  List.fold_right (fun e tl ->
    let e = mkApp addr_of [(e, Nothing)] r in
    let single_e = mkApp singleton [(e, Nothing)] r in
    mkApp union [(single_e, Nothing); (tl, Nothing)] r) elts empty

let mkExplicitApp t args r = match args with
  | [] -> t
  | _ -> match t.tm with
      | Name s -> mk_term (Construct(s, (List.map (fun a -> (a, Nothing)) args))) r Un
      | _ -> List.fold_left (fun t a -> mk_term (App(t, a, Nothing)) r Un) t args

let mkAdmitMagic r =
    let admit =
        let admit_name = mk_term(Var(set_lid_range C.admit_lid r)) r Expr in
        mkExplicitApp admit_name [unit_const r] r in
    let magic =
        let magic_name = mk_term(Var(set_lid_range C.magic_lid r)) r Expr in
        mkExplicitApp magic_name [unit_const r] r in
    let admit_magic = mk_term(Seq(admit, magic)) r Expr in
    admit_magic

let mkWildAdmitMagic r = (mk_pattern (PatWild (None, [])) r, None, mkAdmitMagic r)

let focusBranches branches r =
    let should_filter = Util.for_some fst branches in
        if should_filter
        then let _ = Errors.log_issue r (Errors.Warning_Filtered, "Focusing on only some cases") in
         let focussed = List.filter fst branches |> List.map snd in
                 focussed@[mkWildAdmitMagic r]
        else branches |> List.map snd

let focusLetBindings lbs r =
    let should_filter = Util.for_some fst lbs in
        if should_filter
        then let _ = Errors.log_issue r (Errors.Warning_Filtered, "Focusing on only some cases in this (mutually) recursive definition") in
         List.map (fun (f, lb) ->
              if f then lb
              else (fst lb, mkAdmitMagic r)) lbs
        else lbs |> List.map snd

let focusAttrLetBindings lbs r =
    let should_filter = Util.for_some (fun (attr, (focus, _)) -> focus) lbs in
    if should_filter
    then let _ = Errors.log_issue r (Errors.Warning_Filtered, "Focusing on only some cases in this (mutually) recursive definition") in
        List.map (fun (attr, (f, lb)) ->
            if f then attr, lb
            else (attr, (fst lb, mkAdmitMagic r))) lbs
    else lbs |> List.map (fun (attr, (_, lb)) -> (attr, lb))

let mkFsTypApp t args r =
  mkApp t (List.map (fun a -> (a, FsTypApp)) args) r

  (* TODO : is this valid or should it use Construct ? *)
let mkTuple args r =
  let cons = C.mk_tuple_data_lid (List.length args) r in
  mkApp (mk_term (Name cons) r Expr) (List.map (fun x -> (x, Nothing)) args) r

let mkDTuple args r =
  let cons = C.mk_dtuple_data_lid (List.length args) r in
  mkApp (mk_term (Name cons) r Expr) (List.map (fun x -> (x, Nothing)) args) r

let mkRefinedBinder id t should_bind_var refopt m implicit attrs : binder =
  let b = mk_binder_with_attrs (Annotated(id, t)) m Type_level implicit attrs in
  match refopt with
    | None -> b
    | Some phi ->
        if should_bind_var
        then mk_binder_with_attrs (Annotated(id, mk_term (Refine(b, phi)) m Type_level)) m Type_level implicit attrs
        else
            let x = gen t.range in
            let b = mk_binder_with_attrs (Annotated (x, t)) m Type_level implicit attrs in
            mk_binder_with_attrs (Annotated(id, mk_term (Refine(b, phi)) m Type_level)) m Type_level implicit attrs

let mkRefinedPattern pat t should_bind_pat phi_opt t_range range =
    let t = match phi_opt with
        | None     -> t
        | Some phi ->
            if should_bind_pat
            then
                begin match pat.pat with
                | PatVar (x,_,attrs) ->
                    mk_term (Refine(mk_binder_with_attrs (Annotated(x, t)) t_range Type_level None attrs, phi)) range Type_level
                | _ ->
                    let x = gen t_range in
                    let phi =
                        (* match x with | pat -> phi | _ -> False *)
                        let x_var = mk_term (Var (lid_of_ids [x])) phi.range Formula in
                        let pat_branch = (pat, None, phi)in
                        let otherwise_branch =
                            (mk_pattern (PatWild (None, [])) phi.range, None,
                             mk_term (Name (lid_of_path ["False"] phi.range)) phi.range Formula)
                        in
                        mk_term (Match (x_var, None, None, [pat_branch ; otherwise_branch])) phi.range Formula
                    in
                    mk_term (Refine(mk_binder (Annotated(x, t)) t_range Type_level None, phi)) range Type_level
                end
            else
                let x = gen t.range in
                mk_term (Refine(mk_binder (Annotated (x, t)) t_range Type_level None, phi)) range Type_level
     in
     mk_pattern (PatAscribed(pat, (t, None))) range

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
let rec as_mlist (cur: (lid * decl) * list decl) (ds:list decl) : modul =
    let ((m_name, m_decl), cur) = cur in
    match ds with
    | [] -> Module(m_name, m_decl :: List.rev cur)
    | d :: ds ->
        begin match d.d with
        | TopLevelModule m' ->
            raise_error (Fatal_UnexpectedModuleDeclaration, "Unexpected module declaration") d.drange
        | _ ->
            as_mlist ((m_name, m_decl), d::cur) ds
        end

let as_frag (ds:list decl) : inputFragment =
  let d, ds = match ds with
    | d :: ds -> d, ds
    | [] -> raise Empty_frag
  in
  match d.d with
  | TopLevelModule m ->
      let m = as_mlist ((m,d), []) ds in
      Inl m
  | _ ->
      let ds = d::ds in
      List.iter (function
        | {d=TopLevelModule _; drange=r} -> raise_error (Fatal_UnexpectedModuleDeclaration, "Unexpected module declaration") r
        | _ -> ()
      ) ds;
      Inr ds

// TODO: Move to something like FStar.Compiler.Util
let strip_prefix (prefix s: string): option string
  = if starts_with s prefix
    then Some (substring_from s (String.length prefix))
    else None

let compile_op arity s r =
    let name_of_char = function
      |'&' -> "Amp"
      |'@'  -> "At"
      |'+' -> "Plus"
      |'-' when (arity=1) -> "Minus"
      |'-' -> "Subtraction"
      |'~' -> "Tilde"
      |'/' -> "Slash"
      |'\\' -> "Backslash"
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
      |'$' -> "Dollar"
      |'.' -> "Dot"
      | c -> "u" ^ (Util.string_of_int (Util.int_of_char c))
    in
    match s with
    | ".[]<-" -> "op_String_Assignment"
    | ".()<-" -> "op_Array_Assignment"
    | ".[||]<-" -> "op_Brack_Lens_Assignment"
    | ".(||)<-" -> "op_Lens_Assignment"
    | ".[]" -> "op_String_Access"
    | ".()" -> "op_Array_Access"
    | ".[||]" -> "op_Brack_Lens_Access"
    | ".(||)" -> "op_Lens_Access"
    | _ -> // handle let operators (i.e. [let?] or [and*])
          let prefix, s = if starts_with s "let" || starts_with s "and"
                          then substring s 0 3 ^ "_", substring_from s 3
                          else "", s in
          "op_" ^ prefix ^ String.concat "_" (List.map name_of_char (String.list_of_string s))

let compile_op' s r =
  compile_op (-1) s r

let string_to_op s =
  let name_of_op = function
    | "Amp" ->  Some ("&", None)
    | "At" -> Some ("@", None)
    | "Plus" -> Some ("+", None)
    | "Minus" -> Some ("-", None)
    | "Subtraction" -> Some ("-", Some 2)
    | "Tilde" -> Some ("~", None)
    | "Slash" -> Some ("/", None)
    | "Backslash" -> Some ("\\", None)
    | "Less" -> Some ("<", None)
    | "Equals" -> Some ("=", None)
    | "Greater" -> Some (">", None)
    | "Underscore" -> Some ("_", None)
    | "Bar" -> Some ("|", None)
    | "Bang" -> Some ("!", None)
    | "Hat" -> Some ("^", None)
    | "Percent" -> Some ("%", None)
    | "Star" -> Some ("*", None)
    | "Question" -> Some ("?", None)
    | "Colon" -> Some (":", None)
    | "Dollar" -> Some ("$", None)
    | "Dot" -> Some (".", None)
    | "let" | "and" -> Some (s, None)
    | _ -> None
  in
  match s with
  | "op_String_Assignment" -> Some (".[]<-", None)
  | "op_Array_Assignment" -> Some (".()<-", None)
  | "op_Brack_Lens_Assignment" -> Some (".[||]<-", None)
  | "op_Lens_Assignment" -> Some (".(||)<-", None)
  | "op_String_Access" -> Some (".[]", None)
  | "op_Array_Access" -> Some (".()", None)
  | "op_Brack_Lens_Access" -> Some (".[||]", None)
  | "op_Lens_Access" -> Some (".(||)", None)
  | _ ->
    if starts_with s "op_"
    then let s = split (substring_from s (String.length "op_")) "_" in
         match s with
         | [op] ->
                if starts_with op "u"
                then map_opt (safe_int_of_string (substring_from op 1)) (
                       fun op -> (string_of_char (char_of_int op), None)
                     )
                else name_of_op op
         | _ ->
           let maybeop =
             List.fold_left (fun acc x -> match acc with
                                          | None -> None
                                          | Some acc ->
                                              match x with
                                              | Some (op, _) -> Some (acc ^ op)
                                              | None -> None)
                            (Some "")
                            (List.map name_of_op s)
           in
           map_opt maybeop (fun o -> (o, None))
    else None

//////////////////////////////////////////////////////////////////////////////////////////////
// Printing ASTs, mostly for debugging
//////////////////////////////////////////////////////////////////////////////////////////////

let string_of_fsdoc (comment,keywords) =
    comment ^ (String.concat "," (List.map (fun (k,v) -> k ^ "->" ^ v) keywords))

let string_of_let_qualifier = function
  | NoLetQualifier -> ""
  | Rec -> "rec"
let to_string_l sep f l =
  String.concat sep (List.map f l)
let imp_to_string = function
    | Hash -> "#"
    | _ -> ""
let rec term_to_string (x:term) = match x.tm with
  | Wild -> "_"
  | LexList l -> Util.format1 "%[%s]"
    (match l with
     | [] -> " "
     | hd::tl ->
       tl |> List.fold_left (fun s t -> s ^ "; " ^ term_to_string t) (term_to_string hd))
  | Decreases (t, _) -> Util.format1 "(decreases %s)" (term_to_string t)
  | Requires (t, _) -> Util.format1 "(requires %s)" (term_to_string t)
  | Ensures (t, _) -> Util.format1 "(ensures %s)" (term_to_string t)
  | Labeled (t, l, _) -> Util.format2 "(labeled %s %s)" l (term_to_string t)
  | Const c -> C.const_to_string c
  | Op(s, xs) ->
      Util.format2 "%s(%s)" (string_of_id s) (String.concat ", " (List.map (fun x -> x|> term_to_string) xs))
  | Tvar id
  | Uvar id -> (string_of_id id)
  | Var l
  | Name l -> (string_of_lid l)

  | Projector (rec_lid, field_id) ->
    Util.format2 "%s?.%s" (string_of_lid rec_lid) ((string_of_id field_id))

  | Construct (l, args) ->
    Util.format2 "(%s %s)" (string_of_lid l) (to_string_l " " (fun (a,imp) -> Util.format2 "%s%s" (imp_to_string imp) (term_to_string a)) args)
  | Abs(pats, t) ->
    Util.format2 "(fun %s -> %s)" (to_string_l " " pat_to_string pats) (t|> term_to_string)
  | App(t1, t2, imp) -> Util.format3 "%s %s%s" (t1|> term_to_string) (imp_to_string imp) (t2|> term_to_string)
  | Let (Rec, (a,(p,b))::lbs, body) ->
    Util.format4 "%slet rec %s%s in %s"
        (attrs_opt_to_string a)
        (Util.format2 "%s=%s" (p|> pat_to_string) (b|> term_to_string))
        (to_string_l " "
            (fun (a,(p,b)) ->
                Util.format3 "%sand %s=%s"
                              (attrs_opt_to_string a)
                              (p|> pat_to_string)
                              (b|> term_to_string))
            lbs)
        (body|> term_to_string)
  | Let (q, [(attrs,(pat,tm))], body) ->
    Util.format5 "%slet %s %s = %s in %s"
        (attrs_opt_to_string attrs)
        (string_of_let_qualifier q)
        (pat|> pat_to_string)
        (tm|> term_to_string)
        (body|> term_to_string)
  | Let (_, _, _) ->
    raise_error (Fatal_EmptySurfaceLet, "Internal error: found an invalid surface Let") x.range

  | LetOpen (lid, t) ->
    Util.format2 "let open %s in %s" (string_of_lid lid) (term_to_string t)

  | Seq(t1, t2) ->
    Util.format2 "%s; %s" (t1|> term_to_string) (t2|> term_to_string)

  | Bind (id, t1, t2) ->
    Util.format3 "%s <- %s; %s" (string_of_id id) (term_to_string t1) (term_to_string t2)

  | If(t1, op_opt, ret_opt, t2, t3) ->
    Util.format5 "if%s %s %sthen %s else %s"
      (match op_opt with | Some op -> string_of_id op | None -> "")
      (t1|> term_to_string)
      (match ret_opt with
       | None -> ""
       | Some (as_opt, ret, use_eq) ->
         let s = if use_eq then "returns$" else "returns" in
         Util.format3 "%s%s %s "
           (match as_opt with
            | None -> ""
            | Some as_ident -> Util.format1 " as %s " (string_of_id as_ident))
           s
           (term_to_string ret))
      (t2|> term_to_string)
      (t3|> term_to_string)

  | Match(t, op_opt, ret_opt, branches) -> try_or_match_to_string x t branches op_opt ret_opt
  | TryWith (t, branches) -> try_or_match_to_string x t branches None None

  | Ascribed(t1, t2, None, flag) ->
    let s = if flag then "$:" else "<:" in
    Util.format3 "(%s %s %s)" (t1|> term_to_string) s (t2|> term_to_string)
  | Ascribed(t1, t2, Some tac, flag) ->
    let s = if flag then "$:" else "<:" in
    Util.format4 "(%s %s %s by %s)" (t1|> term_to_string) s (t2|> term_to_string) (tac |> term_to_string)
  | Record(Some e, fields) ->
    Util.format2 "{%s with %s}" (e|> term_to_string) (to_string_l " " (fun (l,e) -> Util.format2 "%s=%s" ((string_of_lid l)) (e|> term_to_string)) fields)
  | Record(None, fields) ->
    Util.format1 "{%s}" (to_string_l " " (fun (l,e) -> Util.format2 "%s=%s" ((string_of_lid l)) (e|> term_to_string)) fields)
  | Project(e,l) ->
    Util.format2 "%s.%s" (e|> term_to_string) ((string_of_lid l))
  | Product([], t) ->
    term_to_string t
  | Product(b::hd::tl, t) ->
    term_to_string (mk_term (Product([b], mk_term (Product(hd::tl, t)) x.range x.level)) x.range x.level)
  | Product([b], t) when (x.level = Type_level) ->
    Util.format2 "%s -> %s" (b|> binder_to_string) (t|> term_to_string)
  | Product([b], t) when (x.level = Kind) ->
    Util.format2 "%s => %s" (b|> binder_to_string) (t|> term_to_string)
  | Sum(binders, t) ->
    (binders@[Inr t]) |>
    List.map (function Inl b -> binder_to_string b
                     | Inr t -> term_to_string t) |>
    String.concat " & "
  | QForall(bs, (_, pats), t) ->
    Util.format3 "forall %s.{:pattern %s} %s"
      (to_string_l " " binder_to_string bs)
      (to_string_l " \/ " (to_string_l "; " term_to_string) pats)
      (t|> term_to_string)
  | QExists(bs, (_, pats), t) ->
    Util.format3 "exists %s.{:pattern %s} %s"
      (to_string_l " " binder_to_string bs)
      (to_string_l " \/ " (to_string_l "; " term_to_string) pats)
      (t|> term_to_string)
  | Refine(b, t) ->
    Util.format2 "%s:{%s}" (b|> binder_to_string) (t|> term_to_string)
  | NamedTyp(x, t) ->
    Util.format2 "%s:%s" (string_of_id x)  (t|> term_to_string)
  | Paren t -> Util.format1 "(%s)" (t|> term_to_string)
  | Product(bs, t) ->
        Util.format2 "Unidentified product: [%s] %s"
          (bs |> List.map binder_to_string |> String.concat ",") (t|> term_to_string)

  | Discrim lid ->
    Util.format1 "%s?" (string_of_lid lid)

  | Attributes ts ->
    Util.format1 "(attributes %s)" (String.concat " " <| List.map term_to_string ts)

  | Antiquote t ->
    Util.format1 "(`#%s)" (term_to_string t)

  | Quote (t, Static) ->
    Util.format1 "(`(%s))" (term_to_string t)

  | Quote (t, Dynamic) ->
    Util.format1 "quote (%s)" (term_to_string t)

  | VQuote t ->
    Util.format1 "`%%%s" (term_to_string t)

  | CalcProof (rel, init, steps) ->
    Util.format3 "calc (%s) { %s %s }" (term_to_string rel)
                                       (term_to_string init)
                                       (String.concat " " <| List.map calc_step_to_string steps)


  | ElimForall(bs, t, vs) ->
    Util.format3 "_elim_ forall %s. %s using %s"
        (binders_to_string " " bs)
        (term_to_string t)
        (String.concat " " (List.map term_to_string vs))

  | ElimExists(bs, p, q, b, e) ->
    Util.format5 "_elim_ exists %s. %s _to_ %s\n\with %s. %s"
        (binders_to_string " " bs)
        (term_to_string p)
        (term_to_string q)
        (binder_to_string b)
        (term_to_string e)

  | ElimImplies(p, q, e) ->
    Util.format3 "_elim_ %s ==> %s with %s"
      (term_to_string p)
      (term_to_string q)
      (term_to_string e)

  | ElimOr(p, q, r, x, e, y, e') ->
     Util.format "_elim_ %s \/ %s _to_ %s\n\with %s. %s\n\and %s.%s"
       [term_to_string p;
        term_to_string q;
        term_to_string r;
        binder_to_string x;
        term_to_string e;
        binder_to_string y;
        term_to_string e']

  | ElimAnd(p, q, r, x, y, e) ->
     Util.format "_elim_ %s /\ %s _to_ %s\n\with %s %s. %s"
       [term_to_string p;
        term_to_string q;
        term_to_string r;
        binder_to_string x;
        binder_to_string y;        
        term_to_string e]

  | IntroForall(xs, p, e) -> 
    Util.format3 "_intro_ forall %s. %s with %s"
      (binders_to_string " " xs)
      (term_to_string p)
      (term_to_string e)
        
  | IntroExists(xs, t, vs, e) ->
    Util.format4 "_intro_ exists %s. %s using %s with %s"
      (binders_to_string " " xs)
      (term_to_string t)
      (String.concat " " (List.map term_to_string vs))
      (term_to_string e)
  
  | IntroImplies(p, q, x, e) ->
    Util.format4 ("_intro_ %s ==> %s with %s. %s")
      (term_to_string p)
      (term_to_string q)
      (binder_to_string x)
      (term_to_string p)
      
  | IntroOr(b, p, q, r) ->
    Util.format4 ("_intro_ %s \/ %s using %s with %s")
      (term_to_string p)
      (term_to_string q)
      (if b then "Left" else "Right")
      (term_to_string r)
      
  | IntroAnd(p, q, e1, e2) ->
    Util.format4 ("_intro_ %s /\ %s with %s and %s")  
      (term_to_string p)
      (term_to_string q)
      (term_to_string e1)
      (term_to_string e2)
      
and binders_to_string sep bs =
    List.map binder_to_string bs |> String.concat sep

and try_or_match_to_string (x:term) scrutinee branches op_opt ret_opt =
  let s =
    match x.tm with
    | Match _ -> "match"
    | TryWith _ -> "try"
    | _ -> failwith "impossible" in
  Util.format5 "%s%s %s %swith %s"
    s
    (match op_opt with | Some op -> string_of_id op | None -> "")
    (scrutinee|> term_to_string)
    (match ret_opt with
     | None -> ""
     | Some (as_opt, ret, use_eq) ->
       let s = if use_eq then "returns$" else "returns" in
       Util.format3 "%s%s %s " s
         (match as_opt with
          | None -> ""
          | Some as_ident -> Util.format1 "as %s " (string_of_id as_ident))
         (term_to_string ret))
    (to_string_l " | " (fun (p,w,e) -> Util.format3 "%s %s -> %s"
      (p |> pat_to_string)
      (match w with | None -> "" | Some e -> Util.format1 "when %s" (term_to_string e))
      (e |> term_to_string)) branches)

and calc_step_to_string (CalcStep (rel, just, next)) =
    Util.format3 "%s{ %s } %s" (term_to_string rel) (term_to_string just) (term_to_string next)

and binder_to_string x =
  let pr x =
    let s = match x.b with
    | Variable i -> (string_of_id i)
    | TVariable i -> Util.format1 "%s:_" ((string_of_id i))
    | TAnnotated(i,t)
    | Annotated(i,t) -> Util.format2 "%s:%s" ((string_of_id i)) (t |> term_to_string)
    | NoName t -> t |> term_to_string in
    Util.format3 "%s%s%s"
      (aqual_to_string x.aqual)
      (attr_list_to_string x.battributes)
      s
  in
  (* Handle typeclass qualifier here *)
  match x.aqual with
  | Some TypeClassArg -> "{| " ^ pr x ^ " |}"
  | _ -> pr x

and aqual_to_string = function
  | Some Equality -> "$"
  | Some Implicit -> "#"
  | None -> ""
  | Some (Meta _)
  | Some TypeClassArg ->
    failwith "aqual_to_strings: meta arg qualifier?"

and attr_list_to_string = function
  | [] -> ""
  | l -> attrs_opt_to_string (Some l)

and pat_to_string x = match x.pat with
  | PatWild (None, attrs) -> attr_list_to_string attrs ^ "_"
  | PatWild (_, attrs) -> "#" ^ (attr_list_to_string attrs) ^ "_" 
  | PatConst c -> C.const_to_string c
  | PatVQuote t -> Util.format1 "`%%%s" (term_to_string t)
  | PatApp(p, ps) -> Util.format2 "(%s %s)" (p |> pat_to_string) (to_string_l " " pat_to_string ps)
  | PatTvar (i, aq, attrs)
  | PatVar (i,  aq, attrs) -> Util.format3 "%s%s%s"
    (aqual_to_string aq)
    (attr_list_to_string attrs)
    (string_of_id i)
  | PatName l -> (string_of_lid l)
  | PatList l -> Util.format1 "[%s]" (to_string_l "; " pat_to_string l)
  | PatTuple (l, false) -> Util.format1 "(%s)" (to_string_l ", " pat_to_string l)
  | PatTuple (l, true) -> Util.format1 "(|%s|)" (to_string_l ", " pat_to_string l)
  | PatRecord l -> Util.format1 "{%s}" (to_string_l "; " (fun (f,e) -> Util.format2 "%s=%s" ((string_of_lid f)) (e |> pat_to_string)) l)
  | PatOr l ->  to_string_l "|\n " pat_to_string l
  | PatOp op ->  Util.format1 "(%s)" (Ident.string_of_id op)
  | PatAscribed(p,(t, None)) -> Util.format2 "(%s:%s)" (p |> pat_to_string) (t |> term_to_string)
  | PatAscribed(p,(t, Some tac)) -> Util.format3 "(%s:%s by %s)" (p |> pat_to_string) (t |> term_to_string) (tac |> term_to_string)

and attrs_opt_to_string = function
  | None -> ""
  | Some attrs -> Util.format1 "[@ %s]" (List.map term_to_string attrs |> String.concat "; ")

let rec head_id_of_pat p = match p.pat with
  | PatName l -> [l]
  | PatVar (i, _, _) -> [FStar.Ident.lid_of_ids [i]]
  | PatApp(p, _) -> head_id_of_pat p
  | PatAscribed(p, _) -> head_id_of_pat p
  | _ -> []

let lids_of_let defs =  defs |> List.collect (fun (p, _) -> head_id_of_pat p)

let id_of_tycon = function
  | TyconAbstract(i, _, _)
  | TyconAbbrev(i, _, _, _)
  | TyconRecord(i, _, _, _, _)
  | TyconVariant(i, _, _, _) -> (string_of_id i)

let decl_to_string (d:decl) = match d.d with
  | TopLevelModule l -> "module " ^ (string_of_lid l)
  | Open l -> "open " ^ (string_of_lid l)
  | Friend l -> "friend " ^ (string_of_lid l)
  | Include l -> "include " ^ (string_of_lid l)
  | ModuleAbbrev (i, l) -> Util.format2 "module %s = %s" (string_of_id i) (string_of_lid l)
  | TopLevelLet(_, pats) -> "let " ^ (lids_of_let pats |> List.map (fun l -> (string_of_lid l)) |> String.concat ", ")
  | Assume(i, _) -> "assume " ^ (string_of_id i)
  | Tycon(_, _, tys) -> "type " ^ (tys |> List.map id_of_tycon |> String.concat ", ")
  | Val(i, _) -> "val " ^ (string_of_id i)
  | Exception(i, _) -> "exception " ^ (string_of_id i)
  | NewEffect(DefineEffect(i, _, _, _))
  | NewEffect(RedefineEffect(i, _, _)) -> "new_effect " ^ (string_of_id i)
  | LayeredEffect(DefineEffect(i, _, _, _))
  | LayeredEffect(RedefineEffect(i, _, _)) -> "layered_effect " ^ (string_of_id i)
  | Polymonadic_bind (l1, l2, l3, _) ->
      Util.format3 "polymonadic_bind (%s, %s) |> %s"
                    (string_of_lid l1) (string_of_lid l2) (string_of_lid l3)
  | Polymonadic_subcomp (l1, l2, _) ->
      Util.format2 "polymonadic_subcomp %s <: %s"
                    (string_of_lid l1) (string_of_lid l2)
  | Splice (ids, t) -> "splice[" ^ (String.concat ";" <| List.map (fun i -> (string_of_id i)) ids) ^ "] (" ^ term_to_string t ^ ")"
  | SubEffect _ -> "sub_effect"
  | Pragma _ -> "pragma"

let modul_to_string (m:modul) = match m with
    | Module (_, decls)
    | Interface (_, decls, _) ->
      decls |> List.map decl_to_string |> String.concat "\n"

let decl_is_val id decl =
    match decl.d with
    | Val (id', _) ->
      Ident.ident_equals id id'
    | _ -> false

let thunk (ens : term) : term =
    let wildpat = mk_pattern (PatWild (None, [])) ens.range in
    mk_term (Abs ([wildpat], ens)) ens.range Expr

let ident_of_binder r b =
  match b.b with
  | Variable i
  | TVariable i
  | Annotated (i, _)
  | TAnnotated (i, _) -> i
  | NoName _ ->
    raise_error (Fatal_MissingQuantifierBinder,
                 "Wildcard binders in quantifiers are not allowed") r

let idents_of_binders bs r =
    bs |> List.map (ident_of_binder r)

let decl_syntax_is_delimited (d:decl) = 
  match d.d with
  | Pragma _
  | NewEffect (DefineEffect _)
  | LayeredEffect (DefineEffect _)
  | SubEffect {braced=true} -> true
  | Tycon(_, b, _) -> b
  | _ -> false

