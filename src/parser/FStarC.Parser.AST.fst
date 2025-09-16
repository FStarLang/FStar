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
module FStarC.Parser.AST

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Range
open FStarC.Const
open FStarC.Errors
open FStarC.Ident
open FStarC.Class.Show
open FStarC.Class.Tagged

(* All of these should be in FStar.String. *)
open FStarC.Util {
  starts_with,
  substring,
  substring_from,
  string_of_char,
  char_of_int,
  safe_int_of_string,
  split
}

module C = FStarC.Parser.Const


instance tagged_term : tagged term = {
  tag_of = (fun t -> match t.tm with
  | Wild             -> "Wild"
  | Const          _ -> "Const"
  | Op             _ -> "Op"
  | Uvar           _ -> "Uvar"
  | Var            _ -> "Var"
  | Name           _ -> "Name"
  | Projector      _ -> "Projector"
  | Construct      _ -> "Construct"
  | Abs            _ -> "Abs"
  | Function       _ -> "Function"
  | App            _ -> "App"
  | Let            _ -> "Let"
  | LetOperator    _ -> "LetOperator"
  | LetOpen        _ -> "LetOpen"
  | LetOpenRecord  _ -> "LetOpenRecord"
  | Seq            _ -> "Seq"
  | Bind           _ -> "Bind"
  | If             _ -> "If"
  | Match          _ -> "Match"
  | TryWith        _ -> "TryWith"
  | Ascribed       _ -> "Ascribed"
  | Record         _ -> "Record"
  | Project        _ -> "Project"
  | Product        _ -> "Product"
  | Sum            _ -> "Sum"
  | QForall        _ -> "QForall"
  | QExists        _ -> "QExists"
  | QuantOp        _ -> "QuantOp"
  | Refine         _ -> "Refine"
  | NamedTyp       _ -> "NamedTyp"
  | Paren          _ -> "Paren"
  | Requires       _ -> "Requires"
  | Ensures        _ -> "Ensures"
  | LexList        _ -> "LexList"
  | WFOrder        _ -> "WFOrder"
  | Decreases      _ -> "Decreases"
  | Labeled        _ -> "Labeled"
  | Discrim        _ -> "Discrim"
  | Attributes     _ -> "Attributes"
  | Antiquote      _ -> "Antiquote"
  | Quote          _ -> "Quote"
  | VQuote         _ -> "VQuote"
  | CalcProof      _ -> "CalcProof"
  | IntroForall    _ -> "IntroForall"
  | IntroExists    _ -> "IntroExists"
  | IntroImplies   _ -> "IntroImplies"
  | IntroOr        _ -> "IntroOr"
  | IntroAnd       _ -> "IntroAnd"
  | ElimForall     _ -> "ElimForall"
  | ElimExists     _ -> "ElimExists"
  | ElimImplies    _ -> "ElimImplies"
  | ElimOr         _ -> "ElimOr"
  | ElimAnd        _ -> "ElimAnd"
  | ListLiteral    _ -> "ListLiteral"
  | SeqLiteral     _ -> "SeqLiteral"
  );
}

instance hasRange_term : hasRange term = {
  pos = (fun t -> t.range);
  setPos = (fun r t -> { t with range = r });
}

instance hasRange_pattern : hasRange pattern = {
  pos = (fun p -> p.prange);
  setPos = (fun r p -> { p with prange = r });
}

instance hasRange_binder : hasRange binder = {
  pos = (fun b -> b.brange);
  setPos = (fun r b -> { b with brange = r });
}

instance hasRange_decl : hasRange decl = {
  pos = (fun d -> d.drange);
  setPos = (fun r d -> { d with drange = r });
}

let lid_of_modul (m:modul) : lid =
  match m with
  | Module {mname}
  | Interface {mname} -> mname

let check_id id =
    let first_char = String.substring (string_of_id id) 0 1 in
    if not (String.lowercase first_char = first_char) then
      raise_error id Fatal_InvalidIdentifier
        (Format.fmt1 "Invalid identifer '%s'; expected a symbol that begins with a lower-case character" (show id))

let at_most_one s (r:range) l = match l with
  | [ x ] -> Some x
  | [] -> None
  | _ ->
    raise_error r Fatal_MoreThanOneDeclaration
      (Format.fmt1 "At most one %s is allowed on declarations" s)

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
  mk_term (Function (branches, r1)) r2 Expr

let un_function p tm = match p.pat, tm.tm with
    | PatVar _, Abs(pats, body) -> Some (mk_pattern (PatApp(p, pats)) p.prange, body)
    | _ -> None

let mkApp t args r = match args with
  | [] -> t
  | _ -> match t.tm with
      | Name s -> mk_term (Construct(s, args)) r Un
      | _ -> List.fold_left (fun t (a,imp) -> mk_term (App(t, a, imp)) r Un) t args

let consPat r hd tl = PatApp(mk_pattern (PatName C.cons_lid) r, [hd;tl])
let consTerm r hd tl = mk_term (Construct(C.cons_lid, [(hd, Nothing);(tl, Nothing)])) r Expr

let mkListLit r elts =
  mk_term (ListLiteral elts) r Expr

let mkSeqLit r elts =
  mk_term (SeqLiteral elts) r Expr

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
        then
          let _ = Errors.log_issue r Errors.Warning_Filtered "Focusing on only some cases" in
          let focussed = List.filter fst branches |> List.map snd in
                 focussed@[mkWildAdmitMagic r]
        else branches |> List.map snd

let focusLetBindings lbs r =
    let should_filter = Util.for_some fst lbs in
        if should_filter
        then 
          let _ = Errors.log_issue r Errors.Warning_Filtered "Focusing on only some cases in this (mutually) recursive definition" in
          List.map (fun (f, lb) ->
              if f then lb
              else (fst lb, mkAdmitMagic r)) lbs
        else lbs |> List.map snd

let focusAttrLetBindings lbs r =
    let should_filter = Util.for_some (fun (attr, (focus, _)) -> focus) lbs in
    if should_filter
    then
      let _ = Errors.log_issue r Errors.Warning_Filtered "Focusing on only some cases in this (mutually) recursive definition" in
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

let rec extract_named_refinement (remove_parens:bool) (t1:term) : option (ident & term & option typ) =
  match t1.tm with
  | NamedTyp(x, t) -> Some (x, t, None)
  | Refine({b=Annotated(x, t)}, t') -> Some (x, t, Some t')
  | Paren t when remove_parens -> extract_named_refinement remove_parens t
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
let rec as_mlist (cur: (lid & decl & bool) & list decl) (ds:list decl) : modul =
    let ((m_name, m_decl, no_prelude), cur) = cur in
    match ds with
    | [] -> Module { no_prelude; mname = m_name; decls = m_decl :: List.rev cur }
    | d :: ds ->
        begin match d.d with
        | TopLevelModule m' ->
            raise_error d Fatal_UnexpectedModuleDeclaration "Unexpected module declaration"
        | _ ->
            as_mlist ((m_name, m_decl, no_prelude), d::cur) ds
        end

let as_frag (ds:list decl) : inputFragment =
  let d, ds = match ds with
    | d :: ds -> d, ds
    | [] -> raise Empty_frag
  in
  match d.d with
  | TopLevelModule m ->
      let no_prelude =
        Options.no_prelude () ||
        d.attrs |> List.existsb (function t ->
          match t.tm with
          | Const (FStarC.Const.Const_string ("no_prelude", _)) -> true
          | _ -> false)
      in
      let m = as_mlist ((m,d, no_prelude), []) ds in
      Inl m
  | _ ->
      let ds = d::ds in
      List.iter (function
        | {d=TopLevelModule _; drange=r} -> raise_error r Fatal_UnexpectedModuleDeclaration "Unexpected module declaration"
        | _ -> ()
      ) ds;
      Inr ds

// TODO: Move to something like FStarC.Util
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
      | c -> "u" ^ show (Util.int_of_char c)
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
    | _ -> // handle let operators (i.e. [let?] or [and*], and [exists*] and [forall*])
          let prefix, s = 
            if starts_with s "let" || starts_with s "and"
            then substring s 0 3 ^ "_", substring_from s 3
            else if starts_with s "exists" || starts_with s "forall"
            then substring s 0 6 ^ "_", substring_from s 6
            else "", s in
          "op_" ^ prefix ^ String.concat "_" (List.map name_of_char (String.list_of_string s))

let compile_op' s r =
  compile_op (-1) s r

let string_to_op s =
  let name_of_op s =
    match s with
    | "Amp" ->  Some ("&", None)
    | "At" -> Some ("@", None)
    | "Plus" -> Some ("+", Some 2)
    | "Minus" -> Some ("-", None)
    | "Subtraction" -> Some ("-", Some 2)
    | "Tilde" -> Some ("~", None)
    | "Slash" -> Some ("/", Some 2)
    | "Backslash" -> Some ("\\", None)
    | "Less" -> Some ("<", Some 2)
    | "Equals" -> Some ("=", None)
    | "Greater" -> Some (">", Some 2)
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
    | "let" | "and" | "forall" | "exists" -> Some (s, None)
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
    then let frags = split (substring_from s (String.length "op_")) "_" in
         match frags with
         | [op] ->
                if starts_with op "u"
                then safe_int_of_string (substring_from op 1) |> Option.map (
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
                            (List.map name_of_op frags)
           in
           Option.map (fun o -> (o, None)) maybeop
    else None

//////////////////////////////////////////////////////////////////////////////////////////////
// Printing ASTs, mostly for debugging
//////////////////////////////////////////////////////////////////////////////////////////////

let string_of_fsdoc (comment,keywords) =
    comment ^ (String.concat "," (List.map (fun (k,v) -> k ^ "->" ^ v) keywords))

let string_of_let_qualifier = function
  | NoLetQualifier -> ""
  | Rec -> "rec"

let string_of_local_let_qualifier = function
  | LocalNoLetQualifier -> ""
  | LocalRec -> "rec"
  | LocalUnfold -> "unfold"
  
let to_string_l sep f l =
  String.concat sep (List.map f l)
let imp_to_string = function
    | Hash -> "#"
    | _ -> ""
let rec term_to_string (x:term) = match x.tm with
  | Wild -> "_"
  | LexList l -> Format.fmt1 "%[%s]"
    (match l with
     | [] -> " "
     | hd::tl ->
       tl |> List.fold_left (fun s t -> s ^ "; " ^ term_to_string t) (term_to_string hd))
  | WFOrder (rel, e) ->
    Format.fmt2 "{:well-founded %s %s}" (term_to_string rel) (term_to_string e)
  | Decreases t -> Format.fmt1 "(decreases %s)" (term_to_string t)
  | Requires t -> Format.fmt1 "(requires %s)" (term_to_string t)
  | Ensures t -> Format.fmt1 "(ensures %s)" (term_to_string t)
  | Labeled (t, l, _) -> Format.fmt2 "(labeled %s %s)" l (term_to_string t)
  | Const c -> C.const_to_string c
  | Op(s, xs) ->
      Format.fmt2 "%s(%s)" (string_of_id s) (String.concat ", " (List.map (fun x -> x|> term_to_string) xs))
  | Uvar id -> (string_of_id id)
  | Var l
  | Name l -> (string_of_lid l)

  | Projector (rec_lid, field_id) ->
    Format.fmt2 "%s?.%s" (string_of_lid rec_lid) ((string_of_id field_id))

  | Construct (l, args) ->
    Format.fmt2 "(%s %s)" (string_of_lid l) (to_string_l " " (fun (a,imp) -> Format.fmt2 "%s%s" (imp_to_string imp) (term_to_string a)) args)
  | Function (branches, r) ->
    Format.fmt1 "(function %s)"
      (to_string_l " | " (fun (p,w,e) -> Format.fmt2 "%s -> %s"
        (p |> pat_to_string)
        (e |> term_to_string)) branches)

  | Abs(pats, t) ->
    Format.fmt2 "(fun %s -> %s)" (to_string_l " " pat_to_string pats) (t|> term_to_string)
  | App(t1, t2, imp) -> Format.fmt3 "%s %s%s" (t1|> term_to_string) (imp_to_string imp) (t2|> term_to_string)
  | Let (LocalRec, (a,(p,b))::lbs, body) ->
    Format.fmt4 "%slet rec %s%s in %s"
        (attrs_opt_to_string a)
        (Format.fmt2 "%s=%s" (p|> pat_to_string) (b|> term_to_string))
        (to_string_l " "
            (fun (a,(p,b)) ->
                Format.fmt3 "%sand %s=%s"
                              (attrs_opt_to_string a)
                              (p|> pat_to_string)
                              (b|> term_to_string))
            lbs)
        (body|> term_to_string)
  | Let (q, [(attrs,(pat,tm))], body) ->
    Format.fmt5 "%slet %s %s = %s in %s"
        (attrs_opt_to_string attrs)
        (string_of_local_let_qualifier q)
        (pat|> pat_to_string)
        (tm|> term_to_string)
        (body|> term_to_string)
  | Let (_, _, _) ->
    raise_error x Fatal_EmptySurfaceLet "Internal error: found an invalid surface Let"

  | LetOperator ((i,p,b)::lbs, body) ->
    Format.fmt4 "let%s rec %s%s in %s"
        (show i)
        (Format.fmt2 "%s=%s" (p|> pat_to_string) (b|> term_to_string))
        (to_string_l " "
            (fun (i,p,b) ->
                Format.fmt3 "and%s %s=%s"
                              (show i)
                              (p|> pat_to_string)
                              (b|> term_to_string))
            lbs)
        (body|> term_to_string)

  | LetOpen (lid, t) ->
    Format.fmt2 "let open %s in %s" (string_of_lid lid) (term_to_string t)

  | LetOpenRecord (e, t, body) ->
    Format.fmt3 "let open %s <: %s in %s\n" (e|> term_to_string) (t|> term_to_string) (body|> term_to_string)

  | Seq(t1, t2) ->
    Format.fmt2 "%s; %s" (t1|> term_to_string) (t2|> term_to_string)

  | Bind (id, t1, t2) ->
    Format.fmt3 "%s <- %s; %s" (string_of_id id) (term_to_string t1) (term_to_string t2)

  | If(t1, op_opt, ret_opt, t2, t3) ->
    Format.fmt5 "if%s %s %sthen %s else %s"
      (match op_opt with | Some op -> string_of_id op | None -> "")
      (t1|> term_to_string)
      (match ret_opt with
       | None -> ""
       | Some (as_opt, ret, use_eq) ->
         let s = if use_eq then "returns$" else "returns" in
         Format.fmt3 "%s%s %s "
           (match as_opt with
            | None -> ""
            | Some as_ident -> Format.fmt1 " as %s " (string_of_id as_ident))
           s
           (term_to_string ret))
      (t2|> term_to_string)
      (t3|> term_to_string)

  | Match(t, op_opt, ret_opt, branches) -> try_or_match_to_string x t branches op_opt ret_opt
  | TryWith (t, branches) -> try_or_match_to_string x t branches None None

  | Ascribed(t1, t2, None, flag) ->
    let s = if flag then "$:" else "<:" in
    Format.fmt3 "(%s %s %s)" (t1|> term_to_string) s (t2|> term_to_string)
  | Ascribed(t1, t2, Some tac, flag) ->
    let s = if flag then "$:" else "<:" in
    Format.fmt4 "(%s %s %s by %s)" (t1|> term_to_string) s (t2|> term_to_string) (tac |> term_to_string)
  | Record(Some e, fields) ->
    Format.fmt2 "{%s with %s}" (e|> term_to_string) (to_string_l " " (fun (l,e) -> Format.fmt2 "%s=%s" ((string_of_lid l)) (e|> term_to_string)) fields)
  | Record(None, fields) ->
    Format.fmt1 "{%s}" (to_string_l " " (fun (l,e) -> Format.fmt2 "%s=%s" ((string_of_lid l)) (e|> term_to_string)) fields)
  | Project(e,l) ->
    Format.fmt2 "%s.%s" (e|> term_to_string) ((string_of_lid l))
  | Product([], t) ->
    term_to_string t
  | Product(b::hd::tl, t) ->
    term_to_string (mk_term (Product([b], mk_term (Product(hd::tl, t)) x.range x.level)) x.range x.level)
  | Product([b], t) when (x.level = Type_level) ->
    Format.fmt2 "%s -> %s" (b|> binder_to_string) (t|> term_to_string)
  | Product([b], t) when (x.level = Kind) ->
    Format.fmt2 "%s => %s" (b|> binder_to_string) (t|> term_to_string)
  | Sum(binders, t) ->
    (binders@[Inr t]) |>
    List.map (function Inl b -> binder_to_string b
                     | Inr t -> term_to_string t) |>
    String.concat " & "
  | QForall(bs, (_, pats), t) ->
    Format.fmt3 "forall %s.{:pattern %s} %s"
      (to_string_l " " binder_to_string bs)
      (to_string_l " \/ " (to_string_l "; " term_to_string) pats)
      (t|> term_to_string)
  | QExists(bs, (_, pats), t) ->
    Format.fmt3 "exists %s.{:pattern %s} %s"
      (to_string_l " " binder_to_string bs)
      (to_string_l " \/ " (to_string_l "; " term_to_string) pats)
      (t|> term_to_string)
  | QuantOp(i, bs, (_, []), t) ->
    Format.fmt3 "%s %s. %s"
      (string_of_id i)
      (to_string_l " " binder_to_string bs)
      (t|> term_to_string)
  | QuantOp(i, bs, (_, pats), t) ->
    Format.fmt4 "%s %s.{:pattern %s} %s"
      (string_of_id i)
      (to_string_l " " binder_to_string bs)
      (to_string_l " \/ " (to_string_l "; " term_to_string) pats)
      (t|> term_to_string)
  | Refine(b, t) ->
    Format.fmt2 "%s:{%s}" (b|> binder_to_string) (t|> term_to_string)
  | NamedTyp(x, t) ->
    Format.fmt2 "%s:%s" (string_of_id x)  (t|> term_to_string)
  | Paren t -> Format.fmt1 "(%s)" (t|> term_to_string)
  | Product(bs, t) ->
        Format.fmt2 "Unidentified product: [%s] %s"
          (bs |> List.map binder_to_string |> String.concat ",") (t|> term_to_string)

  | Discrim lid ->
    Format.fmt1 "%s?" (string_of_lid lid)

  | Attributes ts ->
    Format.fmt1 "(attributes %s)" (String.concat " " <| List.map term_to_string ts)

  | Antiquote t ->
    Format.fmt1 "(`#%s)" (term_to_string t)

  | Quote (t, Static) ->
    Format.fmt1 "(`(%s))" (term_to_string t)

  | Quote (t, Dynamic) ->
    Format.fmt1 "quote (%s)" (term_to_string t)

  | VQuote t ->
    Format.fmt1 "`%%%s" (term_to_string t)

  | CalcProof (rel, init, steps) ->
    Format.fmt3 "calc (%s) { %s %s }" (term_to_string rel)
                                       (term_to_string init)
                                       (String.concat " " <| List.map calc_step_to_string steps)


  | ElimForall(bs, t, vs) ->
    Format.fmt3 "_elim_ forall %s. %s using %s"
        (binders_to_string " " bs)
        (term_to_string t)
        (String.concat " " (List.map term_to_string vs))

  | ElimExists(bs, p, q, b, e) ->
    Format.fmt5 "_elim_ exists %s. %s _to_ %s\n\with %s. %s"
        (binders_to_string " " bs)
        (term_to_string p)
        (term_to_string q)
        (binder_to_string b)
        (term_to_string e)

  | ElimImplies(p, q, e) ->
    Format.fmt3 "_elim_ %s ==> %s with %s"
      (term_to_string p)
      (term_to_string q)
      (term_to_string e)

  | ElimOr(p, q, r, x, e, y, e') ->
     Format.fmt "_elim_ %s \/ %s _to_ %s\n\with %s. %s\n\and %s.%s"
       [term_to_string p;
        term_to_string q;
        term_to_string r;
        binder_to_string x;
        term_to_string e;
        binder_to_string y;
        term_to_string e']

  | ElimAnd(p, q, r, x, y, e) ->
     Format.fmt "_elim_ %s /\ %s _to_ %s\n\with %s %s. %s"
       [term_to_string p;
        term_to_string q;
        term_to_string r;
        binder_to_string x;
        binder_to_string y;        
        term_to_string e]

  | IntroForall(xs, p, e) -> 
    Format.fmt3 "_intro_ forall %s. %s with %s"
      (binders_to_string " " xs)
      (term_to_string p)
      (term_to_string e)
        
  | IntroExists(xs, t, vs, e) ->
    Format.fmt4 "_intro_ exists %s. %s using %s with %s"
      (binders_to_string " " xs)
      (term_to_string t)
      (String.concat " " (List.map term_to_string vs))
      (term_to_string e)
  
  | IntroImplies(p, q, x, e) ->
    Format.fmt4 ("_intro_ %s ==> %s with %s. %s")
      (term_to_string p)
      (term_to_string q)
      (binder_to_string x)
      (term_to_string p)
      
  | IntroOr(b, p, q, r) ->
    Format.fmt4 ("_intro_ %s \/ %s using %s with %s")
      (term_to_string p)
      (term_to_string q)
      (if b then "Left" else "Right")
      (term_to_string r)
      
  | IntroAnd(p, q, e1, e2) ->
    Format.fmt4 ("_intro_ %s /\ %s with %s and %s")  
      (term_to_string p)
      (term_to_string q)
      (term_to_string e1)
      (term_to_string e2)

  | ListLiteral ts ->
    Format.fmt1 "[%s]" (to_string_l "; " term_to_string ts)

  | SeqLiteral ts ->
    Format.fmt1 "seq![%s]" (to_string_l "; " term_to_string ts)
  | _ -> failwith ("AST.term_to_string missing case: " ^ tag_of x)

and binders_to_string sep bs =
    List.map binder_to_string bs |> String.concat sep

and try_or_match_to_string (x:term) scrutinee branches op_opt ret_opt =
  let s =
    match x.tm with
    | Match _ -> "match"
    | TryWith _ -> "try"
    | _ -> failwith "impossible" in
  Format.fmt5 "%s%s %s %swith %s"
    s
    (match op_opt with | Some op -> string_of_id op | None -> "")
    (scrutinee|> term_to_string)
    (match ret_opt with
     | None -> ""
     | Some (as_opt, ret, use_eq) ->
       let s = if use_eq then "returns$" else "returns" in
       Format.fmt3 "%s%s %s " s
         (match as_opt with
          | None -> ""
          | Some as_ident -> Format.fmt1 "as %s " (string_of_id as_ident))
         (term_to_string ret))
    (to_string_l " | " (fun (p,w,e) -> Format.fmt3 "%s %s -> %s"
      (p |> pat_to_string)
      (match w with | None -> "" | Some e -> Format.fmt1 "when %s" (term_to_string e))
      (e |> term_to_string)) branches)

and calc_step_to_string (CalcStep (rel, just, next)) =
    Format.fmt3 "%s{ %s } %s" (term_to_string rel) (term_to_string just) (term_to_string next)

and binder_to_string x =
  let pr x =
    let s = match x.b with
    | Variable i -> (string_of_id i)
    | Annotated(i,t) -> Format.fmt2 "%s:%s" ((string_of_id i)) (t |> term_to_string)
    | NoName t -> t |> term_to_string in
    Format.fmt3 "%s%s%s"
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
  | Some TypeClassArg -> "{||}"

and attr_list_to_string = function
  | [] -> ""
  | l -> attrs_opt_to_string (Some l)

and pat_to_string x = match x.pat with
  | PatWild (None, attrs) -> attr_list_to_string attrs ^ "_"
  | PatWild (_, attrs) -> "#" ^ (attr_list_to_string attrs) ^ "_" 
  | PatConst c -> C.const_to_string c
  | PatVQuote t -> Format.fmt1 "`%%%s" (term_to_string t)
  | PatApp(p, ps) -> Format.fmt2 "(%s %s)" (p |> pat_to_string) (to_string_l " " pat_to_string ps)
  | PatVar (i,  aq, attrs) -> Format.fmt3 "%s%s%s"
    (aqual_to_string aq)
    (attr_list_to_string attrs)
    (string_of_id i)
  | PatName l -> (string_of_lid l)
  | PatList l -> Format.fmt1 "[%s]" (to_string_l "; " pat_to_string l)
  | PatTuple (l, false) -> Format.fmt1 "(%s)" (to_string_l ", " pat_to_string l)
  | PatTuple (l, true) -> Format.fmt1 "(|%s|)" (to_string_l ", " pat_to_string l)
  | PatRecord l -> Format.fmt1 "{%s}" (to_string_l "; " (fun (f,e) -> Format.fmt2 "%s=%s" ((string_of_lid f)) (e |> pat_to_string)) l)
  | PatOr l ->  to_string_l "|\n " pat_to_string l
  | PatOp op ->  Format.fmt1 "(%s)" (Ident.string_of_id op)
  | PatAscribed(p,(t, None)) -> Format.fmt2 "(%s:%s)" (p |> pat_to_string) (t |> term_to_string)
  | PatAscribed(p,(t, Some tac)) -> Format.fmt3 "(%s:%s by %s)" (p |> pat_to_string) (t |> term_to_string) (tac |> term_to_string)
  | PatRest -> ".."

and attrs_opt_to_string = function
  | None -> ""
  | Some attrs -> Format.fmt1 "[@ %s]" (List.map term_to_string attrs |> String.concat "; ")

let rec head_id_of_pat p = match p.pat with
  | PatName l -> [l]
  | PatVar (i, _, _) -> [FStarC.Ident.lid_of_ids [i]]
  | PatApp(p, _) -> head_id_of_pat p
  | PatAscribed(p, _) -> head_id_of_pat p
  | _ -> []

let lids_of_let defs =  defs |> List.collect (fun (p, _) -> head_id_of_pat p)

let id_of_tycon = function
  | TyconAbstract(i, _, _)
  | TyconAbbrev(i, _, _, _)
  | TyconRecord(i, _, _, _, _)
  | TyconVariant(i, _, _, _) -> (string_of_id i)

let string_of_pragma = function
  | ShowOptions  ->   "show-options"
  | SetOptions s ->   Format.fmt1 "set-options \"%s\""   s
  | ResetOptions s -> Format.fmt1 "reset-options \"%s\"" (Option.dflt "" s)
  | PushOptions s ->  Format.fmt1 "push-options \"%s\""  (Option.dflt "" s)
  | PopOptions -> "pop-options"
  | RestartSolver -> "restart-solver"
  | PrintEffectsGraph -> "print-effects-graph"
  | Check t -> "check " ^ term_to_string t

let restriction_to_string: FStarC.Syntax.Syntax.restriction -> string =
  let open FStarC.Syntax.Syntax in
  function | Unrestricted -> ""
           | AllowList allow_list  -> " {" ^ String.concat ", " (List.map (fun (id, renamed) -> string_of_id id ^ Option.dflt "" (Option.map (fun renamed -> " as " ^ string_of_id renamed) renamed)) allow_list)  ^ "}"

let decl_to_string (d:decl) = match d.d with
  | TopLevelModule l -> "module " ^ (string_of_lid l)
  | Open (l, r) -> "open " ^ string_of_lid l ^ restriction_to_string r
  | Friend l -> "friend " ^ (string_of_lid l)
  | Include (l, r) -> "include " ^ string_of_lid l ^ restriction_to_string r
  | ModuleAbbrev (i, l) -> Format.fmt2 "module %s = %s" (string_of_id i) (string_of_lid l)
  | TopLevelLet(_, pats) -> "let " ^ (pats |> List.map (fun (p, t) -> pat_to_string p ^ " = " ^ term_to_string t) |> String.concat ", ")
  | Assume(i, _) -> "assume " ^ (string_of_id i)
  | Tycon(_, _, tys) -> "type " ^ (tys |> List.map id_of_tycon |> String.concat ", ")
  | Val(i, _) -> "val " ^ (string_of_id i)
  | Exception(i, _) -> "exception " ^ (string_of_id i)
  | NewEffect(DefineEffect(i, _, _, _))
  | NewEffect(RedefineEffect(i, _, _)) -> "new_effect " ^ (string_of_id i)
  | LayeredEffect(DefineEffect(i, _, _, _))
  | LayeredEffect(RedefineEffect(i, _, _)) -> "layered_effect " ^ (string_of_id i)
  | Polymonadic_bind (l1, l2, l3, _) ->
      Format.fmt3 "polymonadic_bind (%s, %s) |> %s"
                    (string_of_lid l1) (string_of_lid l2) (string_of_lid l3)
  | Polymonadic_subcomp (l1, l2, _) ->
      Format.fmt2 "polymonadic_subcomp %s <: %s"
                    (string_of_lid l1) (string_of_lid l2)
  | Splice (is_typed, ids, t) ->
    "splice" ^ (if is_typed then "_t" else "")
             ^ "["
             ^ (String.concat ";" <| List.map (fun i -> (string_of_id i)) ids) ^ "] (" ^ term_to_string t ^ ")"
  | SubEffect _ -> "sub_effect"
  | Pragma p -> "pragma #" ^ string_of_pragma p
  | DeclSyntaxExtension (id, content, _, _) -> 
    "```" ^ id ^ "\n" ^ content ^ "\n```"
  | DeclToBeDesugared tbs ->
    "(to_be_desugared: " ^ tbs.to_string tbs.blob^ ")"
  | UseLangDecls str ->
    Format.fmt1 "#lang-%s" str
  | Unparseable ->
    "unparseable"

let modul_to_string (m:modul) =
  match m with
  | Module {decls}
  | Interface {decls} ->
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
  | Annotated (i, _) -> i
  | NoName _ ->
    raise_error r Fatal_MissingQuantifierBinder "Wildcard binders in quantifiers are not allowed"

let idents_of_binders bs r = bs |> List.map (ident_of_binder r)

instance showable_decl : showable decl = { show = decl_to_string; }
instance showable_term : showable term = { show = term_to_string; }
instance showable_pattern : showable pattern = { show = pat_to_string; }
instance showable_binder : showable binder = { show = binder_to_string; }
instance showable_modul : showable modul = { show = modul_to_string; }
instance showable_pragma : showable pragma = { show = string_of_pragma; }

let add_decorations d decorations =
  let decorations = 
    let attrs, quals = List.partition DeclAttributes? decorations in
    let attrs =
      match attrs, d.attrs with
      | attrs, [] -> attrs
      | [DeclAttributes a], attrs -> [DeclAttributes (a @ attrs)]
      | [], attrs -> [DeclAttributes attrs]
      | _ ->
        raise_error d Fatal_MoreThanOneDeclaration
          (Format.fmt2
            "At most one attribute set is allowed on declarations\n got %s;\n and %s"
            (String.concat ", " (List.map (function DeclAttributes a -> show a | _ -> "") attrs))
            (String.concat ", " (List.map show d.attrs)))
    in
    List.map Qualifier d.quals @
    quals @
    attrs
  in
  let attributes_ = at_most_one "attribute set" d.drange (
    List.choose (function DeclAttributes a -> Some a | _ -> None) decorations
  ) in
  let attributes_ = Option.dflt [] attributes_ in
  let qualifiers = List.choose (function Qualifier q -> Some q | _ -> None) decorations in
  { d with quals=qualifiers; attrs=attributes_ }

let mk_decl d r decorations =
  let d = { d=d; drange=r; quals=[]; attrs=[]; interleaved=false } in
  add_decorations d decorations

let as_interface (m:modul) : modul =
    match m with
    | Module {no_prelude; mname; decls} -> Interface { no_prelude; mname; decls; admitted = true }
    | i -> i

let inline_let_attribute 
: term
= mk_term (Var FStarC.Parser.Const.inline_let_attr) Range.dummyRange Expr

let inline_let_vc_attribute 
: term
= mk_term (Var FStarC.Parser.Const.inline_let_vc_attr) Range.dummyRange Expr
