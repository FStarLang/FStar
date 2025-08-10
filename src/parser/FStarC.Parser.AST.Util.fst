(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: N. Swamy and Copilot
*)
module FStarC.Parser.AST.Util
open FStarC.Effect
open FStarC.List
open FStarC.Errors
open FStarC.Range
open FStarC.Ident
open FStarC
open FStarC.Const
open FStarC.Parser.AST

let concat_map = List.collect
let opt_map f (x:option 'a) = match x with | None -> [] | Some x -> f x

let rec lidents_of_term (t:term)
: list FStarC.Ident.lident
= lidents_of_term' t.tm
and lidents_of_term' (t:term')
: list FStarC.Ident.lident
= match t with
  | Wild -> []
  | Const _ -> []
  | Op (s, ts) -> concat_map lidents_of_term ts
  | Uvar _ -> []
  | Var lid -> [lid]
  | Name lid -> [lid]
  | Projector (lid, _) -> [lid]
  | Construct (lid, ts) -> lid :: concat_map (fun (t, _) -> lidents_of_term t) ts
  | Function (brs, _) -> concat_map lidents_of_branch brs
  | Abs (ps, t) -> concat_map lidents_of_pattern ps @ lidents_of_term t
  | App (t1, t2, _) -> lidents_of_term t1 @ lidents_of_term t2
  | Let (_, lbs, t) -> concat_map (fun (_, (p, t)) -> lidents_of_pattern p @ lidents_of_term t) lbs @ lidents_of_term t
  | LetOperator (lbs, t) -> concat_map (fun (_, p, t) -> lidents_of_pattern p @ lidents_of_term t) lbs @ lidents_of_term t
  | LetOpen (lid, t) -> lid :: lidents_of_term t
  | LetOpenRecord (t1, t2, t3) -> lidents_of_term t1 @ lidents_of_term t2 @ lidents_of_term t3
  | Seq (t1, t2) -> lidents_of_term t1 @ lidents_of_term t2
  | Bind (_, t1, t2) -> lidents_of_term t1 @ lidents_of_term t2
  | If (t1, _, _, t2, t3) -> lidents_of_term t1 @ lidents_of_term t2 @ lidents_of_term t3
  | Match (t, _, _, bs) -> lidents_of_term t @ concat_map lidents_of_branch bs
  | TryWith (t, bs) -> lidents_of_term t @ concat_map lidents_of_branch bs
  | Ascribed (t1, t2, _, _) -> lidents_of_term t1 @ lidents_of_term t2
  | Record (t, ts) -> concat_map (fun (_, t) -> lidents_of_term t) ts @ opt_map lidents_of_term t
  | Project (t, _) -> lidents_of_term t
  | Product (ts, t) -> concat_map lidents_of_binder ts @ lidents_of_term t
  | Sum (ts, t) -> concat_map (function Inl b -> lidents_of_binder b | Inr t -> lidents_of_term t) ts @ lidents_of_term t
  | QForall (bs, _pats, t) -> lidents_of_term t
  | QExists (bs, _pats, t) -> lidents_of_term t
  | QuantOp (i, bs, pats, t) -> lidents_of_term t
  | Refine (b, t) -> lidents_of_term t
  | NamedTyp (i, t) -> lidents_of_term t
  | Paren t -> lidents_of_term t
  | Requires t -> lidents_of_term t
  | Ensures t -> lidents_of_term t
  | LexList ts -> concat_map lidents_of_term ts
  | WFOrder (t1, t2) -> lidents_of_term t1 @ lidents_of_term t2
  | Decreases t -> lidents_of_term t
  | Labeled (t, _, _) -> lidents_of_term t
  | Discrim lid -> [lid]
  | Attributes ts -> concat_map lidents_of_term ts
  | Antiquote t -> lidents_of_term t
  | Quote (t, _) -> lidents_of_term t
  | VQuote t -> lidents_of_term t
  | CalcProof (t1, t2, ts) -> lidents_of_term t1 @ lidents_of_term t2 @ concat_map lidents_of_calc_step ts
  | IntroForall (bs, t1, t2) -> lidents_of_term t1 @ lidents_of_term t2
  | IntroExists (bs, t1, ts, t2) -> lidents_of_term t1 @ concat_map lidents_of_term ts @ lidents_of_term t2
  | IntroImplies (t1, t2, b, t3) -> lidents_of_term t1 @ lidents_of_term t2 @ lidents_of_term t3
  | IntroOr (b, t1, t2, t3) -> lidents_of_term t1 @ lidents_of_term t2 @ lidents_of_term t3
  | IntroAnd (t1, t2, t3, t4) -> lidents_of_term t1 @ lidents_of_term t2 @ lidents_of_term t3 @ lidents_of_term t4
  | ElimForall (bs, t1, ts) -> concat_map lidents_of_binder bs @ lidents_of_term t1 @ concat_map lidents_of_term ts
  | ElimExists (bs, t1, t2, b, t3) -> concat_map lidents_of_binder bs @ lidents_of_term t1 @ lidents_of_term t2 @ lidents_of_term t3
  | ElimImplies (t1, t2, t3) -> lidents_of_term t1 @ lidents_of_term t2 @ lidents_of_term t3
  | ElimOr (t1, t2, t3, b1, t4, b2, t5) -> lidents_of_term t1 @ lidents_of_term t2 @ lidents_of_term t3 @ lidents_of_term t4 @ lidents_of_term t5
  | ElimAnd (t1, t2, t3, b1, b2, t4) -> lidents_of_term t1 @ lidents_of_term t2 @ lidents_of_term t3 @ lidents_of_term t4
  | ListLiteral ts -> concat_map lidents_of_term ts
  | SeqLiteral ts -> concat_map lidents_of_term ts
and lidents_of_branch (p, _, t) = lidents_of_pattern p @ lidents_of_term t
and lidents_of_calc_step = function
  | CalcStep (t1, t2, t3) -> lidents_of_term t1 @ lidents_of_term t2 @ lidents_of_term t3
and lidents_of_pattern p =
  match p.pat with
  | PatWild _ -> []
  | PatConst _ -> []
  | PatApp (p, ps) -> lidents_of_pattern p @ concat_map lidents_of_pattern ps
  | PatVar (i, _, _) -> [FStarC.Ident.lid_of_ids [i]]
  | PatName lid -> [lid]
  | PatList ps -> concat_map lidents_of_pattern ps
  | PatTuple (ps, _) -> concat_map lidents_of_pattern ps
  | PatRecord ps -> concat_map (fun (_, p) -> lidents_of_pattern p) ps
  | PatAscribed (p, (t1, t2)) -> lidents_of_pattern p @ lidents_of_term t1 @ opt_map lidents_of_term t2
  | PatOr ps -> concat_map lidents_of_pattern ps
  | PatOp _ -> []
  | PatVQuote t -> lidents_of_term t
  | PatRest -> []
and lidents_of_binder b =
  match b.b with
  | Annotated (_, t)
  | NoName t -> lidents_of_term t
  | _ -> []

let lidents_of_tycon_record (_, _, _, t) =
  lidents_of_term t

let lidents_of_constructor_payload (t:constructor_payload) =
  match t with
  | VpOfNotation t -> lidents_of_term t
  | VpArbitrary t -> lidents_of_term t
  | VpRecord (tc, None) -> concat_map lidents_of_tycon_record tc
  | VpRecord (tc, Some t) -> concat_map lidents_of_tycon_record tc @ lidents_of_term t
  
let lidents_of_tycon_variant (tc:(ident & option constructor_payload & attributes_)) =
  match tc with
  | _, None, _ -> []
  | _, Some t, _ -> lidents_of_constructor_payload t

let lidents_of_tycon (tc:tycon) =
  match tc with
  | TyconAbstract (_, bs, k) -> concat_map lidents_of_binder bs @ opt_map lidents_of_term k
  | TyconAbbrev (_, bs, k, t) -> concat_map lidents_of_binder bs @ opt_map lidents_of_term k @ lidents_of_term t
  | TyconRecord (_, bs, k, _, tcs) ->
    concat_map lidents_of_binder bs @
    opt_map lidents_of_term k @
    concat_map lidents_of_tycon_record tcs
  | TyconVariant (_, bs, k, tcs) -> 
    concat_map lidents_of_binder bs @
    opt_map lidents_of_term k @
    concat_map lidents_of_tycon_variant tcs

let lidents_of_lift (l:lift) = 
  [l.msource; l.mdest]@
  (match l.lift_op with
   | NonReifiableLift t -> lidents_of_term t
   | ReifiableLift (t1, t2) -> lidents_of_term t1 @ lidents_of_term t2
   | LiftForFree t -> lidents_of_term t)

let rec lidents_of_decl (d:decl) =
  match d.d with
  | TopLevelModule _ -> []
  | Open (l, _)
  | Friend l
  | Include (l, _)
  | ModuleAbbrev (_, l) -> [l]
  | TopLevelLet (_q, lbs) -> concat_map (fun (p, t) -> lidents_of_pattern p @ lidents_of_term t) lbs
  | Tycon (_, _, tcs) -> concat_map lidents_of_tycon tcs
  | Val (_, t) -> lidents_of_term t
  | Exception (_, None) -> []
  | Exception (_, Some t) -> lidents_of_term t
  | NewEffect ed
  | LayeredEffect ed -> lidents_of_effect_decl ed
  | SubEffect lift -> lidents_of_lift lift
  | Polymonadic_bind(l0, l1, l2, t) -> l0::l1::l2::lidents_of_term t
  | Polymonadic_subcomp(l0, l1, t) -> l0::l1::lidents_of_term t
  | Pragma _ -> []
  | Assume (_, t) -> lidents_of_term t
  | Splice (_, _, t) -> lidents_of_term t
  | DeclSyntaxExtension _
  | DeclToBeDesugared _ -> []

and lidents_of_effect_decl (ed:effect_decl) =
  match ed with
  | DefineEffect  (_, bs, t, ds) ->
    concat_map lidents_of_binder bs @
    lidents_of_term t @
    concat_map lidents_of_decl ds
  | RedefineEffect (_, bs, t) -> 
    concat_map lidents_of_binder bs @
    lidents_of_term t

let extension_parser_table : SMap.t extension_parser = SMap.create 20
let register_extension_parser (ext:string) (parser:extension_parser) =
  SMap.add extension_parser_table ext parser

let lookup_extension_parser (ext:string) =
  let do () = SMap.try_find extension_parser_table ext in
  match do () with
  | None ->
    if Plugins.autoload_plugin ext
    then do ()
    else None
  | r -> r

let as_open_namespaces_and_abbrevs (ls:list decl)
: open_namespaces_and_abbreviations
= List.fold_right
    (fun d out ->
      match d.d with
      | Open (lid, _) -> {out with open_namespaces = lid :: out.open_namespaces}
      | ModuleAbbrev (i, lid) -> {out with module_abbreviations = (i, lid) :: out.module_abbreviations}
      | _ -> out)
    ls
    {open_namespaces = []; module_abbreviations = []}

let extension_lang_parser_table : SMap.t extension_lang_parser = SMap.create 20
let register_extension_lang_parser (ext:string) (parser:extension_lang_parser) =
  SMap.add extension_lang_parser_table ext parser
let lookup_extension_lang_parser (ext:string) =
  let r = SMap.try_find extension_lang_parser_table ext in
  match r with
  | None ->
    if Plugins.autoload_plugin ext
    then SMap.try_find extension_lang_parser_table ext
    else None
  | _ -> r

let parse_extension_lang (lang_name:string) (raw_text:string) (raw_text_pos:range)
: list decl
= let extension_parser = lookup_extension_lang_parser lang_name in
  match extension_parser with
  | None ->
    raise_error raw_text_pos Errors.Fatal_SyntaxError
      (Format.fmt1 "Unknown language extension %s" lang_name)
  | Some parser ->
    match parser.parse_decls raw_text raw_text_pos with
    | Inl error ->
      raise_error error.range Errors.Fatal_SyntaxError error.message
    | Inr ds ->
      ds
