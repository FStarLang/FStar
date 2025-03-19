(*
   Copyright 2008-2015 Abhishek Anand, Nikhil Swamy and Microsoft Research

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
(* -------------------------------------------------------------------- *)

module FStarC.Extraction.Krml
open FStarC.Effect
open FStarC.List
open FStarC
open FStarC.Util
open FStarC.Extraction
open FStarC.Extraction.ML
open FStarC.Extraction.ML.Syntax
open FStarC.Extraction.ML.UEnv
open FStarC.Const
open FStarC.BaseTypes

open FStarC.Class.Show
open FStarC.Class.PP
open FStarC.Pprint

module BU = FStarC.Util
module FC = FStarC.Const

(** CHANGELOG
- v24: Added a single constructor to the expression type to reflect the addition
  of type applications to the ML extraction language.
- v25: Added a number of type parameters for globals.
- v26: Flags for DExternal and all the DType's
- v27: Added PConstant
- v28: added many things for which the AST wasn't bumped; bumped it for
  TConstBuf which will expect will be used soon
- v29: added a SizeT and PtrdiffT width to machine integers
- v30: Added EBufDiff
- v31: Added a `meta` field to binders. Currently only relevant to propagate `CInline`.
*)
let current_version: version = 31

(* COPY-PASTED ****************************************************************)

type decl =
  | DGlobal of list flag & lident & int & typ & expr
  | DFunction of option cc & list flag & int & typ & lident & list binder & expr
  | DTypeAlias of lident & list flag & int & typ
  | DTypeFlat of lident & list flag & int & fields_t
  | DUnusedRetainedForBackwardsCompat of option cc & list flag & lident & typ
  | DTypeVariant of lident & list flag & int & branches_t
  | DTypeAbstractStruct of lident
  | DExternal of option cc & list flag & lident & typ & list ident
  | DUntaggedUnion of lident & list flag & int & list (ident & typ)

and cc =
  | StdCall
  | CDecl
  | FastCall

and fields_t =
  list (ident & (typ & bool))

and branches_t =
  list (ident & fields_t)

and flag =
  | Private
  | WipeBody
  | CInline
  | Substitute
  | GCType
  | Comment of string
  | MustDisappear
  | Const of string
  | Prologue of string
  | Epilogue of string
  | Abstract
  | IfDef
  | Macro
  | Deprecated of string
  | CNoInline

and fsdoc = string

and lifetime =
  | Eternal
  | Stack
  | ManuallyManaged

and expr =
  | EBound of var
  | EQualified of lident
  | EConstant of constant
  | EUnit
  | EApp of expr & list expr
  | ETypApp of expr & list typ
  | ELet of binder & expr & expr
  | EIfThenElse of expr & expr & expr
  | ESequence of list expr
  | EAssign of expr & expr
  | (** left expression can only be a EBound of EOpen *)
    EBufCreate of lifetime & expr & expr
  | EBufRead of expr & expr
  | EBufWrite of expr & expr & expr
  | EBufSub of expr & expr
  | EBufBlit of expr & expr & expr & expr & expr
  | EMatch of expr & branches
  | EOp of op & width
  | ECast of expr & typ
  | EPushFrame
  | EPopFrame
  | EBool of bool
  | EAny
  | EAbort
  | EReturn of expr
  | EFlat of typ & list (ident & expr)
  | EField of typ & expr & ident
  | EWhile of expr & expr
  | EBufCreateL of lifetime & list expr
  | ETuple of list expr
  | ECons of typ & ident & list expr
  | EBufFill of expr & expr & expr
  | EString of string
  | EFun of list binder & expr & typ
  | EAbortS of string
  | EBufFree of expr
  | EBufCreateNoInit of lifetime & expr
  | EAbortT of string & typ
  | EComment of string & expr & string
  | EStandaloneComment of string
  | EAddrOf of expr
  | EBufNull of typ
  | EBufDiff of expr & expr

and op =
  | Add | AddW | Sub | SubW | Div | DivW | Mult | MultW | Mod
  | BOr | BAnd | BXor | BShiftL | BShiftR | BNot
  | Eq | Neq | Lt | Lte | Gt | Gte
  | And | Or | Xor | Not

and branches =
  list branch

and branch =
  pattern & expr

and pattern =
  | PUnit
  | PBool of bool
  | PVar of binder
  | PCons of (ident & list pattern)
  | PTuple of list pattern
  | PRecord of list (ident & pattern)
  | PConstant of constant

and width =
  | UInt8 | UInt16 | UInt32 | UInt64
  | Int8 | Int16 | Int32 | Int64
  | Bool
  | CInt
  | SizeT | PtrdiffT

and constant = width & string

(* a De Bruijn index *)
and var = int

and binder = {
  name: ident;
  typ: typ;
  mut: bool;
  meta: list flag;
}

(* for pretty-printing *)
and ident = string

and lident =
  list ident & ident

and typ =
  | TInt of width
  | TBuf of typ
  | TUnit
  | TQualified of lident
  | TBool
  | TAny
  | TArrow of typ & typ
  | TBound of int
  | TApp of lident & list typ
  | TTuple of list typ
  | TConstBuf of typ
  | TArray of typ & constant

instance pretty_width = { pp = function
  | UInt8 -> doc_of_string "UInt8"
  | UInt16 -> doc_of_string "UInt16"
  | UInt32 -> doc_of_string "UInt32"
  | UInt64 -> doc_of_string "UInt64"
  | Int8 -> doc_of_string "Int8"
  | Int16 -> doc_of_string "Int16"
  | Int32 -> doc_of_string "Int32"
  | Int64 -> doc_of_string "Int64"
  | Bool -> doc_of_string "Bool"
  | CInt -> doc_of_string "CInt"
  | SizeT -> doc_of_string "SizeT"
  | PtrdiffT -> doc_of_string "PtrdiffT"
}

let record_string (fs : list (string & string)) : string =
  "{" ^
  (String.concat "; " <| List.map (fun (f, s) -> f ^ " = " ^ s) fs) ^
  "}"

let ctor (n: string) (args: list document) =
  nest 2 (group (parens (flow (break_ 1) (doc_of_string n :: args))))
// let ctor (n: string) (arg: document) : document =
//   nest 2 (group (parens (doc_of_string n ^/^ arg)))

let pp_list' (#a:Type) (f: a -> document) (xs: list a) : document =
  (pp_list a { pp = f }).pp xs // hack

let rec typ_to_doc (t:typ) : document =
  match t with
  | TInt w -> ctor "TInt" [pp w]
  | TBuf t -> ctor "TBuf" [typ_to_doc t]
  | TUnit -> doc_of_string "TUnit"
  | TQualified x -> ctor "TQualified" [doc_of_string (show x)]
  | TBool -> doc_of_string "TBool"
  | TAny -> doc_of_string "TAny"
  | TArrow (t1, t2) -> ctor "TArrow" [typ_to_doc t1; typ_to_doc t2]
  | TBound x -> ctor "TBound" [pp x]
  | TApp (x, xs) -> ctor "TApp" [doc_of_string (show x); pp_list' typ_to_doc xs]
  | TTuple ts -> ctor "TTuple" [pp_list' typ_to_doc ts]
  | TConstBuf t -> ctor "TConstBuf" [typ_to_doc t]
  | TArray (t, c) -> ctor "TArray" [typ_to_doc t; parens (separate comma [pp (fst c); doc_of_string (snd c)])]
  
instance pretty_typ = { pp = typ_to_doc }

instance pretty_string = { pp = (fun s -> dquotes (doc_of_string s)) }

instance pretty_flag = { pp = function
  | Private -> doc_of_string "Private"
  | WipeBody -> doc_of_string "WipeBody"
  | CInline -> doc_of_string "CInline"
  | Substitute -> doc_of_string "Substitute"
  | GCType -> doc_of_string "GCType"
  | Comment s -> ctor "Comment" [pp s]
  | MustDisappear -> doc_of_string "MustDisappear"
  | Const s -> ctor "Const" [pp s]
  | Prologue s -> ctor "Prologue" [pp s] 
  | Epilogue s -> ctor "Epilogue" [pp s] 
  | Abstract -> doc_of_string "Abstract"
  | IfDef -> doc_of_string "IfDef"
  | Macro -> doc_of_string "Macro"
  | Deprecated s -> ctor "Deprecated" [pp s]
  | CNoInline -> doc_of_string "CNoInline"
}

let spaced a = break_ 1 ^^ a ^^ break_ 1
let record fs =
  group <| nest 2 <| braces <| spaced <| separate (semi ^^ break_ 1) fs
let fld n v = group <| nest 2 <| doc_of_string (n ^ " =") ^/^ v

instance pretty_binder = { pp = fun b ->
  record [
    fld "name" (pp b.name);
    fld "typ"  (pp b.typ);
    fld "mut"  (pp b.mut);
    fld "meta" (pp b.meta);
  ]
}

instance pretty_lifetime : pretty lifetime = { pp = function
  | Eternal -> doc_of_string "Eternal"
  | Stack -> doc_of_string "Stack"
  | ManuallyManaged -> doc_of_string "ManuallyManaged"
}

instance pretty_op = { pp = function
  | Add -> doc_of_string "Add"
  | AddW -> doc_of_string "AddW"
  | Sub -> doc_of_string "Sub"
  | SubW -> doc_of_string "SubW"
  | Div -> doc_of_string "Div"
  | DivW -> doc_of_string "DivW"
  | Mult -> doc_of_string "Mult"
  | MultW -> doc_of_string "MultW"
  | Mod -> doc_of_string "Mod"
  | BOr -> doc_of_string "BOr"
  | BAnd -> doc_of_string "BAnd"
  | BXor -> doc_of_string "BXor"
  | BShiftL -> doc_of_string "BShiftL"
  | BShiftR -> doc_of_string "BShiftR"
  | BNot -> doc_of_string "BNot"
  | Eq -> doc_of_string "Eq"
  | Neq -> doc_of_string "Neq"
  | Lt -> doc_of_string "Lt"
  | Lte -> doc_of_string "Lte"
  | Gt -> doc_of_string "Gt"
  | Gte -> doc_of_string "Gte"
  | And -> doc_of_string "And"
  | Or -> doc_of_string "Or"
  | Xor -> doc_of_string "Xor"
  | Not -> doc_of_string "Not"
}

instance pretty_cc = { pp = function
  | StdCall -> doc_of_string "StdCall"
  | CDecl -> doc_of_string "CDecl"
  | FastCall -> doc_of_string "FastCall"
}

let rec pattern_to_doc (p:pattern) : document =
  match p with
  | PUnit -> doc_of_string "PUnit"
  | PBool b -> ctor "PBool" [pp b]
  | PVar b -> ctor "PVar" [pp b]
  | PCons (x, ps) -> ctor "PCons" [pp x; pp_list' pattern_to_doc ps]
  | PTuple ps -> ctor "PTuple" [pp_list' pattern_to_doc ps]
  | PRecord fs -> ctor "PRecord" [record (List.map (fun (s, p) -> fld s (pattern_to_doc p)) fs)]
  | PConstant c -> ctor "PConstant" [pp c]

instance pretty_pattern = { pp = pattern_to_doc }

let rec decl_to_doc (d:decl) : document =
  match d with
  | DGlobal (fs, x, i, t, e) -> ctor "DGlobal" [pp fs; pp x; pp i; pp t; expr_to_doc e]
  | DFunction (cc, fs, i, t, x, bs, e) -> ctor "DFunction" [pp cc; pp fs; pp i; pp t; pp x; pp bs; expr_to_doc e]
  | DTypeAlias (x, fs, i, t) -> ctor "DTypeAlias" [pp x; pp fs; pp i; pp t]
  | DTypeFlat (x, fs, i, f) -> ctor "DTypeFlat" [pp x; pp fs; pp i; pp f]
  | DUnusedRetainedForBackwardsCompat (cc, fs, x, t) -> ctor "DUnusedRetainedForBackwardsCompat" [pp cc; pp fs; pp x; pp t]
  | DTypeVariant (x, fs, i, bs) -> ctor "DTypeVariant" [pp x; pp fs; pp i; pp bs]
  | DTypeAbstractStruct x -> ctor "DTypeAbstractStruct" [pp x]
  | DExternal (cc, fs, x, t, xs) -> ctor "DExternal" [pp cc; pp fs; pp x; pp t; pp xs]
  | DUntaggedUnion (x, fs, i, xs) -> ctor "DUntaggedUnion" [pp x; pp fs; pp i; pp xs] 

and expr_to_doc (e:expr) : document =
  match e with
  | EBound x -> ctor "EBound" [pp x]
  | EQualified x -> ctor "EQualified" [pp x]
  | EConstant x -> ctor "EConstant" [pp x]
  | EUnit -> doc_of_string "EUnit"
  | EApp (x, xs) -> ctor "EApp" [expr_to_doc x; pp_list' expr_to_doc xs]
  | ETypApp (x, xs) -> ctor "ETypApp" [expr_to_doc x; pp xs]
  | ELet (x, y, z) -> ctor "ELet" [pp x; expr_to_doc y; expr_to_doc z]
  | EIfThenElse (x, y, z) -> ctor "EIfThenElse" [expr_to_doc x; expr_to_doc y; expr_to_doc z]
  | ESequence xs -> ctor "ESequence" [pp_list' expr_to_doc xs]
  | EAssign (x, y) -> ctor "EAssign" [expr_to_doc x; expr_to_doc y]
  | EBufCreate (x, y, z) -> ctor "EBufCreate" [pp x; expr_to_doc y; expr_to_doc z]
  | EBufRead (x, y) -> ctor "EBufRead" [expr_to_doc x; expr_to_doc y]
  | EBufWrite (x, y, z) -> ctor "EBufWrite" [expr_to_doc x; expr_to_doc y; expr_to_doc z]
  | EBufSub (x, y) -> ctor "EBufSub" [expr_to_doc x; expr_to_doc y]
  | EBufBlit (x, y, z, a, b) -> ctor "EBufBlit" [expr_to_doc x; expr_to_doc y; expr_to_doc z; expr_to_doc a; expr_to_doc b]
  | EMatch (x, bs) -> ctor "EMatch" [expr_to_doc x; pp_list' pp_branch bs]
  | EOp (x, y) -> ctor "EOp" [pp x; pp y]
  | ECast (x, y) -> ctor "ECast" [expr_to_doc x; pp y]
  | EPushFrame -> doc_of_string "EPushFrame"
  | EPopFrame -> doc_of_string "EPopFrame"
  | EBool x -> ctor "EBool" [pp x]
  | EAny -> doc_of_string "EAny"
  | EAbort -> doc_of_string "EAbort"
  | EReturn x -> ctor "EReturn" [expr_to_doc x]
  | EFlat (x, xs) -> ctor "EFlat" [pp x; record (List.map (fun (s, e) -> fld s (expr_to_doc e)) xs)]
  | EField (x, y, z) -> ctor "EField" [pp x; expr_to_doc y; pp z]
  | EWhile (x, y) -> ctor "EWhile" [expr_to_doc x; expr_to_doc y]
  | EBufCreateL (x, xs) -> ctor "EBufCreateL" [pp x; pp_list' expr_to_doc xs]
  | ETuple xs -> ctor "ETuple" [pp_list' expr_to_doc xs]
  | ECons (x, y, xs) -> ctor "ECons" [pp x; pp y; pp_list' expr_to_doc xs]
  | EBufFill (x, y, z) -> ctor "EBufFill" [expr_to_doc x; expr_to_doc y; expr_to_doc z]
  | EString x -> ctor "EString" [pp x]
  | EFun (xs, y, z) -> ctor "EFun" [pp_list' pp xs; expr_to_doc y; pp z]
  | EAbortS x -> ctor "EAbortS" [pp x]
  | EBufFree x -> ctor "EBufFree" [expr_to_doc x]
  | EBufCreateNoInit (x, y) -> ctor "EBufCreateNoInit" [pp x; expr_to_doc y]
  | EAbortT (x, y) -> ctor "EAbortT" [pp x; pp y]
  | EComment (x, y, z) -> ctor "EComment" [pp x; expr_to_doc y; pp z]
  | EStandaloneComment x -> ctor "EStandaloneComment" [pp x]
  | EAddrOf x -> ctor "EAddrOf" [expr_to_doc x]
  | EBufNull x -> ctor "EBufNull" [pp x]
  | EBufDiff (x, y) -> ctor "EBufDiff" [expr_to_doc x; expr_to_doc y]
  
and pp_branch (b:branch) : document =
  let (p, e) = b in
  parens (pp p ^^ comma ^/^ expr_to_doc e)

instance pretty_decl : pretty decl = { pp = decl_to_doc; }
instance showable_decl : showable decl = showable_from_pretty

(* Utilities *****************************************************************)

let fst3 (x, _, _) = x
let snd3 (_, x, _) = x
let thd3 (_, _, x) = x

let mk_width = function
  | "UInt8" -> Some UInt8
  | "UInt16" -> Some UInt16
  | "UInt32" -> Some UInt32
  | "UInt64" -> Some UInt64
  | "Int8" -> Some Int8
  | "Int16" -> Some Int16
  | "Int32" -> Some Int32
  | "Int64" -> Some Int64
  | "SizeT" -> Some SizeT
  | "PtrdiffT" -> Some PtrdiffT
  | _ -> None

let mk_bool_op = function
  | "op_Negation" ->
      Some Not
  | "op_AmpAmp" ->
      Some And
  | "op_BarBar" ->
      Some Or
  | "op_Equality" ->
      Some Eq
  | "op_disEquality" ->
      Some Neq
  | _ ->
      None

let is_bool_op op =
  mk_bool_op op <> None

let mk_op = function
  | "add" | "op_Plus_Hat" | "add_underspec" ->
      Some Add
  | "add_mod" | "op_Plus_Percent_Hat" ->
      Some AddW
  | "sub" | "op_Subtraction_Hat" | "sub_underspec" ->
      Some Sub
  | "sub_mod" | "op_Subtraction_Percent_Hat" ->
      Some SubW
  | "mul" | "op_Star_Hat" | "mul_underspec" ->
      Some Mult
  | "mul_mod" | "op_Star_Percent_Hat" ->
      Some MultW
  | "div" | "op_Slash_Hat" ->
      Some Div
  | "div_mod" | "op_Slash_Percent_Hat" ->
      Some DivW
  | "rem" | "op_Percent_Hat" ->
      Some Mod
  | "logor" | "op_Bar_Hat" ->
      Some BOr
  | "logxor" | "op_Hat_Hat" ->
      Some BXor
  | "logand" | "op_Amp_Hat" ->
      Some BAnd
  | "lognot" ->
      Some BNot
  | "shift_right" | "op_Greater_Greater_Hat" ->
      Some BShiftR
  | "shift_left" | "op_Less_Less_Hat" ->
      Some BShiftL
  | "eq" | "op_Equals_Hat" ->
      Some Eq
  | "op_Greater_Hat" | "gt" ->
      Some Gt
  | "op_Greater_Equals_Hat" | "gte" ->
      Some Gte
  | "op_Less_Hat" | "lt" ->
      Some Lt
  | "op_Less_Equals_Hat" | "lte" ->
      Some Lte
  | _ ->
      None

let is_op op =
  mk_op op <> None

let is_machine_int m =
  mk_width m <> None

(* Environments **************************************************************)

type env = {
  uenv : uenv;
  names: list name;
  names_t: list string;
  module_name: list string;
}

and name = {
  pretty: string;
}

let empty uenv module_name = {
  uenv = uenv;
  names = [];
  names_t = [];
  module_name = module_name
}

let extend env x =
  { env with names = { pretty = x } :: env.names }

let extend_t env x =
  { env with names_t = x :: env.names_t }

let find_name env x =
  match List.tryFind (fun name -> name.pretty = x) env.names with
  | Some name ->
      name
  | None ->
      failwith "internal error: name not found"

let find env x =
  try
    List.index (fun name -> name.pretty = x) env.names
  with _ ->
    failwith (BU.format1 "Internal error: name not found %s\n" x)

let find_t env x =
  try
    List.index (fun name -> name = x) env.names_t
  with _ ->
    failwith (BU.format1 "Internal error: name not found %s\n" x)

let add_binders env bs =
  List.fold_left (fun env {mlbinder_name} -> extend env mlbinder_name) env bs

(* Actual translation ********************************************************)

let list_elements e =
  let lopt = FStarC.Extraction.ML.Util.list_elements e in
  match lopt with
  | None -> failwith "Argument of FStar.Buffer.createL is not a list literal!"
  | Some l -> l

let translate_flags flags =
  List.choose (function
    | Syntax.Private -> Some Private
    | Syntax.NoExtract -> Some WipeBody
    | Syntax.CInline -> Some CInline
    | Syntax.CNoInline -> Some CNoInline
    | Syntax.Substitute -> Some Substitute
    | Syntax.GCType -> Some GCType
    | Syntax.Comment s -> Some (Comment s)
    | Syntax.StackInline -> Some MustDisappear
    | Syntax.CConst s -> Some (Const s)
    | Syntax.CPrologue s -> Some (Prologue s)
    | Syntax.CEpilogue s -> Some (Epilogue s)
    | Syntax.CAbstract -> Some Abstract
    | Syntax.CIfDef -> Some IfDef
    | Syntax.CMacro -> Some Macro
    | Syntax.Deprecated s -> Some (Deprecated s)
    | _ -> None // is this all of them?
  ) flags

let translate_cc flags =
  match List.choose (function | Syntax.CCConv s -> Some s | _ -> None) flags with
  | [ "stdcall" ] -> Some StdCall
  | [ "fastcall" ] -> Some FastCall
  | [ "cdecl" ] -> Some CDecl
  | _ -> None

(* Per FStarLang/karamel#324 *)
let generate_is_null
  (t: typ)
  (x: expr)
: Tot expr
= let dummy = UInt64 in
  EApp (ETypApp (EOp (Eq, dummy), [TBuf t]), [x; EBufNull t])

exception NotSupportedByKrmlExtension

let translate_type_without_decay_t = env -> mlty -> ML typ
let ref_translate_type_without_decay : ref translate_type_without_decay_t = mk_ref (fun _ _ -> raise NotSupportedByKrmlExtension)
let register_pre_translate_type_without_decay
  (f: translate_type_without_decay_t)
: ML unit
= let before : translate_type_without_decay_t = !ref_translate_type_without_decay in
  let after : translate_type_without_decay_t = fun e t ->
    try
      f e t
    with NotSupportedByKrmlExtension -> before e t
  in
  ref_translate_type_without_decay := after
let register_post_translate_type_without_decay
  (f: translate_type_without_decay_t)
: ML unit
= let before : translate_type_without_decay_t = !ref_translate_type_without_decay in
  let after : translate_type_without_decay_t = fun e t ->
    try
      before e t
    with NotSupportedByKrmlExtension -> f e t
  in
  ref_translate_type_without_decay := after
let translate_type_without_decay env t = !ref_translate_type_without_decay env t

// The outermost array type constructor decays to pointer
let translate_type_t = env -> mlty -> ML typ
let ref_translate_type : ref translate_type_t = mk_ref (fun _ _ -> raise NotSupportedByKrmlExtension)
let register_pre_translate_type
  (f: translate_type_t)
: ML unit
= let before : translate_type_t = !ref_translate_type in
  let after : translate_type_t = fun e t ->
    try
      f e t
    with NotSupportedByKrmlExtension -> before e t
  in
  ref_translate_type := after
let register_post_translate_type
  (f: translate_type_t)
: ML unit
= let before : translate_type_t = !ref_translate_type in
  let after : translate_type_t = fun e t ->
    try
      before e t
    with NotSupportedByKrmlExtension -> f e t
  in
  ref_translate_type := after
let translate_type env t = !ref_translate_type env t

let translate_expr_t = env -> mlexpr -> ML expr
let ref_translate_expr : ref translate_expr_t = mk_ref (fun _ _ -> raise NotSupportedByKrmlExtension)
let register_pre_translate_expr
  (f: translate_expr_t)
: ML unit
= let before : translate_expr_t = !ref_translate_expr in
  let after : translate_expr_t = fun e t ->
    try
      f e t
    with NotSupportedByKrmlExtension -> before e t
  in
  ref_translate_expr := after
let register_post_translate_expr
  (f: translate_expr_t)
: ML unit
= let before : translate_expr_t = !ref_translate_expr in
  let after : translate_expr_t = fun e t ->
    try
      before e t
    with NotSupportedByKrmlExtension -> f e t
  in
  ref_translate_expr := after
let translate_expr (env: env) (e: mlexpr) = !ref_translate_expr env e

let translate_type_decl_t = env -> one_mltydecl -> ML (option decl)
let ref_translate_type_decl : ref translate_type_decl_t = mk_ref (fun _ _ -> raise NotSupportedByKrmlExtension)
let register_pre_translate_type_decl
  (f: translate_type_decl_t)
: ML unit
= let before : translate_type_decl_t = !ref_translate_type_decl in
  let after : translate_type_decl_t = fun e t ->
    try
      f e t
    with NotSupportedByKrmlExtension -> before e t
  in
  ref_translate_type_decl := after
let register_post_translate_type_decl
  (f: translate_type_decl_t)
: ML unit
= let before : translate_type_decl_t = !ref_translate_type_decl in
  let after : translate_type_decl_t = fun e t ->
    try
      before e t
    with NotSupportedByKrmlExtension -> f e t
  in
  ref_translate_type_decl := after
let translate_type_decl env ty: option decl =
  if List.mem Syntax.NoExtract ty.tydecl_meta then
    None
  else
    !ref_translate_type_decl env ty

let rec translate_type_without_decay' env t: typ =
  match t with
  | MLTY_Tuple []
  | MLTY_Top ->
      TAny
  | MLTY_Var name ->
      TBound (find_t env name)
  | MLTY_Fun (t1, _, t2) ->
      TArrow (translate_type_without_decay env t1, translate_type_without_decay env t2)
  | MLTY_Erased ->
      TUnit
  | MLTY_Named ([], p) when (Syntax.string_of_mlpath p = "Prims.unit") ->
      TUnit
  | MLTY_Named ([], p) when (Syntax.string_of_mlpath p = "Prims.bool") ->
      TBool
  | MLTY_Named ([], ([ "FStar"; m ], "t")) when is_machine_int m ->
      TInt (must (mk_width m))
  | MLTY_Named ([], ([ "FStar"; m ], "t'")) when is_machine_int m ->
      TInt (must (mk_width m))
  | MLTY_Named ([], p) when (Syntax.string_of_mlpath p = "FStar.Monotonic.HyperStack.mem") ->
      TUnit
  
  | MLTY_Named ([_; arg; _], p) when
    Syntax.string_of_mlpath p = "FStar.Monotonic.HyperStack.s_mref" ||
    Syntax.string_of_mlpath p = "FStar.Monotonic.HyperHeap.mrref"  ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.m_rref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.s_mref"
    ->
      TBuf (translate_type_without_decay env arg)
  
  | MLTY_Named ([arg; _], p) when
    Syntax.string_of_mlpath p = "FStar.Monotonic.HyperStack.mreference" ||
    Syntax.string_of_mlpath p = "FStar.Monotonic.HyperStack.mstackref" ||
    Syntax.string_of_mlpath p = "FStar.Monotonic.HyperStack.mref" ||
    Syntax.string_of_mlpath p = "FStar.Monotonic.HyperStack.mmmstackref" ||
    Syntax.string_of_mlpath p = "FStar.Monotonic.HyperStack.mmmref" ||
    Syntax.string_of_mlpath p = "FStar.Monotonic.Heap.mref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.mreference" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.mstackref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.mref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.mmmstackref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.mmmref"
    ->
      TBuf (translate_type_without_decay env arg)
  
  | MLTY_Named ([arg; _; _], p) when
    Syntax.string_of_mlpath p = "LowStar.Monotonic.Buffer.mbuffer" -> TBuf (translate_type_without_decay env arg)
  
  | MLTY_Named ([arg], p) when
    Syntax.string_of_mlpath p = "LowStar.ConstBuffer.const_buffer" ||
    false
    -> TConstBuf (translate_type_without_decay env arg)

  | MLTY_Named ([arg], p) when
    Syntax.string_of_mlpath p = "FStar.Buffer.buffer" ||
    Syntax.string_of_mlpath p = "LowStar.Buffer.buffer" ||
    Syntax.string_of_mlpath p = "LowStar.ImmutableBuffer.ibuffer" ||
    Syntax.string_of_mlpath p = "LowStar.UninitializedBuffer.ubuffer" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.reference" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.stackref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.mmstackref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.mmref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.reference" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.stackref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.ref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.mmstackref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.mmref" ||
    false
    ->
      TBuf (translate_type_without_decay env arg)
  
  | MLTY_Named ([_;arg], p) when
    Syntax.string_of_mlpath p = "FStar.HyperStack.s_ref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.s_ref"
    ->
      TBuf (translate_type_without_decay env arg)
  
  | MLTY_Named ([arg], p) when
    Syntax.string_of_mlpath p = "FStar.Universe.raise_t"
    ->
      translate_type_without_decay env arg

  | MLTY_Named ([_], p) when (Syntax.string_of_mlpath p = "FStar.Ghost.erased") ->
      TAny
  
  | MLTY_Named ([], (path, type_name)) ->
      // Generate an unbound reference... to be filled in later by glue code.
      TQualified (path, type_name)
  
  | MLTY_Named (args, p)
    when Parser.Const.Tuples.get_tuple_tycon_arity (string_of_mlpath p) = Some (List.length args) ->
      TTuple (List.map (translate_type_without_decay env) args)
  
  | MLTY_Named (args, lid) ->
      if List.length args > 0 then
        TApp (lid, List.map (translate_type_without_decay env) args)
      else
        TQualified lid
  
  | MLTY_Tuple ts ->
      TTuple (List.map (translate_type_without_decay env) ts)
  
and translate_type' env t: typ =
  // The outermost array type constructor decays to pointer
  match t with
      
  | t -> translate_type_without_decay env t

and translate_binders env bs =
  List.map (translate_binder env) bs

and translate_binder env ({mlbinder_name; mlbinder_ty; mlbinder_attrs} ) =
  {
    name = mlbinder_name;
    typ = translate_type env mlbinder_ty;
    mut = false;
    meta = [];
  }

and translate_expr' env e: expr =
  match e.expr with
  | MLE_Tuple [] ->
      EUnit

  | MLE_Const c ->
      translate_constant c

  | MLE_Var name ->
      EBound (find env name)

  // Some of these may not appear beneath an [EApp] node because of partial applications
  | MLE_Name ([ "FStar"; m ], op) when (is_machine_int m && is_op op) ->
      EOp (must (mk_op op), must (mk_width m))

  | MLE_Name ([ "Prims" ], op) when (is_bool_op op) ->
      EOp (must (mk_bool_op op), Bool)

  | MLE_Name n ->
      EQualified n

  | MLE_Let ((flavor, [{
      mllb_name = name;
      mllb_tysc = Some ([], typ); // assuming unquantified type
      mllb_add_unit = add_unit; // ?
      mllb_def = body;
      mllb_meta = flags;
      print_typ = print // ?
    }]), continuation) ->
      let binder = { name = name; typ = translate_type env typ; mut = false; meta = translate_flags flags; } in
      let body = translate_expr env body in
      let env = extend env name in
      let continuation = translate_expr env continuation in
      ELet (binder, body, continuation)

  | MLE_Match (expr, branches) ->
      EMatch (translate_expr env expr, translate_branches env branches)

  // We recognize certain distinguished names from [FStar.HST] and other
  // modules, and translate them into built-in Karamel constructs
  | MLE_App({expr=MLE_TApp ({ expr = MLE_Name p }, [t])}, [arg])
    when string_of_mlpath p = "FStarC.Dyn.undyn" ->
      ECast (translate_expr env arg, translate_type env t)
  | MLE_App({expr=MLE_TApp ({ expr = MLE_Name p }, _)}, _)
    when string_of_mlpath p = "Prims.admit" ->
      EAbort
  | MLE_App({expr=MLE_TApp ({ expr = MLE_Name p }, [ t ])},
    [{ expr = MLE_Const (MLC_String s) }])
    when string_of_mlpath p = "LowStar.Failure.failwith" ->
      EAbortT (s, translate_type env t)
  | MLE_App({expr=MLE_TApp ({ expr = MLE_Name p }, _)}, [arg])
    when string_of_mlpath p = "FStar.HyperStack.All.failwith"
      ||  string_of_mlpath p = "FStar.Error.unexpected"
      ||  string_of_mlpath p = "FStar.Error.unreachable" ->
      (match arg with
       | {expr=MLE_Const (MLC_String msg)} -> EAbortS msg
       | _ ->
         let print_nm = ["FStar"; "HyperStack"; "IO"], "print_string" in
         let print = with_ty MLTY_Top (MLE_Name print_nm) in
         let print = with_ty MLTY_Top (MLE_App (print, [arg])) in
         let t = translate_expr env print in
         ESequence [t; EAbort])

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e ] )
    when string_of_mlpath p = "LowStar.ToFStarBuffer.new_to_old_st" ||
         string_of_mlpath p = "LowStar.ToFStarBuffer.old_to_new_st"
    ->
    translate_expr env e

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2 ])
    when string_of_mlpath p = "FStar.Buffer.index" || string_of_mlpath p = "FStar.Buffer.op_Array_Access"
      || string_of_mlpath p = "LowStar.Monotonic.Buffer.index"
      || string_of_mlpath p = "LowStar.UninitializedBuffer.uindex"
      || string_of_mlpath p = "LowStar.ConstBuffer.index"
      ->
      EBufRead (translate_expr env e1, translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e ])
    when string_of_mlpath p = "FStar.HyperStack.ST.op_Bang"
      ->
      EBufRead (translate_expr env e, EQualified (["C"], "_zero_for_deref"))

  (* Flatten all universes *)

  | MLE_App ({ expr = MLE_TApp ({ expr = MLE_Name p }, _) }, [arg])
    when string_of_mlpath p = "FStar.Universe.raise_val" ->
      translate_expr env arg

  | MLE_App ({ expr = MLE_TApp ({ expr = MLE_Name p }, _) }, [arg])
    when string_of_mlpath p = "FStar.Universe.downgrade_val" ->
      translate_expr env arg

  (* All the distinguished combinators that correspond to allocation, either on
   * the stack, on the heap (GC'd or manually-managed). *)
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ e1; e2 ])
    when (string_of_mlpath p = "FStar.Buffer.create" ||
          string_of_mlpath p = "LowStar.Monotonic.Buffer.malloca" ||
          string_of_mlpath p = "LowStar.ImmutableBuffer.ialloca") ->
      EBufCreate (Stack, translate_expr env e1, translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ elen ])
    when string_of_mlpath p = "LowStar.UninitializedBuffer.ualloca" ->
      EBufCreateNoInit (Stack, translate_expr env elen)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ init ])
    when (
      string_of_mlpath p = "FStar.HyperStack.ST.salloc" ||
      false
    ) ->
      EBufCreate (Stack, translate_expr env init, EConstant (UInt32, "1"))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e2 ])
    when (string_of_mlpath p = "FStar.Buffer.createL" ||
          string_of_mlpath p = "LowStar.Monotonic.Buffer.malloca_of_list" ||
          string_of_mlpath p = "LowStar.ImmutableBuffer.ialloca_of_list") ->
      EBufCreateL (Stack, List.map (translate_expr env) (list_elements e2))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _erid; e2 ])
    when string_of_mlpath p = "LowStar.Monotonic.Buffer.mgcmalloc_of_list" ||
         string_of_mlpath p = "LowStar.ImmutableBuffer.igcmalloc_of_list" ->
      EBufCreateL (Eternal, List.map (translate_expr env) (list_elements e2))

   (*
    * AR: TODO: FIXME:
    *     temporarily extraction of ralloc_drgn is same as ralloc
    *)
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ _rid; init ])
    when (string_of_mlpath p = "FStar.HyperStack.ST.ralloc") ||
         (string_of_mlpath p = "FStar.HyperStack.ST.ralloc_drgn") ->
      EBufCreate (Eternal, translate_expr env init, EConstant (UInt32, "1"))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _e0; e1; e2 ])
    when (string_of_mlpath p = "FStar.Buffer.rcreate" || string_of_mlpath p = "LowStar.Monotonic.Buffer.mgcmalloc" ||
          string_of_mlpath p = "LowStar.ImmutableBuffer.igcmalloc") ->
      EBufCreate (Eternal, translate_expr env e1, translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, _)
    when (string_of_mlpath p = "LowStar.Monotonic.Buffer.mgcmalloc_and_blit" ||
          string_of_mlpath p = "LowStar.Monotonic.Buffer.mmalloc_and_blit"   ||
          string_of_mlpath p = "LowStar.Monotonic.Buffer.malloca_and_blit"   ||
          string_of_mlpath p = "LowStar.ImmutableBuffer.igcmalloc_and_blit"  ||
          string_of_mlpath p = "LowStar.ImmutableBuffer.imalloc_and_blit"    ||
          string_of_mlpath p = "LowStar.ImmutableBuffer.ialloca_and_blit") ->
    EAbortS "alloc_and_blit family of functions are not yet supported downstream"

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _erid; elen ])
    when string_of_mlpath p = "LowStar.UninitializedBuffer.ugcmalloc" ->
      EBufCreateNoInit (Eternal, translate_expr env elen)

   (*
    * AR: TODO: FIXME:
    *     temporarily extraction of ralloc_drgn_mm is same as ralloc_mm
    *)
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ _rid; init ])
    when (string_of_mlpath p = "FStar.HyperStack.ST.ralloc_mm") ||
         (string_of_mlpath p = "FStar.HyperStack.ST.ralloc_drgn_mm") ->
      EBufCreate (ManuallyManaged, translate_expr env init, EConstant (UInt32, "1"))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _e0; e1; e2 ])
    when (string_of_mlpath p = "FStar.Buffer.rcreate_mm" ||
          string_of_mlpath p = "LowStar.Monotonic.Buffer.mmalloc" ||
          string_of_mlpath p = "LowStar.Monotonic.Buffer.mmalloc" ||
          string_of_mlpath p = "LowStar.ImmutableBuffer.imalloc") ->
      EBufCreate (ManuallyManaged, translate_expr env e1, translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _erid; elen ])
    when string_of_mlpath p = "LowStar.UninitializedBuffer.umalloc" ->
      EBufCreateNoInit (ManuallyManaged, translate_expr env elen)

  (* Only manually-managed references and buffers can be freed. *)
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e2 ]) when
      (string_of_mlpath p = "FStar.HyperStack.ST.rfree" ||
       false) ->
      EBufFree (translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e2 ])
    when (string_of_mlpath p = "FStar.Buffer.rfree" ||
          string_of_mlpath p = "LowStar.Monotonic.Buffer.free") ->
      EBufFree (translate_expr env e2)

  (* Generic buffer operations. *)
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2; _e3 ]) when (string_of_mlpath p = "FStar.Buffer.sub") ->
      EBufSub (translate_expr env e1, translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2; _e3 ])
    when string_of_mlpath p = "LowStar.Monotonic.Buffer.msub"
      || string_of_mlpath p = "LowStar.ConstBuffer.sub" ->
      EBufSub (translate_expr env e1, translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2 ]) when (string_of_mlpath p = "FStar.Buffer.join") ->
      (translate_expr env e1)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2 ])
    when string_of_mlpath p = "FStar.Buffer.offset"
      ->
      EBufSub (translate_expr env e1, translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2 ]) when string_of_mlpath p = "LowStar.Monotonic.Buffer.moffset" ->
      EBufSub (translate_expr env e1, translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2; e3 ])
    when string_of_mlpath p = "FStar.Buffer.upd" || string_of_mlpath p = "FStar.Buffer.op_Array_Assignment"
    || string_of_mlpath p = "LowStar.Monotonic.Buffer.upd'"
    || string_of_mlpath p = "LowStar.UninitializedBuffer.uupd"
    ->
      EBufWrite (translate_expr env e1, translate_expr env e2, translate_expr env e3)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2 ])
    when string_of_mlpath p = "FStar.HyperStack.ST.op_Colon_Equals"
      ->
      EBufWrite (translate_expr env e1, EQualified (["C"], "_zero_for_deref"), translate_expr env e2)

  | MLE_App ({ expr = MLE_Name p }, [ _ ]) when (
        string_of_mlpath p = "FStar.HyperStack.ST.push_frame" ||
        false
      ) ->
      EPushFrame
  | MLE_App ({ expr = MLE_Name p }, [ _ ]) when (string_of_mlpath p = "FStar.HyperStack.ST.pop_frame") ->
      EPopFrame
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2; e3; e4; e5 ]) when (
      string_of_mlpath p = "FStar.Buffer.blit" ||
      string_of_mlpath p = "LowStar.Monotonic.Buffer.blit" ||
      string_of_mlpath p = "LowStar.UninitializedBuffer.ublit"
    ) ->
      EBufBlit (translate_expr env e1, translate_expr env e2, translate_expr env e3, translate_expr env e4, translate_expr env e5)
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2; e3 ])
    when (let s = string_of_mlpath p in (s = "FStar.Buffer.fill" || s = "LowStar.Monotonic.Buffer.fill" )) ->
      EBufFill (translate_expr env e1, translate_expr env e2, translate_expr env e3)
  | MLE_App ({ expr = MLE_Name p }, [ _ ]) when string_of_mlpath p = "FStar.HyperStack.ST.get" ->
      // We need to reveal to Karamel that FStar.HST.get is equivalent to
      // (void*)0 so that it can get rid of ghost calls to HST.get at the
      // beginning of functions, which is needed to enforce the push/pop
      // structure.
      EUnit

   (*
    * AR: TODO: FIXME:
    *     temporarily extraction of new_drgn and free_drgn is same just unit
    *)
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ _rid ])
    when (string_of_mlpath p = "FStar.HyperStack.ST.free_drgn") ||
         (string_of_mlpath p = "FStar.HyperStack.ST.new_drgn") ->
      EUnit

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _ebuf; _eseq ])
    when (string_of_mlpath p = "LowStar.Monotonic.Buffer.witness_p" ||
          string_of_mlpath p = "LowStar.Monotonic.Buffer.recall_p" ||
          string_of_mlpath p = "LowStar.ImmutableBuffer.witness_contents" ||
          string_of_mlpath p = "LowStar.ImmutableBuffer.recall_contents") ->
      EUnit

 | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1 ])
   when string_of_mlpath p = "LowStar.ConstBuffer.of_buffer"
     || string_of_mlpath p = "LowStar.ConstBuffer.of_ibuffer"
   ->
     // The injection from *t to const *t should always be re-checkable by the
     // Low* checker and should not necessitate the insertion of casts. This is
     // the C semantics: if the context wants a const pointer, providing a
     // non-const pointer should always be checkable.
     translate_expr env e1

 | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, [ t ]) }, [ _eqal; e1 ])
   when string_of_mlpath p = "LowStar.ConstBuffer.of_qbuf"
   ->
     ECast (translate_expr env e1, TConstBuf (translate_type env t))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, [ t ]) }, [ e1 ])
    when string_of_mlpath p = "LowStar.ConstBuffer.cast" ||
      string_of_mlpath p = "LowStar.ConstBuffer.to_buffer" ||
      string_of_mlpath p = "LowStar.ConstBuffer.to_ibuffer"
    ->
      // See comments in LowStar.ConstBuffer.fsti
      ECast (translate_expr env e1, TBuf (translate_type env t))

  | MLE_App ({ expr = MLE_Name p }, [ e ]) when string_of_mlpath p = "Obj.repr" ->
      ECast (translate_expr env e, TAny)

  // Operators from fixed-width integer modules, e.g. [FStar.Int32.addw].
  | MLE_App ({ expr = MLE_Name ([ "FStar"; m ], op) }, args) when (is_machine_int m && is_op op) ->
      mk_op_app env (must (mk_width m)) (must (mk_op op)) args

  | MLE_App ({ expr = MLE_Name ([ "Prims" ], op) }, args) when (is_bool_op op) ->
      mk_op_app env Bool (must (mk_bool_op op)) args

  // Fixed-width literals are represented as calls to [FStar.Int32.uint_to_t]
  | MLE_App ({ expr = MLE_Name ([ "FStar"; m ], "int_to_t") }, [ { expr = MLE_Const (MLC_Int (c, None)) }])
  | MLE_App ({ expr = MLE_Name ([ "FStar"; m ], "uint_to_t") }, [ { expr = MLE_Const (MLC_Int (c, None)) }]) when is_machine_int m ->
      EConstant (must (mk_width m), c)

  | MLE_App ({ expr = MLE_Name ([ "C" ], "string_of_literal") }, [ { expr = e } ])
  | MLE_App ({ expr = MLE_Name ([ "C"; "Compat"; "String" ], "of_literal") }, [ { expr = e } ])
  | MLE_App ({ expr = MLE_Name ([ "C"; "String" ], "of_literal") }, [ { expr = e } ]) ->
      begin match e with
      | MLE_Const (MLC_String s) ->
          EString s
      | _ ->
          failwith "Cannot extract string_of_literal applied to a non-literal"
      end

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ { expr = ebefore }; e ; { expr = eafter } ] )
    when string_of_mlpath p = "LowStar.Comment.comment_gen" ->
      begin match ebefore, eafter with
      | MLE_Const (MLC_String sbefore), MLE_Const (MLC_String safter) ->
          if contains sbefore "*/"
          then failwith "Before Comment contains end-of-comment marker";
          if contains safter "*/"
          then failwith "After Comment contains end-of-comment marker";
          EComment (sbefore, translate_expr env e, safter)
      | _ ->
          failwith "Cannot extract comment applied to a non-literal"
      end

  | MLE_App ({ expr = MLE_Name p }, [ { expr = e } ] )
    when string_of_mlpath p = "LowStar.Comment.comment" ->
      begin match e with
      | MLE_Const (MLC_String s) ->
          if contains s "*/"
          then failwith "Standalone Comment contains end-of-comment marker";
          EStandaloneComment s
      | _ ->
          failwith "Cannot extract comment applied to a non-literal"
      end

  | MLE_App ({ expr = MLE_Name ([ "LowStar"; "Literal" ], "buffer_of_literal") }, [ { expr = e } ]) ->
      begin match e with
      | MLE_Const (MLC_String s) ->
          ECast (EString s, TBuf (TInt UInt8))
      | _ ->
          failwith "Cannot extract buffer_of_literal applied to a non-literal"
      end

  | MLE_App ({ expr = MLE_Name ([ "FStar"; "Int"; "Cast" ], c) }, [ arg ]) ->
      let is_known_type =
        starts_with c "uint8" || starts_with c "uint16" ||
        starts_with c "uint32" || starts_with c "uint64" ||
        starts_with c "int8" || starts_with c "int16" ||
        starts_with c "int32" || starts_with c "int64"
      in
      if ends_with c "uint64" && is_known_type then
        ECast (translate_expr env arg, TInt UInt64)
      else if ends_with c "uint32" && is_known_type then
        ECast (translate_expr env arg, TInt UInt32)
      else if ends_with c "uint16" && is_known_type then
        ECast (translate_expr env arg, TInt UInt16)
      else if ends_with c "uint8" && is_known_type then
        ECast (translate_expr env arg, TInt UInt8)
      else if ends_with c "int64" && is_known_type then
        ECast (translate_expr env arg, TInt Int64)
      else if ends_with c "int32" && is_known_type then
        ECast (translate_expr env arg, TInt Int32)
      else if ends_with c "int16" && is_known_type then
        ECast (translate_expr env arg, TInt Int16)
      else if ends_with c "int8" && is_known_type then
        ECast (translate_expr env arg, TInt Int8)
      else
        EApp (EQualified ([ "FStar"; "Int"; "Cast" ], c), [ translate_expr env arg ])
        
  | MLE_App ({ expr = MLE_Name p }, [ arg ])
    when string_of_mlpath p = "FStar.SizeT.uint16_to_sizet" ||
         string_of_mlpath p = "FStar.SizeT.uint32_to_sizet" ||
         string_of_mlpath p = "FStar.SizeT.uint64_to_sizet" ||
         string_of_mlpath p = "FStar.PtrdiffT.ptrdifft_to_sizet" ->
      ECast (translate_expr env arg, TInt SizeT)

  | MLE_App ({ expr = MLE_Name p }, [ arg ])
    when string_of_mlpath p = "FStar.SizeT.sizet_to_uint32" ->
      ECast (translate_expr env arg, TInt UInt32)

  | MLE_App ({ expr = MLE_Name p }, [ arg ])
    when string_of_mlpath p = "FStar.SizeT.sizet_to_uint64" ->
      ECast (translate_expr env arg, TInt UInt64)

  | MLE_App (head, args) ->
      EApp (translate_expr env head, List.map (translate_expr env) args)

  | MLE_TApp (head, ty_args) ->
      ETypApp (translate_expr env head, List.map (translate_type env) ty_args)

  | MLE_Coerce (e, t_from, t_to) ->
      ECast (translate_expr env e, translate_type env t_to)

  | MLE_Record (_, _, fields) ->
      EFlat (assert_lid env e.mlty, List.map (fun (field, expr) ->
        field, translate_expr env expr) fields)

  | MLE_Proj (e, path) ->
      EField (assert_lid env e.mlty, translate_expr env e, snd path)

  | MLE_Let _ ->
      (* Things not supported (yet): let-bindings for functions; meaning, rec flags are not
       * supported, and quantified type schemes are not supported either *)
      failwith (BU.format1 "todo: translate_expr [MLE_Let] (expr is: %s)"
        (ML.Code.string_of_mlexpr ([],"") e))
  | MLE_App (head, _) ->
      failwith (BU.format1 "todo: translate_expr [MLE_App] (head is: %s)"
        (ML.Code.string_of_mlexpr ([], "") head))
  | MLE_Seq seqs ->
      ESequence (List.map (translate_expr env) seqs)
  | MLE_Tuple es ->
      ETuple (List.map (translate_expr env) es)

  | MLE_CTor ((_, cons), es) ->
      ECons (assert_lid env e.mlty, cons, List.map (translate_expr env) es)

  | MLE_Fun (bs, body) ->
      let binders = translate_binders env bs in
      let env = add_binders env bs in
      EFun (binders, translate_expr env body, translate_type env body.mlty)

  | MLE_If (e1, e2, e3) ->
      EIfThenElse (translate_expr env e1, translate_expr env e2, (match e3 with
        | None -> EUnit
        | Some e3 -> translate_expr env e3))
  | MLE_Raise _ ->
      failwith "todo: translate_expr [MLE_Raise]"
  | MLE_Try _ ->
      failwith "todo: translate_expr [MLE_Try]"
  | MLE_Coerce _ ->
      failwith "todo: translate_expr [MLE_Coerce]"

and assert_lid env t =
  match t with
  | MLTY_Named (ts, lid) ->
      if List.length ts > 0 then
        TApp (lid, List.map (translate_type env) ts)
      else
        TQualified lid
  | _ -> failwith (BU.format1 "invalid argument: expected MLTY_Named, got %s"
                             (ML.Code.string_of_mlty ([], "") t))

and translate_branches env branches =
  List.map (translate_branch env) branches

and translate_branch env (pat, guard, expr) =
  if guard = None then
    let env, pat = translate_pat env pat in
    pat, translate_expr env expr
  else
    failwith "todo: translate_branch"

and translate_width = function
  | None -> CInt
  | Some (FC.Signed, FC.Int8) -> Int8
  | Some (FC.Signed, FC.Int16) -> Int16
  | Some (FC.Signed, FC.Int32) -> Int32
  | Some (FC.Signed, FC.Int64) -> Int64
  | Some (FC.Unsigned, FC.Int8) -> UInt8
  | Some (FC.Unsigned, FC.Int16) -> UInt16
  | Some (FC.Unsigned, FC.Int32) -> UInt32
  | Some (FC.Unsigned, FC.Int64) -> UInt64
  | Some (FC.Unsigned, FC.Sizet) -> SizeT

and translate_pat env p =
  match p with
  | MLP_Const MLC_Unit ->
      env, PUnit
  | MLP_Const (MLC_Bool b) ->
      env, PBool b
  | MLP_Const (MLC_Int (s, sw)) ->
      env, PConstant (translate_width sw, s)
  | MLP_Var name ->
      let env = extend env name in
      env, PVar ({ name = name; typ = TAny; mut = false; meta = [] })
  | MLP_Wild ->
      let env = extend env "_" in
      env, PVar ({ name = "_"; typ = TAny; mut = false; meta = [] })
  | MLP_CTor ((_, cons), ps) ->
      let env, ps = List.fold_left (fun (env, acc) p ->
        let env, p = translate_pat env p in
        env, p :: acc
      ) (env, []) ps in
      env, PCons (cons, List.rev ps)
  | MLP_Record (_, ps) ->
      let env, ps = List.fold_left (fun (env, acc) (field, p) ->
        let env, p = translate_pat env p in
        env, (field, p) :: acc
      ) (env, []) ps in
      env, PRecord (List.rev ps)

  | MLP_Tuple ps ->
      let env, ps = List.fold_left (fun (env, acc) p ->
        let env, p = translate_pat env p in
        env, p :: acc
      ) (env, []) ps in
      env, PTuple (List.rev ps)

  | MLP_Const _ ->
      failwith "todo: translate_pat [MLP_Const]"
  | MLP_Branch _ ->
      failwith "todo: translate_pat [MLP_Branch]"

and translate_constant c: expr =
  match c with
  | MLC_Unit ->
      EUnit
  | MLC_Bool b ->
      EBool b
  | MLC_String s ->
      if FStar.String.list_of_string s
      |> BU.for_some (fun (c:FStar.Char.char) -> c = FStar.Char.char_of_int 0)
      then failwith (BU.format1 "Refusing to translate a string literal that contains a null character: %s" s);
      EString s
  | MLC_Char c ->
      let i = BU.int_of_char c in
      let s = BU.string_of_int i in
      let c = EConstant (CInt, s) in
      let char_of_int = EQualified (["FStar"; "Char"], "char_of_int") in
      EApp(char_of_int, [c])
  | MLC_Int (s, Some (sg, wd)) ->
      EConstant (translate_width (Some (sg, wd)), s)
  | MLC_Float _ ->
      failwith "todo: translate_expr [MLC_Float]"
  | MLC_Bytes _ ->
      failwith "todo: translate_expr [MLC_Bytes]"
  | MLC_Int (s, None) ->
      EConstant (CInt, s)

(* Helper functions **********************************************************)

and mk_op_app env w op args =
  EApp (EOp (op, w), List.map (translate_expr env) args)

let translate_type_decl' env ty: option decl =
    match ty with
    | {tydecl_assumed=assumed;
       tydecl_name=name;
       tydecl_parameters=args;
       tydecl_meta=flags;
       tydecl_defn= Some (MLTD_Abbrev t)} ->
        let name = env.module_name, name in
        let env = List.fold_left (fun env {ty_param_name} -> extend_t env ty_param_name) env args in
        if assumed && List.mem Syntax.CAbstract flags then
          Some (DTypeAbstractStruct name)
        else if assumed then
          let name = string_of_mlpath name in
          BU.print1_warning "Not extracting type definition %s to KaRaMeL (assumed type)\n" name;
          // JP: TODO: shall we be smarter here?
          None
        else
          Some (DTypeAlias (name, translate_flags flags, List.length args, translate_type env t))

    | {tydecl_name=name;
       tydecl_parameters=args;
       tydecl_meta=flags;
       tydecl_defn=Some (MLTD_Record fields)} ->
        let name = env.module_name, name in
        let env = List.fold_left (fun env {ty_param_name} -> extend_t env ty_param_name) env args in
        Some (DTypeFlat (name, translate_flags flags, List.length args, List.map (fun (f, t) ->
          f, (translate_type_without_decay env t, false)) fields))

    | {tydecl_name=name;
       tydecl_parameters=args;
       tydecl_meta=flags;
       tydecl_defn=Some (MLTD_DType branches)} ->
        let name = env.module_name, name in
        let flags = translate_flags flags in
        let env = args |> ty_param_names |> List.fold_left extend_t env in
        Some (DTypeVariant (name, flags, List.length args, List.map (fun (cons, ts) ->
          cons, List.map (fun (name, t) ->
            name, (translate_type_without_decay env t, false)
          ) ts
        ) branches))
    | {tydecl_name=name} ->
        // JP: TODO: figure out why and how this happens
        Errors.log_issue0 Errors.Warning_DefinitionNotTranslated [
            Errors.Msg.text <| BU.format1 "Error extracting type definition %s to KaRaMeL." name;
          ];
        None

let translate_let' env flavor lb: option decl =
  match lb with
  | {
      mllb_name = name;
      mllb_tysc = Some (tvars, t0);
      mllb_def = e;
      mllb_meta = meta
    } when BU.for_some (function Syntax.Assumed -> true | _ -> false) meta ->
      let name = env.module_name, name in
      let arg_names = match e.expr with
        | MLE_Fun (bs, _) -> List.map (fun {mlbinder_name} -> mlbinder_name) bs
        | _ -> []
      in
      if List.length tvars = 0 then
        Some (DExternal (translate_cc meta, translate_flags meta, name, translate_type env t0, arg_names))
      else begin
        BU.print1_warning "Not extracting %s to KaRaMeL (polymorphic assumes are not supported)\n" (Syntax.string_of_mlpath name);
        None
      end

  | {
      mllb_name = name;
      mllb_tysc = Some (tvars, t0);
      mllb_def = { expr = MLE_Fun (args, body) };
      mllb_meta = meta
    } ->
      if List.mem Syntax.NoExtract meta then
        None
      else
        // Case 1: a possibly-polymorphic function.
        let env = if flavor = Rec then extend env name else env in
        let env = tvars |> ty_param_names |> List.fold_left (fun env name -> extend_t env name) env in
        let rec find_return_type eff i = function
          | MLTY_Fun (_, eff, t) when i > 0 ->
              find_return_type eff (i - 1) t
          | t ->
              i, eff, t
        in
        let name = env.module_name, name in
        let i, eff, t = find_return_type E_PURE (List.length args) t0 in
        if i > 0 then begin
          let msg = "function type annotation has less arrows than the \
            number of arguments; please mark the return type abbreviation as \
            inline_for_extraction" in
          BU.print2_warning "Not extracting %s to KaRaMeL (%s)\n" (Syntax.string_of_mlpath name) msg
        end;
        let t = translate_type env t in
        let binders = translate_binders env args in
        let env = add_binders env args in
        let cc = translate_cc meta in
        let meta = match eff, t with
          | E_ERASABLE, _
          | E_PURE, TUnit -> MustDisappear :: translate_flags meta
          | _ -> translate_flags meta
        in
        begin try
          let body = translate_expr env body in
          Some (DFunction (cc, meta, List.length tvars, t, name, binders, body))
        with e ->
          // JP: TODO: figure out what are the remaining things we don't extract
          let msg = BU.print_exn e in
          Errors.log_issue0 Errors.Warning_FunctionNotExtacted [
            Errors.Msg.text <| BU.format1 "Error while extracting %s to KaRaMeL." (Syntax.string_of_mlpath name);
            Pprint.arbitrary_string msg;
          ];
          let msg = "This function was not extracted:\n" ^ msg in
          Some (DFunction (cc, meta, List.length tvars, t, name, binders, EAbortS msg))
        end

  | {
      mllb_name = name;
      mllb_tysc = Some (tvars, t);
      mllb_def = expr;
      mllb_meta = meta
    } ->
      if List.mem Syntax.NoExtract meta then
        None
      else
        // Case 2: this is a global
        let meta = translate_flags meta in
        let env = tvars |> ty_param_names |> List.fold_left (fun env name -> extend_t env name) env in
        let t = translate_type env t in
        let name = env.module_name, name in
        begin try
          let expr = translate_expr env expr in
          Some (DGlobal (meta, name, List.length tvars, t, expr))
        with e ->
          Errors.log_issue0 Errors.Warning_DefinitionNotTranslated [
              Errors.Msg.text <| BU.format1 "Error extracting %s to KaRaMeL." (Syntax.string_of_mlpath name);
              Pprint.arbitrary_string (BU.print_exn e);
            ];
          Some (DGlobal (meta, name, List.length tvars, t, EAny))
        end

  | { mllb_name = name; mllb_tysc = ts } ->
      // TODO JP: figure out what exactly we're hitting here...?
      Errors.log_issue0 Errors.Warning_DefinitionNotTranslated
        (BU.format1 "Not extracting %s to KaRaMeL\n" name);
      begin match ts with
      | Some (tps, t) ->
          BU.print2 "Type scheme is: forall %s. %s\n"
            (String.concat ", " (ty_param_names tps))
            (ML.Code.string_of_mlty ([], "") t)
      | None ->
          ()
      end;
      None

let translate_let_t = env -> mlletflavor -> mllb -> ML (option decl)
(* translate_let' is not recursive, so we can directly use it to initialize ref_translate_let *)
let ref_translate_let : ref translate_let_t = mk_ref translate_let'
let register_pre_translate_let
  (f: translate_let_t)
: ML unit
= let before : translate_let_t = !ref_translate_let in
  let after : translate_let_t = fun e fl lb ->
    try
      f e fl lb
    with NotSupportedByKrmlExtension -> before e fl lb
  in
  ref_translate_let := after
let translate_let env flavor lb: option decl =
  !ref_translate_let env flavor lb

let translate_decl env d: list decl =
  match d.mlmodule1_m with
  | MLM_Let (flavor, lbs) ->
      // We don't care about mutual recursion, since every C file will include
      // its own header with the forward declarations.
      List.choose (translate_let env flavor) lbs

  | MLM_Loc _ ->
      // JP: TODO: use this to reconstruct location information
      []

  | MLM_Ty tys ->
      // We don't care about mutual recursion, since KaRaMeL will insert forward
      // declarations exactly as needed, as part of its monomorphization phase
      List.choose (translate_type_decl env) tys

  | MLM_Top _ ->
      failwith "todo: translate_decl [MLM_Top]"

  | MLM_Exn (m, _) ->
      BU.print1_warning "Not extracting exception %s to KaRaMeL (exceptions unsupported)\n" m;
      []

let translate_module uenv (m : mlpath & option (mlsig & mlmodulebody)) : file =
  let (module_name, modul) = m in
  let module_name = fst module_name @ [ snd module_name ] in
  let program = match modul with
    | Some (_signature, decls) ->
        List.collect (translate_decl (empty uenv module_name)) decls
    | _ ->
        failwith "Unexpected standalone interface or nested modules"
  in
  (String.concat "_" module_name), program

let translate (ue:uenv) (modules : list mlmodule): list file =
  List.filter_map (fun m ->
    let m_name =
      let path, _ = m in
      Syntax.string_of_mlpath path
    in
    try
      if not (Options.silent()) then (BU.print1 "Attempting to translate module %s\n" m_name);
      Some (translate_module ue m)
    with
    | e ->
        BU.print2 "Unable to translate module: %s because:\n  %s\n"
          m_name (BU.print_exn e);
        None
  ) modules

let _ =
  register_post_translate_type_without_decay translate_type_without_decay';
  register_post_translate_type translate_type';
  register_post_translate_type_decl translate_type_decl';
  register_post_translate_expr translate_expr'
