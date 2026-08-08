(*
   Copyright 2008-2025 Microsoft Research

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

(** The karamel AST, copy-pasted from karamel's [Ast.ml], together with its
    pretty-printers.

    This lives in its own module rather than in {!FStarC.Extraction.Krml} so
    that more than one extraction pipeline can build karamel input: the ML
    extraction does, and so does Custard ({!FStarC.Custard.PrintKrml}).  Any
    change here has to be mirrored in karamel and reflected in the version
    number, which stays in {!FStarC.Extraction.Krml}. *)
module FStarC.Extraction.KrmlAst

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.BaseTypes
open FStarC.Class.Show
open FStarC.Class.PP
open FStarC.Pprint

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
  | ESizeof of typ

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
  | Float32 | Float64

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
  | Float32 -> doc_of_string "Float32"
  | Float64 -> doc_of_string "Float64"
}
instance showable_width : showable width = showable_from_pretty

let ctor (n: string) (args: list document) =
  nest 2 (group (parens (flow (break_ 1) (doc_of_string n :: args))))
// let ctor (n: string) (arg: document) : document =
//   nest 2 (group (parens (doc_of_string n ^/^ arg)))

let pp_list' (#a:Type) (f: a -> ML document) (xs: list a) : ML document =
  group (nest 2 (brackets (flow_map (semi ^^ break_ 1) f xs)))

let rec typ_to_doc (t:typ) : ML document =
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
instance showable_typ : showable typ = showable_from_pretty

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
instance showable_binder : showable binder = showable_from_pretty

instance pretty_lifetime : pretty lifetime = { pp = function
  | Eternal -> doc_of_string "Eternal"
  | Stack -> doc_of_string "Stack"
  | ManuallyManaged -> doc_of_string "ManuallyManaged"
}
instance showable_lifetime : showable lifetime = showable_from_pretty

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
instance showable_op : showable op = showable_from_pretty

instance pretty_cc = { pp = function
  | StdCall -> doc_of_string "StdCall"
  | CDecl -> doc_of_string "CDecl"
  | FastCall -> doc_of_string "FastCall"
}
instance showable_cc : showable cc = showable_from_pretty

let rec pattern_to_doc (p:pattern) : ML document =
  match p with
  | PUnit -> doc_of_string "PUnit"
  | PBool b -> ctor "PBool" [pp b]
  | PVar b -> ctor "PVar" [pp b]
  | PCons (x, ps) -> ctor "PCons" [pp x; pp_list' pattern_to_doc ps]
  | PTuple ps -> ctor "PTuple" [pp_list' pattern_to_doc ps]
  | PRecord fs -> ctor "PRecord" [record (List.map (fun (s, p) -> fld s (pattern_to_doc p)) fs)]
  | PConstant c -> ctor "PConstant" [pp c]

instance pretty_pattern = { pp = pattern_to_doc }
instance showable_pattern : showable pattern = showable_from_pretty

let rec decl_to_doc (d:decl) : ML document =
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

and expr_to_doc (e:expr) : ML document =
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
  | ESizeof t -> ctor "ESizeof" [pp t]

and pp_branch (b:branch) : ML document =
  let (p, e) = b in
  parens (pp p ^^ comma ^/^ expr_to_doc e)

instance pretty_expr : pretty expr = { pp = expr_to_doc; }
instance pretty_decl : pretty decl = { pp = decl_to_doc; }
instance pretty_branch : pretty branch = { pp = pp_branch; }

instance showable_expr : showable expr = showable_from_pretty
instance showable_decl : showable decl = showable_from_pretty
instance showable_branch : showable branch = showable_from_pretty
