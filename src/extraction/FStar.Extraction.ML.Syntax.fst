(*
   Copyright 2008-2016 Abhishek Anand, Nikhil Swamy,
                           Antoine Delignat-Lavaud, Pierre-Yves Strub
                               and Microsoft Research

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
module FStar.Extraction.ML.Syntax
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar
open FStar.Compiler
open FStar.Ident
open FStar.Compiler.Util
open FStar.Const
open FStar.BaseTypes

open FStar.Class.Show

(* -------------------------------------------------------------------- *)
type mlsymbol = string
type mlident  = mlsymbol
type mlpath   = list mlsymbol & mlsymbol //Path and name of a module

(* -------------------------------------------------------------------- *)
let krml_keywords = []

let ocamlkeywords = [
  "and"; "as"; "assert"; "asr"; "begin"; "class";
  "constraint"; "do"; "done"; "downto"; "else"; "end";
  "exception"; "external"; "false"; "for"; "fun"; "function";
  "functor"; "if"; "in"; "include"; "inherit"; "initializer";
  "land"; "lazy"; "let"; "lor"; "lsl"; "lsr";
  "lxor"; "match"; "method"; "mod"; "module"; "mutable";
  "new"; "object"; "of"; "open"; "or"; "private";
  "rec"; "sig"; "struct"; "then"; "to"; "true";
  "try"; "type"; "val"; "virtual"; "when"; "while";
  "with"; "nonrec"
]

let fsharpkeywords = [
  "abstract"; "and"; "as"; "assert"; "base"; "begin"; "class";
  "default"; "delegate"; "do"; "done"; "downcast"; "downto";
  "elif"; "else"; "end"; "exception"; "extern"; "false";
  "finally"; "fixed"; "for"; "fun"; "function"; "global"; "if";
  "in"; "inherit"; "inline"; "interface"; "internal"; "lazy";
  "let"; "let!"; "match"; "member"; "module"; "mutable";
  "namespace"; "new"; "not"; "null"; "of"; "open"; "or";
  "override"; "private"; "public"; "rec"; "return"; "return!";
  "select"; "static"; "struct"; "then"; "to"; "true"; "try";
  "type"; "upcast"; "use"; "use!"; "val"; "void"; "when";
  "while"; "with"; "yield"; "yield!";
  // --mlcompatibility keywords
  "asr"; "land"; "lor";
  "lsl"; "lsr"; "lxor"; "mod"; "sig";
  // reserved keywords
  "atomic"; "break"; "checked"; "component"; "const";
  "constraint"; "constructor"; "continue"; "eager"; "event";
  "external"; "fixed"; "functor"; "include"; "method"; "mixin";
  "object"; "parallel"; "process"; "protected"; "pure";
  "sealed"; "tailcall"; "trait"; "virtual"; "volatile"
]

let string_of_mlpath ((p, s) : mlpath) : mlsymbol =
    String.concat "." (p @ [s])


(* -------------------------------------------------------------------- *)
type mlidents  = list mlident
type mlsymbols = list mlsymbol

(* -------------------------------------------------------------------- *)
type e_tag =
  | E_PURE
  | E_ERASABLE
  | E_IMPURE

// Line number, file name; that's all we can emit in OCaml anyhwow
type mlloc = int & string
let dummy_loc: mlloc = 0, ""

type mlty =
| MLTY_Var   of mlident
| MLTY_Fun   of mlty & e_tag & mlty
| MLTY_Named of list mlty & mlpath
| MLTY_Tuple of list mlty
| MLTY_Top  (* \mathbb{T} type in the thesis, to be used when OCaml is not expressive enough for the source type *)
| MLTY_Erased //a type that extracts to unit

type mlconstant =
| MLC_Unit
| MLC_Bool   of bool
| MLC_Int    of string & option (signedness & width)
| MLC_Float  of float
| MLC_Char   of char
| MLC_String of string
| MLC_Bytes  of array byte

type mlpattern =
| MLP_Wild
| MLP_Const  of mlconstant
| MLP_Var    of mlident
| MLP_CTor   of mlpath & list mlpattern
| MLP_Branch of list mlpattern
(* SUGAR *)
| MLP_Record of list mlsymbol & list (mlsymbol & mlpattern)
| MLP_Tuple  of list mlpattern


(* metadata, suitable for either the C or the OCaml backend *)
type meta =
  | Mutable (* deprecated *)
  | Assumed
  | Private
  | NoExtract
  | CInline
  | Substitute
  | GCType
  | PpxDerivingShow
  | PpxDerivingShowConstant of string
  | PpxDerivingYoJson
  | Comment of string
  | StackInline
  | CPrologue of string
  | CEpilogue of string
  | CConst of string
  | CCConv of string
  | Erased
  | CAbstract
  | CIfDef
  | CMacro
  | Deprecated of string
  | RemoveUnusedTypeParameters of list int & FStar.Compiler.Range.range //positional
  | HasValDecl of FStar.Compiler.Range.range //this symbol appears in the interface of a module
  | CNoInline

// rename
type metadata = list meta

type mlletflavor =
  | Rec
  | NonRec

type mlbinder = {
  mlbinder_name:mlident;
  mlbinder_ty:mlty;
  mlbinder_attrs:list mlattribute;
}

and mlexpr' =
| MLE_Const  of mlconstant
| MLE_Var    of mlident
| MLE_Name   of mlpath
| MLE_Let    of mlletbinding & mlexpr //tyscheme for polymorphic recursion
| MLE_App    of mlexpr & list mlexpr //why are function types curried, but the applications not curried
| MLE_TApp   of mlexpr & list mlty
| MLE_Fun    of list mlbinder & mlexpr
| MLE_Match  of mlexpr & list mlbranch
| MLE_Coerce of mlexpr & mlty & mlty
(* SUGAR *)
| MLE_CTor   of mlpath & list mlexpr
| MLE_Seq    of list mlexpr
| MLE_Tuple  of list mlexpr
| MLE_Record of list mlsymbol & mlsymbol & list (mlsymbol & mlexpr) // path of record type,
                                                                    // name of record type,
                                                                    // and fields with values
| MLE_Proj   of mlexpr & mlpath
| MLE_If     of mlexpr & mlexpr & option mlexpr
| MLE_Raise  of mlpath & list mlexpr
| MLE_Try    of mlexpr & list mlbranch

and mlexpr = {
    expr:mlexpr';
    mlty:mlty;
    loc: mlloc;
}

and mlbranch = mlpattern & option mlexpr & mlexpr

and mllb = {
    mllb_name:mlident;
    mllb_tysc:option mltyscheme; // May be None for top-level bindings only
    mllb_add_unit:bool;
    mllb_def:mlexpr;
    mllb_attrs:list mlattribute;
    mllb_meta:metadata;
    print_typ:bool;
}

and mlletbinding = mlletflavor & list mllb

and mlattribute = mlexpr

and ty_param = {
  ty_param_name : mlident;
  ty_param_attrs : list mlattribute;
}

and mltyscheme = list ty_param & mlty   //forall a1..an. t  (the list of binders can be empty)

type mltybody =
| MLTD_Abbrev of mlty
| MLTD_Record of list (mlsymbol & mlty)
| MLTD_DType  of list (mlsymbol & list (mlsymbol & mlty))
    (*list of constructors? list mlty is the list of arguments of the constructors?
        One could have instead used a mlty and tupled the argument types?
     *)

type one_mltydecl = {
  tydecl_assumed : bool; // bool: this was assumed (C backend)
  tydecl_name    : mlsymbol;
  tydecl_ignored : option mlsymbol;
  tydecl_parameters : list ty_param;
  tydecl_meta    : metadata;
  tydecl_defn    : option mltybody
}

type mltydecl = list one_mltydecl // each element of this list is one among a collection of mutually defined types

type mlmodule1' =
| MLM_Ty  of mltydecl
| MLM_Let of mlletbinding
| MLM_Exn of mlsymbol & list (mlsymbol & mlty)
| MLM_Top of mlexpr // this seems outdated
| MLM_Loc of mlloc // Location information; line number + file; only for the OCaml backend

type mlmodule1 = {
  mlmodule1_m : mlmodule1';
  mlmodule1_attrs : list mlattribute;
}

let mk_mlmodule1 m = { mlmodule1_m = m; mlmodule1_attrs = [] }
let mk_mlmodule1_with_attrs m attrs = { mlmodule1_m = m; mlmodule1_attrs = attrs }

type mlmodule = list mlmodule1

type mlsig1 =
| MLS_Mod of mlsymbol & mlsig
| MLS_Ty  of mltydecl
    (*used for both type schemes and inductive types. Even inductives are defined in OCaml using type ....,
        unlike data in Haskell *)
| MLS_Val of mlsymbol & mltyscheme
| MLS_Exn of mlsymbol & list mlty

and mlsig = list mlsig1

let with_ty_loc t e l = {expr=e; mlty=t; loc = l }
let with_ty t e = with_ty_loc t e dummy_loc

(* -------------------------------------------------------------------- *)
type mllib =
  | MLLib of list (mlpath & option (mlsig & mlmodule) & mllib) //Last field never seems to be used. Refactor?

(* -------------------------------------------------------------------- *)
// do NOT remove Prims, because all mentions of unit/bool in F* are actually Prims.unit/bool.
let ml_unit_ty = MLTY_Erased
let ml_bool_ty = MLTY_Named ([], (["Prims"], "bool"))
let ml_int_ty  = MLTY_Named ([], (["Prims"], "int"))
let ml_string_ty  = MLTY_Named ([], (["Prims"], "string"))
let ml_unit    = with_ty ml_unit_ty (MLE_Const MLC_Unit)
let mlp_lalloc = (["SST"], "lalloc")
let apply_obj_repr :  mlexpr -> mlty -> mlexpr = fun x t ->
    let repr_name = if Options.codegen() = Some Options.FSharp
                    then MLE_Name([], "box")
                    else MLE_Name(["Obj"], "repr") in
    let obj_repr = with_ty (MLTY_Fun(t, E_PURE, MLTY_Top)) repr_name in
    with_ty_loc MLTY_Top (MLE_App(obj_repr, [x])) x.loc

let ty_param_names (tys:list ty_param) =
  tys |> List.map (fun {ty_param_name} -> ty_param_name)

open FStar.Syntax.Syntax

let push_unit (ts : mltyscheme) : mltyscheme =
    let vs, ty = ts in
    vs, MLTY_Fun(ml_unit_ty, E_PURE, ty)

let pop_unit (ts : mltyscheme) : mltyscheme =
    let vs, ty = ts in
    match ty with
    | MLTY_Fun (l, E_PURE, t) ->
        if l = ml_unit_ty
        then vs, t
        else failwith "unexpected: pop_unit: domain was not unit"
    | _ ->
        failwith "unexpected: pop_unit: not a function type"
module BU = FStar.Compiler.Util

let mlpath_to_string mlp = String.concat "." (fst mlp) ^ "." ^ snd mlp

let rec mlty_to_string (t:mlty) =
  match t with
  | MLTY_Var v -> v
  | MLTY_Fun (t1, _, t2) ->
    BU.format2 "(<MLTY_Fun> %s -> %s)" (mlty_to_string t1) (mlty_to_string t2)
  | MLTY_Named (ts, p) ->
    BU.format2 "(<MLTY_Named> %s %s)" (String.concat " " (List.map mlty_to_string ts)) (mlpath_to_string p)
  | MLTY_Tuple ts ->
    BU.format1 "(<MLTY_Tuple> %s)" (String.concat " * " (List.map mlty_to_string ts))
  | MLTY_Top -> "MLTY_Top"
  | MLTY_Erased -> "MLTY_Erased"

let mltyscheme_to_string (tsc:mltyscheme) =
  BU.format2 "(<MLTY_Scheme> [%s], %s)"
    (String.concat ", " (tsc |> fst |> ty_param_names))
    (mlty_to_string (snd tsc))

let rec mlexpr_to_string (e:mlexpr) =
  match e.expr with
  | MLE_Const c ->
    BU.format1 "(MLE_Const %s)" (mlconstant_to_string c)
  | MLE_Var x ->
    BU.format1 "(MLE_Var %s)" x
  | MLE_Name (p, x) ->
    BU.format2 "(MLE_Name (%s, %s))" (String.concat "." p) x
  | MLE_Let (lbs, e) ->
    BU.format2 "(MLE_Let (%s, %s))" (mlletbinding_to_string lbs) (mlexpr_to_string e)
  | MLE_App (e, es) ->
    BU.format2 "(MLE_App (%s, [%s]))" (mlexpr_to_string e) (String.concat "; " (List.map mlexpr_to_string es))
  | MLE_TApp (e, ts) ->
    BU.format2 "(MLE_TApp (%s, [%s]))" (mlexpr_to_string e) (String.concat "; " (List.map mlty_to_string ts))
  | MLE_Fun (bs, e) ->
    BU.format2 "(MLE_Fun ([%s], %s))"
      (String.concat "; " (List.map (fun b -> BU.format2 "(%s, %s)" b.mlbinder_name (mlty_to_string b.mlbinder_ty)) bs))
      (mlexpr_to_string e)
  | MLE_Match (e, bs) ->
    BU.format2 "(MLE_Match (%s, [%s]))" (mlexpr_to_string e) (String.concat "; " (List.map mlbranch_to_string bs))
  | MLE_Coerce (e, t1, t2) ->
    BU.format3 "(MLE_Coerce (%s, %s, %s))" (mlexpr_to_string e) (mlty_to_string t1) (mlty_to_string t2)
  | MLE_CTor (p, es) ->
    BU.format2 "(MLE_CTor (%s, [%s]))" (mlpath_to_string p) (String.concat "; " (List.map mlexpr_to_string es))
  | MLE_Seq es ->
    BU.format1 "(MLE_Seq [%s])" (String.concat "; " (List.map mlexpr_to_string es))
  | MLE_Tuple es ->
    BU.format1 "(MLE_Tuple [%s])" (String.concat "; " (List.map mlexpr_to_string es))
  | MLE_Record (p, n, es) ->
    BU.format2 "(MLE_Record (%s, [%s]))" (String.concat "; " (p@[n])) (String.concat "; " (List.map (fun (x, e) -> BU.format2 "(%s, %s)" x (mlexpr_to_string e)) es))
  | MLE_Proj (e, p) ->
    BU.format2 "(MLE_Proj (%s, %s))" (mlexpr_to_string e) (mlpath_to_string p)
  | MLE_If (e1, e2, None) ->
    BU.format2 "(MLE_If (%s, %s, None))" (mlexpr_to_string e1) (mlexpr_to_string e2)
  | MLE_If (e1, e2, Some e3) ->
    BU.format3 "(MLE_If (%s, %s, %s))" (mlexpr_to_string e1) (mlexpr_to_string e2) (mlexpr_to_string e3)
  | MLE_Raise (p, es) ->
    BU.format2 "(MLE_Raise (%s, [%s]))" (mlpath_to_string p) (String.concat "; " (List.map mlexpr_to_string es))
  | MLE_Try (e, bs) ->
    BU.format2 "(MLE_Try (%s, [%s]))" (mlexpr_to_string e) (String.concat "; " (List.map mlbranch_to_string bs))

and mlbranch_to_string (p, e1, e2) =
  match e1 with
  | None -> BU.format2 "(%s, None, %s)" (mlpattern_to_string p) (mlexpr_to_string e2)
  | Some e1 -> BU.format3 "(%s, Some %s, %s)" (mlpattern_to_string p) (mlexpr_to_string e1) (mlexpr_to_string e2)

and mlletbinding_to_string (lbs) =
  match lbs with
  | (Rec, lbs) -> BU.format1 "(Rec, [%s])" (String.concat "; " (List.map mllb_to_string lbs))
  | (NonRec, lbs) -> BU.format1 "(NonRec, [%s])" (String.concat "; " (List.map mllb_to_string lbs))

and mllb_to_string (lb) =
  BU.format4 "{mllb_name = %s; mllb_tysc = %s; mllb_add_unit = %s; mllb_def = %s}"
    lb.mllb_name
    (match lb.mllb_tysc with
     | None -> "None"
     | Some (_, t) -> BU.format1 "Some %s" (mlty_to_string t))
    (string_of_bool lb.mllb_add_unit)
    (mlexpr_to_string lb.mllb_def)

and mlconstant_to_string mlc =
  match mlc with
  | MLC_Unit -> "MLC_Unit"
  | MLC_Bool b -> BU.format1 "(MLC_Bool %s)" (string_of_bool b)
  | MLC_Int (s, None) -> BU.format1 "(MLC_Int %s)" s
  | MLC_Int (s, Some (s1, s2)) -> BU.format1 "(MLC_Int (%s, _, _))" s
  | MLC_Float f -> "(MLC_Float _)"
  | MLC_Char c -> "(MLC_Char _)"
  | MLC_String s -> BU.format1 "(MLC_String %s)" s
  | MLC_Bytes b -> "(MLC_Bytes _)" 

and mlpattern_to_string mlp =
  match mlp with
  | MLP_Wild -> "MLP_Wild"
  | MLP_Const c -> BU.format1 "(MLP_Const %s)" (mlconstant_to_string c)
  | MLP_Var x -> BU.format1 "(MLP_Var %s)" x
  | MLP_CTor (p, ps) -> BU.format2 "(MLP_CTor (%s, [%s]))" (mlpath_to_string p) (String.concat "; " (List.map mlpattern_to_string ps))
  | MLP_Branch ps -> BU.format1 "(MLP_Branch [%s])" (String.concat "; " (List.map mlpattern_to_string ps))
  | MLP_Record (p, ps) -> BU.format2 "(MLP_Record (%s, [%s]))" (String.concat "; " p) (String.concat "; " (List.map (fun (x, p) -> BU.format2 "(%s, %s)" x (mlpattern_to_string p)) ps))
  | MLP_Tuple ps -> BU.format1 "(MLP_Tuple [%s])" (String.concat "; " (List.map mlpattern_to_string ps))

let mltybody_to_string (d:mltybody) : string =
  match d with
  | MLTD_Abbrev mlty -> BU.format1 "(MLTD_Abbrev %s)" (mlty_to_string mlty)
  | MLTD_Record l ->
    BU.format1 "(MLTD_Record { %s })"
      (String.concat "; " (List.map (fun (x, t) -> BU.format2 "(%s, %s)" x (mlty_to_string t)) l))
  | MLTD_DType l ->
    BU.format1 "(MLTD_DType [ %s ])"
      (String.concat "; " (List.map (fun (x, l) -> BU.format2 "(%s, [%s])" x
                                                     (String.concat "; " (List.map (fun (x, t) -> BU.format2 "(%s, %s)"
                                                                                                    x
                                                                                                    (mlty_to_string t)) l))) l))

let one_mltydecl_to_string (d:one_mltydecl) : string =
  BU.format3 "{tydecl_name = %s; tydecl_parameters = %s; tydecl_defn = %s}"
    d.tydecl_name
    (String.concat "," (d.tydecl_parameters |> ty_param_names))
    (match d.tydecl_defn with
     | None -> "<none>"
     | Some d -> mltybody_to_string d)

let mlmodule1_to_string (m:mlmodule1) : string =
  match m.mlmodule1_m with
  | MLM_Ty d -> BU.format1 "MLM_Ty [%s]" (List.map one_mltydecl_to_string d |> String.concat "; ")
  | MLM_Let l -> BU.format1 "MLM_Let %s" (mlletbinding_to_string l)
  | MLM_Exn (s, l) ->
    BU.format2 "MLM_Exn (%s, [%s])"
      s
      (String.concat "; " (List.map (fun (x, t) -> BU.format2 "(%s, %s)" x (mlty_to_string t)) l))
  | MLM_Top e -> BU.format1 "MLM_Top %s" (mlexpr_to_string e)
  | MLM_Loc _mlloc -> "MLM_Loc"

instance showable_mlmodule1 : showable mlmodule1 = { show = mlmodule1_to_string }

let mlmodule_to_string (m:mlmodule) : string =
  BU.format1 "[ %s ]" (List.map mlmodule1_to_string m |> String.concat ";\n")

instance showable_mlmodule : showable mlmodule = { show = mlmodule_to_string }
