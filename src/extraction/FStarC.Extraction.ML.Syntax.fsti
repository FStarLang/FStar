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
module FStarC.Extraction.ML.Syntax

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Ident
open FStarC.Util
open FStarC.Const
open FStarC.BaseTypes

open FStarC.Class.Show

(* -------------------------------------------------------------------- *)
type mlsymbol = string
type mlident  = mlsymbol
type mlpath   = list mlsymbol & mlsymbol //Path and name of a module

(* -------------------------------------------------------------------- *)
val krml_keywords  : list string
val ocamlkeywords  : list string
val fsharpkeywords : list string

val string_of_mlpath : mlpath -> string

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
val dummy_loc : mlloc

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
| MLC_Bytes  of FStarC.Array.array byte

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
  | RemoveUnusedTypeParameters of list int & FStarC.Range.range //positional
  | HasValDecl of FStarC.Range.range //this symbol appears in the interface of a module
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

val mk_mlmodule1 : mlmodule1' -> mlmodule1
val mk_mlmodule1_with_attrs : mlmodule1' -> list mlattribute -> mlmodule1

type mlmodulebody = list mlmodule1

type mlsig1 =
| MLS_Mod of mlsymbol & mlsig
| MLS_Ty  of mltydecl
    (*used for both type schemes and inductive types. Even inductives are defined in OCaml using type ....,
        unlike data in Haskell *)
| MLS_Val of mlsymbol & mltyscheme
| MLS_Exn of mlsymbol & list mlty

and mlsig = list mlsig1

val with_ty_loc : mlty -> mlexpr' -> mlloc -> mlexpr
val with_ty     : mlty -> mlexpr' -> mlexpr

(* -------------------------------------------------------------------- *)
type mlmodule = mlpath & option (mlsig & mlmodulebody)

(* -------------------------------------------------------------------- *)
val ml_unit_ty   : mlty
val ml_bool_ty   : mlty
val ml_int_ty    : mlty
val ml_string_ty : mlty

val ml_unit      : mlexpr

val apply_obj_repr :  mlexpr -> mlty -> mlexpr

val ty_param_names (tys:list ty_param) : list string

val push_unit (eff:e_tag) (ts : mltyscheme) : mltyscheme
val pop_unit (ts : mltyscheme) : e_tag & mltyscheme

val mltyscheme_to_string (tsc:mltyscheme) : string
val mlbranch_to_string (b:mlbranch) : string
val mlletbinding_to_string (lb:mlletbinding) : string
val mllb_to_string (lb:mllb) : string
val mlpattern_to_string (p:mlpattern) : string

val mlconstant_to_string   (c:mlconstant)   : string
val mlty_to_string         (t:mlty)         : string
val mlexpr_to_string       (e:mlexpr)       : string
val mltybody_to_string     (d:mltybody)     : string
val one_mltydecl_to_string (d:one_mltydecl) : string
val mlmodule1_to_string    (d:mlmodule1)    : string

instance val showable_mlty      : showable mlty
instance val showable_mlconstant : showable mlconstant
instance val showable_mlexpr     : showable mlexpr
instance val showable_mlmodule1 : showable mlmodule1
instance val showable_mlmodulebody : showable mlmodulebody
