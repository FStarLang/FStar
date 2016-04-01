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
#light "off"
(* -------------------------------------------------------------------- *)
module FStar.Extraction.ML.Syntax
open FStar
open FStar.Absyn.Syntax
open FStar.Ident
open FStar.Util
open FStar.Const
open FStar.BaseTypes

(* -------------------------------------------------------------------- *)
type mlsymbol = string
type mlident  = mlsymbol * int //what is the second component? Why do we need it?
type mlpath   = list<mlsymbol> * mlsymbol

(* -------------------------------------------------------------------- *)
let idsym ((s, _) : mlident) : mlsymbol =
    s

let string_of_mlpath ((p, s) : mlpath) : mlsymbol =
    String.concat "." (p @ [s])

type gensym_t = {
    gensym: unit -> mlident;
    reset:unit -> unit;
}

let gs =
  let ctr = Util.mk_ref 0 in
  let n_resets = Util.mk_ref 0 in
  {gensym =(fun () -> "_" ^ (Util.string_of_int !n_resets) ^ "_" ^ (Util.string_of_int (incr ctr; !ctr)), 0);
   reset = (fun () -> ctr := 0; incr n_resets)}

let gensym () = gs.gensym()
let reset_gensym() = gs.reset()
let rec gensyms x = match x with
  | 0 -> []
  | n -> gensym ()::gensyms (n-1)

(* -------------------------------------------------------------------- *)
let mlpath_of_lident (x : lident) : mlpath =
    (List.map (fun x -> x.idText) x.ns, x.ident.idText)

let as_mlident (x:bvdef<'a>) = x.ppname.idText, 0

(* -------------------------------------------------------------------- *)
type mlidents  = list<mlident>
type mlsymbols = list<mlsymbol>

(* -------------------------------------------------------------------- *)
type e_tag =
  | E_PURE
  | E_GHOST
  | E_IMPURE

// Line number, file name; that's all we can emit in OCaml anyhwow
type mlloc = int * string
let dummy_loc: mlloc = 0, ""

type mlty =
| MLTY_Var   of mlident
| MLTY_Fun   of mlty * e_tag * mlty 
| MLTY_Named of list<mlty> * mlpath
| MLTY_Tuple of list<mlty>
| MLTY_Top

type mltyscheme = mlidents * mlty   //forall a1..an. t  (the list of binders can be empty)

type mlconstant =
| MLC_Unit
| MLC_Bool   of bool
| MLC_Int    of string * option<(signedness * width)>
| MLC_Float  of float
| MLC_Char   of char
| MLC_String of string
| MLC_Bytes  of array<byte>

type mlpattern =
| MLP_Wild
| MLP_Const  of mlconstant
| MLP_Var    of mlident
| MLP_CTor   of mlpath * list<mlpattern>
| MLP_Branch of list<mlpattern>
(* SUGAR *)
| MLP_Record of list<mlsymbol> * list<(mlsymbol * mlpattern)>
| MLP_Tuple  of list<mlpattern>

type mlexpr' =
| MLE_Const  of mlconstant
| MLE_Var    of mlident
| MLE_Name   of mlpath
| MLE_Let    of mlletbinding * mlexpr //tyscheme for polymorphic recursion
| MLE_App    of mlexpr * list<mlexpr> //why are function types curried, but the applications not curried
| MLE_Fun    of list<(mlident * mlty)> * mlexpr
| MLE_Match  of mlexpr * list<mlbranch>
| MLE_Coerce of mlexpr * mlty * mlty
(* SUGAR *)
| MLE_CTor   of mlpath * list<mlexpr>
| MLE_Seq    of list<mlexpr>
| MLE_Tuple  of list<mlexpr>
| MLE_Record of list<mlsymbol> * list<(mlsymbol * mlexpr)>
| MLE_Proj   of mlexpr * mlpath
| MLE_If     of mlexpr * mlexpr * option<mlexpr>
| MLE_Raise  of mlpath * list<mlexpr>
| MLE_Try    of mlexpr * list<mlbranch>

and mlexpr = {
    expr:mlexpr';
    mlty:mlty;
    loc: mlloc;
}

and mlbranch = mlpattern * option<mlexpr> * mlexpr

and mllb = {
    mllb_name:mlident;
    mllb_tysc:option<mltyscheme>; // May be None for top-level bindings only
    mllb_add_unit:bool;
    mllb_def:mlexpr;
    print_typ:bool;
}

and mlletbinding = bool * list<mllb>

type mltybody =
| MLTD_Abbrev of mlty
| MLTD_Record of list<(mlsymbol * mlty)>
| MLTD_DType  of list<(mlsymbol * list<mlty>)>
    (*list of constructors? list<mlty> is the list of arguments of the constructors?
        One could have instead used a mlty and tupled the argument types?
     *)

type mltydecl = list<(mlsymbol * mlidents * option<mltybody>)> // each element of this list is one among a collection of mutually defined types

type mlmodule1 =
| MLM_Ty  of mltydecl
| MLM_Let of mlletbinding
| MLM_Exn of mlsymbol * list<mlty>
| MLM_Top of mlexpr
| MLM_Loc of mlloc // Location information; line number + file; only for the OCaml backend

type mlmodule = list<mlmodule1>

type mlsig1 =
| MLS_Mod of mlsymbol * mlsig
| MLS_Ty  of mltydecl
    (*used for both type schemes and inductive types. Even inductives are defined in OCaml using type ....,
        unlike data in Haskell *)
| MLS_Val of mlsymbol * mltyscheme
| MLS_Exn of mlsymbol * list<mlty>

and mlsig = list<mlsig1>

let with_ty_loc t e l = {expr=e; mlty=t; loc = l }
let with_ty t e = with_ty_loc t e dummy_loc

(* -------------------------------------------------------------------- *)
type mllib =
  | MLLib of list<(mlsymbol * option<(mlsig * mlmodule)> * mllib)>

(* -------------------------------------------------------------------- *)
// do NOT remove Prims, because all mentions of unit/bool in F* are actually Prims.unit/bool.
let ml_unit_ty = MLTY_Named ([], (["Prims"], "unit"))
let ml_bool_ty = MLTY_Named ([], (["Prims"], "bool"))
let ml_int_ty  = MLTY_Named ([], (["Prims"], "int"))
let ml_string_ty  = MLTY_Named ([], (["Prims"], "string"))
let ml_unit    = with_ty ml_unit_ty (MLE_Const MLC_Unit) 
let mlp_lalloc = (["SST"], "lalloc")
let apply_obj_repr x t = 
    let obj_repr = with_ty (MLTY_Fun(t, E_PURE, MLTY_Top)) (MLE_Name(["Obj"], "repr")) in
    with_ty_loc MLTY_Top (MLE_App(obj_repr, [x])) x.loc

open FStar.Syntax.Syntax
let bv_as_mlident (x:bv) = 
    if Util.starts_with x.ppname.idText Ident.reserved_prefix
    || is_null_bv x
    then x.ppname.idText ^ "_" ^ (string_of_int x.index), 0
    else x.ppname.idText, 0
