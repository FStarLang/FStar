(* -------------------------------------------------------------------- *)
module FStar.Extraction.ML.Syntax
open FStar
open FStar.Absyn.Syntax

(* -------------------------------------------------------------------- *)
type mlsymbol = string
type mlident  = mlsymbol * int //what is the second component? Why do we need it?
type mlpath   = list<mlsymbol> * mlsymbol

(* -------------------------------------------------------------------- *)
let idsym ((s, _) : mlident) : mlsymbol =
    s

let string_of_mlpath ((p, s) : mlpath) : mlsymbol =
    String.concat "." (p @ [s])



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
| MLC_Byte   of byte
| MLC_Int32  of int32
| MLC_Int64  of int64
| MLC_Int    of string
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

type mlexpr =
| MLE_Const  of mlconstant
| MLE_Var    of mlident
| MLE_Name   of mlpath
| MLE_Let    of mlletbinding * mlexpr //tyscheme for polymorphic recursion
| MLE_App    of mlexpr * list<mlexpr> //why are function types curried, but the applications not curried
| MLE_Fun    of list<(mlident * (option<mlty>))> * mlexpr
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

and mlbranch = mlpattern * option<mlexpr> * mlexpr

and mllb = {
    mllb_name:mlident;
    mllb_tysc:option<mltyscheme>;
    mllb_add_unit:bool;
    mllb_def:mlexpr;
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

type mlmodule = list<mlmodule1>

type mlsig1 =
| MLS_Mod of mlsymbol * mlsig
| MLS_Ty  of mltydecl
    (*used for both type schemes and inductive types. Even inductives are defined in OCaml using type ....,
        unlike data in Haskell *)
| MLS_Val of mlsymbol * mltyscheme
| MLS_Exn of mlsymbol * list<mlty>

and mlsig = list<mlsig1>

(* -------------------------------------------------------------------- *)
type mllib =
  | MLLib of list<(mlsymbol * option<(mlsig * mlmodule)> * mllib)>

(* -------------------------------------------------------------------- *)
let mlseq (e1 : mlexpr) (e2 : mlexpr) =
    match e2 with
    | MLE_Seq s -> MLE_Seq (e1 :: s)
    | _ -> MLE_Seq [e1; e2]

let mlfun (x : mlident) (e : mlexpr) =
    match e with
    | MLE_Fun (xs, e) -> MLE_Fun((x,None) :: xs, e)
    | _ -> MLE_Fun ([x,None], e)

let mlif (b : mlexpr) ((e1, e2) : mlexpr * mlexpr) =
    match e2 with
    | MLE_Const MLC_Unit -> MLE_If (b, e1, None)
    | _ -> MLE_If (b, e1, Some e2)


let ml_unit    = MLE_Const MLC_Unit

// do NOT remove Prims, because all mentions of unit/bool in F* are actually Prims.unit/bool.
let ml_bool_ty = MLTY_Named ([], (["Prims"], "bool"))
let ml_unit_ty = MLTY_Named ([], (["Prims"], "unit"))

let mlp_lalloc = (["SST"], "lalloc")
