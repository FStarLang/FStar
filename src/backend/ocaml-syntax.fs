(* -------------------------------------------------------------------- *)
module Microsoft.FStar.Backends.OCaml.Syntax

open Microsoft.FStar.Absyn.Syntax

(* -------------------------------------------------------------------- *)
type mlsymbol = string
type mlident  = mlsymbol * int
type mlpath   = list<mlsymbol> * mlsymbol

(* -------------------------------------------------------------------- *)
let idsym ((s, _) : mlident) : mlsymbol =
    s

let ptsym ((_, s) : mlpath) : mlsymbol =
    s

(* -------------------------------------------------------------------- *)
let mlpath_of_lident (x : lident) : mlpath =
    (List.map (fun x -> x.idText) x.ns, x.ident.idText)

(* -------------------------------------------------------------------- *)
type mlidents  = list<mlident>
type mlsymbols = list<mlsymbol>

(* -------------------------------------------------------------------- *)
type mlty =
| MLTY_Var   of mlident
| MLTY_Fun   of mlty * mlty
| MLTY_Named of list<mlty> * mlpath
| MLTY_Tuple of list<mlty>

type mltyscheme = mlidents * mlty

type mlconstant =
| MLC_Unit
| MLC_Bool   of bool
| MLC_Byte   of byte
| MLC_Int    of int64
| MLC_Float  of float
| MLC_Char   of char
| MLC_String of string
| MLC_Bytes  of byte array

type mlpattern =
| MLP_Wild
| MLP_Const  of mlconstant
| MLP_Var    of mlident
| MLP_Record of mlpath * list<mlsymbol * mlpattern>
| MLP_CTor   of mlpath * list<mlpattern>
| MLP_Tuple  of list<mlpattern>
| MLP_Branch of list<mlpattern>

type mlexpr =
| MLE_Seq    of list<mlexpr>
| MLE_Const  of mlconstant
| MLE_Var    of mlident
| MLE_Name   of mlpath
| MLE_Record of mlpath * list<mlsymbol * mlexpr>
| MLE_CTor   of mlpath * list<mlexpr>
| MLE_Tuple  of mlexpr list
| MLE_Let    of bool * list<mlident * mlidents * mlexpr> * mlexpr
| MLE_App    of mlexpr * list<mlexpr>
| MLE_Fun    of mlidents * mlexpr
| MLE_If     of mlexpr * mlexpr * option<mlexpr>
| MLE_Match  of mlexpr * list<mlpattern * option<mlexpr> * mlexpr>
| MLE_Raise  of mlpath * list<mlexpr>
| MLE_Try    of mlexpr * list<mlpattern * option<mlexpr> * mlexpr>

type mltybody =
| MLTD_Abbrev of mlty
| MLTD_Record of list<mlsymbol * mlty>
| MLTD_DType  of list<mlsymbol * mlty list>

type mlmodule1 =
| MLM_Ty  of list<mlsymbol * mlidents * option<mltybody>>
| MLM_Let of bool * list<mlsymbol * mlidents * mlexpr>
| MLM_Exn of mlsymbol * list<mlty>
| MLM_Top of mlexpr

type mlmodule = list<mlmodule1>

type mlsig1 =
| MLS_Ty  of list<mlsymbol * mlidents * option<mltybody>>
| MLS_Val of mlsymbol * mltyscheme
| MLS_Exn of mlsymbol * list<mlty>

type mlsig = list<mlsig1>

(* -------------------------------------------------------------------- *)
let mlseq (e1 : mlexpr) (e2 : mlexpr) =
    match e2 with
    | MLE_Seq s -> MLE_Seq (e1 :: s)
    | _ -> MLE_Seq [e1; e2]

let mlfun (x : mlident) (e : mlexpr) =
    match e with
    | MLE_Fun (xs, e) -> MLE_Fun(x :: xs, e)
    | _ -> MLE_Fun ([x], e)

let mlif (b : mlexpr) ((e1, e2) : mlexpr * mlexpr) =
    match e2 with
    | MLE_Const MLC_Unit -> MLE_If (b, e1, None)
    | _ -> MLE_If (b, e1, Some e2)
