module Microsoft.FStar.Backends.OCaml.Syntax

type mlsymbol = string
type mlident  = mlsymbol * int
type mlpath   = list<mlsymbol> * mlsymbol

type mlidents  = list<mlident>
type mlsymbols = list<mlsymbol>

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
| MLC_Int    of int
| MLC_Char   of char
| MLC_String of string

type mlpattern =
| MLP_Wild
| MLP_Const  of mlconstant
| MLP_Var    of mlident
| MLP_Record of mlpath * list<mlsymbol * mlpattern>
| MLP_CTor   of mlpath * list<mlpattern>
| MLP_Tuple  of list<mlpattern>
| MLP_Named  of mlident * mlpattern

type mlexpr =
| MLE_Const  of mlconstant
| MLE_Var    of mlident
| MLE_Name   of mlpath
| MLE_Record of mlpath * list<mlsymbol * mlexpr>
| MLE_CTor   of mlpath * list<mlexpr>
| MLE_Tuple  of mlexpr list
| MLE_Let    of bool * list<mlident * mlidents * mlexpr>
| MLE_App    of mlexpr * list<mlexpr>
| MLE_Fun    of mlidents * mlexpr
| MLE_Match  of mlexpr * list<mlpattern * option<mlexpr> * mlexpr>

type mltybody =
| MLTD_Abbrev of mlty
| MLTD_Record of list<mlsymbol * mlty>
| MLTD_DType  of list<mlsymbol * mlty list>

type module1 =
| MLM_Ty  of list<mlidents * mltybody>
| MLM_Let of bool * list<mlsymbol * mlidents * mlexpr>

type module_ = list<module1>

type sig1 =
| MLS_Ty  of (mlident list * mltybody option) list
| MLS_Val of mltyscheme

type sig_ = list<sig1>
