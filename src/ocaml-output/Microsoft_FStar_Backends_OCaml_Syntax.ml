
type mlsymbol =
string

type mlident =
(mlsymbol * int)

type mlpath =
(mlsymbol list * mlsymbol)

let idsym = (fun _493757 -> (match (_493757) with
| (s, _) -> begin
s
end))

let ptsym = (fun _493760 -> (match (_493760) with
| (p, s) -> begin
(let s = if ((Support.Char.lowercase (Support.String.get s 0)) <> (Support.String.get s 0)) then begin
(Support.String.strcat "l__" s)
end else begin
s
end
in (Support.String.concat "." (Support.List.append p ((s)::[]))))
end))

let ptctor = (fun _493764 -> (match (_493764) with
| (p, s) -> begin
(let s = if ((Support.Char.uppercase (Support.String.get s 0)) <> (Support.String.get s 0)) then begin
(Support.String.strcat "U__" s)
end else begin
s
end
in (Support.String.concat "." (Support.List.append p ((s)::[]))))
end))

let mlpath_of_lident = (fun x -> ((Support.List.map (fun x -> x.Microsoft_FStar_Absyn_Syntax.idText) x.Microsoft_FStar_Absyn_Syntax.ns), x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText))

type mlidents =
mlident list

type mlsymbols =
mlsymbol list

type mlty =
| MLTY_Var of mlident
| MLTY_Fun of (mlty * mlty)
| MLTY_Named of (mlty list * mlpath)
| MLTY_Tuple of mlty list
| MLTY_App of (mlty * mlty)

type mltyscheme =
(mlidents * mlty)

type mlconstant =
| MLC_Unit
| MLC_Bool of bool
| MLC_Byte of Support.Prims.byte
| MLC_Int32 of Support.Prims.int32
| MLC_Int64 of Int64.t
| MLC_Float of Support.Prims.float
| MLC_Char of char
| MLC_String of string
| MLC_Bytes of Support.Prims.byte array

type mlpattern =
| MLP_Wild
| MLP_Const of mlconstant
| MLP_Var of mlident
| MLP_Record of (mlsymbol list * (mlsymbol * mlpattern) list)
| MLP_CTor of (mlpath * mlpattern list)
| MLP_Tuple of mlpattern list
| MLP_Branch of mlpattern list

type mlexpr =
| MLE_Seq of mlexpr list
| MLE_Const of mlconstant
| MLE_Var of mlident
| MLE_Name of mlpath
| MLE_Record of (mlsymbol list * (mlsymbol * mlexpr) list)
| MLE_CTor of (mlpath * mlexpr list)
| MLE_Tuple of mlexpr list
| MLE_Let of (bool * (mlident * mlidents * mlexpr) list * mlexpr)
| MLE_App of (mlexpr * mlexpr list)
| MLE_Proj of (mlexpr * mlpath)
| MLE_Fun of (mlidents * mlexpr)
| MLE_If of (mlexpr * mlexpr * mlexpr option)
| MLE_Match of (mlexpr * mlbranch list)
| MLE_Raise of (mlpath * mlexpr list)
| MLE_Try of (mlexpr * mlbranch list) and mlbranch =
(mlpattern * mlexpr option * mlexpr)

type mltybody =
| MLTD_Abbrev of mlty
| MLTD_Record of (mlsymbol * mlty) list
| MLTD_DType of (mlsymbol * mlty list) list

type mltydecl =
(mlsymbol * mlidents * mltybody option) list

type mlmodule1 =
| MLM_Ty of mltydecl
| MLM_Let of (bool * (mlsymbol * mlidents * mlexpr) list)
| MLM_Exn of (mlsymbol * mlty list)
| MLM_Top of mlexpr

type mlmodule =
mlmodule1 list

type mlsig1 =
| MLS_Mod of (mlsymbol * mlsig)
| MLS_Ty of mltydecl
| MLS_Val of (mlsymbol * mltyscheme)
| MLS_Exn of (mlsymbol * mlty list) and mlsig =
mlsig1 list

type mllib =
| MLLib of (mlsymbol * (mlsig * mlmodule) option * mllib) list

let mlseq = (fun e1 e2 -> (match (e2) with
| MLE_Seq (s) -> begin
MLE_Seq ((e1)::s)
end
| _ -> begin
MLE_Seq ((e1)::(e2)::[])
end))

let mlfun = (fun x e -> (match (e) with
| MLE_Fun ((xs, e)) -> begin
MLE_Fun (((x)::xs, e))
end
| _ -> begin
MLE_Fun (((x)::[], e))
end))

let mlif = (fun b _493876 -> (match (_493876) with
| (e1, e2) -> begin
(match (e2) with
| MLE_Const (MLC_Unit) -> begin
MLE_If ((b, e1, None))
end
| _ -> begin
MLE_If ((b, e1, Some (e2)))
end)
end))




