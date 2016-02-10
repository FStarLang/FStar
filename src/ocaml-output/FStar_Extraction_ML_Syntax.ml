
open Prims
# 8 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

type mlsymbol =
Prims.string

# 9 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

type mlident =
(mlsymbol * Prims.int)

# 10 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

type mlpath =
(mlsymbol Prims.list * mlsymbol)

# 13 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let idsym : mlident  ->  mlsymbol = (fun _73_4 -> (match (_73_4) with
| (s, _73_3) -> begin
s
end))

# 16 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let string_of_mlpath : mlpath  ->  mlsymbol = (fun _73_7 -> (match (_73_7) with
| (p, s) -> begin
(FStar_String.concat "." (FStar_List.append p ((s)::[])))
end))

# 22 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let mlpath_of_lident : FStar_Ident.lident  ->  (Prims.string Prims.list * Prims.string) = (fun x -> (let _175_8 = (FStar_List.map (fun x -> x.FStar_Ident.idText) x.FStar_Ident.ns)
in (_175_8, x.FStar_Ident.ident.FStar_Ident.idText)))

# 25 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let as_mlident = (fun x -> (x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText, 0))

# 28 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

type mlidents =
mlident Prims.list

# 29 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

type mlsymbols =
mlsymbol Prims.list

# 32 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

type e_tag =
| E_PURE
| E_GHOST
| E_IMPURE

# 33 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_E_PURE = (fun _discr_ -> (match (_discr_) with
| E_PURE (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_E_GHOST = (fun _discr_ -> (match (_discr_) with
| E_GHOST (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_E_IMPURE = (fun _discr_ -> (match (_discr_) with
| E_IMPURE (_) -> begin
true
end
| _ -> begin
false
end))

# 37 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

type mlty =
| MLTY_Var of mlident
| MLTY_Fun of (mlty * e_tag * mlty)
| MLTY_Named of (mlty Prims.list * mlpath)
| MLTY_Tuple of mlty Prims.list
| MLTY_Top

# 38 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLTY_Var = (fun _discr_ -> (match (_discr_) with
| MLTY_Var (_) -> begin
true
end
| _ -> begin
false
end))

# 39 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLTY_Fun = (fun _discr_ -> (match (_discr_) with
| MLTY_Fun (_) -> begin
true
end
| _ -> begin
false
end))

# 40 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLTY_Named = (fun _discr_ -> (match (_discr_) with
| MLTY_Named (_) -> begin
true
end
| _ -> begin
false
end))

# 41 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLTY_Tuple = (fun _discr_ -> (match (_discr_) with
| MLTY_Tuple (_) -> begin
true
end
| _ -> begin
false
end))

# 42 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLTY_Top = (fun _discr_ -> (match (_discr_) with
| MLTY_Top (_) -> begin
true
end
| _ -> begin
false
end))

# 38 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLTY_Var____0 : mlty  ->  mlident = (fun projectee -> (match (projectee) with
| MLTY_Var (_73_14) -> begin
_73_14
end))

# 39 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLTY_Fun____0 : mlty  ->  (mlty * e_tag * mlty) = (fun projectee -> (match (projectee) with
| MLTY_Fun (_73_17) -> begin
_73_17
end))

# 40 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLTY_Named____0 : mlty  ->  (mlty Prims.list * mlpath) = (fun projectee -> (match (projectee) with
| MLTY_Named (_73_20) -> begin
_73_20
end))

# 41 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLTY_Tuple____0 : mlty  ->  mlty Prims.list = (fun projectee -> (match (projectee) with
| MLTY_Tuple (_73_23) -> begin
_73_23
end))

# 44 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

type mltyscheme =
(mlidents * mlty)

# 46 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

type mlconstant =
| MLC_Unit
| MLC_Bool of Prims.bool
| MLC_Byte of Prims.byte
| MLC_Int32 of Prims.int32
| MLC_Int64 of Prims.int64
| MLC_Int of Prims.string
| MLC_Float of Prims.float
| MLC_Char of Prims.char
| MLC_String of Prims.string
| MLC_Bytes of Prims.byte Prims.array

# 47 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLC_Unit = (fun _discr_ -> (match (_discr_) with
| MLC_Unit (_) -> begin
true
end
| _ -> begin
false
end))

# 48 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLC_Bool = (fun _discr_ -> (match (_discr_) with
| MLC_Bool (_) -> begin
true
end
| _ -> begin
false
end))

# 49 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLC_Byte = (fun _discr_ -> (match (_discr_) with
| MLC_Byte (_) -> begin
true
end
| _ -> begin
false
end))

# 50 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLC_Int32 = (fun _discr_ -> (match (_discr_) with
| MLC_Int32 (_) -> begin
true
end
| _ -> begin
false
end))

# 51 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLC_Int64 = (fun _discr_ -> (match (_discr_) with
| MLC_Int64 (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLC_Int = (fun _discr_ -> (match (_discr_) with
| MLC_Int (_) -> begin
true
end
| _ -> begin
false
end))

# 53 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLC_Float = (fun _discr_ -> (match (_discr_) with
| MLC_Float (_) -> begin
true
end
| _ -> begin
false
end))

# 54 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLC_Char = (fun _discr_ -> (match (_discr_) with
| MLC_Char (_) -> begin
true
end
| _ -> begin
false
end))

# 55 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLC_String = (fun _discr_ -> (match (_discr_) with
| MLC_String (_) -> begin
true
end
| _ -> begin
false
end))

# 56 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLC_Bytes = (fun _discr_ -> (match (_discr_) with
| MLC_Bytes (_) -> begin
true
end
| _ -> begin
false
end))

# 48 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLC_Bool____0 : mlconstant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLC_Bool (_73_26) -> begin
_73_26
end))

# 49 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLC_Byte____0 : mlconstant  ->  Prims.byte = (fun projectee -> (match (projectee) with
| MLC_Byte (_73_29) -> begin
_73_29
end))

# 50 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLC_Int32____0 : mlconstant  ->  Prims.int32 = (fun projectee -> (match (projectee) with
| MLC_Int32 (_73_32) -> begin
_73_32
end))

# 51 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLC_Int64____0 : mlconstant  ->  Prims.int64 = (fun projectee -> (match (projectee) with
| MLC_Int64 (_73_35) -> begin
_73_35
end))

# 52 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLC_Int____0 : mlconstant  ->  Prims.string = (fun projectee -> (match (projectee) with
| MLC_Int (_73_38) -> begin
_73_38
end))

# 53 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLC_Float____0 : mlconstant  ->  Prims.float = (fun projectee -> (match (projectee) with
| MLC_Float (_73_41) -> begin
_73_41
end))

# 54 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLC_Char____0 : mlconstant  ->  Prims.char = (fun projectee -> (match (projectee) with
| MLC_Char (_73_44) -> begin
_73_44
end))

# 55 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLC_String____0 : mlconstant  ->  Prims.string = (fun projectee -> (match (projectee) with
| MLC_String (_73_47) -> begin
_73_47
end))

# 56 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLC_Bytes____0 : mlconstant  ->  Prims.byte Prims.array = (fun projectee -> (match (projectee) with
| MLC_Bytes (_73_50) -> begin
_73_50
end))

# 58 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

type mlpattern =
| MLP_Wild
| MLP_Const of mlconstant
| MLP_Var of mlident
| MLP_CTor of (mlpath * mlpattern Prims.list)
| MLP_Branch of mlpattern Prims.list
| MLP_Record of (mlsymbol Prims.list * (mlsymbol * mlpattern) Prims.list)
| MLP_Tuple of mlpattern Prims.list

# 59 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLP_Wild = (fun _discr_ -> (match (_discr_) with
| MLP_Wild (_) -> begin
true
end
| _ -> begin
false
end))

# 60 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLP_Const = (fun _discr_ -> (match (_discr_) with
| MLP_Const (_) -> begin
true
end
| _ -> begin
false
end))

# 61 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLP_Var = (fun _discr_ -> (match (_discr_) with
| MLP_Var (_) -> begin
true
end
| _ -> begin
false
end))

# 62 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLP_CTor = (fun _discr_ -> (match (_discr_) with
| MLP_CTor (_) -> begin
true
end
| _ -> begin
false
end))

# 63 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLP_Branch = (fun _discr_ -> (match (_discr_) with
| MLP_Branch (_) -> begin
true
end
| _ -> begin
false
end))

# 65 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLP_Record = (fun _discr_ -> (match (_discr_) with
| MLP_Record (_) -> begin
true
end
| _ -> begin
false
end))

# 66 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLP_Tuple = (fun _discr_ -> (match (_discr_) with
| MLP_Tuple (_) -> begin
true
end
| _ -> begin
false
end))

# 60 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLP_Const____0 : mlpattern  ->  mlconstant = (fun projectee -> (match (projectee) with
| MLP_Const (_73_53) -> begin
_73_53
end))

# 61 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLP_Var____0 : mlpattern  ->  mlident = (fun projectee -> (match (projectee) with
| MLP_Var (_73_56) -> begin
_73_56
end))

# 62 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLP_CTor____0 : mlpattern  ->  (mlpath * mlpattern Prims.list) = (fun projectee -> (match (projectee) with
| MLP_CTor (_73_59) -> begin
_73_59
end))

# 63 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLP_Branch____0 : mlpattern  ->  mlpattern Prims.list = (fun projectee -> (match (projectee) with
| MLP_Branch (_73_62) -> begin
_73_62
end))

# 65 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLP_Record____0 : mlpattern  ->  (mlsymbol Prims.list * (mlsymbol * mlpattern) Prims.list) = (fun projectee -> (match (projectee) with
| MLP_Record (_73_65) -> begin
_73_65
end))

# 66 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLP_Tuple____0 : mlpattern  ->  mlpattern Prims.list = (fun projectee -> (match (projectee) with
| MLP_Tuple (_73_68) -> begin
_73_68
end))

# 68 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

type mlexpr' =
| MLE_Const of mlconstant
| MLE_Var of mlident
| MLE_Name of mlpath
| MLE_Let of (mlletbinding * mlexpr)
| MLE_App of (mlexpr * mlexpr Prims.list)
| MLE_Fun of ((mlident * mlty) Prims.list * mlexpr)
| MLE_Match of (mlexpr * mlbranch Prims.list)
| MLE_Coerce of (mlexpr * mlty * mlty)
| MLE_CTor of (mlpath * mlexpr Prims.list)
| MLE_Seq of mlexpr Prims.list
| MLE_Tuple of mlexpr Prims.list
| MLE_Record of (mlsymbol Prims.list * (mlsymbol * mlexpr) Prims.list)
| MLE_Proj of (mlexpr * mlpath)
| MLE_If of (mlexpr * mlexpr * mlexpr Prims.option)
| MLE_Raise of (mlpath * mlexpr Prims.list)
| MLE_Try of (mlexpr * mlbranch Prims.list) 
 and mlexpr =
{expr : mlexpr'; ty : mlty} 
 and mllb =
{mllb_name : mlident; mllb_tysc : mltyscheme; mllb_add_unit : Prims.bool; mllb_def : mlexpr} 
 and mlbranch =
(mlpattern * mlexpr Prims.option * mlexpr) 
 and mlletbinding =
(Prims.bool * mllb Prims.list)

# 69 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLE_Const = (fun _discr_ -> (match (_discr_) with
| MLE_Const (_) -> begin
true
end
| _ -> begin
false
end))

# 70 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLE_Var = (fun _discr_ -> (match (_discr_) with
| MLE_Var (_) -> begin
true
end
| _ -> begin
false
end))

# 71 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLE_Name = (fun _discr_ -> (match (_discr_) with
| MLE_Name (_) -> begin
true
end
| _ -> begin
false
end))

# 72 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLE_Let = (fun _discr_ -> (match (_discr_) with
| MLE_Let (_) -> begin
true
end
| _ -> begin
false
end))

# 73 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLE_App = (fun _discr_ -> (match (_discr_) with
| MLE_App (_) -> begin
true
end
| _ -> begin
false
end))

# 74 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLE_Fun = (fun _discr_ -> (match (_discr_) with
| MLE_Fun (_) -> begin
true
end
| _ -> begin
false
end))

# 75 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLE_Match = (fun _discr_ -> (match (_discr_) with
| MLE_Match (_) -> begin
true
end
| _ -> begin
false
end))

# 76 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLE_Coerce = (fun _discr_ -> (match (_discr_) with
| MLE_Coerce (_) -> begin
true
end
| _ -> begin
false
end))

# 78 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLE_CTor = (fun _discr_ -> (match (_discr_) with
| MLE_CTor (_) -> begin
true
end
| _ -> begin
false
end))

# 79 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLE_Seq = (fun _discr_ -> (match (_discr_) with
| MLE_Seq (_) -> begin
true
end
| _ -> begin
false
end))

# 80 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLE_Tuple = (fun _discr_ -> (match (_discr_) with
| MLE_Tuple (_) -> begin
true
end
| _ -> begin
false
end))

# 81 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLE_Record = (fun _discr_ -> (match (_discr_) with
| MLE_Record (_) -> begin
true
end
| _ -> begin
false
end))

# 82 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLE_Proj = (fun _discr_ -> (match (_discr_) with
| MLE_Proj (_) -> begin
true
end
| _ -> begin
false
end))

# 83 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLE_If = (fun _discr_ -> (match (_discr_) with
| MLE_If (_) -> begin
true
end
| _ -> begin
false
end))

# 84 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLE_Raise = (fun _discr_ -> (match (_discr_) with
| MLE_Raise (_) -> begin
true
end
| _ -> begin
false
end))

# 85 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLE_Try = (fun _discr_ -> (match (_discr_) with
| MLE_Try (_) -> begin
true
end
| _ -> begin
false
end))

# 87 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_Mkmlexpr : mlexpr  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmlexpr"))))

# 94 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_Mkmllb : mllb  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmllb"))))

# 69 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLE_Const____0 : mlexpr'  ->  mlconstant = (fun projectee -> (match (projectee) with
| MLE_Const (_73_77) -> begin
_73_77
end))

# 70 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLE_Var____0 : mlexpr'  ->  mlident = (fun projectee -> (match (projectee) with
| MLE_Var (_73_80) -> begin
_73_80
end))

# 71 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLE_Name____0 : mlexpr'  ->  mlpath = (fun projectee -> (match (projectee) with
| MLE_Name (_73_83) -> begin
_73_83
end))

# 72 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLE_Let____0 : mlexpr'  ->  (mlletbinding * mlexpr) = (fun projectee -> (match (projectee) with
| MLE_Let (_73_86) -> begin
_73_86
end))

# 73 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLE_App____0 : mlexpr'  ->  (mlexpr * mlexpr Prims.list) = (fun projectee -> (match (projectee) with
| MLE_App (_73_89) -> begin
_73_89
end))

# 74 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLE_Fun____0 : mlexpr'  ->  ((mlident * mlty) Prims.list * mlexpr) = (fun projectee -> (match (projectee) with
| MLE_Fun (_73_92) -> begin
_73_92
end))

# 75 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLE_Match____0 : mlexpr'  ->  (mlexpr * mlbranch Prims.list) = (fun projectee -> (match (projectee) with
| MLE_Match (_73_95) -> begin
_73_95
end))

# 76 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLE_Coerce____0 : mlexpr'  ->  (mlexpr * mlty * mlty) = (fun projectee -> (match (projectee) with
| MLE_Coerce (_73_98) -> begin
_73_98
end))

# 78 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLE_CTor____0 : mlexpr'  ->  (mlpath * mlexpr Prims.list) = (fun projectee -> (match (projectee) with
| MLE_CTor (_73_101) -> begin
_73_101
end))

# 79 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLE_Seq____0 : mlexpr'  ->  mlexpr Prims.list = (fun projectee -> (match (projectee) with
| MLE_Seq (_73_104) -> begin
_73_104
end))

# 80 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLE_Tuple____0 : mlexpr'  ->  mlexpr Prims.list = (fun projectee -> (match (projectee) with
| MLE_Tuple (_73_107) -> begin
_73_107
end))

# 81 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLE_Record____0 : mlexpr'  ->  (mlsymbol Prims.list * (mlsymbol * mlexpr) Prims.list) = (fun projectee -> (match (projectee) with
| MLE_Record (_73_110) -> begin
_73_110
end))

# 82 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLE_Proj____0 : mlexpr'  ->  (mlexpr * mlpath) = (fun projectee -> (match (projectee) with
| MLE_Proj (_73_113) -> begin
_73_113
end))

# 83 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLE_If____0 : mlexpr'  ->  (mlexpr * mlexpr * mlexpr Prims.option) = (fun projectee -> (match (projectee) with
| MLE_If (_73_116) -> begin
_73_116
end))

# 84 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLE_Raise____0 : mlexpr'  ->  (mlpath * mlexpr Prims.list) = (fun projectee -> (match (projectee) with
| MLE_Raise (_73_119) -> begin
_73_119
end))

# 85 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLE_Try____0 : mlexpr'  ->  (mlexpr * mlbranch Prims.list) = (fun projectee -> (match (projectee) with
| MLE_Try (_73_122) -> begin
_73_122
end))

# 103 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

type mltybody =
| MLTD_Abbrev of mlty
| MLTD_Record of (mlsymbol * mlty) Prims.list
| MLTD_DType of (mlsymbol * mlty Prims.list) Prims.list

# 104 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLTD_Abbrev = (fun _discr_ -> (match (_discr_) with
| MLTD_Abbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 105 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLTD_Record = (fun _discr_ -> (match (_discr_) with
| MLTD_Record (_) -> begin
true
end
| _ -> begin
false
end))

# 106 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLTD_DType = (fun _discr_ -> (match (_discr_) with
| MLTD_DType (_) -> begin
true
end
| _ -> begin
false
end))

# 104 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLTD_Abbrev____0 : mltybody  ->  mlty = (fun projectee -> (match (projectee) with
| MLTD_Abbrev (_73_127) -> begin
_73_127
end))

# 105 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLTD_Record____0 : mltybody  ->  (mlsymbol * mlty) Prims.list = (fun projectee -> (match (projectee) with
| MLTD_Record (_73_130) -> begin
_73_130
end))

# 106 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLTD_DType____0 : mltybody  ->  (mlsymbol * mlty Prims.list) Prims.list = (fun projectee -> (match (projectee) with
| MLTD_DType (_73_133) -> begin
_73_133
end))

# 111 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

type mltydecl =
(mlsymbol * mlidents * mltybody Prims.option) Prims.list

# 113 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

type mlmodule1 =
| MLM_Ty of mltydecl
| MLM_Let of mlletbinding
| MLM_Exn of (mlsymbol * mlty Prims.list)
| MLM_Top of mlexpr
| MLM_Loc of (Prims.int * Prims.string)

# 114 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLM_Ty = (fun _discr_ -> (match (_discr_) with
| MLM_Ty (_) -> begin
true
end
| _ -> begin
false
end))

# 115 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLM_Let = (fun _discr_ -> (match (_discr_) with
| MLM_Let (_) -> begin
true
end
| _ -> begin
false
end))

# 116 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLM_Exn = (fun _discr_ -> (match (_discr_) with
| MLM_Exn (_) -> begin
true
end
| _ -> begin
false
end))

# 117 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLM_Top = (fun _discr_ -> (match (_discr_) with
| MLM_Top (_) -> begin
true
end
| _ -> begin
false
end))

# 118 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLM_Loc = (fun _discr_ -> (match (_discr_) with
| MLM_Loc (_) -> begin
true
end
| _ -> begin
false
end))

# 114 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLM_Ty____0 : mlmodule1  ->  mltydecl = (fun projectee -> (match (projectee) with
| MLM_Ty (_73_136) -> begin
_73_136
end))

# 115 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLM_Let____0 : mlmodule1  ->  mlletbinding = (fun projectee -> (match (projectee) with
| MLM_Let (_73_139) -> begin
_73_139
end))

# 116 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLM_Exn____0 : mlmodule1  ->  (mlsymbol * mlty Prims.list) = (fun projectee -> (match (projectee) with
| MLM_Exn (_73_142) -> begin
_73_142
end))

# 117 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLM_Top____0 : mlmodule1  ->  mlexpr = (fun projectee -> (match (projectee) with
| MLM_Top (_73_145) -> begin
_73_145
end))

# 118 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLM_Loc____0 : mlmodule1  ->  (Prims.int * Prims.string) = (fun projectee -> (match (projectee) with
| MLM_Loc (_73_148) -> begin
_73_148
end))

# 120 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

type mlmodule =
mlmodule1 Prims.list

# 122 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

type mlsig1 =
| MLS_Mod of (mlsymbol * mlsig)
| MLS_Ty of mltydecl
| MLS_Val of (mlsymbol * mltyscheme)
| MLS_Exn of (mlsymbol * mlty Prims.list) 
 and mlsig =
mlsig1 Prims.list

# 123 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLS_Mod = (fun _discr_ -> (match (_discr_) with
| MLS_Mod (_) -> begin
true
end
| _ -> begin
false
end))

# 124 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLS_Ty = (fun _discr_ -> (match (_discr_) with
| MLS_Ty (_) -> begin
true
end
| _ -> begin
false
end))

# 127 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLS_Val = (fun _discr_ -> (match (_discr_) with
| MLS_Val (_) -> begin
true
end
| _ -> begin
false
end))

# 128 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLS_Exn = (fun _discr_ -> (match (_discr_) with
| MLS_Exn (_) -> begin
true
end
| _ -> begin
false
end))

# 123 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLS_Mod____0 : mlsig1  ->  (mlsymbol * mlsig) = (fun projectee -> (match (projectee) with
| MLS_Mod (_73_151) -> begin
_73_151
end))

# 124 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLS_Ty____0 : mlsig1  ->  mltydecl = (fun projectee -> (match (projectee) with
| MLS_Ty (_73_154) -> begin
_73_154
end))

# 127 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLS_Val____0 : mlsig1  ->  (mlsymbol * mltyscheme) = (fun projectee -> (match (projectee) with
| MLS_Val (_73_157) -> begin
_73_157
end))

# 128 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLS_Exn____0 : mlsig1  ->  (mlsymbol * mlty Prims.list) = (fun projectee -> (match (projectee) with
| MLS_Exn (_73_160) -> begin
_73_160
end))

# 132 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let with_ty : mlty  ->  mlexpr'  ->  mlexpr = (fun t e -> {expr = e; ty = t})

# 135 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

type mllib =
| MLLib of (mlsymbol * (mlsig * mlmodule) Prims.option * mllib) Prims.list

# 136 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let is_MLLib = (fun _discr_ -> (match (_discr_) with
| MLLib (_) -> begin
true
end
| _ -> begin
false
end))

# 136 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ___MLLib____0 : mllib  ->  (mlsymbol * (mlsig * mlmodule) Prims.option * mllib) Prims.list = (fun projectee -> (match (projectee) with
| MLLib (_73_164) -> begin
_73_164
end))

# 140 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ml_unit_ty : mlty = MLTY_Named (([], (("Prims")::[], "unit")))

# 141 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ml_bool_ty : mlty = MLTY_Named (([], (("Prims")::[], "bool")))

# 142 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ml_int_ty : mlty = MLTY_Named (([], (("Prims")::[], "int")))

# 143 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ml_string_ty : mlty = MLTY_Named (([], (("Prims")::[], "string")))

# 144 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let ml_unit : mlexpr = (FStar_All.pipe_left (with_ty ml_unit_ty) (MLE_Const (MLC_Unit)))

# 145 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let mlp_lalloc : (Prims.string Prims.list * Prims.string) = (("SST")::[], "lalloc")

# 146 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\ml-syntax.fs"

let apply_obj_repr : mlexpr  ->  mlty  ->  mlexpr = (fun x t -> (let obj_repr = (FStar_All.pipe_left (with_ty (MLTY_Fun ((t, E_PURE, MLTY_Top)))) (MLE_Name ((("Obj")::[], "repr"))))
in (FStar_All.pipe_left (with_ty MLTY_Top) (MLE_App ((obj_repr, (x)::[]))))))




