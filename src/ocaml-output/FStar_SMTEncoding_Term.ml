
open Prims
open FStar_Pervasives
type sort =
| Bool_sort
| Int_sort
| String_sort
| Term_sort
| Fuel_sort
| BitVec_sort of Prims.int
| Array of (sort * sort)
| Arrow of (sort * sort)
| Sort of Prims.string


let uu___is_Bool_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool_sort -> begin
true
end
| uu____34 -> begin
false
end))


let uu___is_Int_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int_sort -> begin
true
end
| uu____40 -> begin
false
end))


let uu___is_String_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| String_sort -> begin
true
end
| uu____46 -> begin
false
end))


let uu___is_Term_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Term_sort -> begin
true
end
| uu____52 -> begin
false
end))


let uu___is_Fuel_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fuel_sort -> begin
true
end
| uu____58 -> begin
false
end))


let uu___is_BitVec_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BitVec_sort (_0) -> begin
true
end
| uu____65 -> begin
false
end))


let __proj__BitVec_sort__item___0 : sort  ->  Prims.int = (fun projectee -> (match (projectee) with
| BitVec_sort (_0) -> begin
_0
end))


let uu___is_Array : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Array (_0) -> begin
true
end
| uu____83 -> begin
false
end))


let __proj__Array__item___0 : sort  ->  (sort * sort) = (fun projectee -> (match (projectee) with
| Array (_0) -> begin
_0
end))


let uu___is_Arrow : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Arrow (_0) -> begin
true
end
| uu____113 -> begin
false
end))


let __proj__Arrow__item___0 : sort  ->  (sort * sort) = (fun projectee -> (match (projectee) with
| Arrow (_0) -> begin
_0
end))


let uu___is_Sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sort (_0) -> begin
true
end
| uu____139 -> begin
false
end))


let __proj__Sort__item___0 : sort  ->  Prims.string = (fun projectee -> (match (projectee) with
| Sort (_0) -> begin
_0
end))


let rec strSort : sort  ->  Prims.string = (fun x -> (match (x) with
| Bool_sort -> begin
"Bool"
end
| Int_sort -> begin
"Int"
end
| Term_sort -> begin
"Term"
end
| String_sort -> begin
"FString"
end
| Fuel_sort -> begin
"Fuel"
end
| BitVec_sort (n1) -> begin
(

let uu____153 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ BitVec %s)" uu____153))
end
| Array (s1, s2) -> begin
(

let uu____156 = (strSort s1)
in (

let uu____157 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" uu____156 uu____157)))
end
| Arrow (s1, s2) -> begin
(

let uu____160 = (strSort s1)
in (

let uu____161 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" uu____160 uu____161)))
end
| Sort (s) -> begin
s
end))

type op =
| TrueOp
| FalseOp
| Not
| And
| Or
| Imp
| Iff
| Eq
| LT
| LTE
| GT
| GTE
| Add
| Sub
| Div
| Mul
| Minus
| Mod
| BvAnd
| BvXor
| BvOr
| BvAdd
| BvSub
| BvShl
| BvShr
| BvUdiv
| BvMod
| BvMul
| BvUlt
| BvUext of Prims.int
| NatToBv of Prims.int
| BvToNat
| ITE
| Var of Prims.string


let uu___is_TrueOp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TrueOp -> begin
true
end
| uu____183 -> begin
false
end))


let uu___is_FalseOp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FalseOp -> begin
true
end
| uu____189 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____195 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____201 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____207 -> begin
false
end))


let uu___is_Imp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Imp -> begin
true
end
| uu____213 -> begin
false
end))


let uu___is_Iff : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iff -> begin
true
end
| uu____219 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____225 -> begin
false
end))


let uu___is_LT : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LT -> begin
true
end
| uu____231 -> begin
false
end))


let uu___is_LTE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LTE -> begin
true
end
| uu____237 -> begin
false
end))


let uu___is_GT : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GT -> begin
true
end
| uu____243 -> begin
false
end))


let uu___is_GTE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GTE -> begin
true
end
| uu____249 -> begin
false
end))


let uu___is_Add : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Add -> begin
true
end
| uu____255 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____261 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____267 -> begin
false
end))


let uu___is_Mul : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mul -> begin
true
end
| uu____273 -> begin
false
end))


let uu___is_Minus : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Minus -> begin
true
end
| uu____279 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____285 -> begin
false
end))


let uu___is_BvAnd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvAnd -> begin
true
end
| uu____291 -> begin
false
end))


let uu___is_BvXor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvXor -> begin
true
end
| uu____297 -> begin
false
end))


let uu___is_BvOr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvOr -> begin
true
end
| uu____303 -> begin
false
end))


let uu___is_BvAdd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvAdd -> begin
true
end
| uu____309 -> begin
false
end))


let uu___is_BvSub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvSub -> begin
true
end
| uu____315 -> begin
false
end))


let uu___is_BvShl : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvShl -> begin
true
end
| uu____321 -> begin
false
end))


let uu___is_BvShr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvShr -> begin
true
end
| uu____327 -> begin
false
end))


let uu___is_BvUdiv : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvUdiv -> begin
true
end
| uu____333 -> begin
false
end))


let uu___is_BvMod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvMod -> begin
true
end
| uu____339 -> begin
false
end))


let uu___is_BvMul : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvMul -> begin
true
end
| uu____345 -> begin
false
end))


let uu___is_BvUlt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvUlt -> begin
true
end
| uu____351 -> begin
false
end))


let uu___is_BvUext : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvUext (_0) -> begin
true
end
| uu____358 -> begin
false
end))


let __proj__BvUext__item___0 : op  ->  Prims.int = (fun projectee -> (match (projectee) with
| BvUext (_0) -> begin
_0
end))


let uu___is_NatToBv : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NatToBv (_0) -> begin
true
end
| uu____372 -> begin
false
end))


let __proj__NatToBv__item___0 : op  ->  Prims.int = (fun projectee -> (match (projectee) with
| NatToBv (_0) -> begin
_0
end))


let uu___is_BvToNat : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvToNat -> begin
true
end
| uu____385 -> begin
false
end))


let uu___is_ITE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ITE -> begin
true
end
| uu____391 -> begin
false
end))


let uu___is_Var : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Var (_0) -> begin
true
end
| uu____398 -> begin
false
end))


let __proj__Var__item___0 : op  ->  Prims.string = (fun projectee -> (match (projectee) with
| Var (_0) -> begin
_0
end))

type qop =
| Forall
| Exists


let uu___is_Forall : qop  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Forall -> begin
true
end
| uu____411 -> begin
false
end))


let uu___is_Exists : qop  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exists -> begin
true
end
| uu____417 -> begin
false
end))

type term' =
| Integer of Prims.string
| BoundV of Prims.int
| FreeV of (Prims.string * sort)
| App of (op * term Prims.list)
| Quant of (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)
| Let of (term Prims.list * term)
| Labeled of (term * Prims.string * FStar_Range.range)
| LblPos of (term * Prims.string) 
 and term =
{tm : term'; freevars : (Prims.string * sort) Prims.list FStar_Syntax_Syntax.memo; rng : FStar_Range.range}


let uu___is_Integer : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Integer (_0) -> begin
true
end
| uu____600 -> begin
false
end))


let __proj__Integer__item___0 : term'  ->  Prims.string = (fun projectee -> (match (projectee) with
| Integer (_0) -> begin
_0
end))


let uu___is_BoundV : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BoundV (_0) -> begin
true
end
| uu____614 -> begin
false
end))


let __proj__BoundV__item___0 : term'  ->  Prims.int = (fun projectee -> (match (projectee) with
| BoundV (_0) -> begin
_0
end))


let uu___is_FreeV : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FreeV (_0) -> begin
true
end
| uu____632 -> begin
false
end))


let __proj__FreeV__item___0 : term'  ->  (Prims.string * sort) = (fun projectee -> (match (projectee) with
| FreeV (_0) -> begin
_0
end))


let uu___is_App : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| App (_0) -> begin
true
end
| uu____664 -> begin
false
end))


let __proj__App__item___0 : term'  ->  (op * term Prims.list) = (fun projectee -> (match (projectee) with
| App (_0) -> begin
_0
end))


let uu___is_Quant : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Quant (_0) -> begin
true
end
| uu____714 -> begin
false
end))


let __proj__Quant__item___0 : term'  ->  (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term) = (fun projectee -> (match (projectee) with
| Quant (_0) -> begin
_0
end))


let uu___is_Let : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Let (_0) -> begin
true
end
| uu____788 -> begin
false
end))


let __proj__Let__item___0 : term'  ->  (term Prims.list * term) = (fun projectee -> (match (projectee) with
| Let (_0) -> begin
_0
end))


let uu___is_Labeled : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Labeled (_0) -> begin
true
end
| uu____826 -> begin
false
end))


let __proj__Labeled__item___0 : term'  ->  (term * Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Labeled (_0) -> begin
_0
end))


let uu___is_LblPos : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LblPos (_0) -> begin
true
end
| uu____862 -> begin
false
end))


let __proj__LblPos__item___0 : term'  ->  (term * Prims.string) = (fun projectee -> (match (projectee) with
| LblPos (_0) -> begin
_0
end))


let __proj__Mkterm__item__tm : term  ->  term' = (fun projectee -> (match (projectee) with
| {tm = __fname__tm; freevars = __fname__freevars; rng = __fname__rng} -> begin
__fname__tm
end))


let __proj__Mkterm__item__freevars : term  ->  (Prims.string * sort) Prims.list FStar_Syntax_Syntax.memo = (fun projectee -> (match (projectee) with
| {tm = __fname__tm; freevars = __fname__freevars; rng = __fname__rng} -> begin
__fname__freevars
end))


let __proj__Mkterm__item__rng : term  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {tm = __fname__tm; freevars = __fname__freevars; rng = __fname__rng} -> begin
__fname__rng
end))


type pat =
term


type fv =
(Prims.string * sort)


type fvs =
(Prims.string * sort) Prims.list


type caption =
Prims.string FStar_Pervasives_Native.option


type binders =
(Prims.string * sort) Prims.list


type constructor_field =
(Prims.string * sort * Prims.bool)


type constructor_t =
(Prims.string * constructor_field Prims.list * sort * Prims.int * Prims.bool)


type constructors =
constructor_t Prims.list

type fact_db_id =
| Name of FStar_Ident.lid
| Namespace of FStar_Ident.lid
| Tag of Prims.string


let uu___is_Name : fact_db_id  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Name (_0) -> begin
true
end
| uu____1110 -> begin
false
end))


let __proj__Name__item___0 : fact_db_id  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Name (_0) -> begin
_0
end))


let uu___is_Namespace : fact_db_id  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Namespace (_0) -> begin
true
end
| uu____1124 -> begin
false
end))


let __proj__Namespace__item___0 : fact_db_id  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Namespace (_0) -> begin
_0
end))


let uu___is_Tag : fact_db_id  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tag (_0) -> begin
true
end
| uu____1138 -> begin
false
end))


let __proj__Tag__item___0 : fact_db_id  ->  Prims.string = (fun projectee -> (match (projectee) with
| Tag (_0) -> begin
_0
end))

type assumption =
{assumption_term : term; assumption_caption : caption; assumption_name : Prims.string; assumption_fact_ids : fact_db_id Prims.list}


let __proj__Mkassumption__item__assumption_term : assumption  ->  term = (fun projectee -> (match (projectee) with
| {assumption_term = __fname__assumption_term; assumption_caption = __fname__assumption_caption; assumption_name = __fname__assumption_name; assumption_fact_ids = __fname__assumption_fact_ids} -> begin
__fname__assumption_term
end))


let __proj__Mkassumption__item__assumption_caption : assumption  ->  caption = (fun projectee -> (match (projectee) with
| {assumption_term = __fname__assumption_term; assumption_caption = __fname__assumption_caption; assumption_name = __fname__assumption_name; assumption_fact_ids = __fname__assumption_fact_ids} -> begin
__fname__assumption_caption
end))


let __proj__Mkassumption__item__assumption_name : assumption  ->  Prims.string = (fun projectee -> (match (projectee) with
| {assumption_term = __fname__assumption_term; assumption_caption = __fname__assumption_caption; assumption_name = __fname__assumption_name; assumption_fact_ids = __fname__assumption_fact_ids} -> begin
__fname__assumption_name
end))


let __proj__Mkassumption__item__assumption_fact_ids : assumption  ->  fact_db_id Prims.list = (fun projectee -> (match (projectee) with
| {assumption_term = __fname__assumption_term; assumption_caption = __fname__assumption_caption; assumption_name = __fname__assumption_name; assumption_fact_ids = __fname__assumption_fact_ids} -> begin
__fname__assumption_fact_ids
end))

type decl =
| DefPrelude
| DeclFun of (Prims.string * sort Prims.list * sort * caption)
| DefineFun of (Prims.string * sort Prims.list * sort * term * caption)
| Assume of assumption
| Caption of Prims.string
| Eval of term
| Echo of Prims.string
| RetainAssumptions of Prims.string Prims.list
| Push
| Pop
| CheckSat
| GetUnsatCore
| SetOption of (Prims.string * Prims.string)
| GetStatistics
| GetReasonUnknown


let uu___is_DefPrelude : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DefPrelude -> begin
true
end
| uu____1289 -> begin
false
end))


let uu___is_DeclFun : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DeclFun (_0) -> begin
true
end
| uu____1306 -> begin
false
end))


let __proj__DeclFun__item___0 : decl  ->  (Prims.string * sort Prims.list * sort * caption) = (fun projectee -> (match (projectee) with
| DeclFun (_0) -> begin
_0
end))


let uu___is_DefineFun : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DefineFun (_0) -> begin
true
end
| uu____1362 -> begin
false
end))


let __proj__DefineFun__item___0 : decl  ->  (Prims.string * sort Prims.list * sort * term * caption) = (fun projectee -> (match (projectee) with
| DefineFun (_0) -> begin
_0
end))


let uu___is_Assume : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Assume (_0) -> begin
true
end
| uu____1412 -> begin
false
end))


let __proj__Assume__item___0 : decl  ->  assumption = (fun projectee -> (match (projectee) with
| Assume (_0) -> begin
_0
end))


let uu___is_Caption : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Caption (_0) -> begin
true
end
| uu____1426 -> begin
false
end))


let __proj__Caption__item___0 : decl  ->  Prims.string = (fun projectee -> (match (projectee) with
| Caption (_0) -> begin
_0
end))


let uu___is_Eval : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eval (_0) -> begin
true
end
| uu____1440 -> begin
false
end))


let __proj__Eval__item___0 : decl  ->  term = (fun projectee -> (match (projectee) with
| Eval (_0) -> begin
_0
end))


let uu___is_Echo : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Echo (_0) -> begin
true
end
| uu____1454 -> begin
false
end))


let __proj__Echo__item___0 : decl  ->  Prims.string = (fun projectee -> (match (projectee) with
| Echo (_0) -> begin
_0
end))


let uu___is_RetainAssumptions : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| RetainAssumptions (_0) -> begin
true
end
| uu____1470 -> begin
false
end))


let __proj__RetainAssumptions__item___0 : decl  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| RetainAssumptions (_0) -> begin
_0
end))


let uu___is_Push : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push -> begin
true
end
| uu____1489 -> begin
false
end))


let uu___is_Pop : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____1495 -> begin
false
end))


let uu___is_CheckSat : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckSat -> begin
true
end
| uu____1501 -> begin
false
end))


let uu___is_GetUnsatCore : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetUnsatCore -> begin
true
end
| uu____1507 -> begin
false
end))


let uu___is_SetOption : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOption (_0) -> begin
true
end
| uu____1518 -> begin
false
end))


let __proj__SetOption__item___0 : decl  ->  (Prims.string * Prims.string) = (fun projectee -> (match (projectee) with
| SetOption (_0) -> begin
_0
end))


let uu___is_GetStatistics : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetStatistics -> begin
true
end
| uu____1543 -> begin
false
end))


let uu___is_GetReasonUnknown : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetReasonUnknown -> begin
true
end
| uu____1549 -> begin
false
end))


type decls_t =
decl Prims.list


type error_label =
(fv * Prims.string * FStar_Range.range)


type error_labels =
error_label Prims.list


let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> (Prims.op_Equality (FStar_Pervasives_Native.fst x) (FStar_Pervasives_Native.fst y)))


let fv_sort : 'Auu____1576 'Auu____1577 . ('Auu____1576 * 'Auu____1577)  ->  'Auu____1577 = (fun x -> (FStar_Pervasives_Native.snd x))


let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match (((x.tm), (y.tm))) with
| (FreeV (x1), FreeV (y1)) -> begin
(fv_eq x1 y1)
end
| uu____1611 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun uu___51_1620 -> (match (uu___51_1620) with
| {tm = FreeV (x); freevars = uu____1622; rng = uu____1623} -> begin
(fv_sort x)
end
| uu____1636 -> begin
(failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun uu___52_1641 -> (match (uu___52_1641) with
| {tm = FreeV (fv); freevars = uu____1643; rng = uu____1644} -> begin
fv
end
| uu____1657 -> begin
(failwith "impossible")
end))


let rec freevars : term  ->  (Prims.string * sort) Prims.list = (fun t -> (match (t.tm) with
| Integer (uu____1675) -> begin
[]
end
| BoundV (uu____1680) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (uu____1698, tms) -> begin
(FStar_List.collect freevars tms)
end
| Quant (uu____1708, uu____1709, uu____1710, uu____1711, t1) -> begin
(freevars t1)
end
| Labeled (t1, uu____1730, uu____1731) -> begin
(freevars t1)
end
| LblPos (t1, uu____1733) -> begin
(freevars t1)
end
| Let (es, body) -> begin
(FStar_List.collect freevars ((body)::es))
end))


let free_variables : term  ->  fvs = (fun t -> (

let uu____1749 = (FStar_ST.op_Bang t.freevars)
in (match (uu____1749) with
| FStar_Pervasives_Native.Some (b) -> begin
b
end
| FStar_Pervasives_Native.None -> begin
(

let fvs = (

let uu____1825 = (freevars t)
in (FStar_Util.remove_dups fv_eq uu____1825))
in ((FStar_ST.op_Colon_Equals t.freevars (FStar_Pervasives_Native.Some (fvs)));
fvs;
))
end)))


let qop_to_string : qop  ->  Prims.string = (fun uu___53_1880 -> (match (uu___53_1880) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun uu___54_1885 -> (match (uu___54_1885) with
| TrueOp -> begin
"true"
end
| FalseOp -> begin
"false"
end
| Not -> begin
"not"
end
| And -> begin
"and"
end
| Or -> begin
"or"
end
| Imp -> begin
"implies"
end
| Iff -> begin
"iff"
end
| Eq -> begin
"="
end
| LT -> begin
"<"
end
| LTE -> begin
"<="
end
| GT -> begin
">"
end
| GTE -> begin
">="
end
| Add -> begin
"+"
end
| Sub -> begin
"-"
end
| Div -> begin
"div"
end
| Mul -> begin
"*"
end
| Minus -> begin
"-"
end
| Mod -> begin
"mod"
end
| ITE -> begin
"ite"
end
| BvAnd -> begin
"bvand"
end
| BvXor -> begin
"bvxor"
end
| BvOr -> begin
"bvor"
end
| BvAdd -> begin
"bvadd"
end
| BvSub -> begin
"bvsub"
end
| BvShl -> begin
"bvshl"
end
| BvShr -> begin
"bvlshr"
end
| BvUdiv -> begin
"bvudiv"
end
| BvMod -> begin
"bvurem"
end
| BvMul -> begin
"bvmul"
end
| BvUlt -> begin
"bvult"
end
| BvToNat -> begin
"bv2int"
end
| BvUext (n1) -> begin
(

let uu____1887 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ zero_extend %s)" uu____1887))
end
| NatToBv (n1) -> begin
(

let uu____1889 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ int2bv %s)" uu____1889))
end
| Var (s) -> begin
s
end))


let weightToSmt : Prims.int FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___55_1897 -> (match (uu___55_1897) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (i) -> begin
(

let uu____1901 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" uu____1901))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____1913 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" uu____1913))
end
| FreeV (x) -> begin
(

let uu____1919 = (

let uu____1920 = (strSort (FStar_Pervasives_Native.snd x))
in (Prims.strcat ":" uu____1920))
in (Prims.strcat (FStar_Pervasives_Native.fst x) uu____1919))
end
| App (op, tms) -> begin
(

let uu____1927 = (

let uu____1928 = (op_to_string op)
in (

let uu____1929 = (

let uu____1930 = (

let uu____1931 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right uu____1931 (FStar_String.concat " ")))
in (Prims.strcat uu____1930 ")"))
in (Prims.strcat uu____1928 uu____1929)))
in (Prims.strcat "(" uu____1927))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____1939 = (hash_of_term t1)
in (

let uu____1940 = (

let uu____1941 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 uu____1941))
in (Prims.strcat uu____1939 uu____1940)))
end
| LblPos (t1, r) -> begin
(

let uu____1944 = (

let uu____1945 = (hash_of_term t1)
in (Prims.strcat uu____1945 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " uu____1944))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let uu____1967 = (

let uu____1968 = (

let uu____1969 = (

let uu____1970 = (

let uu____1971 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right uu____1971 (FStar_String.concat " ")))
in (

let uu____1976 = (

let uu____1977 = (

let uu____1978 = (hash_of_term body)
in (

let uu____1979 = (

let uu____1980 = (

let uu____1981 = (weightToSmt wopt)
in (

let uu____1982 = (

let uu____1983 = (

let uu____1984 = (

let uu____1985 = (FStar_All.pipe_right pats (FStar_List.map (fun pats1 -> (

let uu____2001 = (FStar_List.map hash_of_term pats1)
in (FStar_All.pipe_right uu____2001 (FStar_String.concat " "))))))
in (FStar_All.pipe_right uu____1985 (FStar_String.concat "; ")))
in (Prims.strcat uu____1984 "))"))
in (Prims.strcat " " uu____1983))
in (Prims.strcat uu____1981 uu____1982)))
in (Prims.strcat " " uu____1980))
in (Prims.strcat uu____1978 uu____1979)))
in (Prims.strcat ")(! " uu____1977))
in (Prims.strcat uu____1970 uu____1976)))
in (Prims.strcat " (" uu____1969))
in (Prims.strcat (qop_to_string qop) uu____1968))
in (Prims.strcat "(" uu____1967))
end
| Let (es, body) -> begin
(

let uu____2014 = (

let uu____2015 = (

let uu____2016 = (FStar_List.map hash_of_term es)
in (FStar_All.pipe_right uu____2016 (FStar_String.concat " ")))
in (

let uu____2021 = (

let uu____2022 = (

let uu____2023 = (hash_of_term body)
in (Prims.strcat uu____2023 ")"))
in (Prims.strcat ") " uu____2022))
in (Prims.strcat uu____2015 uu____2021)))
in (Prims.strcat "(let (" uu____2014))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mkBoxFunctions : Prims.string  ->  (Prims.string * Prims.string) = (fun s -> ((s), ((Prims.strcat s "_proj_0"))))


let boxIntFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxInt")


let boxBoolFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxBool")


let boxStringFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxString")


let boxBitVecFun : Prims.int  ->  (Prims.string * Prims.string) = (fun sz -> (

let uu____2055 = (

let uu____2056 = (FStar_Util.string_of_int sz)
in (Prims.strcat "BoxBitVec" uu____2056))
in (mkBoxFunctions uu____2055)))


let isInjective : Prims.string  ->  Prims.bool = (fun s -> (match (((FStar_String.length s) >= (Prims.parse_int "3"))) with
| true -> begin
((

let uu____2064 = (FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3"))
in (Prims.op_Equality uu____2064 "Box")) && (

let uu____2066 = (

let uu____2067 = (FStar_String.list_of_string s)
in (FStar_List.existsML (fun c -> (Prims.op_Equality c 46 (*.*))) uu____2067))
in (not (uu____2066))))
end
| uu____2077 -> begin
false
end))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (

let uu____2088 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {tm = t; freevars = uu____2088; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((TrueOp), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((FalseOp), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____2205 = (

let uu____2206 = (FStar_Util.ensure_decimal i)
in Integer (uu____2206))
in (mk uu____2205 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____2217 = (FStar_Util.string_of_int i)
in (mkInteger uu____2217 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun uu____2282 r -> (match (uu____2282) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (TrueOp, uu____2308) -> begin
(mkFalse r)
end
| App (FalseOp, uu____2313) -> begin
(mkTrue r)
end
| uu____2318 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____2333 r -> (match (uu____2333) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____2341), uu____2342) -> begin
t2
end
| (uu____2347, App (TrueOp, uu____2348)) -> begin
t1
end
| (App (FalseOp, uu____2353), uu____2354) -> begin
(mkFalse r)
end
| (uu____2359, App (FalseOp, uu____2360)) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (uu____2377, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), uu____2386) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____2393 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____2412 r -> (match (uu____2412) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____2420), uu____2421) -> begin
(mkTrue r)
end
| (uu____2426, App (TrueOp, uu____2427)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____2432), uu____2433) -> begin
t2
end
| (uu____2438, App (FalseOp, uu____2439)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (uu____2456, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), uu____2465) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____2472 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____2491 r -> (match (uu____2491) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (uu____2499, App (TrueOp, uu____2500)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____2505), uu____2506) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____2511), uu____2512) -> begin
t2
end
| (uu____2517, App (Imp, (t1')::(t2')::[])) -> begin
(

let uu____2522 = (

let uu____2529 = (

let uu____2532 = (mkAnd ((t1), (t1')) r)
in (uu____2532)::(t2')::[])
in ((Imp), (uu____2529)))
in (mkApp' uu____2522 r))
end
| uu____2535 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op uu____2559 r -> (match (uu____2559) with
| (t1, t2) -> begin
(mkApp' ((op), ((t1)::(t2)::[])) r)
end))


let mkMinus : term  ->  FStar_Range.range  ->  term = (fun t r -> (mkApp' ((Minus), ((t)::[])) r))


let mkNatToBv : Prims.int  ->  term  ->  FStar_Range.range  ->  term = (fun sz t r -> (mkApp' ((NatToBv (sz)), ((t)::[])) r))


let mkBvUext : Prims.int  ->  term  ->  FStar_Range.range  ->  term = (fun sz t r -> (mkApp' ((BvUext (sz)), ((t)::[])) r))


let mkBvToNat : term  ->  FStar_Range.range  ->  term = (fun t r -> (mkApp' ((BvToNat), ((t)::[])) r))


let mkBvAnd : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvAnd)


let mkBvXor : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvXor)


let mkBvOr : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvOr)


let mkBvAdd : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvAdd)


let mkBvSub : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvSub)


let mkBvShl : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2704 r -> (match (uu____2704) with
| (t1, t2) -> begin
(

let uu____2712 = (

let uu____2719 = (

let uu____2722 = (

let uu____2725 = (mkNatToBv sz t2 r)
in (uu____2725)::[])
in (t1)::uu____2722)
in ((BvShl), (uu____2719)))
in (mkApp' uu____2712 r))
end))


let mkBvShr : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2745 r -> (match (uu____2745) with
| (t1, t2) -> begin
(

let uu____2753 = (

let uu____2760 = (

let uu____2763 = (

let uu____2766 = (mkNatToBv sz t2 r)
in (uu____2766)::[])
in (t1)::uu____2763)
in ((BvShr), (uu____2760)))
in (mkApp' uu____2753 r))
end))


let mkBvUdiv : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2786 r -> (match (uu____2786) with
| (t1, t2) -> begin
(

let uu____2794 = (

let uu____2801 = (

let uu____2804 = (

let uu____2807 = (mkNatToBv sz t2 r)
in (uu____2807)::[])
in (t1)::uu____2804)
in ((BvUdiv), (uu____2801)))
in (mkApp' uu____2794 r))
end))


let mkBvMod : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2827 r -> (match (uu____2827) with
| (t1, t2) -> begin
(

let uu____2835 = (

let uu____2842 = (

let uu____2845 = (

let uu____2848 = (mkNatToBv sz t2 r)
in (uu____2848)::[])
in (t1)::uu____2845)
in ((BvMod), (uu____2842)))
in (mkApp' uu____2835 r))
end))


let mkBvMul : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2868 r -> (match (uu____2868) with
| (t1, t2) -> begin
(

let uu____2876 = (

let uu____2883 = (

let uu____2886 = (

let uu____2889 = (mkNatToBv sz t2 r)
in (uu____2889)::[])
in (t1)::uu____2886)
in ((BvMul), (uu____2883)))
in (mkApp' uu____2876 r))
end))


let mkBvUlt : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvUlt)


let mkIff : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Iff)


let mkEq : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____2928 r -> (match (uu____2928) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (Var (f1), (s1)::[]), App (Var (f2), (s2)::[])) when ((Prims.op_Equality f1 f2) && (isInjective f1)) -> begin
(mk_bin_op Eq ((s1), (s2)) r)
end
| uu____2944 -> begin
(mk_bin_op Eq ((t1), (t2)) r)
end)
end))


let mkLT : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op LT)


let mkLTE : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op LTE)


let mkGT : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op GT)


let mkGTE : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op GTE)


let mkAdd : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Add)


let mkSub : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Sub)


let mkDiv : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Div)


let mkMul : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Mul)


let mkMod : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Mod)


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun uu____3071 r -> (match (uu____3071) with
| (t1, t2, t3) -> begin
(match (t1.tm) with
| App (TrueOp, uu____3082) -> begin
t2
end
| App (FalseOp, uu____3087) -> begin
t3
end
| uu____3092 -> begin
(match (((t2.tm), (t3.tm))) with
| (App (TrueOp, uu____3093), App (TrueOp, uu____3094)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____3103), uu____3104) -> begin
(

let uu____3109 = (

let uu____3114 = (mkNot t1 t1.rng)
in ((uu____3114), (t3)))
in (mkImp uu____3109 r))
end
| (uu____3115, App (TrueOp, uu____3116)) -> begin
(mkImp ((t1), (t2)) r)
end
| (uu____3121, uu____3122) -> begin
(mkApp' ((ITE), ((t1)::(t2)::(t3)::[])) r)
end)
end)
end))


let mkCases : term Prims.list  ->  FStar_Range.range  ->  term = (fun t r -> (match (t) with
| [] -> begin
(failwith "Impos")
end
| (hd1)::tl1 -> begin
(FStar_List.fold_left (fun out t1 -> (mkAnd ((out), (t1)) r)) hd1 tl1)
end))


let mkQuant : (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____3173 r -> (match (uu____3173) with
| (qop, pats, wopt, vars, body) -> begin
(match ((Prims.op_Equality (FStar_List.length vars) (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____3214 -> begin
(match (body.tm) with
| App (TrueOp, uu____3215) -> begin
body
end
| uu____3220 -> begin
(mk (Quant (((qop), (pats), (wopt), (vars), (body)))) r)
end)
end)
end))


let mkLet : (term Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____3243 r -> (match (uu____3243) with
| (es, body) -> begin
(match ((Prims.op_Equality (FStar_List.length es) (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____3257 -> begin
(mk (Let (((es), (body)))) r)
end)
end))


let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (

let nvars = (FStar_List.length fvs)
in (

let index_of = (fun fv -> (

let uu____3283 = (FStar_Util.try_find_index (fv_eq fv) fvs)
in (match (uu____3283) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((nvars - (i + (Prims.parse_int "1"))))
end)))
in (

let rec aux = (fun ix t1 -> (

let uu____3306 = (FStar_ST.op_Bang t1.freevars)
in (match (uu____3306) with
| FStar_Pervasives_Native.Some ([]) -> begin
t1
end
| uu____3370 -> begin
(match (t1.tm) with
| Integer (uu____3379) -> begin
t1
end
| BoundV (uu____3380) -> begin
t1
end
| FreeV (x) -> begin
(

let uu____3386 = (index_of x)
in (match (uu____3386) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (i) -> begin
(mkBoundV (i + ix) t1.rng)
end))
end
| App (op, tms) -> begin
(

let uu____3396 = (

let uu____3403 = (FStar_List.map (aux ix) tms)
in ((op), (uu____3403)))
in (mkApp' uu____3396 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____3411 = (

let uu____3412 = (

let uu____3419 = (aux ix t2)
in ((uu____3419), (r1), (r2)))
in Labeled (uu____3412))
in (mk uu____3411 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____3422 = (

let uu____3423 = (

let uu____3428 = (aux ix t2)
in ((uu____3428), (r)))
in LblPos (uu____3423))
in (mk uu____3422 t2.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n1 = (FStar_List.length vars)
in (

let uu____3451 = (

let uu____3470 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n1)))))
in (

let uu____3491 = (aux (ix + n1) body)
in ((qop), (uu____3470), (wopt), (vars), (uu____3491))))
in (mkQuant uu____3451 t1.rng)))
end
| Let (es, body) -> begin
(

let uu____3510 = (FStar_List.fold_left (fun uu____3528 e -> (match (uu____3528) with
| (ix1, l) -> begin
(

let uu____3548 = (

let uu____3551 = (aux ix1 e)
in (uu____3551)::l)
in (((ix1 + (Prims.parse_int "1"))), (uu____3548)))
end)) ((ix), ([])) es)
in (match (uu____3510) with
| (ix1, es_rev) -> begin
(

let uu____3562 = (

let uu____3569 = (aux ix1 body)
in (((FStar_List.rev es_rev)), (uu____3569)))
in (mkLet uu____3562 t1.rng))
end))
end)
end)))
in (aux (Prims.parse_int "0") t)))))


let inst : term Prims.list  ->  term  ->  term = (fun tms t -> (

let tms1 = (FStar_List.rev tms)
in (

let n1 = (FStar_List.length tms1)
in (

let rec aux = (fun shift t1 -> (match (t1.tm) with
| Integer (uu____3601) -> begin
t1
end
| FreeV (uu____3602) -> begin
t1
end
| BoundV (i) -> begin
(match ((((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1))) with
| true -> begin
(FStar_List.nth tms1 (i - shift))
end
| uu____3612 -> begin
t1
end)
end
| App (op, tms2) -> begin
(

let uu____3619 = (

let uu____3626 = (FStar_List.map (aux shift) tms2)
in ((op), (uu____3626)))
in (mkApp' uu____3619 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____3634 = (

let uu____3635 = (

let uu____3642 = (aux shift t2)
in ((uu____3642), (r1), (r2)))
in Labeled (uu____3635))
in (mk uu____3634 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____3645 = (

let uu____3646 = (

let uu____3651 = (aux shift t2)
in ((uu____3651), (r)))
in LblPos (uu____3646))
in (mk uu____3645 t2.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift1 = (shift + m)
in (

let uu____3679 = (

let uu____3698 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift1))))
in (

let uu____3715 = (aux shift1 body)
in ((qop), (uu____3698), (wopt), (vars), (uu____3715))))
in (mkQuant uu____3679 t1.rng))))
end
| Let (es, body) -> begin
(

let uu____3730 = (FStar_List.fold_left (fun uu____3748 e -> (match (uu____3748) with
| (ix, es1) -> begin
(

let uu____3768 = (

let uu____3771 = (aux shift e)
in (uu____3771)::es1)
in (((shift + (Prims.parse_int "1"))), (uu____3768)))
end)) ((shift), ([])) es)
in (match (uu____3730) with
| (shift1, es_rev) -> begin
(

let uu____3782 = (

let uu____3789 = (aux shift1 body)
in (((FStar_List.rev es_rev)), (uu____3789)))
in (mkLet uu____3782 t1.rng))
end))
end))
in (aux (Prims.parse_int "0") t)))))


let subst : term  ->  fv  ->  term  ->  term = (fun t fv s -> (

let uu____3807 = (abstr ((fv)::[]) t)
in (inst ((s)::[]) uu____3807)))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fv Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____3833 -> (match (uu____3833) with
| (qop, pats, wopt, vars, body) -> begin
(

let uu____3876 = (

let uu____3895 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (

let uu____3912 = (FStar_List.map fv_sort vars)
in (

let uu____3919 = (abstr vars body)
in ((qop), (uu____3895), (wopt), (uu____3912), (uu____3919)))))
in (mkQuant uu____3876))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____3952 r -> (match (uu____3952) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)) r)
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____4020 r -> (match (uu____4020) with
| (pats, wopt, vars, body) -> begin
(

let uu____4052 = (mkQuant' ((Forall), (pats), (wopt), (vars), (body)))
in (uu____4052 r))
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____4081 r -> (match (uu____4081) with
| (pats, vars, body) -> begin
(

let uu____4104 = (mkQuant' ((Forall), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
in (uu____4104 r))
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____4133 r -> (match (uu____4133) with
| (pats, vars, body) -> begin
(

let uu____4156 = (mkQuant' ((Exists), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
in (uu____4156 r))
end))


let mkLet' : ((fv * term) Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____4185 r -> (match (uu____4185) with
| (bindings, body) -> begin
(

let uu____4211 = (FStar_List.split bindings)
in (match (uu____4211) with
| (vars, es) -> begin
(

let uu____4230 = (

let uu____4237 = (abstr vars body)
in ((es), (uu____4237)))
in (mkLet uu____4230 r))
end))
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun uu____4260 -> (match (uu____4260) with
| (nm, vars, s, tm, c) -> begin
(

let uu____4294 = (

let uu____4307 = (FStar_List.map fv_sort vars)
in (

let uu____4314 = (abstr vars tm)
in ((nm), (uu____4307), (s), (uu____4314), (c))))
in DefineFun (uu____4294))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (

let uu____4322 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" uu____4322)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun uu____4335 id1 -> (match (uu____4335) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (

let a = (

let uu____4345 = (

let uu____4346 = (

let uu____4351 = (mkInteger' id1 norng)
in (

let uu____4352 = (

let uu____4353 = (

let uu____4360 = (constr_id_of_sort sort)
in (

let uu____4361 = (

let uu____4364 = (mkApp ((tok_name), ([])) norng)
in (uu____4364)::[])
in ((uu____4360), (uu____4361))))
in (mkApp uu____4353 norng))
in ((uu____4351), (uu____4352))))
in (mkEq uu____4346 norng))
in {assumption_term = uu____4345; assumption_caption = FStar_Pervasives_Native.Some ("fresh token"); assumption_name = a_name; assumption_fact_ids = []})
in Assume (a)))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun uu____4383 -> (match (uu____4383) with
| (name, arg_sorts, sort, id1) -> begin
(

let id2 = (FStar_Util.string_of_int id1)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (

let uu____4415 = (

let uu____4420 = (

let uu____4421 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____4421))
in ((uu____4420), (s)))
in (mkFreeV uu____4415 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (

let uu____4429 = (

let uu____4436 = (constr_id_of_sort sort)
in ((uu____4436), ((capp)::[])))
in (mkApp uu____4429 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (

let a = (

let uu____4441 = (

let uu____4442 = (

let uu____4453 = (

let uu____4454 = (

let uu____4459 = (mkInteger id2 norng)
in ((uu____4459), (cid_app)))
in (mkEq uu____4454 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____4453)))
in (mkForall uu____4442 norng))
in {assumption_term = uu____4441; assumption_caption = FStar_Pervasives_Native.Some ("Consrtructor distinct"); assumption_name = a_name; assumption_fact_ids = []})
in Assume (a))))))))
end))


let injective_constructor : (Prims.string * constructor_field Prims.list * sort)  ->  decls_t = (fun uu____4482 -> (match (uu____4482) with
| (name, fields, sort) -> begin
(

let n_bvars = (FStar_List.length fields)
in (

let bvar_name = (fun i -> (

let uu____4505 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____4505)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (

let uu____4532 = (

let uu____4537 = (bvar_name i)
in ((uu____4537), (s)))
in (mkFreeV uu____4532)))
in (

let bvars = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____4558 -> (match (uu____4558) with
| (uu____4565, s, uu____4567) -> begin
(

let uu____4568 = (bvar i s)
in (uu____4568 norng))
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let uu____4579 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____4607 -> (match (uu____4607) with
| (name1, s, projectible) -> begin
(

let cproj_app = (mkApp ((name1), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((name1), ((sort)::[]), (s), (FStar_Pervasives_Native.Some ("Projector"))))
in (match (projectible) with
| true -> begin
(

let a = (

let uu____4630 = (

let uu____4631 = (

let uu____4642 = (

let uu____4643 = (

let uu____4648 = (

let uu____4649 = (bvar i s)
in (uu____4649 norng))
in ((cproj_app), (uu____4648)))
in (mkEq uu____4643 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____4642)))
in (mkForall uu____4631 norng))
in {assumption_term = uu____4630; assumption_caption = FStar_Pervasives_Native.Some ("Projection inverse"); assumption_name = (Prims.strcat "projection_inverse_" name1); assumption_fact_ids = []})
in (proj_name)::(Assume (a))::[])
end
| uu____4664 -> begin
(proj_name)::[]
end)))
end))))
in (FStar_All.pipe_right uu____4579 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun uu____4675 -> (match (uu____4675) with
| (name, fields, sort, id1, injective) -> begin
(

let injective1 = (injective || true)
in (

let field_sorts = (FStar_All.pipe_right fields (FStar_List.map (fun uu____4703 -> (match (uu____4703) with
| (uu____4710, sort1, uu____4712) -> begin
sort1
end))))
in (

let cdecl = DeclFun (((name), (field_sorts), (sort), (FStar_Pervasives_Native.Some ("Constructor"))))
in (

let cid = (fresh_constructor ((name), (field_sorts), (sort), (id1)))
in (

let disc = (

let disc_name = (Prims.strcat "is-" name)
in (

let xfv = (("x"), (sort))
in (

let xx = (mkFreeV xfv norng)
in (

let disc_eq = (

let uu____4730 = (

let uu____4735 = (

let uu____4736 = (

let uu____4743 = (constr_id_of_sort sort)
in ((uu____4743), ((xx)::[])))
in (mkApp uu____4736 norng))
in (

let uu____4746 = (

let uu____4747 = (FStar_Util.string_of_int id1)
in (mkInteger uu____4747 norng))
in ((uu____4735), (uu____4746))))
in (mkEq uu____4730 norng))
in (

let uu____4748 = (

let uu____4763 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____4813 -> (match (uu____4813) with
| (proj, s, projectible) -> begin
(match (projectible) with
| true -> begin
(

let uu____4843 = (mkApp ((proj), ((xx)::[])) norng)
in ((uu____4843), ([])))
end
| uu____4856 -> begin
(

let fi = (

let uu____4862 = (

let uu____4863 = (FStar_Util.string_of_int i)
in (Prims.strcat "f_" uu____4863))
in ((uu____4862), (s)))
in (

let uu____4864 = (mkFreeV fi norng)
in ((uu____4864), ((fi)::[]))))
end)
end))))
in (FStar_All.pipe_right uu____4763 FStar_List.split))
in (match (uu____4748) with
| (proj_terms, ex_vars) -> begin
(

let ex_vars1 = (FStar_List.flatten ex_vars)
in (

let disc_inv_body = (

let uu____4945 = (

let uu____4950 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (uu____4950)))
in (mkEq uu____4945 norng))
in (

let disc_inv_body1 = (match (ex_vars1) with
| [] -> begin
disc_inv_body
end
| uu____4958 -> begin
(mkExists (([]), (ex_vars1), (disc_inv_body)) norng)
end)
in (

let disc_ax = (mkAnd ((disc_eq), (disc_inv_body1)) norng)
in (

let def = (mkDefineFun ((disc_name), ((xfv)::[]), (Bool_sort), (disc_ax), (FStar_Pervasives_Native.Some ("Discriminator definition"))))
in def)))))
end))))))
in (

let projs = (match (injective1) with
| true -> begin
(injective_constructor ((name), (fields), (sort)))
end
| uu____4998 -> begin
[]
end)
in (

let uu____4999 = (

let uu____5002 = (

let uu____5003 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (uu____5003))
in (uu____5002)::(cdecl)::(cid)::projs)
in (

let uu____5004 = (

let uu____5007 = (

let uu____5010 = (

let uu____5011 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (uu____5011))
in (uu____5010)::[])
in (FStar_List.append ((disc)::[]) uu____5007))
in (FStar_List.append uu____4999 uu____5004)))))))))
end))


let name_binders_inner : Prims.string FStar_Pervasives_Native.option  ->  (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun prefix_opt outer_names start sorts -> (

let uu____5066 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun uu____5121 s -> (match (uu____5121) with
| (names1, binders, n1) -> begin
(

let prefix1 = (match (s) with
| Term_sort -> begin
"@x"
end
| uu____5171 -> begin
"@u"
end)
in (

let prefix2 = (match (prefix_opt) with
| FStar_Pervasives_Native.None -> begin
prefix1
end
| FStar_Pervasives_Native.Some (p) -> begin
(Prims.strcat p prefix1)
end)
in (

let nm = (

let uu____5175 = (FStar_Util.string_of_int n1)
in (Prims.strcat prefix2 uu____5175))
in (

let names2 = (((nm), (s)))::names1
in (

let b = (

let uu____5188 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm uu____5188))
in ((names2), ((b)::binders), ((n1 + (Prims.parse_int "1")))))))))
end)) ((outer_names), ([]), (start))))
in (match (uu____5066) with
| (names1, binders, n1) -> begin
((names1), ((FStar_List.rev binders)), (n1))
end)))


let name_macro_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let uu____5267 = (name_binders_inner (FStar_Pervasives_Native.Some ("__")) [] (Prims.parse_int "0") sorts)
in (match (uu____5267) with
| (names1, binders, n1) -> begin
(((FStar_List.rev names1)), (binders))
end)))


let termToSmt : Prims.bool  ->  Prims.string  ->  term  ->  Prims.string = (fun print_ranges enclosing_name t -> (

let next_qid = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun depth -> (

let n1 = (FStar_ST.op_Bang ctr)
in ((FStar_Util.incr ctr);
(match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
enclosing_name
end
| uu____5559 -> begin
(

let uu____5560 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "%s.%s" enclosing_name uu____5560))
end);
))))
in (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (uu____5604); freevars = uu____5605; rng = uu____5606})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| uu____5620 -> begin
tm
end))))))))
in (

let rec aux' = (fun depth n1 names1 t1 -> (

let aux1 = (aux (depth + (Prims.parse_int "1")))
in (match (t1.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____5682 = (FStar_List.nth names1 i)
in (FStar_All.pipe_right uu____5682 FStar_Pervasives_Native.fst))
end
| FreeV (x) -> begin
(FStar_Pervasives_Native.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(

let uu____5697 = (op_to_string op)
in (

let uu____5698 = (

let uu____5699 = (FStar_List.map (aux1 n1 names1) tms)
in (FStar_All.pipe_right uu____5699 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" uu____5697 uu____5698)))
end
| Labeled (t2, uu____5705, uu____5706) -> begin
(aux1 n1 names1 t2)
end
| LblPos (t2, s) -> begin
(

let uu____5709 = (aux1 n1 names1 t2)
in (FStar_Util.format2 "(! %s :lblpos %s)" uu____5709 s))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let qid = (next_qid ())
in (

let uu____5732 = (name_binders_inner FStar_Pervasives_Native.None names1 n1 sorts)
in (match (uu____5732) with
| (names2, binders, n2) -> begin
(

let binders1 = (FStar_All.pipe_right binders (FStar_String.concat " "))
in (

let pats1 = (remove_guard_free pats)
in (

let pats_str = (match (pats1) with
| ([])::[] -> begin
";;no pats"
end
| [] -> begin
";;no pats"
end
| uu____5781 -> begin
(

let uu____5786 = (FStar_All.pipe_right pats1 (FStar_List.map (fun pats2 -> (

let uu____5802 = (

let uu____5803 = (FStar_List.map (fun p -> (

let uu____5809 = (aux1 n2 names2 p)
in (FStar_Util.format1 "%s" uu____5809))) pats2)
in (FStar_String.concat " " uu____5803))
in (FStar_Util.format1 "\n:pattern (%s)" uu____5802)))))
in (FStar_All.pipe_right uu____5786 (FStar_String.concat "\n")))
end)
in (

let uu____5812 = (

let uu____5815 = (

let uu____5818 = (

let uu____5821 = (aux1 n2 names2 body)
in (

let uu____5822 = (

let uu____5825 = (weightToSmt wopt)
in (uu____5825)::(pats_str)::(qid)::[])
in (uu____5821)::uu____5822))
in (binders1)::uu____5818)
in ((qop_to_string qop))::uu____5815)
in (FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))" uu____5812)))))
end)))
end
| Let (es, body) -> begin
(

let uu____5832 = (FStar_List.fold_left (fun uu____5869 e -> (match (uu____5869) with
| (names0, binders, n0) -> begin
(

let nm = (

let uu____5919 = (FStar_Util.string_of_int n0)
in (Prims.strcat "@lb" uu____5919))
in (

let names01 = (((nm), (Term_sort)))::names0
in (

let b = (

let uu____5932 = (aux1 n1 names1 e)
in (FStar_Util.format2 "(%s %s)" nm uu____5932))
in ((names01), ((b)::binders), ((n0 + (Prims.parse_int "1")))))))
end)) ((names1), ([]), (n1)) es)
in (match (uu____5832) with
| (names2, binders, n2) -> begin
(

let uu____5964 = (aux1 n2 names2 body)
in (FStar_Util.format2 "(let (%s)\n%s)" (FStar_String.concat " " binders) uu____5964))
end))
end)))
and aux = (fun depth n1 names1 t1 -> (

let s = (aux' depth n1 names1 t1)
in (match ((print_ranges && (Prims.op_disEquality t1.rng norng))) with
| true -> begin
(

let uu____5972 = (FStar_Range.string_of_range t1.rng)
in (

let uu____5973 = (FStar_Range.string_of_use_range t1.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____5972 uu____5973 s)))
end
| uu____5974 -> begin
s
end)))
in (aux (Prims.parse_int "0") (Prims.parse_int "0") [] t)))))


let caption_to_string : Prims.string FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___56_5981 -> (match (uu___56_5981) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (c) -> begin
(Prims.strcat ";;;;;;;;;;;;;;;;" (Prims.strcat c "\n"))
end))


let rec declToSmt' : Prims.bool  ->  Prims.string  ->  decl  ->  Prims.string = (fun print_ranges z3options decl -> (

let escape = (fun s -> (FStar_Util.replace_char s 39 (*'*) 95 (*_*)))
in (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(

let uu____6029 = (FStar_Options.log_queries ())
in (match (uu____6029) with
| true -> begin
(

let uu____6030 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun uu___57_6034 -> (match (uu___57_6034) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" uu____6030))
end
| uu____6041 -> begin
""
end))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (

let uu____6053 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" (caption_to_string c) f (FStar_String.concat " " l) uu____6053)))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let uu____6063 = (name_macro_binders arg_sorts)
in (match (uu____6063) with
| (names1, binders) -> begin
(

let body1 = (

let uu____6095 = (FStar_List.map (fun x -> (mkFreeV x norng)) names1)
in (inst uu____6095 body))
in (

let uu____6108 = (strSort retsort)
in (

let uu____6109 = (termToSmt print_ranges (escape f) body1)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" (caption_to_string c) f (FStar_String.concat " " binders) uu____6108 uu____6109))))
end))
end
| Assume (a) -> begin
(

let fact_ids_to_string = (fun ids -> (FStar_All.pipe_right ids (FStar_List.map (fun uu___58_6130 -> (match (uu___58_6130) with
| Name (n1) -> begin
(

let uu____6132 = (FStar_Ident.text_of_lid n1)
in (Prims.strcat "Name " uu____6132))
end
| Namespace (ns) -> begin
(

let uu____6134 = (FStar_Ident.text_of_lid ns)
in (Prims.strcat "Namespace " uu____6134))
end
| Tag (t) -> begin
(Prims.strcat "Tag " t)
end)))))
in (

let fids = (

let uu____6137 = (FStar_Options.log_queries ())
in (match (uu____6137) with
| true -> begin
(

let uu____6138 = (

let uu____6139 = (fact_ids_to_string a.assumption_fact_ids)
in (FStar_String.concat "; " uu____6139))
in (FStar_Util.format1 ";;; Fact-ids: %s\n" uu____6138))
end
| uu____6142 -> begin
""
end))
in (

let n1 = (escape a.assumption_name)
in (

let uu____6144 = (termToSmt print_ranges n1 a.assumption_term)
in (FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" (caption_to_string a.assumption_caption) fids uu____6144 n1)))))
end
| Eval (t) -> begin
(

let uu____6146 = (termToSmt print_ranges "eval" t)
in (FStar_Util.format1 "(eval %s)" uu____6146))
end
| Echo (s) -> begin
(FStar_Util.format1 "(echo \"%s\")" s)
end
| RetainAssumptions (uu____6148) -> begin
""
end
| CheckSat -> begin
"(echo \"<result>\")\n(check-sat)\n(echo \"</result>\")"
end
| GetUnsatCore -> begin
"(echo \"<unsat-core>\")\n(get-unsat-core)\n(echo \"</unsat-core>\")"
end
| Push -> begin
"(push)"
end
| Pop -> begin
"(pop)"
end
| SetOption (s, v1) -> begin
(FStar_Util.format2 "(set-option :%s %s)" s v1)
end
| GetStatistics -> begin
"(echo \"<statistics>\")\n(get-info :all-statistics)\n(echo \"</statistics>\")"
end
| GetReasonUnknown -> begin
"(echo \"<reason-unknown>\")\n(get-info :reason-unknown)\n(echo \"</reason-unknown>\")"
end)))
and declToSmt : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (declToSmt' true z3options decl))
and declToSmt_no_caps : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (declToSmt' false z3options decl))
and mkPrelude : Prims.string  ->  Prims.string = (fun z3options -> (

let basic = (Prims.strcat z3options "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (iff (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(declare-fun __uu__PartialApp () Term)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))")
in (

let constrs = ((("FString_const"), (((("FString_const_proj_0"), (Int_sort), (true)))::[]), (String_sort), ((Prims.parse_int "0")), (true)))::((("Tm_type"), ([]), (Term_sort), ((Prims.parse_int "2")), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "3")), (false)))::((("Tm_unit"), ([]), (Term_sort), ((Prims.parse_int "6")), (true)))::((((FStar_Pervasives_Native.fst boxIntFun)), (((((FStar_Pervasives_Native.snd boxIntFun)), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "7")), (true)))::((((FStar_Pervasives_Native.fst boxBoolFun)), (((((FStar_Pervasives_Native.snd boxBoolFun)), (Bool_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "8")), (true)))::((((FStar_Pervasives_Native.fst boxStringFun)), (((((FStar_Pervasives_Native.snd boxStringFun)), (String_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "9")), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort), (true)))::((("LexCons_1"), (Term_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "11")), (true)))::[]
in (

let bcons = (

let uu____6477 = (

let uu____6480 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right uu____6480 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right uu____6477 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mkBvConstructor : Prims.int  ->  decls_t = (fun sz -> (

let uu____6497 = (

let uu____6516 = (

let uu____6517 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____6517))
in (

let uu____6522 = (

let uu____6531 = (

let uu____6538 = (

let uu____6539 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____6539))
in ((uu____6538), (BitVec_sort (sz)), (true)))
in (uu____6531)::[])
in ((uu____6516), (uu____6522), (Term_sort), (((Prims.parse_int "12") + sz)), (true))))
in (FStar_All.pipe_right uu____6497 constructor_to_decl)))


let __range_c : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let mk_Range_const : unit  ->  term = (fun uu____6623 -> (

let i = (FStar_ST.op_Bang __range_c)
in ((

let uu____6655 = (

let uu____6656 = (FStar_ST.op_Bang __range_c)
in (uu____6656 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals __range_c uu____6655));
(

let uu____6715 = (

let uu____6722 = (

let uu____6725 = (mkInteger' i norng)
in (uu____6725)::[])
in (("Range_const"), (uu____6722)))
in (mkApp uu____6715 norng));
)))


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____6757 = (

let uu____6764 = (

let uu____6767 = (mkInteger' i norng)
in (uu____6767)::[])
in (("Tm_uvar"), (uu____6764)))
in (mkApp uu____6757 r)))


let mk_Term_unit : term = (mkApp (("Tm_unit"), ([])) norng)


let elim_box : Prims.bool  ->  Prims.string  ->  Prims.string  ->  term  ->  term = (fun cond u v1 t -> (match (t.tm) with
| App (Var (v'), (t1)::[]) when ((Prims.op_Equality v1 v') && cond) -> begin
t1
end
| uu____6796 -> begin
(mkApp ((u), ((t)::[])) t.rng)
end))


let maybe_elim_box : Prims.string  ->  Prims.string  ->  term  ->  term = (fun u v1 t -> (

let uu____6814 = (FStar_Options.smtencoding_elim_box ())
in (elim_box uu____6814 u v1 t)))


let boxInt : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxIntFun) (FStar_Pervasives_Native.snd boxIntFun) t))


let unboxInt : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxIntFun) (FStar_Pervasives_Native.fst boxIntFun) t))


let boxBool : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxBoolFun) (FStar_Pervasives_Native.snd boxBoolFun) t))


let unboxBool : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxBoolFun) (FStar_Pervasives_Native.fst boxBoolFun) t))


let boxString : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxStringFun) (FStar_Pervasives_Native.snd boxStringFun) t))


let unboxString : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxStringFun) (FStar_Pervasives_Native.fst boxStringFun) t))


let boxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let uu____6855 = (

let uu____6856 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____6856))
in (

let uu____6861 = (

let uu____6862 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____6862))
in (elim_box true uu____6855 uu____6861 t))))


let unboxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let uu____6877 = (

let uu____6878 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____6878))
in (

let uu____6883 = (

let uu____6884 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____6884))
in (elim_box true uu____6877 uu____6883 t))))


let boxTerm : sort  ->  term  ->  term = (fun sort t -> (match (sort) with
| Int_sort -> begin
(boxInt t)
end
| Bool_sort -> begin
(boxBool t)
end
| String_sort -> begin
(boxString t)
end
| BitVec_sort (sz) -> begin
(boxBitVec sz t)
end
| uu____6900 -> begin
(FStar_Exn.raise FStar_Util.Impos)
end))


let unboxTerm : sort  ->  term  ->  term = (fun sort t -> (match (sort) with
| Int_sort -> begin
(unboxInt t)
end
| Bool_sort -> begin
(unboxBool t)
end
| String_sort -> begin
(unboxString t)
end
| BitVec_sort (sz) -> begin
(unboxBitVec sz t)
end
| uu____6912 -> begin
(FStar_Exn.raise FStar_Util.Impos)
end))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n1) -> begin
(FStar_Util.format1 "(Integer %s)" n1)
end
| BoundV (n1) -> begin
(

let uu____6934 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(BoundV %s)" uu____6934))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv))
end
| App (op, l) -> begin
(

let uu____6946 = (op_to_string op)
in (

let uu____6947 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" uu____6946 uu____6947)))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____6951 = (print_smt_term t1)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 uu____6951))
end
| LblPos (t1, s) -> begin
(

let uu____6954 = (print_smt_term t1)
in (FStar_Util.format2 "(LblPos %s %s)" s uu____6954))
end
| Quant (qop, l, uu____6957, uu____6958, t1) -> begin
(

let uu____6976 = (print_smt_term_list_list l)
in (

let uu____6977 = (print_smt_term t1)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____6976 uu____6977)))
end
| Let (es, body) -> begin
(

let uu____6984 = (print_smt_term_list es)
in (

let uu____6985 = (print_smt_term body)
in (FStar_Util.format2 "(let %s %s)" uu____6984 uu____6985)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (

let uu____6989 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right uu____6989 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l1 -> (

let uu____7008 = (

let uu____7009 = (

let uu____7010 = (print_smt_term_list l1)
in (Prims.strcat uu____7010 " ] "))
in (Prims.strcat "; [ " uu____7009))
in (Prims.strcat s uu____7008))) "" l))


let getBoxedInteger : term  ->  Prims.int FStar_Pervasives_Native.option = (fun t -> (match (t.tm) with
| App (Var (s), (t2)::[]) when (Prims.op_Equality s (FStar_Pervasives_Native.fst boxIntFun)) -> begin
(match (t2.tm) with
| Integer (n1) -> begin
(

let uu____7027 = (FStar_Util.int_of_string n1)
in FStar_Pervasives_Native.Some (uu____7027))
end
| uu____7028 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____7029 -> begin
FStar_Pervasives_Native.None
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2p"), ({tm = App (Var ("Prims.op_Equality"), (uu____7042)::(t1)::(t2)::[]); freevars = uu____7045; rng = uu____7046})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2p"), ({tm = App (Var ("Prims.op_disEquality"), (uu____7059)::(t1)::(t2)::[]); freevars = uu____7062; rng = uu____7063})::[]) -> begin
(

let uu____7076 = (mkEq ((t1), (t2)) norng)
in (mkNot uu____7076 t.rng))
end
| App (Var ("Prims.b2p"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = uu____7079; rng = uu____7080})::[]) -> begin
(

let uu____7093 = (

let uu____7098 = (unboxInt t1)
in (

let uu____7099 = (unboxInt t2)
in ((uu____7098), (uu____7099))))
in (mkLTE uu____7093 t.rng))
end
| App (Var ("Prims.b2p"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = uu____7102; rng = uu____7103})::[]) -> begin
(

let uu____7116 = (

let uu____7121 = (unboxInt t1)
in (

let uu____7122 = (unboxInt t2)
in ((uu____7121), (uu____7122))))
in (mkLT uu____7116 t.rng))
end
| App (Var ("Prims.b2p"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = uu____7125; rng = uu____7126})::[]) -> begin
(

let uu____7139 = (

let uu____7144 = (unboxInt t1)
in (

let uu____7145 = (unboxInt t2)
in ((uu____7144), (uu____7145))))
in (mkGTE uu____7139 t.rng))
end
| App (Var ("Prims.b2p"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = uu____7148; rng = uu____7149})::[]) -> begin
(

let uu____7162 = (

let uu____7167 = (unboxInt t1)
in (

let uu____7168 = (unboxInt t2)
in ((uu____7167), (uu____7168))))
in (mkGT uu____7162 t.rng))
end
| App (Var ("Prims.b2p"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = uu____7171; rng = uu____7172})::[]) -> begin
(

let uu____7185 = (

let uu____7190 = (unboxBool t1)
in (

let uu____7191 = (unboxBool t2)
in ((uu____7190), (uu____7191))))
in (mkAnd uu____7185 t.rng))
end
| App (Var ("Prims.b2p"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = uu____7194; rng = uu____7195})::[]) -> begin
(

let uu____7208 = (

let uu____7213 = (unboxBool t1)
in (

let uu____7214 = (unboxBool t2)
in ((uu____7213), (uu____7214))))
in (mkOr uu____7208 t.rng))
end
| App (Var ("Prims.b2p"), ({tm = App (Var ("Prims.op_Negation"), (t1)::[]); freevars = uu____7216; rng = uu____7217})::[]) -> begin
(

let uu____7230 = (unboxBool t1)
in (mkNot uu____7230 t1.rng))
end
| App (Var ("Prims.b2p"), ({tm = App (Var ("FStar.BV.bvult"), (t0)::(t1)::(t2)::[]); freevars = uu____7234; rng = uu____7235})::[]) when (

let uu____7248 = (getBoxedInteger t0)
in (FStar_Util.is_some uu____7248)) -> begin
(

let sz = (

let uu____7252 = (getBoxedInteger t0)
in (match (uu____7252) with
| FStar_Pervasives_Native.Some (sz) -> begin
sz
end
| uu____7256 -> begin
(failwith "impossible")
end))
in (

let uu____7259 = (

let uu____7264 = (unboxBitVec sz t1)
in (

let uu____7265 = (unboxBitVec sz t2)
in ((uu____7264), (uu____7265))))
in (mkBvUlt uu____7259 t.rng)))
end
| App (Var ("Prims.equals"), (uu____7266)::({tm = App (Var ("FStar.BV.bvult"), (t0)::(t1)::(t2)::[]); freevars = uu____7270; rng = uu____7271})::(uu____7272)::[]) when (

let uu____7285 = (getBoxedInteger t0)
in (FStar_Util.is_some uu____7285)) -> begin
(

let sz = (

let uu____7289 = (getBoxedInteger t0)
in (match (uu____7289) with
| FStar_Pervasives_Native.Some (sz) -> begin
sz
end
| uu____7293 -> begin
(failwith "impossible")
end))
in (

let uu____7296 = (

let uu____7301 = (unboxBitVec sz t1)
in (

let uu____7302 = (unboxBitVec sz t2)
in ((uu____7301), (uu____7302))))
in (mkBvUlt uu____7296 t.rng)))
end
| App (Var ("Prims.b2p"), (t1)::[]) -> begin
(

let uu___59_7306 = (unboxBool t1)
in {tm = uu___59_7306.tm; freevars = uu___59_7306.freevars; rng = t.rng})
end
| uu____7307 -> begin
(mkApp (("Valid"), ((t)::[])) t.rng)
end))


let mk_HasType : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasType"), ((v1)::(t)::[])) t.rng))


let mk_HasTypeZ : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasTypeZ"), ((v1)::(t)::[])) t.rng))


let mk_IsTyped : term  ->  term = (fun v1 -> (mkApp (("IsTyped"), ((v1)::[])) norng))


let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v1 t -> (

let uu____7356 = (FStar_Options.unthrottle_inductives ())
in (match (uu____7356) with
| true -> begin
(mk_HasType v1 t)
end
| uu____7357 -> begin
(mkApp (("HasTypeFuel"), ((f)::(v1)::(t)::[])) t.rng)
end)))


let mk_HasTypeWithFuel : term FStar_Pervasives_Native.option  ->  term  ->  term  ->  term = (fun f v1 t -> (match (f) with
| FStar_Pervasives_Native.None -> begin
(mk_HasType v1 t)
end
| FStar_Pervasives_Native.Some (f1) -> begin
(mk_HasTypeFuel f1 v1 t)
end))


let mk_NoHoist : term  ->  term  ->  term = (fun dummy b -> (mkApp (("NoHoist"), ((dummy)::(b)::[])) b.rng))


let mk_Destruct : term  ->  FStar_Range.range  ->  term = (fun v1 -> (mkApp (("Destruct"), ((v1)::[]))))


let mk_Rank : term  ->  FStar_Range.range  ->  term = (fun x -> (mkApp (("Rank"), ((x)::[]))))


let mk_tester : Prims.string  ->  term  ->  term = (fun n1 t -> (mkApp (((Prims.strcat "is-" n1)), ((t)::[])) t.rng))


let mk_ApplyTF : term  ->  term  ->  term = (fun t t' -> (mkApp (("ApplyTF"), ((t)::(t')::[])) t.rng))


let mk_ApplyTT : term  ->  term  ->  FStar_Range.range  ->  term = (fun t t' r -> (mkApp (("ApplyTT"), ((t)::(t')::[])) r))


let kick_partial_app : term  ->  term = (fun t -> (

let uu____7462 = (

let uu____7463 = (mkApp (("__uu__PartialApp"), ([])) t.rng)
in (mk_ApplyTT uu____7463 t t.rng))
in (FStar_All.pipe_right uu____7462 mk_Valid)))


let mk_String_const : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____7476 = (

let uu____7483 = (

let uu____7486 = (mkInteger' i norng)
in (uu____7486)::[])
in (("FString_const"), (uu____7483)))
in (mkApp uu____7476 r)))


let mk_Precedes : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (

let uu____7504 = (mkApp (("Precedes"), ((x1)::(x2)::[])) r)
in (FStar_All.pipe_right uu____7504 mk_Valid)))


let mk_LexCons : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (mkApp (("LexCons"), ((x1)::(x2)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
(mkApp (("ZFuel"), ([])) norng)
end
| uu____7531 -> begin
(

let uu____7532 = (

let uu____7539 = (

let uu____7542 = (n_fuel (n1 - (Prims.parse_int "1")))
in (uu____7542)::[])
in (("SFuel"), (uu____7539)))
in (mkApp uu____7532 norng))
end))


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term FStar_Pervasives_Native.option  ->  term FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  term FStar_Pervasives_Native.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (FStar_Pervasives_Native.Some (p11), FStar_Pervasives_Native.Some (p21)) -> begin
(

let uu____7582 = (mkAnd ((p11), (p21)) r)
in FStar_Pervasives_Native.Some (uu____7582))
end
| (FStar_Pervasives_Native.Some (p), FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.Some (p)
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (p)) -> begin
FStar_Pervasives_Native.Some (p)
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.None
end))


let mk_and_opt_l : term FStar_Pervasives_Native.option Prims.list  ->  FStar_Range.range  ->  term FStar_Pervasives_Native.option = (fun pl r -> (FStar_List.fold_right (fun p out -> (mk_and_opt p out r)) pl FStar_Pervasives_Native.None))


let mk_and_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____7643 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l uu____7643)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____7662 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l uu____7662)))


let mk_haseq : term  ->  term = (fun t -> (

let uu____7672 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid uu____7672)))




