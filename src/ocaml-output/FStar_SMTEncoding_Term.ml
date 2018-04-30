
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
| uu____552 -> begin
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
| uu____566 -> begin
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
| uu____584 -> begin
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
| uu____616 -> begin
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
| uu____666 -> begin
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
| uu____740 -> begin
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
| uu____778 -> begin
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
| uu____814 -> begin
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
| uu____990 -> begin
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
| uu____1004 -> begin
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
| uu____1018 -> begin
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
| uu____1169 -> begin
false
end))


let uu___is_DeclFun : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DeclFun (_0) -> begin
true
end
| uu____1186 -> begin
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
| uu____1242 -> begin
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
| uu____1292 -> begin
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
| uu____1306 -> begin
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
| uu____1320 -> begin
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
| uu____1334 -> begin
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
| uu____1350 -> begin
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
| uu____1369 -> begin
false
end))


let uu___is_Pop : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____1375 -> begin
false
end))


let uu___is_CheckSat : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckSat -> begin
true
end
| uu____1381 -> begin
false
end))


let uu___is_GetUnsatCore : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetUnsatCore -> begin
true
end
| uu____1387 -> begin
false
end))


let uu___is_SetOption : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOption (_0) -> begin
true
end
| uu____1398 -> begin
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
| uu____1423 -> begin
false
end))


let uu___is_GetReasonUnknown : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetReasonUnknown -> begin
true
end
| uu____1429 -> begin
false
end))


type decls_t =
decl Prims.list


type error_label =
(fv * Prims.string * FStar_Range.range)


type error_labels =
error_label Prims.list


let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> (Prims.op_Equality (FStar_Pervasives_Native.fst x) (FStar_Pervasives_Native.fst y)))


let fv_sort : 'Auu____1456 'Auu____1457 . ('Auu____1456 * 'Auu____1457)  ->  'Auu____1457 = (fun x -> (FStar_Pervasives_Native.snd x))


let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match (((x.tm), (y.tm))) with
| (FreeV (x1), FreeV (y1)) -> begin
(fv_eq x1 y1)
end
| uu____1491 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun uu___48_1500 -> (match (uu___48_1500) with
| {tm = FreeV (x); freevars = uu____1502; rng = uu____1503} -> begin
(fv_sort x)
end
| uu____1516 -> begin
(failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun uu___49_1521 -> (match (uu___49_1521) with
| {tm = FreeV (fv); freevars = uu____1523; rng = uu____1524} -> begin
fv
end
| uu____1537 -> begin
(failwith "impossible")
end))


let rec freevars : term  ->  (Prims.string * sort) Prims.list = (fun t -> (match (t.tm) with
| Integer (uu____1555) -> begin
[]
end
| BoundV (uu____1560) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (uu____1578, tms) -> begin
(FStar_List.collect freevars tms)
end
| Quant (uu____1588, uu____1589, uu____1590, uu____1591, t1) -> begin
(freevars t1)
end
| Labeled (t1, uu____1610, uu____1611) -> begin
(freevars t1)
end
| LblPos (t1, uu____1613) -> begin
(freevars t1)
end
| Let (es, body) -> begin
(FStar_List.collect freevars ((body)::es))
end))


let free_variables : term  ->  fvs = (fun t -> (

let uu____1629 = (FStar_ST.op_Bang t.freevars)
in (match (uu____1629) with
| FStar_Pervasives_Native.Some (b) -> begin
b
end
| FStar_Pervasives_Native.None -> begin
(

let fvs = (

let uu____1703 = (freevars t)
in (FStar_Util.remove_dups fv_eq uu____1703))
in ((FStar_ST.op_Colon_Equals t.freevars (FStar_Pervasives_Native.Some (fvs)));
fvs;
))
end)))


let qop_to_string : qop  ->  Prims.string = (fun uu___50_1764 -> (match (uu___50_1764) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun uu___51_1769 -> (match (uu___51_1769) with
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

let uu____1771 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ zero_extend %s)" uu____1771))
end
| NatToBv (n1) -> begin
(

let uu____1773 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ int2bv %s)" uu____1773))
end
| Var (s) -> begin
s
end))


let weightToSmt : Prims.int FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___52_1781 -> (match (uu___52_1781) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (i) -> begin
(

let uu____1785 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" uu____1785))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____1797 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" uu____1797))
end
| FreeV (x) -> begin
(

let uu____1803 = (

let uu____1804 = (strSort (FStar_Pervasives_Native.snd x))
in (Prims.strcat ":" uu____1804))
in (Prims.strcat (FStar_Pervasives_Native.fst x) uu____1803))
end
| App (op, tms) -> begin
(

let uu____1811 = (

let uu____1812 = (op_to_string op)
in (

let uu____1813 = (

let uu____1814 = (

let uu____1815 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right uu____1815 (FStar_String.concat " ")))
in (Prims.strcat uu____1814 ")"))
in (Prims.strcat uu____1812 uu____1813)))
in (Prims.strcat "(" uu____1811))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____1823 = (hash_of_term t1)
in (

let uu____1824 = (

let uu____1825 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 uu____1825))
in (Prims.strcat uu____1823 uu____1824)))
end
| LblPos (t1, r) -> begin
(

let uu____1828 = (

let uu____1829 = (hash_of_term t1)
in (Prims.strcat uu____1829 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " uu____1828))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let uu____1851 = (

let uu____1852 = (

let uu____1853 = (

let uu____1854 = (

let uu____1855 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right uu____1855 (FStar_String.concat " ")))
in (

let uu____1860 = (

let uu____1861 = (

let uu____1862 = (hash_of_term body)
in (

let uu____1863 = (

let uu____1864 = (

let uu____1865 = (weightToSmt wopt)
in (

let uu____1866 = (

let uu____1867 = (

let uu____1868 = (

let uu____1869 = (FStar_All.pipe_right pats (FStar_List.map (fun pats1 -> (

let uu____1885 = (FStar_List.map hash_of_term pats1)
in (FStar_All.pipe_right uu____1885 (FStar_String.concat " "))))))
in (FStar_All.pipe_right uu____1869 (FStar_String.concat "; ")))
in (Prims.strcat uu____1868 "))"))
in (Prims.strcat " " uu____1867))
in (Prims.strcat uu____1865 uu____1866)))
in (Prims.strcat " " uu____1864))
in (Prims.strcat uu____1862 uu____1863)))
in (Prims.strcat ")(! " uu____1861))
in (Prims.strcat uu____1854 uu____1860)))
in (Prims.strcat " (" uu____1853))
in (Prims.strcat (qop_to_string qop) uu____1852))
in (Prims.strcat "(" uu____1851))
end
| Let (es, body) -> begin
(

let uu____1898 = (

let uu____1899 = (

let uu____1900 = (FStar_List.map hash_of_term es)
in (FStar_All.pipe_right uu____1900 (FStar_String.concat " ")))
in (

let uu____1905 = (

let uu____1906 = (

let uu____1907 = (hash_of_term body)
in (Prims.strcat uu____1907 ")"))
in (Prims.strcat ") " uu____1906))
in (Prims.strcat uu____1899 uu____1905)))
in (Prims.strcat "(let (" uu____1898))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mkBoxFunctions : Prims.string  ->  (Prims.string * Prims.string) = (fun s -> ((s), ((Prims.strcat s "_proj_0"))))


let boxIntFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxInt")


let boxBoolFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxBool")


let boxStringFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxString")


let boxBitVecFun : Prims.int  ->  (Prims.string * Prims.string) = (fun sz -> (

let uu____1939 = (

let uu____1940 = (FStar_Util.string_of_int sz)
in (Prims.strcat "BoxBitVec" uu____1940))
in (mkBoxFunctions uu____1939)))


let isInjective : Prims.string  ->  Prims.bool = (fun s -> (match (((FStar_String.length s) >= (Prims.parse_int "3"))) with
| true -> begin
((

let uu____1948 = (FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3"))
in (Prims.op_Equality uu____1948 "Box")) && (

let uu____1950 = (

let uu____1951 = (FStar_String.list_of_string s)
in (FStar_List.existsML (fun c -> (Prims.op_Equality c 46 (*.*))) uu____1951))
in (not (uu____1950))))
end
| uu____1961 -> begin
false
end))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (

let uu____1972 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {tm = t; freevars = uu____1972; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((TrueOp), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((FalseOp), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____2041 = (

let uu____2042 = (FStar_Util.ensure_decimal i)
in Integer (uu____2042))
in (mk uu____2041 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____2053 = (FStar_Util.string_of_int i)
in (mkInteger uu____2053 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun uu____2118 r -> (match (uu____2118) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (TrueOp, uu____2144) -> begin
(mkFalse r)
end
| App (FalseOp, uu____2149) -> begin
(mkTrue r)
end
| uu____2154 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____2169 r -> (match (uu____2169) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____2177), uu____2178) -> begin
t2
end
| (uu____2183, App (TrueOp, uu____2184)) -> begin
t1
end
| (App (FalseOp, uu____2189), uu____2190) -> begin
(mkFalse r)
end
| (uu____2195, App (FalseOp, uu____2196)) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (uu____2213, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), uu____2222) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____2229 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____2248 r -> (match (uu____2248) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____2256), uu____2257) -> begin
(mkTrue r)
end
| (uu____2262, App (TrueOp, uu____2263)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____2268), uu____2269) -> begin
t2
end
| (uu____2274, App (FalseOp, uu____2275)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (uu____2292, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), uu____2301) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____2308 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____2327 r -> (match (uu____2327) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (uu____2335, App (TrueOp, uu____2336)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____2341), uu____2342) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____2347), uu____2348) -> begin
t2
end
| (uu____2353, App (Imp, (t1')::(t2')::[])) -> begin
(

let uu____2358 = (

let uu____2365 = (

let uu____2368 = (mkAnd ((t1), (t1')) r)
in (uu____2368)::(t2')::[])
in ((Imp), (uu____2365)))
in (mkApp' uu____2358 r))
end
| uu____2371 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op uu____2395 r -> (match (uu____2395) with
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


let mkBvShl : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2540 r -> (match (uu____2540) with
| (t1, t2) -> begin
(

let uu____2548 = (

let uu____2555 = (

let uu____2558 = (

let uu____2561 = (mkNatToBv sz t2 r)
in (uu____2561)::[])
in (t1)::uu____2558)
in ((BvShl), (uu____2555)))
in (mkApp' uu____2548 r))
end))


let mkBvShr : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2581 r -> (match (uu____2581) with
| (t1, t2) -> begin
(

let uu____2589 = (

let uu____2596 = (

let uu____2599 = (

let uu____2602 = (mkNatToBv sz t2 r)
in (uu____2602)::[])
in (t1)::uu____2599)
in ((BvShr), (uu____2596)))
in (mkApp' uu____2589 r))
end))


let mkBvUdiv : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2622 r -> (match (uu____2622) with
| (t1, t2) -> begin
(

let uu____2630 = (

let uu____2637 = (

let uu____2640 = (

let uu____2643 = (mkNatToBv sz t2 r)
in (uu____2643)::[])
in (t1)::uu____2640)
in ((BvUdiv), (uu____2637)))
in (mkApp' uu____2630 r))
end))


let mkBvMod : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2663 r -> (match (uu____2663) with
| (t1, t2) -> begin
(

let uu____2671 = (

let uu____2678 = (

let uu____2681 = (

let uu____2684 = (mkNatToBv sz t2 r)
in (uu____2684)::[])
in (t1)::uu____2681)
in ((BvMod), (uu____2678)))
in (mkApp' uu____2671 r))
end))


let mkBvMul : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2704 r -> (match (uu____2704) with
| (t1, t2) -> begin
(

let uu____2712 = (

let uu____2719 = (

let uu____2722 = (

let uu____2725 = (mkNatToBv sz t2 r)
in (uu____2725)::[])
in (t1)::uu____2722)
in ((BvMul), (uu____2719)))
in (mkApp' uu____2712 r))
end))


let mkBvUlt : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvUlt)


let mkIff : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Iff)


let mkEq : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____2764 r -> (match (uu____2764) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (Var (f1), (s1)::[]), App (Var (f2), (s2)::[])) when ((Prims.op_Equality f1 f2) && (isInjective f1)) -> begin
(mk_bin_op Eq ((s1), (s2)) r)
end
| uu____2780 -> begin
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


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun uu____2907 r -> (match (uu____2907) with
| (t1, t2, t3) -> begin
(match (t1.tm) with
| App (TrueOp, uu____2918) -> begin
t2
end
| App (FalseOp, uu____2923) -> begin
t3
end
| uu____2928 -> begin
(match (((t2.tm), (t3.tm))) with
| (App (TrueOp, uu____2929), App (TrueOp, uu____2930)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____2939), uu____2940) -> begin
(

let uu____2945 = (

let uu____2950 = (mkNot t1 t1.rng)
in ((uu____2950), (t3)))
in (mkImp uu____2945 r))
end
| (uu____2951, App (TrueOp, uu____2952)) -> begin
(mkImp ((t1), (t2)) r)
end
| (uu____2957, uu____2958) -> begin
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


let mkQuant : (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____3009 r -> (match (uu____3009) with
| (qop, pats, wopt, vars, body) -> begin
(match ((Prims.op_Equality (FStar_List.length vars) (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____3051 -> begin
(match (body.tm) with
| App (TrueOp, uu____3052) -> begin
body
end
| uu____3057 -> begin
(mk (Quant (((qop), (pats), (wopt), (vars), (body)))) r)
end)
end)
end))


let mkLet : (term Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____3080 r -> (match (uu____3080) with
| (es, body) -> begin
(match ((Prims.op_Equality (FStar_List.length es) (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____3095 -> begin
(mk (Let (((es), (body)))) r)
end)
end))


let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (

let nvars = (FStar_List.length fvs)
in (

let index_of = (fun fv -> (

let uu____3121 = (FStar_Util.try_find_index (fv_eq fv) fvs)
in (match (uu____3121) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((nvars - (i + (Prims.parse_int "1"))))
end)))
in (

let rec aux = (fun ix t1 -> (

let uu____3144 = (FStar_ST.op_Bang t1.freevars)
in (match (uu____3144) with
| FStar_Pervasives_Native.Some ([]) -> begin
t1
end
| uu____3202 -> begin
(match (t1.tm) with
| Integer (uu____3211) -> begin
t1
end
| BoundV (uu____3212) -> begin
t1
end
| FreeV (x) -> begin
(

let uu____3218 = (index_of x)
in (match (uu____3218) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (i) -> begin
(mkBoundV (i + ix) t1.rng)
end))
end
| App (op, tms) -> begin
(

let uu____3228 = (

let uu____3235 = (FStar_List.map (aux ix) tms)
in ((op), (uu____3235)))
in (mkApp' uu____3228 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____3243 = (

let uu____3244 = (

let uu____3251 = (aux ix t2)
in ((uu____3251), (r1), (r2)))
in Labeled (uu____3244))
in (mk uu____3243 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____3254 = (

let uu____3255 = (

let uu____3260 = (aux ix t2)
in ((uu____3260), (r)))
in LblPos (uu____3255))
in (mk uu____3254 t2.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n1 = (FStar_List.length vars)
in (

let uu____3283 = (

let uu____3302 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n1)))))
in (

let uu____3323 = (aux (ix + n1) body)
in ((qop), (uu____3302), (wopt), (vars), (uu____3323))))
in (mkQuant uu____3283 t1.rng)))
end
| Let (es, body) -> begin
(

let uu____3342 = (FStar_List.fold_left (fun uu____3360 e -> (match (uu____3360) with
| (ix1, l) -> begin
(

let uu____3380 = (

let uu____3383 = (aux ix1 e)
in (uu____3383)::l)
in (((ix1 + (Prims.parse_int "1"))), (uu____3380)))
end)) ((ix), ([])) es)
in (match (uu____3342) with
| (ix1, es_rev) -> begin
(

let uu____3394 = (

let uu____3401 = (aux ix1 body)
in (((FStar_List.rev es_rev)), (uu____3401)))
in (mkLet uu____3394 t1.rng))
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
| Integer (uu____3433) -> begin
t1
end
| FreeV (uu____3434) -> begin
t1
end
| BoundV (i) -> begin
(match ((((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1))) with
| true -> begin
(FStar_List.nth tms1 (i - shift))
end
| uu____3444 -> begin
t1
end)
end
| App (op, tms2) -> begin
(

let uu____3451 = (

let uu____3458 = (FStar_List.map (aux shift) tms2)
in ((op), (uu____3458)))
in (mkApp' uu____3451 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____3466 = (

let uu____3467 = (

let uu____3474 = (aux shift t2)
in ((uu____3474), (r1), (r2)))
in Labeled (uu____3467))
in (mk uu____3466 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____3477 = (

let uu____3478 = (

let uu____3483 = (aux shift t2)
in ((uu____3483), (r)))
in LblPos (uu____3478))
in (mk uu____3477 t2.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift1 = (shift + m)
in (

let uu____3511 = (

let uu____3530 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift1))))
in (

let uu____3547 = (aux shift1 body)
in ((qop), (uu____3530), (wopt), (vars), (uu____3547))))
in (mkQuant uu____3511 t1.rng))))
end
| Let (es, body) -> begin
(

let uu____3562 = (FStar_List.fold_left (fun uu____3580 e -> (match (uu____3580) with
| (ix, es1) -> begin
(

let uu____3600 = (

let uu____3603 = (aux shift e)
in (uu____3603)::es1)
in (((shift + (Prims.parse_int "1"))), (uu____3600)))
end)) ((shift), ([])) es)
in (match (uu____3562) with
| (shift1, es_rev) -> begin
(

let uu____3614 = (

let uu____3621 = (aux shift1 body)
in (((FStar_List.rev es_rev)), (uu____3621)))
in (mkLet uu____3614 t1.rng))
end))
end))
in (aux (Prims.parse_int "0") t)))))


let subst : term  ->  fv  ->  term  ->  term = (fun t fv s -> (

let uu____3639 = (abstr ((fv)::[]) t)
in (inst ((s)::[]) uu____3639)))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fv Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____3665 -> (match (uu____3665) with
| (qop, pats, wopt, vars, body) -> begin
(

let uu____3708 = (

let uu____3727 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (

let uu____3744 = (FStar_List.map fv_sort vars)
in (

let uu____3747 = (abstr vars body)
in ((qop), (uu____3727), (wopt), (uu____3744), (uu____3747)))))
in (mkQuant uu____3708))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____3780 r -> (match (uu____3780) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)) r)
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____3848 r -> (match (uu____3848) with
| (pats, wopt, vars, body) -> begin
(

let uu____3880 = (mkQuant' ((Forall), (pats), (wopt), (vars), (body)))
in (uu____3880 r))
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____3911 r -> (match (uu____3911) with
| (pats, vars, body) -> begin
(

let uu____3934 = (mkQuant' ((Forall), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
in (uu____3934 r))
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____3965 r -> (match (uu____3965) with
| (pats, vars, body) -> begin
(

let uu____3988 = (mkQuant' ((Exists), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
in (uu____3988 r))
end))


let mkLet' : ((fv * term) Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____4019 r -> (match (uu____4019) with
| (bindings, body) -> begin
(

let uu____4045 = (FStar_List.split bindings)
in (match (uu____4045) with
| (vars, es) -> begin
(

let uu____4064 = (

let uu____4071 = (abstr vars body)
in ((es), (uu____4071)))
in (mkLet uu____4064 r))
end))
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun uu____4094 -> (match (uu____4094) with
| (nm, vars, s, tm, c) -> begin
(

let uu____4128 = (

let uu____4141 = (FStar_List.map fv_sort vars)
in (

let uu____4148 = (abstr vars tm)
in ((nm), (uu____4141), (s), (uu____4148), (c))))
in DefineFun (uu____4128))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (

let uu____4156 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" uu____4156)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun uu____4169 id1 -> (match (uu____4169) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (

let a = (

let uu____4179 = (

let uu____4180 = (

let uu____4185 = (mkInteger' id1 norng)
in (

let uu____4186 = (

let uu____4187 = (

let uu____4194 = (constr_id_of_sort sort)
in (

let uu____4195 = (

let uu____4198 = (mkApp ((tok_name), ([])) norng)
in (uu____4198)::[])
in ((uu____4194), (uu____4195))))
in (mkApp uu____4187 norng))
in ((uu____4185), (uu____4186))))
in (mkEq uu____4180 norng))
in {assumption_term = uu____4179; assumption_caption = FStar_Pervasives_Native.Some ("fresh token"); assumption_name = a_name; assumption_fact_ids = []})
in Assume (a)))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun uu____4217 -> (match (uu____4217) with
| (name, arg_sorts, sort, id1) -> begin
(

let id2 = (FStar_Util.string_of_int id1)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (

let uu____4249 = (

let uu____4254 = (

let uu____4255 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____4255))
in ((uu____4254), (s)))
in (mkFreeV uu____4249 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (

let uu____4271 = (

let uu____4278 = (constr_id_of_sort sort)
in ((uu____4278), ((capp)::[])))
in (mkApp uu____4271 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (

let a = (

let uu____4283 = (

let uu____4284 = (

let uu____4295 = (

let uu____4296 = (

let uu____4301 = (mkInteger id2 norng)
in ((uu____4301), (cid_app)))
in (mkEq uu____4296 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____4295)))
in (mkForall uu____4284 norng))
in {assumption_term = uu____4283; assumption_caption = FStar_Pervasives_Native.Some ("Consrtructor distinct"); assumption_name = a_name; assumption_fact_ids = []})
in Assume (a))))))))
end))


let injective_constructor : (Prims.string * constructor_field Prims.list * sort)  ->  decls_t = (fun uu____4322 -> (match (uu____4322) with
| (name, fields, sort) -> begin
(

let n_bvars = (FStar_List.length fields)
in (

let bvar_name = (fun i -> (

let uu____4345 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____4345)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (

let uu____4372 = (

let uu____4377 = (bvar_name i)
in ((uu____4377), (s)))
in (mkFreeV uu____4372)))
in (

let bvars = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____4404 -> (match (uu____4404) with
| (uu____4411, s, uu____4413) -> begin
(

let uu____4414 = (bvar i s)
in (uu____4414 norng))
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let uu____4433 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____4467 -> (match (uu____4467) with
| (name1, s, projectible) -> begin
(

let cproj_app = (mkApp ((name1), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((name1), ((sort)::[]), (s), (FStar_Pervasives_Native.Some ("Projector"))))
in (match (projectible) with
| true -> begin
(

let a = (

let uu____4488 = (

let uu____4489 = (

let uu____4500 = (

let uu____4501 = (

let uu____4506 = (

let uu____4507 = (bvar i s)
in (uu____4507 norng))
in ((cproj_app), (uu____4506)))
in (mkEq uu____4501 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____4500)))
in (mkForall uu____4489 norng))
in {assumption_term = uu____4488; assumption_caption = FStar_Pervasives_Native.Some ("Projection inverse"); assumption_name = (Prims.strcat "projection_inverse_" name1); assumption_fact_ids = []})
in (proj_name)::(Assume (a))::[])
end
| uu____4520 -> begin
(proj_name)::[]
end)))
end))))
in (FStar_All.pipe_right uu____4433 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun uu____4529 -> (match (uu____4529) with
| (name, fields, sort, id1, injective) -> begin
(

let injective1 = (injective || true)
in (

let field_sorts = (FStar_All.pipe_right fields (FStar_List.map (fun uu____4563 -> (match (uu____4563) with
| (uu____4570, sort1, uu____4572) -> begin
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

let uu____4588 = (

let uu____4593 = (

let uu____4594 = (

let uu____4601 = (constr_id_of_sort sort)
in ((uu____4601), ((xx)::[])))
in (mkApp uu____4594 norng))
in (

let uu____4604 = (

let uu____4605 = (FStar_Util.string_of_int id1)
in (mkInteger uu____4605 norng))
in ((uu____4593), (uu____4604))))
in (mkEq uu____4588 norng))
in (

let uu____4606 = (

let uu____4621 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____4677 -> (match (uu____4677) with
| (proj, s, projectible) -> begin
(match (projectible) with
| true -> begin
(

let uu____4707 = (mkApp ((proj), ((xx)::[])) norng)
in ((uu____4707), ([])))
end
| uu____4720 -> begin
(

let fi = (

let uu____4726 = (

let uu____4727 = (FStar_Util.string_of_int i)
in (Prims.strcat "f_" uu____4727))
in ((uu____4726), (s)))
in (

let uu____4728 = (mkFreeV fi norng)
in ((uu____4728), ((fi)::[]))))
end)
end))))
in (FStar_All.pipe_right uu____4621 FStar_List.split))
in (match (uu____4606) with
| (proj_terms, ex_vars) -> begin
(

let ex_vars1 = (FStar_List.flatten ex_vars)
in (

let disc_inv_body = (

let uu____4809 = (

let uu____4814 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (uu____4814)))
in (mkEq uu____4809 norng))
in (

let disc_inv_body1 = (match (ex_vars1) with
| [] -> begin
disc_inv_body
end
| uu____4822 -> begin
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
| uu____4858 -> begin
[]
end)
in (

let uu____4859 = (

let uu____4862 = (

let uu____4863 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (uu____4863))
in (uu____4862)::(cdecl)::(cid)::projs)
in (

let uu____4864 = (

let uu____4867 = (

let uu____4870 = (

let uu____4871 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (uu____4871))
in (uu____4870)::[])
in (FStar_List.append ((disc)::[]) uu____4867))
in (FStar_List.append uu____4859 uu____4864)))))))))
end))


let name_binders_inner : Prims.string FStar_Pervasives_Native.option  ->  (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun prefix_opt outer_names start sorts -> (

let uu____4926 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun uu____4981 s -> (match (uu____4981) with
| (names1, binders, n1) -> begin
(

let prefix1 = (match (s) with
| Term_sort -> begin
"@x"
end
| uu____5031 -> begin
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

let uu____5035 = (FStar_Util.string_of_int n1)
in (Prims.strcat prefix2 uu____5035))
in (

let names2 = (((nm), (s)))::names1
in (

let b = (

let uu____5048 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm uu____5048))
in ((names2), ((b)::binders), ((n1 + (Prims.parse_int "1")))))))))
end)) ((outer_names), ([]), (start))))
in (match (uu____4926) with
| (names1, binders, n1) -> begin
((names1), ((FStar_List.rev binders)), (n1))
end)))


let name_macro_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let uu____5127 = (name_binders_inner (FStar_Pervasives_Native.Some ("__")) [] (Prims.parse_int "0") sorts)
in (match (uu____5127) with
| (names1, binders, n1) -> begin
(((FStar_List.rev names1)), (binders))
end)))


let termToSmt : Prims.bool  ->  Prims.string  ->  term  ->  Prims.string = (fun print_ranges enclosing_name t -> (

let next_qid = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun uu____5212 -> (

let n1 = (FStar_ST.op_Bang ctr)
in ((FStar_Util.incr ctr);
(match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
enclosing_name
end
| uu____5293 -> begin
(

let uu____5294 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "%s.%s" enclosing_name uu____5294))
end);
))))
in (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (uu____5338); freevars = uu____5339; rng = uu____5340})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| uu____5354 -> begin
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

let uu____5416 = (FStar_List.nth names1 i)
in (FStar_All.pipe_right uu____5416 FStar_Pervasives_Native.fst))
end
| FreeV (x) -> begin
(FStar_Pervasives_Native.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(

let uu____5439 = (op_to_string op)
in (

let uu____5440 = (

let uu____5441 = (FStar_List.map (aux1 n1 names1) tms)
in (FStar_All.pipe_right uu____5441 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" uu____5439 uu____5440)))
end
| Labeled (t2, uu____5447, uu____5448) -> begin
(aux1 n1 names1 t2)
end
| LblPos (t2, s) -> begin
(

let uu____5451 = (aux1 n1 names1 t2)
in (FStar_Util.format2 "(! %s :lblpos %s)" uu____5451 s))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let qid = (next_qid ())
in (

let uu____5474 = (name_binders_inner FStar_Pervasives_Native.None names1 n1 sorts)
in (match (uu____5474) with
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
| uu____5523 -> begin
(

let uu____5528 = (FStar_All.pipe_right pats1 (FStar_List.map (fun pats2 -> (

let uu____5544 = (

let uu____5545 = (FStar_List.map (fun p -> (

let uu____5551 = (aux1 n2 names2 p)
in (FStar_Util.format1 "%s" uu____5551))) pats2)
in (FStar_String.concat " " uu____5545))
in (FStar_Util.format1 "\n:pattern (%s)" uu____5544)))))
in (FStar_All.pipe_right uu____5528 (FStar_String.concat "\n")))
end)
in (

let uu____5554 = (

let uu____5557 = (

let uu____5560 = (

let uu____5563 = (aux1 n2 names2 body)
in (

let uu____5564 = (

let uu____5567 = (weightToSmt wopt)
in (uu____5567)::(pats_str)::(qid)::[])
in (uu____5563)::uu____5564))
in (binders1)::uu____5560)
in ((qop_to_string qop))::uu____5557)
in (FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))" uu____5554)))))
end)))
end
| Let (es, body) -> begin
(

let uu____5574 = (FStar_List.fold_left (fun uu____5611 e -> (match (uu____5611) with
| (names0, binders, n0) -> begin
(

let nm = (

let uu____5661 = (FStar_Util.string_of_int n0)
in (Prims.strcat "@lb" uu____5661))
in (

let names01 = (((nm), (Term_sort)))::names0
in (

let b = (

let uu____5674 = (aux1 n1 names1 e)
in (FStar_Util.format2 "(%s %s)" nm uu____5674))
in ((names01), ((b)::binders), ((n0 + (Prims.parse_int "1")))))))
end)) ((names1), ([]), (n1)) es)
in (match (uu____5574) with
| (names2, binders, n2) -> begin
(

let uu____5710 = (aux1 n2 names2 body)
in (FStar_Util.format2 "(let (%s)\n%s)" (FStar_String.concat " " binders) uu____5710))
end))
end)))
and aux = (fun depth n1 names1 t1 -> (

let s = (aux' depth n1 names1 t1)
in (match ((print_ranges && (Prims.op_disEquality t1.rng norng))) with
| true -> begin
(

let uu____5718 = (FStar_Range.string_of_range t1.rng)
in (

let uu____5719 = (FStar_Range.string_of_use_range t1.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____5718 uu____5719 s)))
end
| uu____5720 -> begin
s
end)))
in (aux (Prims.parse_int "0") (Prims.parse_int "0") [] t)))))


let caption_to_string : Prims.string FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___53_5727 -> (match (uu___53_5727) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let uu____5731 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(failwith "Impossible")
end
| (hd1)::[] -> begin
((hd1), (""))
end
| (hd1)::uu____5746 -> begin
((hd1), ("..."))
end)
in (match (uu____5731) with
| (hd1, suffix) -> begin
(FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
end))
end))


let rec declToSmt' : Prims.bool  ->  Prims.string  ->  decl  ->  Prims.string = (fun print_ranges z3options decl -> (

let escape = (fun s -> (FStar_Util.replace_char s 39 (*'*) 95 (*_*)))
in (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(

let uu____5795 = (FStar_Options.log_queries ())
in (match (uu____5795) with
| true -> begin
(

let uu____5796 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun uu___54_5800 -> (match (uu___54_5800) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" uu____5796))
end
| uu____5807 -> begin
""
end))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (

let uu____5819 = (caption_to_string c)
in (

let uu____5820 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____5819 f (FStar_String.concat " " l) uu____5820))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let uu____5830 = (name_macro_binders arg_sorts)
in (match (uu____5830) with
| (names1, binders) -> begin
(

let body1 = (

let uu____5862 = (FStar_List.map (fun x -> (mkFreeV x norng)) names1)
in (inst uu____5862 body))
in (

let uu____5875 = (caption_to_string c)
in (

let uu____5876 = (strSort retsort)
in (

let uu____5877 = (termToSmt print_ranges (escape f) body1)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____5875 f (FStar_String.concat " " binders) uu____5876 uu____5877)))))
end))
end
| Assume (a) -> begin
(

let fact_ids_to_string = (fun ids -> (FStar_All.pipe_right ids (FStar_List.map (fun uu___55_5898 -> (match (uu___55_5898) with
| Name (n1) -> begin
(

let uu____5900 = (FStar_Ident.text_of_lid n1)
in (Prims.strcat "Name " uu____5900))
end
| Namespace (ns) -> begin
(

let uu____5902 = (FStar_Ident.text_of_lid ns)
in (Prims.strcat "Namespace " uu____5902))
end
| Tag (t) -> begin
(Prims.strcat "Tag " t)
end)))))
in (

let fids = (

let uu____5905 = (FStar_Options.log_queries ())
in (match (uu____5905) with
| true -> begin
(

let uu____5906 = (

let uu____5907 = (fact_ids_to_string a.assumption_fact_ids)
in (FStar_String.concat "; " uu____5907))
in (FStar_Util.format1 ";;; Fact-ids: %s\n" uu____5906))
end
| uu____5910 -> begin
""
end))
in (

let n1 = (escape a.assumption_name)
in (

let uu____5912 = (caption_to_string a.assumption_caption)
in (

let uu____5913 = (termToSmt print_ranges n1 a.assumption_term)
in (FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____5912 fids uu____5913 n1))))))
end
| Eval (t) -> begin
(

let uu____5915 = (termToSmt print_ranges "eval" t)
in (FStar_Util.format1 "(eval %s)" uu____5915))
end
| Echo (s) -> begin
(FStar_Util.format1 "(echo \"%s\")" s)
end
| RetainAssumptions (uu____5917) -> begin
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

let basic = (Prims.strcat z3options "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (iff (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))")
in (

let constrs = ((("FString_const"), (((("FString_const_proj_0"), (Int_sort), (true)))::[]), (String_sort), ((Prims.parse_int "0")), (true)))::((("Tm_type"), ([]), (Term_sort), ((Prims.parse_int "2")), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "3")), (false)))::((("Tm_unit"), ([]), (Term_sort), ((Prims.parse_int "6")), (true)))::((((FStar_Pervasives_Native.fst boxIntFun)), (((((FStar_Pervasives_Native.snd boxIntFun)), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "7")), (true)))::((((FStar_Pervasives_Native.fst boxBoolFun)), (((((FStar_Pervasives_Native.snd boxBoolFun)), (Bool_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "8")), (true)))::((((FStar_Pervasives_Native.fst boxStringFun)), (((((FStar_Pervasives_Native.snd boxStringFun)), (String_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "9")), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort), (true)))::((("LexCons_1"), (Term_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "11")), (true)))::[]
in (

let bcons = (

let uu____5946 = (

let uu____5949 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right uu____5949 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right uu____5946 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mkBvConstructor : Prims.int  ->  decls_t = (fun sz -> (

let uu____5968 = (

let uu____5969 = (

let uu____5970 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____5970))
in (

let uu____5975 = (

let uu____5978 = (

let uu____5979 = (

let uu____5980 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____5980))
in ((uu____5979), (BitVec_sort (sz)), (true)))
in (uu____5978)::[])
in ((uu____5969), (uu____5975), (Term_sort), (((Prims.parse_int "12") + sz)), (true))))
in (FStar_All.pipe_right uu____5968 constructor_to_decl)))


let __range_c : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let mk_Range_const : unit  ->  term = (fun uu____6004 -> (

let i = (FStar_ST.op_Bang __range_c)
in ((

let uu____6030 = (

let uu____6031 = (FStar_ST.op_Bang __range_c)
in (uu____6031 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals __range_c uu____6030));
(

let uu____6078 = (

let uu____6085 = (

let uu____6088 = (mkInteger' i norng)
in (uu____6088)::[])
in (("Range_const"), (uu____6085)))
in (mkApp uu____6078 norng));
)))


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____6120 = (

let uu____6127 = (

let uu____6130 = (mkInteger' i norng)
in (uu____6130)::[])
in (("Tm_uvar"), (uu____6127)))
in (mkApp uu____6120 r)))


let mk_Term_unit : term = (mkApp (("Tm_unit"), ([])) norng)


let elim_box : Prims.bool  ->  Prims.string  ->  Prims.string  ->  term  ->  term = (fun cond u v1 t -> (match (t.tm) with
| App (Var (v'), (t1)::[]) when ((Prims.op_Equality v1 v') && cond) -> begin
t1
end
| uu____6159 -> begin
(mkApp ((u), ((t)::[])) t.rng)
end))


let maybe_elim_box : Prims.string  ->  Prims.string  ->  term  ->  term = (fun u v1 t -> (

let uu____6177 = (FStar_Options.smtencoding_elim_box ())
in (elim_box uu____6177 u v1 t)))


let boxInt : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxIntFun) (FStar_Pervasives_Native.snd boxIntFun) t))


let unboxInt : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxIntFun) (FStar_Pervasives_Native.fst boxIntFun) t))


let boxBool : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxBoolFun) (FStar_Pervasives_Native.snd boxBoolFun) t))


let unboxBool : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxBoolFun) (FStar_Pervasives_Native.fst boxBoolFun) t))


let boxString : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxStringFun) (FStar_Pervasives_Native.snd boxStringFun) t))


let unboxString : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxStringFun) (FStar_Pervasives_Native.fst boxStringFun) t))


let boxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let uu____6218 = (

let uu____6219 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____6219))
in (

let uu____6224 = (

let uu____6225 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____6225))
in (elim_box true uu____6218 uu____6224 t))))


let unboxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let uu____6240 = (

let uu____6241 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____6241))
in (

let uu____6246 = (

let uu____6247 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____6247))
in (elim_box true uu____6240 uu____6246 t))))


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
| uu____6263 -> begin
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
| uu____6275 -> begin
(FStar_Exn.raise FStar_Util.Impos)
end))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n1) -> begin
(FStar_Util.format1 "(Integer %s)" n1)
end
| BoundV (n1) -> begin
(

let uu____6297 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(BoundV %s)" uu____6297))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv))
end
| App (op, l) -> begin
(

let uu____6309 = (op_to_string op)
in (

let uu____6310 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" uu____6309 uu____6310)))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____6314 = (print_smt_term t1)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 uu____6314))
end
| LblPos (t1, s) -> begin
(

let uu____6317 = (print_smt_term t1)
in (FStar_Util.format2 "(LblPos %s %s)" s uu____6317))
end
| Quant (qop, l, uu____6320, uu____6321, t1) -> begin
(

let uu____6339 = (print_smt_term_list_list l)
in (

let uu____6340 = (print_smt_term t1)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____6339 uu____6340)))
end
| Let (es, body) -> begin
(

let uu____6347 = (print_smt_term_list es)
in (

let uu____6348 = (print_smt_term body)
in (FStar_Util.format2 "(let %s %s)" uu____6347 uu____6348)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (

let uu____6352 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right uu____6352 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l1 -> (

let uu____6371 = (

let uu____6372 = (

let uu____6373 = (print_smt_term_list l1)
in (Prims.strcat uu____6373 " ] "))
in (Prims.strcat "; [ " uu____6372))
in (Prims.strcat s uu____6371))) "" l))


let getBoxedInteger : term  ->  Prims.int FStar_Pervasives_Native.option = (fun t -> (match (t.tm) with
| App (Var (s), (t2)::[]) when (Prims.op_Equality s (FStar_Pervasives_Native.fst boxIntFun)) -> begin
(match (t2.tm) with
| Integer (n1) -> begin
(

let uu____6390 = (FStar_Util.int_of_string n1)
in FStar_Pervasives_Native.Some (uu____6390))
end
| uu____6391 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____6392 -> begin
FStar_Pervasives_Native.None
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (uu____6405)::(t1)::(t2)::[]); freevars = uu____6408; rng = uu____6409})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (uu____6422)::(t1)::(t2)::[]); freevars = uu____6425; rng = uu____6426})::[]) -> begin
(

let uu____6439 = (mkEq ((t1), (t2)) norng)
in (mkNot uu____6439 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = uu____6442; rng = uu____6443})::[]) -> begin
(

let uu____6456 = (

let uu____6461 = (unboxInt t1)
in (

let uu____6462 = (unboxInt t2)
in ((uu____6461), (uu____6462))))
in (mkLTE uu____6456 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = uu____6465; rng = uu____6466})::[]) -> begin
(

let uu____6479 = (

let uu____6484 = (unboxInt t1)
in (

let uu____6485 = (unboxInt t2)
in ((uu____6484), (uu____6485))))
in (mkLT uu____6479 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = uu____6488; rng = uu____6489})::[]) -> begin
(

let uu____6502 = (

let uu____6507 = (unboxInt t1)
in (

let uu____6508 = (unboxInt t2)
in ((uu____6507), (uu____6508))))
in (mkGTE uu____6502 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = uu____6511; rng = uu____6512})::[]) -> begin
(

let uu____6525 = (

let uu____6530 = (unboxInt t1)
in (

let uu____6531 = (unboxInt t2)
in ((uu____6530), (uu____6531))))
in (mkGT uu____6525 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = uu____6534; rng = uu____6535})::[]) -> begin
(

let uu____6548 = (

let uu____6553 = (unboxBool t1)
in (

let uu____6554 = (unboxBool t2)
in ((uu____6553), (uu____6554))))
in (mkAnd uu____6548 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = uu____6557; rng = uu____6558})::[]) -> begin
(

let uu____6571 = (

let uu____6576 = (unboxBool t1)
in (

let uu____6577 = (unboxBool t2)
in ((uu____6576), (uu____6577))))
in (mkOr uu____6571 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t1)::[]); freevars = uu____6579; rng = uu____6580})::[]) -> begin
(

let uu____6593 = (unboxBool t1)
in (mkNot uu____6593 t1.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("FStar.BV.bvult"), (t0)::(t1)::(t2)::[]); freevars = uu____6597; rng = uu____6598})::[]) when (

let uu____6611 = (getBoxedInteger t0)
in (FStar_Util.is_some uu____6611)) -> begin
(

let sz = (

let uu____6615 = (getBoxedInteger t0)
in (match (uu____6615) with
| FStar_Pervasives_Native.Some (sz) -> begin
sz
end
| uu____6619 -> begin
(failwith "impossible")
end))
in (

let uu____6622 = (

let uu____6627 = (unboxBitVec sz t1)
in (

let uu____6628 = (unboxBitVec sz t2)
in ((uu____6627), (uu____6628))))
in (mkBvUlt uu____6622 t.rng)))
end
| App (Var ("Prims.equals"), (uu____6629)::({tm = App (Var ("FStar.BV.bvult"), (t0)::(t1)::(t2)::[]); freevars = uu____6633; rng = uu____6634})::(uu____6635)::[]) when (

let uu____6648 = (getBoxedInteger t0)
in (FStar_Util.is_some uu____6648)) -> begin
(

let sz = (

let uu____6652 = (getBoxedInteger t0)
in (match (uu____6652) with
| FStar_Pervasives_Native.Some (sz) -> begin
sz
end
| uu____6656 -> begin
(failwith "impossible")
end))
in (

let uu____6659 = (

let uu____6664 = (unboxBitVec sz t1)
in (

let uu____6665 = (unboxBitVec sz t2)
in ((uu____6664), (uu____6665))))
in (mkBvUlt uu____6659 t.rng)))
end
| App (Var ("Prims.b2t"), (t1)::[]) -> begin
(

let uu___56_6669 = (unboxBool t1)
in {tm = uu___56_6669.tm; freevars = uu___56_6669.freevars; rng = t.rng})
end
| uu____6670 -> begin
(mkApp (("Valid"), ((t)::[])) t.rng)
end))


let mk_HasType : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasType"), ((v1)::(t)::[])) t.rng))


let mk_HasTypeZ : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasTypeZ"), ((v1)::(t)::[])) t.rng))


let mk_IsTyped : term  ->  term = (fun v1 -> (mkApp (("IsTyped"), ((v1)::[])) norng))


let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v1 t -> (

let uu____6719 = (FStar_Options.unthrottle_inductives ())
in (match (uu____6719) with
| true -> begin
(mk_HasType v1 t)
end
| uu____6720 -> begin
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


let mk_String_const : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____6830 = (

let uu____6837 = (

let uu____6840 = (mkInteger' i norng)
in (uu____6840)::[])
in (("FString_const"), (uu____6837)))
in (mkApp uu____6830 r)))


let mk_Precedes : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (

let uu____6858 = (mkApp (("Precedes"), ((x1)::(x2)::[])) r)
in (FStar_All.pipe_right uu____6858 mk_Valid)))


let mk_LexCons : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (mkApp (("LexCons"), ((x1)::(x2)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
(mkApp (("ZFuel"), ([])) norng)
end
| uu____6885 -> begin
(

let uu____6886 = (

let uu____6893 = (

let uu____6896 = (n_fuel (n1 - (Prims.parse_int "1")))
in (uu____6896)::[])
in (("SFuel"), (uu____6893)))
in (mkApp uu____6886 norng))
end))


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term FStar_Pervasives_Native.option  ->  term FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  term FStar_Pervasives_Native.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (FStar_Pervasives_Native.Some (p11), FStar_Pervasives_Native.Some (p21)) -> begin
(

let uu____6936 = (mkAnd ((p11), (p21)) r)
in FStar_Pervasives_Native.Some (uu____6936))
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

let uu____6997 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l uu____6997)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____7016 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l uu____7016)))


let mk_haseq : term  ->  term = (fun t -> (

let uu____7026 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid uu____7026)))




