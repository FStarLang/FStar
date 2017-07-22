
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
| uu____29 -> begin
false
end))


let uu___is_Int_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int_sort -> begin
true
end
| uu____34 -> begin
false
end))


let uu___is_String_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| String_sort -> begin
true
end
| uu____39 -> begin
false
end))


let uu___is_Term_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Term_sort -> begin
true
end
| uu____44 -> begin
false
end))


let uu___is_Fuel_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fuel_sort -> begin
true
end
| uu____49 -> begin
false
end))


let uu___is_BitVec_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BitVec_sort (_0) -> begin
true
end
| uu____55 -> begin
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
| uu____73 -> begin
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
| uu____103 -> begin
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
| uu____129 -> begin
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

let uu____143 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ BitVec %s)" uu____143))
end
| Array (s1, s2) -> begin
(

let uu____146 = (strSort s1)
in (

let uu____147 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" uu____146 uu____147)))
end
| Arrow (s1, s2) -> begin
(

let uu____150 = (strSort s1)
in (

let uu____151 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" uu____150 uu____151)))
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
| uu____169 -> begin
false
end))


let uu___is_FalseOp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FalseOp -> begin
true
end
| uu____174 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____179 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____184 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____189 -> begin
false
end))


let uu___is_Imp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Imp -> begin
true
end
| uu____194 -> begin
false
end))


let uu___is_Iff : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iff -> begin
true
end
| uu____199 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____204 -> begin
false
end))


let uu___is_LT : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LT -> begin
true
end
| uu____209 -> begin
false
end))


let uu___is_LTE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LTE -> begin
true
end
| uu____214 -> begin
false
end))


let uu___is_GT : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GT -> begin
true
end
| uu____219 -> begin
false
end))


let uu___is_GTE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GTE -> begin
true
end
| uu____224 -> begin
false
end))


let uu___is_Add : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Add -> begin
true
end
| uu____229 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____234 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____239 -> begin
false
end))


let uu___is_Mul : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mul -> begin
true
end
| uu____244 -> begin
false
end))


let uu___is_Minus : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Minus -> begin
true
end
| uu____249 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____254 -> begin
false
end))


let uu___is_BvAnd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvAnd -> begin
true
end
| uu____259 -> begin
false
end))


let uu___is_BvXor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvXor -> begin
true
end
| uu____264 -> begin
false
end))


let uu___is_BvOr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvOr -> begin
true
end
| uu____269 -> begin
false
end))


let uu___is_BvShl : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvShl -> begin
true
end
| uu____274 -> begin
false
end))


let uu___is_BvShr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvShr -> begin
true
end
| uu____279 -> begin
false
end))


let uu___is_BvUdiv : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvUdiv -> begin
true
end
| uu____284 -> begin
false
end))


let uu___is_BvMod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvMod -> begin
true
end
| uu____289 -> begin
false
end))


let uu___is_BvMul : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvMul -> begin
true
end
| uu____294 -> begin
false
end))


let uu___is_BvUlt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvUlt -> begin
true
end
| uu____299 -> begin
false
end))


let uu___is_BvUext : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvUext (_0) -> begin
true
end
| uu____305 -> begin
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
| uu____319 -> begin
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
| uu____332 -> begin
false
end))


let uu___is_ITE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ITE -> begin
true
end
| uu____337 -> begin
false
end))


let uu___is_Var : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Var (_0) -> begin
true
end
| uu____343 -> begin
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
| uu____356 -> begin
false
end))


let uu___is_Exists : qop  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exists -> begin
true
end
| uu____361 -> begin
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
| uu____464 -> begin
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
| uu____478 -> begin
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
| uu____496 -> begin
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
| uu____528 -> begin
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
| uu____578 -> begin
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
| uu____652 -> begin
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
| uu____690 -> begin
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
| uu____726 -> begin
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
| uu____866 -> begin
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
| uu____880 -> begin
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
| uu____894 -> begin
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
| uu____1029 -> begin
false
end))


let uu___is_DeclFun : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DeclFun (_0) -> begin
true
end
| uu____1045 -> begin
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
| uu____1101 -> begin
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
| uu____1151 -> begin
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
| uu____1165 -> begin
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
| uu____1179 -> begin
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
| uu____1193 -> begin
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
| uu____1209 -> begin
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
| uu____1228 -> begin
false
end))


let uu___is_Pop : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____1233 -> begin
false
end))


let uu___is_CheckSat : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckSat -> begin
true
end
| uu____1238 -> begin
false
end))


let uu___is_GetUnsatCore : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetUnsatCore -> begin
true
end
| uu____1243 -> begin
false
end))


let uu___is_SetOption : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOption (_0) -> begin
true
end
| uu____1253 -> begin
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
| uu____1278 -> begin
false
end))


let uu___is_GetReasonUnknown : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetReasonUnknown -> begin
true
end
| uu____1283 -> begin
false
end))


type decls_t =
decl Prims.list


type error_label =
(fv * Prims.string * FStar_Range.range)


type error_labels =
error_label Prims.list


let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> ((FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst y)))


let fv_sort : 'Auu____1308 'Auu____1309 . ('Auu____1309 * 'Auu____1308)  ->  'Auu____1308 = (fun x -> (FStar_Pervasives_Native.snd x))


let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match (((x.tm), (y.tm))) with
| (FreeV (x1), FreeV (y1)) -> begin
(fv_eq x1 y1)
end
| uu____1340 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun uu___87_1348 -> (match (uu___87_1348) with
| {tm = FreeV (x); freevars = uu____1350; rng = uu____1351} -> begin
(fv_sort x)
end
| uu____1364 -> begin
(failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun uu___88_1368 -> (match (uu___88_1368) with
| {tm = FreeV (fv); freevars = uu____1370; rng = uu____1371} -> begin
fv
end
| uu____1384 -> begin
(failwith "impossible")
end))


let rec freevars : term  ->  (Prims.string * sort) Prims.list = (fun t -> (match (t.tm) with
| Integer (uu____1401) -> begin
[]
end
| BoundV (uu____1406) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (uu____1424, tms) -> begin
(FStar_List.collect freevars tms)
end
| Quant (uu____1434, uu____1435, uu____1436, uu____1437, t1) -> begin
(freevars t1)
end
| Labeled (t1, uu____1456, uu____1457) -> begin
(freevars t1)
end
| LblPos (t1, uu____1459) -> begin
(freevars t1)
end
| Let (es, body) -> begin
(FStar_List.collect freevars ((body)::es))
end))


let free_variables : term  ->  fvs = (fun t -> (

let uu____1474 = (FStar_ST.read t.freevars)
in (match (uu____1474) with
| FStar_Pervasives_Native.Some (b) -> begin
b
end
| FStar_Pervasives_Native.None -> begin
(

let fvs = (

let uu____1513 = (freevars t)
in (FStar_Util.remove_dups fv_eq uu____1513))
in ((FStar_ST.write t.freevars (FStar_Pervasives_Native.Some (fvs)));
fvs;
))
end)))


let qop_to_string : qop  ->  Prims.string = (fun uu___89_1530 -> (match (uu___89_1530) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun uu___90_1534 -> (match (uu___90_1534) with
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

let uu____1536 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ zero_extend %s)" uu____1536))
end
| NatToBv (n1) -> begin
(

let uu____1538 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ int2bv %s)" uu____1538))
end
| Var (s) -> begin
s
end))


let weightToSmt : Prims.int FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___91_1545 -> (match (uu___91_1545) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (i) -> begin
(

let uu____1549 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" uu____1549))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____1557 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" uu____1557))
end
| FreeV (x) -> begin
(

let uu____1563 = (

let uu____1564 = (strSort (FStar_Pervasives_Native.snd x))
in (Prims.strcat ":" uu____1564))
in (Prims.strcat (FStar_Pervasives_Native.fst x) uu____1563))
end
| App (op, tms) -> begin
(

let uu____1571 = (

let uu____1572 = (op_to_string op)
in (

let uu____1573 = (

let uu____1574 = (

let uu____1575 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right uu____1575 (FStar_String.concat " ")))
in (Prims.strcat uu____1574 ")"))
in (Prims.strcat uu____1572 uu____1573)))
in (Prims.strcat "(" uu____1571))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____1583 = (hash_of_term t1)
in (

let uu____1584 = (

let uu____1585 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 uu____1585))
in (Prims.strcat uu____1583 uu____1584)))
end
| LblPos (t1, r) -> begin
(

let uu____1588 = (

let uu____1589 = (hash_of_term t1)
in (Prims.strcat uu____1589 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " uu____1588))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let uu____1611 = (

let uu____1612 = (

let uu____1613 = (

let uu____1614 = (

let uu____1615 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right uu____1615 (FStar_String.concat " ")))
in (

let uu____1620 = (

let uu____1621 = (

let uu____1622 = (hash_of_term body)
in (

let uu____1623 = (

let uu____1624 = (

let uu____1625 = (weightToSmt wopt)
in (

let uu____1626 = (

let uu____1627 = (

let uu____1628 = (

let uu____1629 = (FStar_All.pipe_right pats (FStar_List.map (fun pats1 -> (

let uu____1645 = (FStar_List.map hash_of_term pats1)
in (FStar_All.pipe_right uu____1645 (FStar_String.concat " "))))))
in (FStar_All.pipe_right uu____1629 (FStar_String.concat "; ")))
in (Prims.strcat uu____1628 "))"))
in (Prims.strcat " " uu____1627))
in (Prims.strcat uu____1625 uu____1626)))
in (Prims.strcat " " uu____1624))
in (Prims.strcat uu____1622 uu____1623)))
in (Prims.strcat ")(! " uu____1621))
in (Prims.strcat uu____1614 uu____1620)))
in (Prims.strcat " (" uu____1613))
in (Prims.strcat (qop_to_string qop) uu____1612))
in (Prims.strcat "(" uu____1611))
end
| Let (es, body) -> begin
(

let uu____1658 = (

let uu____1659 = (

let uu____1660 = (FStar_List.map hash_of_term es)
in (FStar_All.pipe_right uu____1660 (FStar_String.concat " ")))
in (

let uu____1665 = (

let uu____1666 = (

let uu____1667 = (hash_of_term body)
in (Prims.strcat uu____1667 ")"))
in (Prims.strcat ") " uu____1666))
in (Prims.strcat uu____1659 uu____1665)))
in (Prims.strcat "(let (" uu____1658))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mkBoxFunctions : Prims.string  ->  (Prims.string * Prims.string) = (fun s -> ((s), ((Prims.strcat s "_proj_0"))))


let boxIntFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxInt")


let boxBoolFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxBool")


let boxStringFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxString")


let boxBitVecFun : Prims.int  ->  (Prims.string * Prims.string) = (fun sz -> (

let uu____1697 = (

let uu____1698 = (FStar_Util.string_of_int sz)
in (Prims.strcat "BoxBitVec" uu____1698))
in (mkBoxFunctions uu____1697)))


let isInjective : Prims.string  ->  Prims.bool = (fun s -> (match (((FStar_String.length s) >= (Prims.parse_int "3"))) with
| true -> begin
((

let uu____1705 = (FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3"))
in (uu____1705 = "Box")) && (

let uu____1707 = (

let uu____1708 = (FStar_String.list_of_string s)
in (FStar_List.existsML (fun c -> (c = '.')) uu____1708))
in (not (uu____1707))))
end
| uu____1713 -> begin
false
end))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (

let uu____1722 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {tm = t; freevars = uu____1722; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((TrueOp), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((FalseOp), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____1767 = (

let uu____1768 = (FStar_Util.ensure_decimal i)
in Integer (uu____1768))
in (mk uu____1767 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____1777 = (FStar_Util.string_of_int i)
in (mkInteger uu____1777 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun uu____1834 r -> (match (uu____1834) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (TrueOp, uu____1858) -> begin
(mkFalse r)
end
| App (FalseOp, uu____1863) -> begin
(mkTrue r)
end
| uu____1868 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1881 r -> (match (uu____1881) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____1889), uu____1890) -> begin
t2
end
| (uu____1895, App (TrueOp, uu____1896)) -> begin
t1
end
| (App (FalseOp, uu____1901), uu____1902) -> begin
(mkFalse r)
end
| (uu____1907, App (FalseOp, uu____1908)) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (uu____1925, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), uu____1934) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____1941 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1958 r -> (match (uu____1958) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____1966), uu____1967) -> begin
(mkTrue r)
end
| (uu____1972, App (TrueOp, uu____1973)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____1978), uu____1979) -> begin
t2
end
| (uu____1984, App (FalseOp, uu____1985)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (uu____2002, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), uu____2011) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____2018 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____2035 r -> (match (uu____2035) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (uu____2043, App (TrueOp, uu____2044)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____2049), uu____2050) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____2055), uu____2056) -> begin
t2
end
| (uu____2061, App (Imp, (t1')::(t2')::[])) -> begin
(

let uu____2066 = (

let uu____2073 = (

let uu____2076 = (mkAnd ((t1), (t1')) r)
in (uu____2076)::(t2')::[])
in ((Imp), (uu____2073)))
in (mkApp' uu____2066 r))
end
| uu____2079 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op uu____2100 r -> (match (uu____2100) with
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


let mkBvShl : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2202 r -> (match (uu____2202) with
| (t1, t2) -> begin
(

let uu____2210 = (

let uu____2217 = (

let uu____2220 = (

let uu____2223 = (mkNatToBv sz t2 r)
in (uu____2223)::[])
in (t1)::uu____2220)
in ((BvShl), (uu____2217)))
in (mkApp' uu____2210 r))
end))


let mkBvShr : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2240 r -> (match (uu____2240) with
| (t1, t2) -> begin
(

let uu____2248 = (

let uu____2255 = (

let uu____2258 = (

let uu____2261 = (mkNatToBv sz t2 r)
in (uu____2261)::[])
in (t1)::uu____2258)
in ((BvShr), (uu____2255)))
in (mkApp' uu____2248 r))
end))


let mkBvUdiv : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2278 r -> (match (uu____2278) with
| (t1, t2) -> begin
(

let uu____2286 = (

let uu____2293 = (

let uu____2296 = (

let uu____2299 = (mkNatToBv sz t2 r)
in (uu____2299)::[])
in (t1)::uu____2296)
in ((BvUdiv), (uu____2293)))
in (mkApp' uu____2286 r))
end))


let mkBvMod : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2316 r -> (match (uu____2316) with
| (t1, t2) -> begin
(

let uu____2324 = (

let uu____2331 = (

let uu____2334 = (

let uu____2337 = (mkNatToBv sz t2 r)
in (uu____2337)::[])
in (t1)::uu____2334)
in ((BvMod), (uu____2331)))
in (mkApp' uu____2324 r))
end))


let mkBvMul : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2354 r -> (match (uu____2354) with
| (t1, t2) -> begin
(

let uu____2362 = (

let uu____2369 = (

let uu____2372 = (

let uu____2375 = (mkNatToBv sz t2 r)
in (uu____2375)::[])
in (t1)::uu____2372)
in ((BvMul), (uu____2369)))
in (mkApp' uu____2362 r))
end))


let mkBvUlt : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvUlt)


let mkIff : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Iff)


let mkEq : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____2408 r -> (match (uu____2408) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (Var (f1), (s1)::[]), App (Var (f2), (s2)::[])) when ((f1 = f2) && (isInjective f1)) -> begin
(mk_bin_op Eq ((s1), (s2)) r)
end
| uu____2424 -> begin
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


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun uu____2531 r -> (match (uu____2531) with
| (t1, t2, t3) -> begin
(match (t1.tm) with
| App (TrueOp, uu____2542) -> begin
t2
end
| App (FalseOp, uu____2547) -> begin
t3
end
| uu____2552 -> begin
(match (((t2.tm), (t3.tm))) with
| (App (TrueOp, uu____2553), App (TrueOp, uu____2554)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____2563), uu____2564) -> begin
(

let uu____2569 = (

let uu____2574 = (mkNot t1 t1.rng)
in ((uu____2574), (t3)))
in (mkImp uu____2569 r))
end
| (uu____2575, App (TrueOp, uu____2576)) -> begin
(mkImp ((t1), (t2)) r)
end
| (uu____2581, uu____2582) -> begin
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


let mkQuant : (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____2629 r -> (match (uu____2629) with
| (qop, pats, wopt, vars, body) -> begin
(match (((FStar_List.length vars) = (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____2670 -> begin
(match (body.tm) with
| App (TrueOp, uu____2671) -> begin
body
end
| uu____2676 -> begin
(mk (Quant (((qop), (pats), (wopt), (vars), (body)))) r)
end)
end)
end))


let mkLet : (term Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____2697 r -> (match (uu____2697) with
| (es, body) -> begin
(match (((FStar_List.length es) = (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____2711 -> begin
(mk (Let (((es), (body)))) r)
end)
end))


let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (

let nvars = (FStar_List.length fvs)
in (

let index_of = (fun fv -> (

let uu____2733 = (FStar_Util.try_find_index (fv_eq fv) fvs)
in (match (uu____2733) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((nvars - (i + (Prims.parse_int "1"))))
end)))
in (

let rec aux = (fun ix t1 -> (

let uu____2752 = (FStar_ST.read t1.freevars)
in (match (uu____2752) with
| FStar_Pervasives_Native.Some ([]) -> begin
t1
end
| uu____2779 -> begin
(match (t1.tm) with
| Integer (uu____2788) -> begin
t1
end
| BoundV (uu____2789) -> begin
t1
end
| FreeV (x) -> begin
(

let uu____2795 = (index_of x)
in (match (uu____2795) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (i) -> begin
(mkBoundV (i + ix) t1.rng)
end))
end
| App (op, tms) -> begin
(

let uu____2805 = (

let uu____2812 = (FStar_List.map (aux ix) tms)
in ((op), (uu____2812)))
in (mkApp' uu____2805 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____2820 = (

let uu____2821 = (

let uu____2828 = (aux ix t2)
in ((uu____2828), (r1), (r2)))
in Labeled (uu____2821))
in (mk uu____2820 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____2831 = (

let uu____2832 = (

let uu____2837 = (aux ix t2)
in ((uu____2837), (r)))
in LblPos (uu____2832))
in (mk uu____2831 t2.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n1 = (FStar_List.length vars)
in (

let uu____2860 = (

let uu____2879 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n1)))))
in (

let uu____2900 = (aux (ix + n1) body)
in ((qop), (uu____2879), (wopt), (vars), (uu____2900))))
in (mkQuant uu____2860 t1.rng)))
end
| Let (es, body) -> begin
(

let uu____2919 = (FStar_List.fold_left (fun uu____2937 e -> (match (uu____2937) with
| (ix1, l) -> begin
(

let uu____2957 = (

let uu____2960 = (aux ix1 e)
in (uu____2960)::l)
in (((ix1 + (Prims.parse_int "1"))), (uu____2957)))
end)) ((ix), ([])) es)
in (match (uu____2919) with
| (ix1, es_rev) -> begin
(

let uu____2971 = (

let uu____2978 = (aux ix1 body)
in (((FStar_List.rev es_rev)), (uu____2978)))
in (mkLet uu____2971 t1.rng))
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
| Integer (uu____3004) -> begin
t1
end
| FreeV (uu____3005) -> begin
t1
end
| BoundV (i) -> begin
(match ((((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1))) with
| true -> begin
(FStar_List.nth tms1 (i - shift))
end
| uu____3015 -> begin
t1
end)
end
| App (op, tms2) -> begin
(

let uu____3022 = (

let uu____3029 = (FStar_List.map (aux shift) tms2)
in ((op), (uu____3029)))
in (mkApp' uu____3022 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____3037 = (

let uu____3038 = (

let uu____3045 = (aux shift t2)
in ((uu____3045), (r1), (r2)))
in Labeled (uu____3038))
in (mk uu____3037 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____3048 = (

let uu____3049 = (

let uu____3054 = (aux shift t2)
in ((uu____3054), (r)))
in LblPos (uu____3049))
in (mk uu____3048 t2.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift1 = (shift + m)
in (

let uu____3082 = (

let uu____3101 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift1))))
in (

let uu____3118 = (aux shift1 body)
in ((qop), (uu____3101), (wopt), (vars), (uu____3118))))
in (mkQuant uu____3082 t1.rng))))
end
| Let (es, body) -> begin
(

let uu____3133 = (FStar_List.fold_left (fun uu____3151 e -> (match (uu____3151) with
| (ix, es1) -> begin
(

let uu____3171 = (

let uu____3174 = (aux shift e)
in (uu____3174)::es1)
in (((shift + (Prims.parse_int "1"))), (uu____3171)))
end)) ((shift), ([])) es)
in (match (uu____3133) with
| (shift1, es_rev) -> begin
(

let uu____3185 = (

let uu____3192 = (aux shift1 body)
in (((FStar_List.rev es_rev)), (uu____3192)))
in (mkLet uu____3185 t1.rng))
end))
end))
in (aux (Prims.parse_int "0") t)))))


let subst : term  ->  fv  ->  term  ->  term = (fun t fv s -> (

let uu____3207 = (abstr ((fv)::[]) t)
in (inst ((s)::[]) uu____3207)))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fv Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____3231 -> (match (uu____3231) with
| (qop, pats, wopt, vars, body) -> begin
(

let uu____3273 = (

let uu____3292 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (

let uu____3309 = (FStar_List.map fv_sort vars)
in (

let uu____3316 = (abstr vars body)
in ((qop), (uu____3292), (wopt), (uu____3309), (uu____3316)))))
in (mkQuant uu____3273))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____3347 r -> (match (uu____3347) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)) r)
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____3413 r -> (match (uu____3413) with
| (pats, wopt, vars, body) -> begin
(

let uu____3445 = (mkQuant' ((Forall), (pats), (wopt), (vars), (body)))
in (uu____3445 r))
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____3470 r -> (match (uu____3470) with
| (pats, vars, body) -> begin
(

let uu____3493 = (mkQuant' ((Forall), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
in (uu____3493 r))
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____3518 r -> (match (uu____3518) with
| (pats, vars, body) -> begin
(

let uu____3541 = (mkQuant' ((Exists), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
in (uu____3541 r))
end))


let mkLet' : ((fv * term) Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____3566 r -> (match (uu____3566) with
| (bindings, body) -> begin
(

let uu____3592 = (FStar_List.split bindings)
in (match (uu____3592) with
| (vars, es) -> begin
(

let uu____3611 = (

let uu____3618 = (abstr vars body)
in ((es), (uu____3618)))
in (mkLet uu____3611 r))
end))
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun uu____3640 -> (match (uu____3640) with
| (nm, vars, s, tm, c) -> begin
(

let uu____3674 = (

let uu____3687 = (FStar_List.map fv_sort vars)
in (

let uu____3694 = (abstr vars tm)
in ((nm), (uu____3687), (s), (uu____3694), (c))))
in DefineFun (uu____3674))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (

let uu____3701 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" uu____3701)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun uu____3712 id -> (match (uu____3712) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (

let a = (

let uu____3722 = (

let uu____3723 = (

let uu____3728 = (mkInteger' id norng)
in (

let uu____3729 = (

let uu____3730 = (

let uu____3737 = (constr_id_of_sort sort)
in (

let uu____3738 = (

let uu____3741 = (mkApp ((tok_name), ([])) norng)
in (uu____3741)::[])
in ((uu____3737), (uu____3738))))
in (mkApp uu____3730 norng))
in ((uu____3728), (uu____3729))))
in (mkEq uu____3723 norng))
in {assumption_term = uu____3722; assumption_caption = FStar_Pervasives_Native.Some ("fresh token"); assumption_name = a_name; assumption_fact_ids = []})
in Assume (a)))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun uu____3759 -> (match (uu____3759) with
| (name, arg_sorts, sort, id) -> begin
(

let id1 = (FStar_Util.string_of_int id)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (

let uu____3791 = (

let uu____3796 = (

let uu____3797 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____3797))
in ((uu____3796), (s)))
in (mkFreeV uu____3791 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (

let uu____3805 = (

let uu____3812 = (constr_id_of_sort sort)
in ((uu____3812), ((capp)::[])))
in (mkApp uu____3805 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (

let a = (

let uu____3817 = (

let uu____3818 = (

let uu____3829 = (

let uu____3830 = (

let uu____3835 = (mkInteger id1 norng)
in ((uu____3835), (cid_app)))
in (mkEq uu____3830 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____3829)))
in (mkForall uu____3818 norng))
in {assumption_term = uu____3817; assumption_caption = FStar_Pervasives_Native.Some ("Consrtructor distinct"); assumption_name = a_name; assumption_fact_ids = []})
in Assume (a))))))))
end))


let injective_constructor : (Prims.string * constructor_field Prims.list * sort)  ->  decls_t = (fun uu____3857 -> (match (uu____3857) with
| (name, fields, sort) -> begin
(

let n_bvars = (FStar_List.length fields)
in (

let bvar_name = (fun i -> (

let uu____3878 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____3878)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (

let uu____3898 = (

let uu____3903 = (bvar_name i)
in ((uu____3903), (s)))
in (mkFreeV uu____3898)))
in (

let bvars = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____3924 -> (match (uu____3924) with
| (uu____3931, s, uu____3933) -> begin
(

let uu____3934 = (bvar i s)
in (uu____3934 norng))
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let uu____3943 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____3971 -> (match (uu____3971) with
| (name1, s, projectible) -> begin
(

let cproj_app = (mkApp ((name1), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((name1), ((sort)::[]), (s), (FStar_Pervasives_Native.Some ("Projector"))))
in (match (projectible) with
| true -> begin
(

let a = (

let uu____3994 = (

let uu____3995 = (

let uu____4006 = (

let uu____4007 = (

let uu____4012 = (

let uu____4013 = (bvar i s)
in (uu____4013 norng))
in ((cproj_app), (uu____4012)))
in (mkEq uu____4007 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____4006)))
in (mkForall uu____3995 norng))
in {assumption_term = uu____3994; assumption_caption = FStar_Pervasives_Native.Some ("Projection inverse"); assumption_name = (Prims.strcat "projection_inverse_" name1); assumption_fact_ids = []})
in (proj_name)::(Assume (a))::[])
end
| uu____4026 -> begin
(proj_name)::[]
end)))
end))))
in (FStar_All.pipe_right uu____3943 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun uu____4036 -> (match (uu____4036) with
| (name, fields, sort, id, injective) -> begin
(

let injective1 = (injective || true)
in (

let field_sorts = (FStar_All.pipe_right fields (FStar_List.map (fun uu____4064 -> (match (uu____4064) with
| (uu____4071, sort1, uu____4073) -> begin
sort1
end))))
in (

let cdecl = DeclFun (((name), (field_sorts), (sort), (FStar_Pervasives_Native.Some ("Constructor"))))
in (

let cid = (fresh_constructor ((name), (field_sorts), (sort), (id)))
in (

let disc = (

let disc_name = (Prims.strcat "is-" name)
in (

let xfv = (("x"), (sort))
in (

let xx = (mkFreeV xfv norng)
in (

let disc_eq = (

let uu____4091 = (

let uu____4096 = (

let uu____4097 = (

let uu____4104 = (constr_id_of_sort sort)
in ((uu____4104), ((xx)::[])))
in (mkApp uu____4097 norng))
in (

let uu____4107 = (

let uu____4108 = (FStar_Util.string_of_int id)
in (mkInteger uu____4108 norng))
in ((uu____4096), (uu____4107))))
in (mkEq uu____4091 norng))
in (

let uu____4109 = (

let uu____4124 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____4174 -> (match (uu____4174) with
| (proj, s, projectible) -> begin
(match (projectible) with
| true -> begin
(

let uu____4204 = (mkApp ((proj), ((xx)::[])) norng)
in ((uu____4204), ([])))
end
| uu____4217 -> begin
(

let fi = (

let uu____4223 = (

let uu____4224 = (FStar_Util.string_of_int i)
in (Prims.strcat "f_" uu____4224))
in ((uu____4223), (s)))
in (

let uu____4225 = (mkFreeV fi norng)
in ((uu____4225), ((fi)::[]))))
end)
end))))
in (FStar_All.pipe_right uu____4124 FStar_List.split))
in (match (uu____4109) with
| (proj_terms, ex_vars) -> begin
(

let ex_vars1 = (FStar_List.flatten ex_vars)
in (

let disc_inv_body = (

let uu____4306 = (

let uu____4311 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (uu____4311)))
in (mkEq uu____4306 norng))
in (

let disc_inv_body1 = (match (ex_vars1) with
| [] -> begin
disc_inv_body
end
| uu____4319 -> begin
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
| uu____4359 -> begin
[]
end)
in (

let uu____4360 = (

let uu____4363 = (

let uu____4364 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (uu____4364))
in (uu____4363)::(cdecl)::(cid)::projs)
in (

let uu____4365 = (

let uu____4368 = (

let uu____4371 = (

let uu____4372 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (uu____4372))
in (uu____4371)::[])
in (FStar_List.append ((disc)::[]) uu____4368))
in (FStar_List.append uu____4360 uu____4365)))))))))
end))


let name_binders_inner : Prims.string FStar_Pervasives_Native.option  ->  (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun prefix_opt outer_names start sorts -> (

let uu____4423 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun uu____4478 s -> (match (uu____4478) with
| (names1, binders, n1) -> begin
(

let prefix1 = (match (s) with
| Term_sort -> begin
"@x"
end
| uu____4528 -> begin
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

let uu____4532 = (FStar_Util.string_of_int n1)
in (Prims.strcat prefix2 uu____4532))
in (

let names2 = (((nm), (s)))::names1
in (

let b = (

let uu____4545 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm uu____4545))
in ((names2), ((b)::binders), ((n1 + (Prims.parse_int "1")))))))))
end)) ((outer_names), ([]), (start))))
in (match (uu____4423) with
| (names1, binders, n1) -> begin
((names1), ((FStar_List.rev binders)), (n1))
end)))


let name_macro_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let uu____4623 = (name_binders_inner (FStar_Pervasives_Native.Some ("__")) [] (Prims.parse_int "0") sorts)
in (match (uu____4623) with
| (names1, binders, n1) -> begin
(((FStar_List.rev names1)), (binders))
end)))


let termToSmt : Prims.string  ->  term  ->  Prims.string = (fun enclosing_name t -> (

let next_qid = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun depth -> (

let n1 = (FStar_ST.read ctr)
in ((FStar_Util.incr ctr);
(match ((n1 = (Prims.parse_int "0"))) with
| true -> begin
enclosing_name
end
| uu____4707 -> begin
(

let uu____4708 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "%s.%s" enclosing_name uu____4708))
end);
))))
in (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (uu____4750); freevars = uu____4751; rng = uu____4752})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| uu____4766 -> begin
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

let uu____4806 = (FStar_List.nth names1 i)
in (FStar_All.pipe_right uu____4806 FStar_Pervasives_Native.fst))
end
| FreeV (x) -> begin
(FStar_Pervasives_Native.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(

let uu____4821 = (op_to_string op)
in (

let uu____4822 = (

let uu____4823 = (FStar_List.map (aux1 n1 names1) tms)
in (FStar_All.pipe_right uu____4823 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" uu____4821 uu____4822)))
end
| Labeled (t2, uu____4829, uu____4830) -> begin
(aux1 n1 names1 t2)
end
| LblPos (t2, s) -> begin
(

let uu____4833 = (aux1 n1 names1 t2)
in (FStar_Util.format2 "(! %s :lblpos %s)" uu____4833 s))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let qid = (next_qid ())
in (

let uu____4856 = (name_binders_inner FStar_Pervasives_Native.None names1 n1 sorts)
in (match (uu____4856) with
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
| uu____4905 -> begin
(

let uu____4910 = (FStar_All.pipe_right pats1 (FStar_List.map (fun pats2 -> (

let uu____4926 = (

let uu____4927 = (FStar_List.map (fun p -> (

let uu____4933 = (aux1 n2 names2 p)
in (FStar_Util.format1 "%s" uu____4933))) pats2)
in (FStar_String.concat " " uu____4927))
in (FStar_Util.format1 "\n:pattern (%s)" uu____4926)))))
in (FStar_All.pipe_right uu____4910 (FStar_String.concat "\n")))
end)
in (

let uu____4936 = (

let uu____4939 = (

let uu____4942 = (

let uu____4945 = (aux1 n2 names2 body)
in (

let uu____4946 = (

let uu____4949 = (weightToSmt wopt)
in (uu____4949)::(pats_str)::(qid)::[])
in (uu____4945)::uu____4946))
in (binders1)::uu____4942)
in ((qop_to_string qop))::uu____4939)
in (FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))" uu____4936)))))
end)))
end
| Let (es, body) -> begin
(

let uu____4956 = (FStar_List.fold_left (fun uu____4993 e -> (match (uu____4993) with
| (names0, binders, n0) -> begin
(

let nm = (

let uu____5043 = (FStar_Util.string_of_int n0)
in (Prims.strcat "@lb" uu____5043))
in (

let names01 = (((nm), (Term_sort)))::names0
in (

let b = (

let uu____5056 = (aux1 n1 names1 e)
in (FStar_Util.format2 "(%s %s)" nm uu____5056))
in ((names01), ((b)::binders), ((n0 + (Prims.parse_int "1")))))))
end)) ((names1), ([]), (n1)) es)
in (match (uu____4956) with
| (names2, binders, n2) -> begin
(

let uu____5088 = (aux1 n2 names2 body)
in (FStar_Util.format2 "(let (%s)\n%s)" (FStar_String.concat " " binders) uu____5088))
end))
end)))
and aux = (fun depth n1 names1 t1 -> (

let s = (aux' depth n1 names1 t1)
in (match ((t1.rng <> norng)) with
| true -> begin
(

let uu____5096 = (FStar_Range.string_of_range t1.rng)
in (

let uu____5097 = (FStar_Range.string_of_use_range t1.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____5096 uu____5097 s)))
end
| uu____5098 -> begin
s
end)))
in (aux (Prims.parse_int "0") (Prims.parse_int "0") [] t)))))


let caption_to_string : Prims.string FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___92_5104 -> (match (uu___92_5104) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let uu____5108 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(failwith "Impossible")
end
| (hd1)::[] -> begin
((hd1), (""))
end
| (hd1)::uu____5123 -> begin
((hd1), ("..."))
end)
in (match (uu____5108) with
| (hd1, suffix) -> begin
(FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
end))
end))


let rec declToSmt : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (

let escape = (fun s -> (FStar_Util.replace_char s '\'' '_'))
in (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(

let uu____5141 = (FStar_Options.log_queries ())
in (match (uu____5141) with
| true -> begin
(

let uu____5142 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun uu___93_5146 -> (match (uu___93_5146) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" uu____5142))
end
| uu____5153 -> begin
""
end))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (

let uu____5165 = (caption_to_string c)
in (

let uu____5166 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____5165 f (FStar_String.concat " " l) uu____5166))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let uu____5176 = (name_macro_binders arg_sorts)
in (match (uu____5176) with
| (names1, binders) -> begin
(

let body1 = (

let uu____5208 = (FStar_List.map (fun x -> (mkFreeV x norng)) names1)
in (inst uu____5208 body))
in (

let uu____5221 = (caption_to_string c)
in (

let uu____5222 = (strSort retsort)
in (

let uu____5223 = (termToSmt (escape f) body1)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____5221 f (FStar_String.concat " " binders) uu____5222 uu____5223)))))
end))
end
| Assume (a) -> begin
(

let fact_ids_to_string = (fun ids -> (FStar_All.pipe_right ids (FStar_List.map (fun uu___94_5241 -> (match (uu___94_5241) with
| Name (n1) -> begin
(Prims.strcat "Name " (FStar_Ident.text_of_lid n1))
end
| Namespace (ns) -> begin
(Prims.strcat "Namespace " (FStar_Ident.text_of_lid ns))
end
| Tag (t) -> begin
(Prims.strcat "Tag " t)
end)))))
in (

let fids = (

let uu____5246 = (FStar_Options.log_queries ())
in (match (uu____5246) with
| true -> begin
(

let uu____5247 = (

let uu____5248 = (fact_ids_to_string a.assumption_fact_ids)
in (FStar_String.concat "; " uu____5248))
in (FStar_Util.format1 ";;; Fact-ids: %s\n" uu____5247))
end
| uu____5251 -> begin
""
end))
in (

let n1 = (escape a.assumption_name)
in (

let uu____5253 = (caption_to_string a.assumption_caption)
in (

let uu____5254 = (termToSmt n1 a.assumption_term)
in (FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____5253 fids uu____5254 n1))))))
end
| Eval (t) -> begin
(

let uu____5256 = (termToSmt "eval" t)
in (FStar_Util.format1 "(eval %s)" uu____5256))
end
| Echo (s) -> begin
(FStar_Util.format1 "(echo \"%s\")" s)
end
| RetainAssumptions (uu____5258) -> begin
""
end
| CheckSat -> begin
"(check-sat)"
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
and mkPrelude : Prims.string  ->  Prims.string = (fun z3options -> (

let basic = (Prims.strcat z3options "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))")
in (

let constrs = ((("FString_const"), (((("FString_const_proj_0"), (Int_sort), (true)))::[]), (String_sort), ((Prims.parse_int "0")), (true)))::((("Tm_type"), ([]), (Term_sort), ((Prims.parse_int "2")), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "3")), (false)))::((("Tm_unit"), ([]), (Term_sort), ((Prims.parse_int "6")), (true)))::((((FStar_Pervasives_Native.fst boxIntFun)), (((((FStar_Pervasives_Native.snd boxIntFun)), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "7")), (true)))::((((FStar_Pervasives_Native.fst boxBoolFun)), (((((FStar_Pervasives_Native.snd boxBoolFun)), (Bool_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "8")), (true)))::((((FStar_Pervasives_Native.fst boxStringFun)), (((((FStar_Pervasives_Native.snd boxStringFun)), (String_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "9")), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort), (true)))::((("LexCons_1"), (Term_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "11")), (true)))::[]
in (

let bcons = (

let uu____5583 = (

let uu____5586 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right uu____5586 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right uu____5583 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mkBvConstructor : Prims.int  ->  decls_t = (fun sz -> (

let uu____5602 = (

let uu____5621 = (

let uu____5622 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____5622))
in (

let uu____5627 = (

let uu____5636 = (

let uu____5643 = (

let uu____5644 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____5644))
in ((uu____5643), (BitVec_sort (sz)), (true)))
in (uu____5636)::[])
in ((uu____5621), (uu____5627), (Term_sort), (((Prims.parse_int "12") + sz)), (true))))
in (FStar_All.pipe_right uu____5602 constructor_to_decl)))


let mk_Range_const : term = (mkApp (("Range_const"), ([])) norng)


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____5713 = (

let uu____5720 = (

let uu____5723 = (mkInteger' i norng)
in (uu____5723)::[])
in (("Tm_uvar"), (uu____5720)))
in (mkApp uu____5713 r)))


let mk_Term_unit : term = (mkApp (("Tm_unit"), ([])) norng)


let elim_box : Prims.bool  ->  Prims.string  ->  Prims.string  ->  term  ->  term = (fun cond u v1 t -> (match (t.tm) with
| App (Var (v'), (t1)::[]) when ((v1 = v') && cond) -> begin
t1
end
| uu____5748 -> begin
(mkApp ((u), ((t)::[])) t.rng)
end))


let maybe_elim_box : Prims.string  ->  Prims.string  ->  term  ->  term = (fun u v1 t -> (

let uu____5763 = (FStar_Options.smtencoding_elim_box ())
in (elim_box uu____5763 u v1 t)))


let boxInt : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxIntFun) (FStar_Pervasives_Native.snd boxIntFun) t))


let unboxInt : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxIntFun) (FStar_Pervasives_Native.fst boxIntFun) t))


let boxBool : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxBoolFun) (FStar_Pervasives_Native.snd boxBoolFun) t))


let unboxBool : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxBoolFun) (FStar_Pervasives_Native.fst boxBoolFun) t))


let boxString : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxStringFun) (FStar_Pervasives_Native.snd boxStringFun) t))


let unboxString : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxStringFun) (FStar_Pervasives_Native.fst boxStringFun) t))


let boxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let uu____5796 = (

let uu____5797 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____5797))
in (

let uu____5802 = (

let uu____5803 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____5803))
in (elim_box true uu____5796 uu____5802 t))))


let unboxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let uu____5816 = (

let uu____5817 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____5817))
in (

let uu____5822 = (

let uu____5823 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____5823))
in (elim_box true uu____5816 uu____5822 t))))


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
| uu____5837 -> begin
(FStar_Pervasives.raise FStar_Util.Impos)
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
| uu____5847 -> begin
(FStar_Pervasives.raise FStar_Util.Impos)
end))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n1) -> begin
(FStar_Util.format1 "(Integer %s)" n1)
end
| BoundV (n1) -> begin
(

let uu____5863 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(BoundV %s)" uu____5863))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv))
end
| App (op, l) -> begin
(

let uu____5875 = (op_to_string op)
in (

let uu____5876 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" uu____5875 uu____5876)))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____5880 = (print_smt_term t1)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 uu____5880))
end
| LblPos (t1, s) -> begin
(

let uu____5883 = (print_smt_term t1)
in (FStar_Util.format2 "(LblPos %s %s)" s uu____5883))
end
| Quant (qop, l, uu____5886, uu____5887, t1) -> begin
(

let uu____5905 = (print_smt_term_list_list l)
in (

let uu____5906 = (print_smt_term t1)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____5905 uu____5906)))
end
| Let (es, body) -> begin
(

let uu____5913 = (print_smt_term_list es)
in (

let uu____5914 = (print_smt_term body)
in (FStar_Util.format2 "(let %s %s)" uu____5913 uu____5914)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (

let uu____5918 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right uu____5918 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l1 -> (

let uu____5937 = (

let uu____5938 = (

let uu____5939 = (print_smt_term_list l1)
in (Prims.strcat uu____5939 " ] "))
in (Prims.strcat "; [ " uu____5938))
in (Prims.strcat s uu____5937))) "" l))


let getBoxedInteger : term  ->  Prims.int FStar_Pervasives_Native.option = (fun t -> (match (t.tm) with
| App (Var (s), (t2)::[]) when (s = (FStar_Pervasives_Native.fst boxIntFun)) -> begin
(match (t2.tm) with
| Integer (n1) -> begin
(

let uu____5955 = (FStar_Util.int_of_string n1)
in FStar_Pervasives_Native.Some (uu____5955))
end
| uu____5956 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____5957 -> begin
FStar_Pervasives_Native.None
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (uu____5968)::(t1)::(t2)::[]); freevars = uu____5971; rng = uu____5972})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (uu____5985)::(t1)::(t2)::[]); freevars = uu____5988; rng = uu____5989})::[]) -> begin
(

let uu____6002 = (mkEq ((t1), (t2)) norng)
in (mkNot uu____6002 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = uu____6005; rng = uu____6006})::[]) -> begin
(

let uu____6019 = (

let uu____6024 = (unboxInt t1)
in (

let uu____6025 = (unboxInt t2)
in ((uu____6024), (uu____6025))))
in (mkLTE uu____6019 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = uu____6028; rng = uu____6029})::[]) -> begin
(

let uu____6042 = (

let uu____6047 = (unboxInt t1)
in (

let uu____6048 = (unboxInt t2)
in ((uu____6047), (uu____6048))))
in (mkLT uu____6042 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = uu____6051; rng = uu____6052})::[]) -> begin
(

let uu____6065 = (

let uu____6070 = (unboxInt t1)
in (

let uu____6071 = (unboxInt t2)
in ((uu____6070), (uu____6071))))
in (mkGTE uu____6065 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = uu____6074; rng = uu____6075})::[]) -> begin
(

let uu____6088 = (

let uu____6093 = (unboxInt t1)
in (

let uu____6094 = (unboxInt t2)
in ((uu____6093), (uu____6094))))
in (mkGT uu____6088 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = uu____6097; rng = uu____6098})::[]) -> begin
(

let uu____6111 = (

let uu____6116 = (unboxBool t1)
in (

let uu____6117 = (unboxBool t2)
in ((uu____6116), (uu____6117))))
in (mkAnd uu____6111 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = uu____6120; rng = uu____6121})::[]) -> begin
(

let uu____6134 = (

let uu____6139 = (unboxBool t1)
in (

let uu____6140 = (unboxBool t2)
in ((uu____6139), (uu____6140))))
in (mkOr uu____6134 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t1)::[]); freevars = uu____6142; rng = uu____6143})::[]) -> begin
(

let uu____6156 = (unboxBool t1)
in (mkNot uu____6156 t1.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("FStar.BV.bvult"), (t0)::(t1)::(t2)::[]); freevars = uu____6160; rng = uu____6161})::[]) when (

let uu____6174 = (getBoxedInteger t0)
in (FStar_Util.is_some uu____6174)) -> begin
(

let sz = (

let uu____6178 = (getBoxedInteger t0)
in (match (uu____6178) with
| FStar_Pervasives_Native.Some (sz) -> begin
sz
end
| uu____6182 -> begin
(failwith "impossible")
end))
in (

let uu____6185 = (

let uu____6190 = (unboxBitVec sz t1)
in (

let uu____6191 = (unboxBitVec sz t2)
in ((uu____6190), (uu____6191))))
in (mkBvUlt uu____6185 t.rng)))
end
| App (Var ("Prims.equals"), (uu____6192)::({tm = App (Var ("FStar.BV.bvult"), (t0)::(t1)::(t2)::[]); freevars = uu____6196; rng = uu____6197})::(uu____6198)::[]) when (

let uu____6211 = (getBoxedInteger t0)
in (FStar_Util.is_some uu____6211)) -> begin
(

let sz = (

let uu____6215 = (getBoxedInteger t0)
in (match (uu____6215) with
| FStar_Pervasives_Native.Some (sz) -> begin
sz
end
| uu____6219 -> begin
(failwith "impossible")
end))
in (

let uu____6222 = (

let uu____6227 = (unboxBitVec sz t1)
in (

let uu____6228 = (unboxBitVec sz t2)
in ((uu____6227), (uu____6228))))
in (mkBvUlt uu____6222 t.rng)))
end
| App (Var ("Prims.b2t"), (t1)::[]) -> begin
(

let uu___95_6232 = (unboxBool t1)
in {tm = uu___95_6232.tm; freevars = uu___95_6232.freevars; rng = t.rng})
end
| uu____6233 -> begin
(mkApp (("Valid"), ((t)::[])) t.rng)
end))


let mk_HasType : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasType"), ((v1)::(t)::[])) t.rng))


let mk_HasTypeZ : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasTypeZ"), ((v1)::(t)::[])) t.rng))


let mk_IsTyped : term  ->  term = (fun v1 -> (mkApp (("IsTyped"), ((v1)::[])) norng))


let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v1 t -> (

let uu____6274 = (FStar_Options.unthrottle_inductives ())
in (match (uu____6274) with
| true -> begin
(mk_HasType v1 t)
end
| uu____6275 -> begin
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

let uu____6365 = (

let uu____6372 = (

let uu____6375 = (mkInteger' i norng)
in (uu____6375)::[])
in (("FString_const"), (uu____6372)))
in (mkApp uu____6365 r)))


let mk_Precedes : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (

let uu____6390 = (mkApp (("Precedes"), ((x1)::(x2)::[])) r)
in (FStar_All.pipe_right uu____6390 mk_Valid)))


let mk_LexCons : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (mkApp (("LexCons"), ((x1)::(x2)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n1 -> (match ((n1 = (Prims.parse_int "0"))) with
| true -> begin
(mkApp (("ZFuel"), ([])) norng)
end
| uu____6413 -> begin
(

let uu____6414 = (

let uu____6421 = (

let uu____6424 = (n_fuel (n1 - (Prims.parse_int "1")))
in (uu____6424)::[])
in (("SFuel"), (uu____6421)))
in (mkApp uu____6414 norng))
end))


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term FStar_Pervasives_Native.option  ->  term FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  term FStar_Pervasives_Native.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (FStar_Pervasives_Native.Some (p11), FStar_Pervasives_Native.Some (p21)) -> begin
(

let uu____6461 = (mkAnd ((p11), (p21)) r)
in FStar_Pervasives_Native.Some (uu____6461))
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

let uu____6518 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l uu____6518)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____6535 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l uu____6535)))


let mk_haseq : term  ->  term = (fun t -> (

let uu____6544 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid uu____6544)))




