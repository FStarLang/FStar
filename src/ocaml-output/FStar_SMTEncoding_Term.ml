
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
| uu____476 -> begin
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
| uu____490 -> begin
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
| uu____508 -> begin
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
| uu____540 -> begin
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
| uu____590 -> begin
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
| uu____664 -> begin
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
| uu____702 -> begin
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
| uu____738 -> begin
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
| uu____896 -> begin
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
| uu____910 -> begin
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
| uu____924 -> begin
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
| uu____1059 -> begin
false
end))


let uu___is_DeclFun : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DeclFun (_0) -> begin
true
end
| uu____1075 -> begin
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
| uu____1131 -> begin
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
| uu____1181 -> begin
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
| uu____1195 -> begin
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
| uu____1209 -> begin
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
| uu____1223 -> begin
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
| uu____1239 -> begin
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
| uu____1258 -> begin
false
end))


let uu___is_Pop : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____1263 -> begin
false
end))


let uu___is_CheckSat : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckSat -> begin
true
end
| uu____1268 -> begin
false
end))


let uu___is_GetUnsatCore : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetUnsatCore -> begin
true
end
| uu____1273 -> begin
false
end))


let uu___is_SetOption : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOption (_0) -> begin
true
end
| uu____1283 -> begin
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
| uu____1308 -> begin
false
end))


let uu___is_GetReasonUnknown : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetReasonUnknown -> begin
true
end
| uu____1313 -> begin
false
end))


type decls_t =
decl Prims.list


type error_label =
(fv * Prims.string * FStar_Range.range)


type error_labels =
error_label Prims.list


let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> (Prims.op_Equality (FStar_Pervasives_Native.fst x) (FStar_Pervasives_Native.fst y)))


let fv_sort : 'Auu____1338 'Auu____1339 . ('Auu____1339 * 'Auu____1338)  ->  'Auu____1338 = (fun x -> (FStar_Pervasives_Native.snd x))


let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match (((x.tm), (y.tm))) with
| (FreeV (x1), FreeV (y1)) -> begin
(fv_eq x1 y1)
end
| uu____1370 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun uu___87_1378 -> (match (uu___87_1378) with
| {tm = FreeV (x); freevars = uu____1380; rng = uu____1381} -> begin
(fv_sort x)
end
| uu____1394 -> begin
(failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun uu___88_1398 -> (match (uu___88_1398) with
| {tm = FreeV (fv); freevars = uu____1400; rng = uu____1401} -> begin
fv
end
| uu____1414 -> begin
(failwith "impossible")
end))


let rec freevars : term  ->  (Prims.string * sort) Prims.list = (fun t -> (match (t.tm) with
| Integer (uu____1431) -> begin
[]
end
| BoundV (uu____1436) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (uu____1454, tms) -> begin
(FStar_List.collect freevars tms)
end
| Quant (uu____1464, uu____1465, uu____1466, uu____1467, t1) -> begin
(freevars t1)
end
| Labeled (t1, uu____1486, uu____1487) -> begin
(freevars t1)
end
| LblPos (t1, uu____1489) -> begin
(freevars t1)
end
| Let (es, body) -> begin
(FStar_List.collect freevars ((body)::es))
end))


let free_variables : term  ->  fvs = (fun t -> (

let uu____1504 = (FStar_ST.op_Bang t.freevars)
in (match (uu____1504) with
| FStar_Pervasives_Native.Some (b) -> begin
b
end
| FStar_Pervasives_Native.None -> begin
(

let fvs = (

let uu____1597 = (freevars t)
in (FStar_Util.remove_dups fv_eq uu____1597))
in ((FStar_ST.op_Colon_Equals t.freevars (FStar_Pervasives_Native.Some (fvs)));
fvs;
))
end)))


let qop_to_string : qop  ->  Prims.string = (fun uu___89_1668 -> (match (uu___89_1668) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun uu___90_1672 -> (match (uu___90_1672) with
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

let uu____1674 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ zero_extend %s)" uu____1674))
end
| NatToBv (n1) -> begin
(

let uu____1676 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ int2bv %s)" uu____1676))
end
| Var (s) -> begin
s
end))


let weightToSmt : Prims.int FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___91_1683 -> (match (uu___91_1683) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (i) -> begin
(

let uu____1687 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" uu____1687))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____1695 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" uu____1695))
end
| FreeV (x) -> begin
(

let uu____1701 = (

let uu____1702 = (strSort (FStar_Pervasives_Native.snd x))
in (Prims.strcat ":" uu____1702))
in (Prims.strcat (FStar_Pervasives_Native.fst x) uu____1701))
end
| App (op, tms) -> begin
(

let uu____1709 = (

let uu____1710 = (op_to_string op)
in (

let uu____1711 = (

let uu____1712 = (

let uu____1713 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right uu____1713 (FStar_String.concat " ")))
in (Prims.strcat uu____1712 ")"))
in (Prims.strcat uu____1710 uu____1711)))
in (Prims.strcat "(" uu____1709))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____1721 = (hash_of_term t1)
in (

let uu____1722 = (

let uu____1723 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 uu____1723))
in (Prims.strcat uu____1721 uu____1722)))
end
| LblPos (t1, r) -> begin
(

let uu____1726 = (

let uu____1727 = (hash_of_term t1)
in (Prims.strcat uu____1727 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " uu____1726))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let uu____1749 = (

let uu____1750 = (

let uu____1751 = (

let uu____1752 = (

let uu____1753 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right uu____1753 (FStar_String.concat " ")))
in (

let uu____1758 = (

let uu____1759 = (

let uu____1760 = (hash_of_term body)
in (

let uu____1761 = (

let uu____1762 = (

let uu____1763 = (weightToSmt wopt)
in (

let uu____1764 = (

let uu____1765 = (

let uu____1766 = (

let uu____1767 = (FStar_All.pipe_right pats (FStar_List.map (fun pats1 -> (

let uu____1783 = (FStar_List.map hash_of_term pats1)
in (FStar_All.pipe_right uu____1783 (FStar_String.concat " "))))))
in (FStar_All.pipe_right uu____1767 (FStar_String.concat "; ")))
in (Prims.strcat uu____1766 "))"))
in (Prims.strcat " " uu____1765))
in (Prims.strcat uu____1763 uu____1764)))
in (Prims.strcat " " uu____1762))
in (Prims.strcat uu____1760 uu____1761)))
in (Prims.strcat ")(! " uu____1759))
in (Prims.strcat uu____1752 uu____1758)))
in (Prims.strcat " (" uu____1751))
in (Prims.strcat (qop_to_string qop) uu____1750))
in (Prims.strcat "(" uu____1749))
end
| Let (es, body) -> begin
(

let uu____1796 = (

let uu____1797 = (

let uu____1798 = (FStar_List.map hash_of_term es)
in (FStar_All.pipe_right uu____1798 (FStar_String.concat " ")))
in (

let uu____1803 = (

let uu____1804 = (

let uu____1805 = (hash_of_term body)
in (Prims.strcat uu____1805 ")"))
in (Prims.strcat ") " uu____1804))
in (Prims.strcat uu____1797 uu____1803)))
in (Prims.strcat "(let (" uu____1796))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mkBoxFunctions : Prims.string  ->  (Prims.string * Prims.string) = (fun s -> ((s), ((Prims.strcat s "_proj_0"))))


let boxIntFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxInt")


let boxBoolFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxBool")


let boxStringFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxString")


let boxBitVecFun : Prims.int  ->  (Prims.string * Prims.string) = (fun sz -> (

let uu____1835 = (

let uu____1836 = (FStar_Util.string_of_int sz)
in (Prims.strcat "BoxBitVec" uu____1836))
in (mkBoxFunctions uu____1835)))


let isInjective : Prims.string  ->  Prims.bool = (fun s -> (match (((FStar_String.length s) >= (Prims.parse_int "3"))) with
| true -> begin
((

let uu____1843 = (FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3"))
in (Prims.op_Equality uu____1843 "Box")) && (

let uu____1845 = (

let uu____1846 = (FStar_String.list_of_string s)
in (FStar_List.existsML (fun c -> (Prims.op_Equality c 46 (*.*))) uu____1846))
in (not (uu____1845))))
end
| uu____1851 -> begin
false
end))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (

let uu____1860 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {tm = t; freevars = uu____1860; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((TrueOp), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((FalseOp), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____1917 = (

let uu____1918 = (FStar_Util.ensure_decimal i)
in Integer (uu____1918))
in (mk uu____1917 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____1927 = (FStar_Util.string_of_int i)
in (mkInteger uu____1927 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun uu____1984 r -> (match (uu____1984) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (TrueOp, uu____2008) -> begin
(mkFalse r)
end
| App (FalseOp, uu____2013) -> begin
(mkTrue r)
end
| uu____2018 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____2031 r -> (match (uu____2031) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____2039), uu____2040) -> begin
t2
end
| (uu____2045, App (TrueOp, uu____2046)) -> begin
t1
end
| (App (FalseOp, uu____2051), uu____2052) -> begin
(mkFalse r)
end
| (uu____2057, App (FalseOp, uu____2058)) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (uu____2075, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), uu____2084) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____2091 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____2108 r -> (match (uu____2108) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____2116), uu____2117) -> begin
(mkTrue r)
end
| (uu____2122, App (TrueOp, uu____2123)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____2128), uu____2129) -> begin
t2
end
| (uu____2134, App (FalseOp, uu____2135)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (uu____2152, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), uu____2161) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____2168 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____2185 r -> (match (uu____2185) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (uu____2193, App (TrueOp, uu____2194)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____2199), uu____2200) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____2205), uu____2206) -> begin
t2
end
| (uu____2211, App (Imp, (t1')::(t2')::[])) -> begin
(

let uu____2216 = (

let uu____2223 = (

let uu____2226 = (mkAnd ((t1), (t1')) r)
in (uu____2226)::(t2')::[])
in ((Imp), (uu____2223)))
in (mkApp' uu____2216 r))
end
| uu____2229 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op uu____2250 r -> (match (uu____2250) with
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


let mkBvShl : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2352 r -> (match (uu____2352) with
| (t1, t2) -> begin
(

let uu____2360 = (

let uu____2367 = (

let uu____2370 = (

let uu____2373 = (mkNatToBv sz t2 r)
in (uu____2373)::[])
in (t1)::uu____2370)
in ((BvShl), (uu____2367)))
in (mkApp' uu____2360 r))
end))


let mkBvShr : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2390 r -> (match (uu____2390) with
| (t1, t2) -> begin
(

let uu____2398 = (

let uu____2405 = (

let uu____2408 = (

let uu____2411 = (mkNatToBv sz t2 r)
in (uu____2411)::[])
in (t1)::uu____2408)
in ((BvShr), (uu____2405)))
in (mkApp' uu____2398 r))
end))


let mkBvUdiv : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2428 r -> (match (uu____2428) with
| (t1, t2) -> begin
(

let uu____2436 = (

let uu____2443 = (

let uu____2446 = (

let uu____2449 = (mkNatToBv sz t2 r)
in (uu____2449)::[])
in (t1)::uu____2446)
in ((BvUdiv), (uu____2443)))
in (mkApp' uu____2436 r))
end))


let mkBvMod : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2466 r -> (match (uu____2466) with
| (t1, t2) -> begin
(

let uu____2474 = (

let uu____2481 = (

let uu____2484 = (

let uu____2487 = (mkNatToBv sz t2 r)
in (uu____2487)::[])
in (t1)::uu____2484)
in ((BvMod), (uu____2481)))
in (mkApp' uu____2474 r))
end))


let mkBvMul : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2504 r -> (match (uu____2504) with
| (t1, t2) -> begin
(

let uu____2512 = (

let uu____2519 = (

let uu____2522 = (

let uu____2525 = (mkNatToBv sz t2 r)
in (uu____2525)::[])
in (t1)::uu____2522)
in ((BvMul), (uu____2519)))
in (mkApp' uu____2512 r))
end))


let mkBvUlt : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvUlt)


let mkIff : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Iff)


let mkEq : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____2558 r -> (match (uu____2558) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (Var (f1), (s1)::[]), App (Var (f2), (s2)::[])) when ((Prims.op_Equality f1 f2) && (isInjective f1)) -> begin
(mk_bin_op Eq ((s1), (s2)) r)
end
| uu____2574 -> begin
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


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun uu____2681 r -> (match (uu____2681) with
| (t1, t2, t3) -> begin
(match (t1.tm) with
| App (TrueOp, uu____2692) -> begin
t2
end
| App (FalseOp, uu____2697) -> begin
t3
end
| uu____2702 -> begin
(match (((t2.tm), (t3.tm))) with
| (App (TrueOp, uu____2703), App (TrueOp, uu____2704)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____2713), uu____2714) -> begin
(

let uu____2719 = (

let uu____2724 = (mkNot t1 t1.rng)
in ((uu____2724), (t3)))
in (mkImp uu____2719 r))
end
| (uu____2725, App (TrueOp, uu____2726)) -> begin
(mkImp ((t1), (t2)) r)
end
| (uu____2731, uu____2732) -> begin
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


let mkQuant : (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____2779 r -> (match (uu____2779) with
| (qop, pats, wopt, vars, body) -> begin
(match ((Prims.op_Equality (FStar_List.length vars) (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____2820 -> begin
(match (body.tm) with
| App (TrueOp, uu____2821) -> begin
body
end
| uu____2826 -> begin
(mk (Quant (((qop), (pats), (wopt), (vars), (body)))) r)
end)
end)
end))


let mkLet : (term Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____2847 r -> (match (uu____2847) with
| (es, body) -> begin
(match ((Prims.op_Equality (FStar_List.length es) (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____2861 -> begin
(mk (Let (((es), (body)))) r)
end)
end))


let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (

let nvars = (FStar_List.length fvs)
in (

let index_of = (fun fv -> (

let uu____2883 = (FStar_Util.try_find_index (fv_eq fv) fvs)
in (match (uu____2883) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((nvars - (i + (Prims.parse_int "1"))))
end)))
in (

let rec aux = (fun ix t1 -> (

let uu____2902 = (FStar_ST.op_Bang t1.freevars)
in (match (uu____2902) with
| FStar_Pervasives_Native.Some ([]) -> begin
t1
end
| uu____2983 -> begin
(match (t1.tm) with
| Integer (uu____2992) -> begin
t1
end
| BoundV (uu____2993) -> begin
t1
end
| FreeV (x) -> begin
(

let uu____2999 = (index_of x)
in (match (uu____2999) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (i) -> begin
(mkBoundV (i + ix) t1.rng)
end))
end
| App (op, tms) -> begin
(

let uu____3009 = (

let uu____3016 = (FStar_List.map (aux ix) tms)
in ((op), (uu____3016)))
in (mkApp' uu____3009 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____3024 = (

let uu____3025 = (

let uu____3032 = (aux ix t2)
in ((uu____3032), (r1), (r2)))
in Labeled (uu____3025))
in (mk uu____3024 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____3035 = (

let uu____3036 = (

let uu____3041 = (aux ix t2)
in ((uu____3041), (r)))
in LblPos (uu____3036))
in (mk uu____3035 t2.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n1 = (FStar_List.length vars)
in (

let uu____3064 = (

let uu____3083 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n1)))))
in (

let uu____3104 = (aux (ix + n1) body)
in ((qop), (uu____3083), (wopt), (vars), (uu____3104))))
in (mkQuant uu____3064 t1.rng)))
end
| Let (es, body) -> begin
(

let uu____3123 = (FStar_List.fold_left (fun uu____3141 e -> (match (uu____3141) with
| (ix1, l) -> begin
(

let uu____3161 = (

let uu____3164 = (aux ix1 e)
in (uu____3164)::l)
in (((ix1 + (Prims.parse_int "1"))), (uu____3161)))
end)) ((ix), ([])) es)
in (match (uu____3123) with
| (ix1, es_rev) -> begin
(

let uu____3175 = (

let uu____3182 = (aux ix1 body)
in (((FStar_List.rev es_rev)), (uu____3182)))
in (mkLet uu____3175 t1.rng))
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
| Integer (uu____3208) -> begin
t1
end
| FreeV (uu____3209) -> begin
t1
end
| BoundV (i) -> begin
(match ((((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1))) with
| true -> begin
(FStar_List.nth tms1 (i - shift))
end
| uu____3219 -> begin
t1
end)
end
| App (op, tms2) -> begin
(

let uu____3226 = (

let uu____3233 = (FStar_List.map (aux shift) tms2)
in ((op), (uu____3233)))
in (mkApp' uu____3226 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____3241 = (

let uu____3242 = (

let uu____3249 = (aux shift t2)
in ((uu____3249), (r1), (r2)))
in Labeled (uu____3242))
in (mk uu____3241 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____3252 = (

let uu____3253 = (

let uu____3258 = (aux shift t2)
in ((uu____3258), (r)))
in LblPos (uu____3253))
in (mk uu____3252 t2.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift1 = (shift + m)
in (

let uu____3286 = (

let uu____3305 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift1))))
in (

let uu____3322 = (aux shift1 body)
in ((qop), (uu____3305), (wopt), (vars), (uu____3322))))
in (mkQuant uu____3286 t1.rng))))
end
| Let (es, body) -> begin
(

let uu____3337 = (FStar_List.fold_left (fun uu____3355 e -> (match (uu____3355) with
| (ix, es1) -> begin
(

let uu____3375 = (

let uu____3378 = (aux shift e)
in (uu____3378)::es1)
in (((shift + (Prims.parse_int "1"))), (uu____3375)))
end)) ((shift), ([])) es)
in (match (uu____3337) with
| (shift1, es_rev) -> begin
(

let uu____3389 = (

let uu____3396 = (aux shift1 body)
in (((FStar_List.rev es_rev)), (uu____3396)))
in (mkLet uu____3389 t1.rng))
end))
end))
in (aux (Prims.parse_int "0") t)))))


let subst : term  ->  fv  ->  term  ->  term = (fun t fv s -> (

let uu____3411 = (abstr ((fv)::[]) t)
in (inst ((s)::[]) uu____3411)))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fv Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____3435 -> (match (uu____3435) with
| (qop, pats, wopt, vars, body) -> begin
(

let uu____3477 = (

let uu____3496 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (

let uu____3513 = (FStar_List.map fv_sort vars)
in (

let uu____3520 = (abstr vars body)
in ((qop), (uu____3496), (wopt), (uu____3513), (uu____3520)))))
in (mkQuant uu____3477))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____3551 r -> (match (uu____3551) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)) r)
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____3617 r -> (match (uu____3617) with
| (pats, wopt, vars, body) -> begin
(

let uu____3649 = (mkQuant' ((Forall), (pats), (wopt), (vars), (body)))
in (uu____3649 r))
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____3674 r -> (match (uu____3674) with
| (pats, vars, body) -> begin
(

let uu____3697 = (mkQuant' ((Forall), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
in (uu____3697 r))
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____3722 r -> (match (uu____3722) with
| (pats, vars, body) -> begin
(

let uu____3745 = (mkQuant' ((Exists), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
in (uu____3745 r))
end))


let mkLet' : ((fv * term) Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____3770 r -> (match (uu____3770) with
| (bindings, body) -> begin
(

let uu____3796 = (FStar_List.split bindings)
in (match (uu____3796) with
| (vars, es) -> begin
(

let uu____3815 = (

let uu____3822 = (abstr vars body)
in ((es), (uu____3822)))
in (mkLet uu____3815 r))
end))
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun uu____3844 -> (match (uu____3844) with
| (nm, vars, s, tm, c) -> begin
(

let uu____3878 = (

let uu____3891 = (FStar_List.map fv_sort vars)
in (

let uu____3898 = (abstr vars tm)
in ((nm), (uu____3891), (s), (uu____3898), (c))))
in DefineFun (uu____3878))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (

let uu____3905 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" uu____3905)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun uu____3916 id -> (match (uu____3916) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (

let a = (

let uu____3926 = (

let uu____3927 = (

let uu____3932 = (mkInteger' id norng)
in (

let uu____3933 = (

let uu____3934 = (

let uu____3941 = (constr_id_of_sort sort)
in (

let uu____3942 = (

let uu____3945 = (mkApp ((tok_name), ([])) norng)
in (uu____3945)::[])
in ((uu____3941), (uu____3942))))
in (mkApp uu____3934 norng))
in ((uu____3932), (uu____3933))))
in (mkEq uu____3927 norng))
in {assumption_term = uu____3926; assumption_caption = FStar_Pervasives_Native.Some ("fresh token"); assumption_name = a_name; assumption_fact_ids = []})
in Assume (a)))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun uu____3963 -> (match (uu____3963) with
| (name, arg_sorts, sort, id) -> begin
(

let id1 = (FStar_Util.string_of_int id)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (

let uu____3995 = (

let uu____4000 = (

let uu____4001 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____4001))
in ((uu____4000), (s)))
in (mkFreeV uu____3995 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (

let uu____4009 = (

let uu____4016 = (constr_id_of_sort sort)
in ((uu____4016), ((capp)::[])))
in (mkApp uu____4009 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (

let a = (

let uu____4021 = (

let uu____4022 = (

let uu____4033 = (

let uu____4034 = (

let uu____4039 = (mkInteger id1 norng)
in ((uu____4039), (cid_app)))
in (mkEq uu____4034 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____4033)))
in (mkForall uu____4022 norng))
in {assumption_term = uu____4021; assumption_caption = FStar_Pervasives_Native.Some ("Consrtructor distinct"); assumption_name = a_name; assumption_fact_ids = []})
in Assume (a))))))))
end))


let injective_constructor : (Prims.string * constructor_field Prims.list * sort)  ->  decls_t = (fun uu____4061 -> (match (uu____4061) with
| (name, fields, sort) -> begin
(

let n_bvars = (FStar_List.length fields)
in (

let bvar_name = (fun i -> (

let uu____4082 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____4082)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (

let uu____4102 = (

let uu____4107 = (bvar_name i)
in ((uu____4107), (s)))
in (mkFreeV uu____4102)))
in (

let bvars = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____4128 -> (match (uu____4128) with
| (uu____4135, s, uu____4137) -> begin
(

let uu____4138 = (bvar i s)
in (uu____4138 norng))
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let uu____4147 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____4175 -> (match (uu____4175) with
| (name1, s, projectible) -> begin
(

let cproj_app = (mkApp ((name1), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((name1), ((sort)::[]), (s), (FStar_Pervasives_Native.Some ("Projector"))))
in (match (projectible) with
| true -> begin
(

let a = (

let uu____4198 = (

let uu____4199 = (

let uu____4210 = (

let uu____4211 = (

let uu____4216 = (

let uu____4217 = (bvar i s)
in (uu____4217 norng))
in ((cproj_app), (uu____4216)))
in (mkEq uu____4211 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____4210)))
in (mkForall uu____4199 norng))
in {assumption_term = uu____4198; assumption_caption = FStar_Pervasives_Native.Some ("Projection inverse"); assumption_name = (Prims.strcat "projection_inverse_" name1); assumption_fact_ids = []})
in (proj_name)::(Assume (a))::[])
end
| uu____4230 -> begin
(proj_name)::[]
end)))
end))))
in (FStar_All.pipe_right uu____4147 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun uu____4240 -> (match (uu____4240) with
| (name, fields, sort, id, injective) -> begin
(

let injective1 = (injective || true)
in (

let field_sorts = (FStar_All.pipe_right fields (FStar_List.map (fun uu____4268 -> (match (uu____4268) with
| (uu____4275, sort1, uu____4277) -> begin
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

let uu____4295 = (

let uu____4300 = (

let uu____4301 = (

let uu____4308 = (constr_id_of_sort sort)
in ((uu____4308), ((xx)::[])))
in (mkApp uu____4301 norng))
in (

let uu____4311 = (

let uu____4312 = (FStar_Util.string_of_int id)
in (mkInteger uu____4312 norng))
in ((uu____4300), (uu____4311))))
in (mkEq uu____4295 norng))
in (

let uu____4313 = (

let uu____4328 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____4378 -> (match (uu____4378) with
| (proj, s, projectible) -> begin
(match (projectible) with
| true -> begin
(

let uu____4408 = (mkApp ((proj), ((xx)::[])) norng)
in ((uu____4408), ([])))
end
| uu____4421 -> begin
(

let fi = (

let uu____4427 = (

let uu____4428 = (FStar_Util.string_of_int i)
in (Prims.strcat "f_" uu____4428))
in ((uu____4427), (s)))
in (

let uu____4429 = (mkFreeV fi norng)
in ((uu____4429), ((fi)::[]))))
end)
end))))
in (FStar_All.pipe_right uu____4328 FStar_List.split))
in (match (uu____4313) with
| (proj_terms, ex_vars) -> begin
(

let ex_vars1 = (FStar_List.flatten ex_vars)
in (

let disc_inv_body = (

let uu____4510 = (

let uu____4515 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (uu____4515)))
in (mkEq uu____4510 norng))
in (

let disc_inv_body1 = (match (ex_vars1) with
| [] -> begin
disc_inv_body
end
| uu____4523 -> begin
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
| uu____4563 -> begin
[]
end)
in (

let uu____4564 = (

let uu____4567 = (

let uu____4568 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (uu____4568))
in (uu____4567)::(cdecl)::(cid)::projs)
in (

let uu____4569 = (

let uu____4572 = (

let uu____4575 = (

let uu____4576 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (uu____4576))
in (uu____4575)::[])
in (FStar_List.append ((disc)::[]) uu____4572))
in (FStar_List.append uu____4564 uu____4569)))))))))
end))


let name_binders_inner : Prims.string FStar_Pervasives_Native.option  ->  (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun prefix_opt outer_names start sorts -> (

let uu____4627 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun uu____4682 s -> (match (uu____4682) with
| (names1, binders, n1) -> begin
(

let prefix1 = (match (s) with
| Term_sort -> begin
"@x"
end
| uu____4732 -> begin
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

let uu____4736 = (FStar_Util.string_of_int n1)
in (Prims.strcat prefix2 uu____4736))
in (

let names2 = (((nm), (s)))::names1
in (

let b = (

let uu____4749 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm uu____4749))
in ((names2), ((b)::binders), ((n1 + (Prims.parse_int "1")))))))))
end)) ((outer_names), ([]), (start))))
in (match (uu____4627) with
| (names1, binders, n1) -> begin
((names1), ((FStar_List.rev binders)), (n1))
end)))


let name_macro_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let uu____4827 = (name_binders_inner (FStar_Pervasives_Native.Some ("__")) [] (Prims.parse_int "0") sorts)
in (match (uu____4827) with
| (names1, binders, n1) -> begin
(((FStar_List.rev names1)), (binders))
end)))


let termToSmt : Prims.string  ->  term  ->  Prims.string = (fun enclosing_name t -> (

let next_qid = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun depth -> (

let n1 = (FStar_ST.op_Bang ctr)
in ((FStar_Util.incr ctr);
(match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
enclosing_name
end
| uu____4987 -> begin
(

let uu____4988 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "%s.%s" enclosing_name uu____4988))
end);
))))
in (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (uu____5030); freevars = uu____5031; rng = uu____5032})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| uu____5046 -> begin
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

let uu____5086 = (FStar_List.nth names1 i)
in (FStar_All.pipe_right uu____5086 FStar_Pervasives_Native.fst))
end
| FreeV (x) -> begin
(FStar_Pervasives_Native.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(

let uu____5101 = (op_to_string op)
in (

let uu____5102 = (

let uu____5103 = (FStar_List.map (aux1 n1 names1) tms)
in (FStar_All.pipe_right uu____5103 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" uu____5101 uu____5102)))
end
| Labeled (t2, uu____5109, uu____5110) -> begin
(aux1 n1 names1 t2)
end
| LblPos (t2, s) -> begin
(

let uu____5113 = (aux1 n1 names1 t2)
in (FStar_Util.format2 "(! %s :lblpos %s)" uu____5113 s))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let qid = (next_qid ())
in (

let uu____5136 = (name_binders_inner FStar_Pervasives_Native.None names1 n1 sorts)
in (match (uu____5136) with
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
| uu____5185 -> begin
(

let uu____5190 = (FStar_All.pipe_right pats1 (FStar_List.map (fun pats2 -> (

let uu____5206 = (

let uu____5207 = (FStar_List.map (fun p -> (

let uu____5213 = (aux1 n2 names2 p)
in (FStar_Util.format1 "%s" uu____5213))) pats2)
in (FStar_String.concat " " uu____5207))
in (FStar_Util.format1 "\n:pattern (%s)" uu____5206)))))
in (FStar_All.pipe_right uu____5190 (FStar_String.concat "\n")))
end)
in (

let uu____5216 = (

let uu____5219 = (

let uu____5222 = (

let uu____5225 = (aux1 n2 names2 body)
in (

let uu____5226 = (

let uu____5229 = (weightToSmt wopt)
in (uu____5229)::(pats_str)::(qid)::[])
in (uu____5225)::uu____5226))
in (binders1)::uu____5222)
in ((qop_to_string qop))::uu____5219)
in (FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))" uu____5216)))))
end)))
end
| Let (es, body) -> begin
(

let uu____5236 = (FStar_List.fold_left (fun uu____5273 e -> (match (uu____5273) with
| (names0, binders, n0) -> begin
(

let nm = (

let uu____5323 = (FStar_Util.string_of_int n0)
in (Prims.strcat "@lb" uu____5323))
in (

let names01 = (((nm), (Term_sort)))::names0
in (

let b = (

let uu____5336 = (aux1 n1 names1 e)
in (FStar_Util.format2 "(%s %s)" nm uu____5336))
in ((names01), ((b)::binders), ((n0 + (Prims.parse_int "1")))))))
end)) ((names1), ([]), (n1)) es)
in (match (uu____5236) with
| (names2, binders, n2) -> begin
(

let uu____5368 = (aux1 n2 names2 body)
in (FStar_Util.format2 "(let (%s)\n%s)" (FStar_String.concat " " binders) uu____5368))
end))
end)))
and aux = (fun depth n1 names1 t1 -> (

let s = (aux' depth n1 names1 t1)
in (match ((Prims.op_disEquality t1.rng norng)) with
| true -> begin
(

let uu____5376 = (FStar_Range.string_of_range t1.rng)
in (

let uu____5377 = (FStar_Range.string_of_use_range t1.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____5376 uu____5377 s)))
end
| uu____5378 -> begin
s
end)))
in (aux (Prims.parse_int "0") (Prims.parse_int "0") [] t)))))


let caption_to_string : Prims.string FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___92_5384 -> (match (uu___92_5384) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let uu____5388 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(failwith "Impossible")
end
| (hd1)::[] -> begin
((hd1), (""))
end
| (hd1)::uu____5403 -> begin
((hd1), ("..."))
end)
in (match (uu____5388) with
| (hd1, suffix) -> begin
(FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
end))
end))


let rec declToSmt : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (

let escape = (fun s -> (FStar_Util.replace_char s 39 (*'*) 95 (*_*)))
in (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(

let uu____5421 = (FStar_Options.log_queries ())
in (match (uu____5421) with
| true -> begin
(

let uu____5422 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun uu___93_5426 -> (match (uu___93_5426) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" uu____5422))
end
| uu____5433 -> begin
""
end))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (

let uu____5445 = (caption_to_string c)
in (

let uu____5446 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____5445 f (FStar_String.concat " " l) uu____5446))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let uu____5456 = (name_macro_binders arg_sorts)
in (match (uu____5456) with
| (names1, binders) -> begin
(

let body1 = (

let uu____5488 = (FStar_List.map (fun x -> (mkFreeV x norng)) names1)
in (inst uu____5488 body))
in (

let uu____5501 = (caption_to_string c)
in (

let uu____5502 = (strSort retsort)
in (

let uu____5503 = (termToSmt (escape f) body1)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____5501 f (FStar_String.concat " " binders) uu____5502 uu____5503)))))
end))
end
| Assume (a) -> begin
(

let fact_ids_to_string = (fun ids -> (FStar_All.pipe_right ids (FStar_List.map (fun uu___94_5521 -> (match (uu___94_5521) with
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

let uu____5526 = (FStar_Options.log_queries ())
in (match (uu____5526) with
| true -> begin
(

let uu____5527 = (

let uu____5528 = (fact_ids_to_string a.assumption_fact_ids)
in (FStar_String.concat "; " uu____5528))
in (FStar_Util.format1 ";;; Fact-ids: %s\n" uu____5527))
end
| uu____5531 -> begin
""
end))
in (

let n1 = (escape a.assumption_name)
in (

let uu____5533 = (caption_to_string a.assumption_caption)
in (

let uu____5534 = (termToSmt n1 a.assumption_term)
in (FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____5533 fids uu____5534 n1))))))
end
| Eval (t) -> begin
(

let uu____5536 = (termToSmt "eval" t)
in (FStar_Util.format1 "(eval %s)" uu____5536))
end
| Echo (s) -> begin
(FStar_Util.format1 "(echo \"%s\")" s)
end
| RetainAssumptions (uu____5538) -> begin
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
and mkPrelude : Prims.string  ->  Prims.string = (fun z3options -> (

let basic = (Prims.strcat z3options "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))")
in (

let constrs = ((("FString_const"), (((("FString_const_proj_0"), (Int_sort), (true)))::[]), (String_sort), ((Prims.parse_int "0")), (true)))::((("Tm_type"), ([]), (Term_sort), ((Prims.parse_int "2")), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "3")), (false)))::((("Tm_unit"), ([]), (Term_sort), ((Prims.parse_int "6")), (true)))::((((FStar_Pervasives_Native.fst boxIntFun)), (((((FStar_Pervasives_Native.snd boxIntFun)), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "7")), (true)))::((((FStar_Pervasives_Native.fst boxBoolFun)), (((((FStar_Pervasives_Native.snd boxBoolFun)), (Bool_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "8")), (true)))::((((FStar_Pervasives_Native.fst boxStringFun)), (((((FStar_Pervasives_Native.snd boxStringFun)), (String_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "9")), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort), (true)))::((("LexCons_1"), (Term_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "11")), (true)))::[]
in (

let bcons = (

let uu____5863 = (

let uu____5866 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right uu____5866 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right uu____5863 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mkBvConstructor : Prims.int  ->  decls_t = (fun sz -> (

let uu____5882 = (

let uu____5901 = (

let uu____5902 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____5902))
in (

let uu____5907 = (

let uu____5916 = (

let uu____5923 = (

let uu____5924 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____5924))
in ((uu____5923), (BitVec_sort (sz)), (true)))
in (uu____5916)::[])
in ((uu____5901), (uu____5907), (Term_sort), (((Prims.parse_int "12") + sz)), (true))))
in (FStar_All.pipe_right uu____5882 constructor_to_decl)))


let mk_Range_const : term = (mkApp (("Range_const"), ([])) norng)


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____5993 = (

let uu____6000 = (

let uu____6003 = (mkInteger' i norng)
in (uu____6003)::[])
in (("Tm_uvar"), (uu____6000)))
in (mkApp uu____5993 r)))


let mk_Term_unit : term = (mkApp (("Tm_unit"), ([])) norng)


let elim_box : Prims.bool  ->  Prims.string  ->  Prims.string  ->  term  ->  term = (fun cond u v1 t -> (match (t.tm) with
| App (Var (v'), (t1)::[]) when ((Prims.op_Equality v1 v') && cond) -> begin
t1
end
| uu____6028 -> begin
(mkApp ((u), ((t)::[])) t.rng)
end))


let maybe_elim_box : Prims.string  ->  Prims.string  ->  term  ->  term = (fun u v1 t -> (

let uu____6043 = (FStar_Options.smtencoding_elim_box ())
in (elim_box uu____6043 u v1 t)))


let boxInt : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxIntFun) (FStar_Pervasives_Native.snd boxIntFun) t))


let unboxInt : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxIntFun) (FStar_Pervasives_Native.fst boxIntFun) t))


let boxBool : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxBoolFun) (FStar_Pervasives_Native.snd boxBoolFun) t))


let unboxBool : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxBoolFun) (FStar_Pervasives_Native.fst boxBoolFun) t))


let boxString : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxStringFun) (FStar_Pervasives_Native.snd boxStringFun) t))


let unboxString : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxStringFun) (FStar_Pervasives_Native.fst boxStringFun) t))


let boxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let uu____6076 = (

let uu____6077 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____6077))
in (

let uu____6082 = (

let uu____6083 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____6083))
in (elim_box true uu____6076 uu____6082 t))))


let unboxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let uu____6096 = (

let uu____6097 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____6097))
in (

let uu____6102 = (

let uu____6103 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____6103))
in (elim_box true uu____6096 uu____6102 t))))


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
| uu____6117 -> begin
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
| uu____6127 -> begin
(FStar_Exn.raise FStar_Util.Impos)
end))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n1) -> begin
(FStar_Util.format1 "(Integer %s)" n1)
end
| BoundV (n1) -> begin
(

let uu____6143 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(BoundV %s)" uu____6143))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv))
end
| App (op, l) -> begin
(

let uu____6155 = (op_to_string op)
in (

let uu____6156 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" uu____6155 uu____6156)))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____6160 = (print_smt_term t1)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 uu____6160))
end
| LblPos (t1, s) -> begin
(

let uu____6163 = (print_smt_term t1)
in (FStar_Util.format2 "(LblPos %s %s)" s uu____6163))
end
| Quant (qop, l, uu____6166, uu____6167, t1) -> begin
(

let uu____6185 = (print_smt_term_list_list l)
in (

let uu____6186 = (print_smt_term t1)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____6185 uu____6186)))
end
| Let (es, body) -> begin
(

let uu____6193 = (print_smt_term_list es)
in (

let uu____6194 = (print_smt_term body)
in (FStar_Util.format2 "(let %s %s)" uu____6193 uu____6194)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (

let uu____6198 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right uu____6198 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l1 -> (

let uu____6217 = (

let uu____6218 = (

let uu____6219 = (print_smt_term_list l1)
in (Prims.strcat uu____6219 " ] "))
in (Prims.strcat "; [ " uu____6218))
in (Prims.strcat s uu____6217))) "" l))


let getBoxedInteger : term  ->  Prims.int FStar_Pervasives_Native.option = (fun t -> (match (t.tm) with
| App (Var (s), (t2)::[]) when (Prims.op_Equality s (FStar_Pervasives_Native.fst boxIntFun)) -> begin
(match (t2.tm) with
| Integer (n1) -> begin
(

let uu____6235 = (FStar_Util.int_of_string n1)
in FStar_Pervasives_Native.Some (uu____6235))
end
| uu____6236 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____6237 -> begin
FStar_Pervasives_Native.None
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (uu____6248)::(t1)::(t2)::[]); freevars = uu____6251; rng = uu____6252})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (uu____6265)::(t1)::(t2)::[]); freevars = uu____6268; rng = uu____6269})::[]) -> begin
(

let uu____6282 = (mkEq ((t1), (t2)) norng)
in (mkNot uu____6282 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = uu____6285; rng = uu____6286})::[]) -> begin
(

let uu____6299 = (

let uu____6304 = (unboxInt t1)
in (

let uu____6305 = (unboxInt t2)
in ((uu____6304), (uu____6305))))
in (mkLTE uu____6299 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = uu____6308; rng = uu____6309})::[]) -> begin
(

let uu____6322 = (

let uu____6327 = (unboxInt t1)
in (

let uu____6328 = (unboxInt t2)
in ((uu____6327), (uu____6328))))
in (mkLT uu____6322 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = uu____6331; rng = uu____6332})::[]) -> begin
(

let uu____6345 = (

let uu____6350 = (unboxInt t1)
in (

let uu____6351 = (unboxInt t2)
in ((uu____6350), (uu____6351))))
in (mkGTE uu____6345 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = uu____6354; rng = uu____6355})::[]) -> begin
(

let uu____6368 = (

let uu____6373 = (unboxInt t1)
in (

let uu____6374 = (unboxInt t2)
in ((uu____6373), (uu____6374))))
in (mkGT uu____6368 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = uu____6377; rng = uu____6378})::[]) -> begin
(

let uu____6391 = (

let uu____6396 = (unboxBool t1)
in (

let uu____6397 = (unboxBool t2)
in ((uu____6396), (uu____6397))))
in (mkAnd uu____6391 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = uu____6400; rng = uu____6401})::[]) -> begin
(

let uu____6414 = (

let uu____6419 = (unboxBool t1)
in (

let uu____6420 = (unboxBool t2)
in ((uu____6419), (uu____6420))))
in (mkOr uu____6414 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t1)::[]); freevars = uu____6422; rng = uu____6423})::[]) -> begin
(

let uu____6436 = (unboxBool t1)
in (mkNot uu____6436 t1.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("FStar.BV.bvult"), (t0)::(t1)::(t2)::[]); freevars = uu____6440; rng = uu____6441})::[]) when (

let uu____6454 = (getBoxedInteger t0)
in (FStar_Util.is_some uu____6454)) -> begin
(

let sz = (

let uu____6458 = (getBoxedInteger t0)
in (match (uu____6458) with
| FStar_Pervasives_Native.Some (sz) -> begin
sz
end
| uu____6462 -> begin
(failwith "impossible")
end))
in (

let uu____6465 = (

let uu____6470 = (unboxBitVec sz t1)
in (

let uu____6471 = (unboxBitVec sz t2)
in ((uu____6470), (uu____6471))))
in (mkBvUlt uu____6465 t.rng)))
end
| App (Var ("Prims.equals"), (uu____6472)::({tm = App (Var ("FStar.BV.bvult"), (t0)::(t1)::(t2)::[]); freevars = uu____6476; rng = uu____6477})::(uu____6478)::[]) when (

let uu____6491 = (getBoxedInteger t0)
in (FStar_Util.is_some uu____6491)) -> begin
(

let sz = (

let uu____6495 = (getBoxedInteger t0)
in (match (uu____6495) with
| FStar_Pervasives_Native.Some (sz) -> begin
sz
end
| uu____6499 -> begin
(failwith "impossible")
end))
in (

let uu____6502 = (

let uu____6507 = (unboxBitVec sz t1)
in (

let uu____6508 = (unboxBitVec sz t2)
in ((uu____6507), (uu____6508))))
in (mkBvUlt uu____6502 t.rng)))
end
| App (Var ("Prims.b2t"), (t1)::[]) -> begin
(

let uu___95_6512 = (unboxBool t1)
in {tm = uu___95_6512.tm; freevars = uu___95_6512.freevars; rng = t.rng})
end
| uu____6513 -> begin
(mkApp (("Valid"), ((t)::[])) t.rng)
end))


let mk_HasType : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasType"), ((v1)::(t)::[])) t.rng))


let mk_HasTypeZ : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasTypeZ"), ((v1)::(t)::[])) t.rng))


let mk_IsTyped : term  ->  term = (fun v1 -> (mkApp (("IsTyped"), ((v1)::[])) norng))


let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v1 t -> (

let uu____6554 = (FStar_Options.unthrottle_inductives ())
in (match (uu____6554) with
| true -> begin
(mk_HasType v1 t)
end
| uu____6555 -> begin
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

let uu____6645 = (

let uu____6652 = (

let uu____6655 = (mkInteger' i norng)
in (uu____6655)::[])
in (("FString_const"), (uu____6652)))
in (mkApp uu____6645 r)))


let mk_Precedes : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (

let uu____6670 = (mkApp (("Precedes"), ((x1)::(x2)::[])) r)
in (FStar_All.pipe_right uu____6670 mk_Valid)))


let mk_LexCons : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (mkApp (("LexCons"), ((x1)::(x2)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
(mkApp (("ZFuel"), ([])) norng)
end
| uu____6693 -> begin
(

let uu____6694 = (

let uu____6701 = (

let uu____6704 = (n_fuel (n1 - (Prims.parse_int "1")))
in (uu____6704)::[])
in (("SFuel"), (uu____6701)))
in (mkApp uu____6694 norng))
end))


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term FStar_Pervasives_Native.option  ->  term FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  term FStar_Pervasives_Native.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (FStar_Pervasives_Native.Some (p11), FStar_Pervasives_Native.Some (p21)) -> begin
(

let uu____6741 = (mkAnd ((p11), (p21)) r)
in FStar_Pervasives_Native.Some (uu____6741))
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

let uu____6798 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l uu____6798)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____6815 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l uu____6815)))


let mk_haseq : term  ->  term = (fun t -> (

let uu____6824 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid uu____6824)))




