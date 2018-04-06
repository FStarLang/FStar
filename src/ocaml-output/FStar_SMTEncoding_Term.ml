
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
| uu____28 -> begin
false
end))


let uu___is_Int_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int_sort -> begin
true
end
| uu____32 -> begin
false
end))


let uu___is_String_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| String_sort -> begin
true
end
| uu____36 -> begin
false
end))


let uu___is_Term_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Term_sort -> begin
true
end
| uu____40 -> begin
false
end))


let uu___is_Fuel_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fuel_sort -> begin
true
end
| uu____44 -> begin
false
end))


let uu___is_BitVec_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BitVec_sort (_0) -> begin
true
end
| uu____49 -> begin
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
| uu____65 -> begin
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
| uu____93 -> begin
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
| uu____117 -> begin
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

let uu____129 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ BitVec %s)" uu____129))
end
| Array (s1, s2) -> begin
(

let uu____132 = (strSort s1)
in (

let uu____133 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" uu____132 uu____133)))
end
| Arrow (s1, s2) -> begin
(

let uu____136 = (strSort s1)
in (

let uu____137 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" uu____136 uu____137)))
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
| uu____154 -> begin
false
end))


let uu___is_FalseOp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FalseOp -> begin
true
end
| uu____158 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____162 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____166 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____170 -> begin
false
end))


let uu___is_Imp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Imp -> begin
true
end
| uu____174 -> begin
false
end))


let uu___is_Iff : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iff -> begin
true
end
| uu____178 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____182 -> begin
false
end))


let uu___is_LT : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LT -> begin
true
end
| uu____186 -> begin
false
end))


let uu___is_LTE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LTE -> begin
true
end
| uu____190 -> begin
false
end))


let uu___is_GT : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GT -> begin
true
end
| uu____194 -> begin
false
end))


let uu___is_GTE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GTE -> begin
true
end
| uu____198 -> begin
false
end))


let uu___is_Add : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Add -> begin
true
end
| uu____202 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____206 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____210 -> begin
false
end))


let uu___is_Mul : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mul -> begin
true
end
| uu____214 -> begin
false
end))


let uu___is_Minus : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Minus -> begin
true
end
| uu____218 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____222 -> begin
false
end))


let uu___is_BvAnd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvAnd -> begin
true
end
| uu____226 -> begin
false
end))


let uu___is_BvXor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvXor -> begin
true
end
| uu____230 -> begin
false
end))


let uu___is_BvOr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvOr -> begin
true
end
| uu____234 -> begin
false
end))


let uu___is_BvAdd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvAdd -> begin
true
end
| uu____238 -> begin
false
end))


let uu___is_BvSub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvSub -> begin
true
end
| uu____242 -> begin
false
end))


let uu___is_BvShl : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvShl -> begin
true
end
| uu____246 -> begin
false
end))


let uu___is_BvShr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvShr -> begin
true
end
| uu____250 -> begin
false
end))


let uu___is_BvUdiv : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvUdiv -> begin
true
end
| uu____254 -> begin
false
end))


let uu___is_BvMod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvMod -> begin
true
end
| uu____258 -> begin
false
end))


let uu___is_BvMul : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvMul -> begin
true
end
| uu____262 -> begin
false
end))


let uu___is_BvUlt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvUlt -> begin
true
end
| uu____266 -> begin
false
end))


let uu___is_BvUext : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvUext (_0) -> begin
true
end
| uu____271 -> begin
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
| uu____283 -> begin
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
| uu____294 -> begin
false
end))


let uu___is_ITE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ITE -> begin
true
end
| uu____298 -> begin
false
end))


let uu___is_Var : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Var (_0) -> begin
true
end
| uu____303 -> begin
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
| uu____314 -> begin
false
end))


let uu___is_Exists : qop  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exists -> begin
true
end
| uu____318 -> begin
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
| uu____488 -> begin
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
| uu____500 -> begin
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
| uu____516 -> begin
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
| uu____546 -> begin
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
| uu____594 -> begin
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
| uu____666 -> begin
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
| uu____736 -> begin
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
| uu____973 -> begin
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
| uu____985 -> begin
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
| uu____997 -> begin
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
| uu____1126 -> begin
false
end))


let uu___is_DeclFun : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DeclFun (_0) -> begin
true
end
| uu____1141 -> begin
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
| uu____1195 -> begin
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
| uu____1243 -> begin
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
| uu____1255 -> begin
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
| uu____1267 -> begin
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
| uu____1279 -> begin
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
| uu____1293 -> begin
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
| uu____1310 -> begin
false
end))


let uu___is_Pop : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____1314 -> begin
false
end))


let uu___is_CheckSat : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckSat -> begin
true
end
| uu____1318 -> begin
false
end))


let uu___is_GetUnsatCore : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetUnsatCore -> begin
true
end
| uu____1322 -> begin
false
end))


let uu___is_SetOption : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOption (_0) -> begin
true
end
| uu____1331 -> begin
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
| uu____1354 -> begin
false
end))


let uu___is_GetReasonUnknown : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetReasonUnknown -> begin
true
end
| uu____1358 -> begin
false
end))


type decls_t =
decl Prims.list


type error_label =
(fv * Prims.string * FStar_Range.range)


type error_labels =
error_label Prims.list


let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> (Prims.op_Equality (FStar_Pervasives_Native.fst x) (FStar_Pervasives_Native.fst y)))


let fv_sort : 'Auu____1378 'Auu____1379 . ('Auu____1378 * 'Auu____1379)  ->  'Auu____1379 = (fun x -> (FStar_Pervasives_Native.snd x))


let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match (((x.tm), (y.tm))) with
| (FreeV (x1), FreeV (y1)) -> begin
(fv_eq x1 y1)
end
| uu____1408 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun uu___49_1415 -> (match (uu___49_1415) with
| {tm = FreeV (x); freevars = uu____1417; rng = uu____1418} -> begin
(fv_sort x)
end
| uu____1431 -> begin
(failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun uu___50_1434 -> (match (uu___50_1434) with
| {tm = FreeV (fv); freevars = uu____1436; rng = uu____1437} -> begin
fv
end
| uu____1450 -> begin
(failwith "impossible")
end))


let rec freevars : term  ->  (Prims.string * sort) Prims.list = (fun t -> (match (t.tm) with
| Integer (uu____1466) -> begin
[]
end
| BoundV (uu____1471) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (uu____1489, tms) -> begin
(FStar_List.collect freevars tms)
end
| Quant (uu____1499, uu____1500, uu____1501, uu____1502, t1) -> begin
(freevars t1)
end
| Labeled (t1, uu____1521, uu____1522) -> begin
(freevars t1)
end
| LblPos (t1, uu____1524) -> begin
(freevars t1)
end
| Let (es, body) -> begin
(FStar_List.collect freevars ((body)::es))
end))


let free_variables : term  ->  fvs = (fun t -> (

let uu____1538 = (FStar_ST.op_Bang t.freevars)
in (match (uu____1538) with
| FStar_Pervasives_Native.Some (b) -> begin
b
end
| FStar_Pervasives_Native.None -> begin
(

let fvs = (

let uu____1610 = (freevars t)
in (FStar_Util.remove_dups fv_eq uu____1610))
in ((FStar_ST.op_Colon_Equals t.freevars (FStar_Pervasives_Native.Some (fvs)));
fvs;
))
end)))


let qop_to_string : qop  ->  Prims.string = (fun uu___51_1659 -> (match (uu___51_1659) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun uu___52_1662 -> (match (uu___52_1662) with
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

let uu____1664 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ zero_extend %s)" uu____1664))
end
| NatToBv (n1) -> begin
(

let uu____1666 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ int2bv %s)" uu____1666))
end
| Var (s) -> begin
s
end))


let weightToSmt : Prims.int FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___53_1672 -> (match (uu___53_1672) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (i) -> begin
(

let uu____1676 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" uu____1676))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____1684 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" uu____1684))
end
| FreeV (x) -> begin
(

let uu____1690 = (

let uu____1691 = (strSort (FStar_Pervasives_Native.snd x))
in (Prims.strcat ":" uu____1691))
in (Prims.strcat (FStar_Pervasives_Native.fst x) uu____1690))
end
| App (op, tms) -> begin
(

let uu____1698 = (

let uu____1699 = (op_to_string op)
in (

let uu____1700 = (

let uu____1701 = (

let uu____1702 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right uu____1702 (FStar_String.concat " ")))
in (Prims.strcat uu____1701 ")"))
in (Prims.strcat uu____1699 uu____1700)))
in (Prims.strcat "(" uu____1698))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____1710 = (hash_of_term t1)
in (

let uu____1711 = (

let uu____1712 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 uu____1712))
in (Prims.strcat uu____1710 uu____1711)))
end
| LblPos (t1, r) -> begin
(

let uu____1715 = (

let uu____1716 = (hash_of_term t1)
in (Prims.strcat uu____1716 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " uu____1715))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let uu____1738 = (

let uu____1739 = (

let uu____1740 = (

let uu____1741 = (

let uu____1742 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right uu____1742 (FStar_String.concat " ")))
in (

let uu____1747 = (

let uu____1748 = (

let uu____1749 = (hash_of_term body)
in (

let uu____1750 = (

let uu____1751 = (

let uu____1752 = (weightToSmt wopt)
in (

let uu____1753 = (

let uu____1754 = (

let uu____1755 = (

let uu____1756 = (FStar_All.pipe_right pats (FStar_List.map (fun pats1 -> (

let uu____1772 = (FStar_List.map hash_of_term pats1)
in (FStar_All.pipe_right uu____1772 (FStar_String.concat " "))))))
in (FStar_All.pipe_right uu____1756 (FStar_String.concat "; ")))
in (Prims.strcat uu____1755 "))"))
in (Prims.strcat " " uu____1754))
in (Prims.strcat uu____1752 uu____1753)))
in (Prims.strcat " " uu____1751))
in (Prims.strcat uu____1749 uu____1750)))
in (Prims.strcat ")(! " uu____1748))
in (Prims.strcat uu____1741 uu____1747)))
in (Prims.strcat " (" uu____1740))
in (Prims.strcat (qop_to_string qop) uu____1739))
in (Prims.strcat "(" uu____1738))
end
| Let (es, body) -> begin
(

let uu____1785 = (

let uu____1786 = (

let uu____1787 = (FStar_List.map hash_of_term es)
in (FStar_All.pipe_right uu____1787 (FStar_String.concat " ")))
in (

let uu____1792 = (

let uu____1793 = (

let uu____1794 = (hash_of_term body)
in (Prims.strcat uu____1794 ")"))
in (Prims.strcat ") " uu____1793))
in (Prims.strcat uu____1786 uu____1792)))
in (Prims.strcat "(let (" uu____1785))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mkBoxFunctions : Prims.string  ->  (Prims.string * Prims.string) = (fun s -> ((s), ((Prims.strcat s "_proj_0"))))


let boxIntFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxInt")


let boxBoolFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxBool")


let boxStringFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxString")


let boxBitVecFun : Prims.int  ->  (Prims.string * Prims.string) = (fun sz -> (

let uu____1822 = (

let uu____1823 = (FStar_Util.string_of_int sz)
in (Prims.strcat "BoxBitVec" uu____1823))
in (mkBoxFunctions uu____1822)))


let isInjective : Prims.string  ->  Prims.bool = (fun s -> (match (((FStar_String.length s) >= (Prims.parse_int "3"))) with
| true -> begin
((

let uu____1829 = (FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3"))
in (Prims.op_Equality uu____1829 "Box")) && (

let uu____1831 = (

let uu____1832 = (FStar_String.list_of_string s)
in (FStar_List.existsML (fun c -> (Prims.op_Equality c 46 (*.*))) uu____1832))
in (not (uu____1831))))
end
| uu____1842 -> begin
false
end))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (

let uu____1849 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {tm = t; freevars = uu____1849; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((TrueOp), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((FalseOp), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____1958 = (

let uu____1959 = (FStar_Util.ensure_decimal i)
in Integer (uu____1959))
in (mk uu____1958 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____1966 = (FStar_Util.string_of_int i)
in (mkInteger uu____1966 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun uu____2015 r -> (match (uu____2015) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (TrueOp, uu____2037) -> begin
(mkFalse r)
end
| App (FalseOp, uu____2042) -> begin
(mkTrue r)
end
| uu____2047 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____2058 r -> (match (uu____2058) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____2066), uu____2067) -> begin
t2
end
| (uu____2072, App (TrueOp, uu____2073)) -> begin
t1
end
| (App (FalseOp, uu____2078), uu____2079) -> begin
(mkFalse r)
end
| (uu____2084, App (FalseOp, uu____2085)) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (uu____2102, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), uu____2111) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____2118 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____2133 r -> (match (uu____2133) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____2141), uu____2142) -> begin
(mkTrue r)
end
| (uu____2147, App (TrueOp, uu____2148)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____2153), uu____2154) -> begin
t2
end
| (uu____2159, App (FalseOp, uu____2160)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (uu____2177, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), uu____2186) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____2193 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____2208 r -> (match (uu____2208) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (uu____2216, App (TrueOp, uu____2217)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____2222), uu____2223) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____2228), uu____2229) -> begin
t2
end
| (uu____2234, App (Imp, (t1')::(t2')::[])) -> begin
(

let uu____2239 = (

let uu____2246 = (

let uu____2249 = (mkAnd ((t1), (t1')) r)
in (uu____2249)::(t2')::[])
in ((Imp), (uu____2246)))
in (mkApp' uu____2239 r))
end
| uu____2252 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op uu____2270 r -> (match (uu____2270) with
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


let mkBvShl : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2369 r -> (match (uu____2369) with
| (t1, t2) -> begin
(

let uu____2377 = (

let uu____2384 = (

let uu____2387 = (

let uu____2390 = (mkNatToBv sz t2 r)
in (uu____2390)::[])
in (t1)::uu____2387)
in ((BvShl), (uu____2384)))
in (mkApp' uu____2377 r))
end))


let mkBvShr : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2404 r -> (match (uu____2404) with
| (t1, t2) -> begin
(

let uu____2412 = (

let uu____2419 = (

let uu____2422 = (

let uu____2425 = (mkNatToBv sz t2 r)
in (uu____2425)::[])
in (t1)::uu____2422)
in ((BvShr), (uu____2419)))
in (mkApp' uu____2412 r))
end))


let mkBvUdiv : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2439 r -> (match (uu____2439) with
| (t1, t2) -> begin
(

let uu____2447 = (

let uu____2454 = (

let uu____2457 = (

let uu____2460 = (mkNatToBv sz t2 r)
in (uu____2460)::[])
in (t1)::uu____2457)
in ((BvUdiv), (uu____2454)))
in (mkApp' uu____2447 r))
end))


let mkBvMod : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2474 r -> (match (uu____2474) with
| (t1, t2) -> begin
(

let uu____2482 = (

let uu____2489 = (

let uu____2492 = (

let uu____2495 = (mkNatToBv sz t2 r)
in (uu____2495)::[])
in (t1)::uu____2492)
in ((BvMod), (uu____2489)))
in (mkApp' uu____2482 r))
end))


let mkBvMul : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____2509 r -> (match (uu____2509) with
| (t1, t2) -> begin
(

let uu____2517 = (

let uu____2524 = (

let uu____2527 = (

let uu____2530 = (mkNatToBv sz t2 r)
in (uu____2530)::[])
in (t1)::uu____2527)
in ((BvMul), (uu____2524)))
in (mkApp' uu____2517 r))
end))


let mkBvUlt : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvUlt)


let mkIff : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Iff)


let mkEq : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____2557 r -> (match (uu____2557) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (Var (f1), (s1)::[]), App (Var (f2), (s2)::[])) when ((Prims.op_Equality f1 f2) && (isInjective f1)) -> begin
(mk_bin_op Eq ((s1), (s2)) r)
end
| uu____2573 -> begin
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


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun uu____2660 r -> (match (uu____2660) with
| (t1, t2, t3) -> begin
(match (t1.tm) with
| App (TrueOp, uu____2671) -> begin
t2
end
| App (FalseOp, uu____2676) -> begin
t3
end
| uu____2681 -> begin
(match (((t2.tm), (t3.tm))) with
| (App (TrueOp, uu____2682), App (TrueOp, uu____2683)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____2692), uu____2693) -> begin
(

let uu____2698 = (

let uu____2703 = (mkNot t1 t1.rng)
in ((uu____2703), (t3)))
in (mkImp uu____2698 r))
end
| (uu____2704, App (TrueOp, uu____2705)) -> begin
(mkImp ((t1), (t2)) r)
end
| (uu____2710, uu____2711) -> begin
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


let mkQuant : (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____2754 r -> (match (uu____2754) with
| (qop, pats, wopt, vars, body) -> begin
(match ((Prims.op_Equality (FStar_List.length vars) (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____2795 -> begin
(match (body.tm) with
| App (TrueOp, uu____2796) -> begin
body
end
| uu____2801 -> begin
(mk (Quant (((qop), (pats), (wopt), (vars), (body)))) r)
end)
end)
end))


let mkLet : (term Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____2820 r -> (match (uu____2820) with
| (es, body) -> begin
(match ((Prims.op_Equality (FStar_List.length es) (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____2834 -> begin
(mk (Let (((es), (body)))) r)
end)
end))


let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (

let nvars = (FStar_List.length fvs)
in (

let index_of = (fun fv -> (

let uu____2854 = (FStar_Util.try_find_index (fv_eq fv) fvs)
in (match (uu____2854) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((nvars - (i + (Prims.parse_int "1"))))
end)))
in (

let rec aux = (fun ix t1 -> (

let uu____2873 = (FStar_ST.op_Bang t1.freevars)
in (match (uu____2873) with
| FStar_Pervasives_Native.Some ([]) -> begin
t1
end
| uu____2933 -> begin
(match (t1.tm) with
| Integer (uu____2942) -> begin
t1
end
| BoundV (uu____2943) -> begin
t1
end
| FreeV (x) -> begin
(

let uu____2949 = (index_of x)
in (match (uu____2949) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (i) -> begin
(mkBoundV (i + ix) t1.rng)
end))
end
| App (op, tms) -> begin
(

let uu____2959 = (

let uu____2966 = (FStar_List.map (aux ix) tms)
in ((op), (uu____2966)))
in (mkApp' uu____2959 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____2974 = (

let uu____2975 = (

let uu____2982 = (aux ix t2)
in ((uu____2982), (r1), (r2)))
in Labeled (uu____2975))
in (mk uu____2974 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____2985 = (

let uu____2986 = (

let uu____2991 = (aux ix t2)
in ((uu____2991), (r)))
in LblPos (uu____2986))
in (mk uu____2985 t2.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n1 = (FStar_List.length vars)
in (

let uu____3014 = (

let uu____3033 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n1)))))
in (

let uu____3054 = (aux (ix + n1) body)
in ((qop), (uu____3033), (wopt), (vars), (uu____3054))))
in (mkQuant uu____3014 t1.rng)))
end
| Let (es, body) -> begin
(

let uu____3073 = (FStar_List.fold_left (fun uu____3091 e -> (match (uu____3091) with
| (ix1, l) -> begin
(

let uu____3111 = (

let uu____3114 = (aux ix1 e)
in (uu____3114)::l)
in (((ix1 + (Prims.parse_int "1"))), (uu____3111)))
end)) ((ix), ([])) es)
in (match (uu____3073) with
| (ix1, es_rev) -> begin
(

let uu____3125 = (

let uu____3132 = (aux ix1 body)
in (((FStar_List.rev es_rev)), (uu____3132)))
in (mkLet uu____3125 t1.rng))
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
| Integer (uu____3156) -> begin
t1
end
| FreeV (uu____3157) -> begin
t1
end
| BoundV (i) -> begin
(match ((((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1))) with
| true -> begin
(FStar_List.nth tms1 (i - shift))
end
| uu____3167 -> begin
t1
end)
end
| App (op, tms2) -> begin
(

let uu____3174 = (

let uu____3181 = (FStar_List.map (aux shift) tms2)
in ((op), (uu____3181)))
in (mkApp' uu____3174 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____3189 = (

let uu____3190 = (

let uu____3197 = (aux shift t2)
in ((uu____3197), (r1), (r2)))
in Labeled (uu____3190))
in (mk uu____3189 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____3200 = (

let uu____3201 = (

let uu____3206 = (aux shift t2)
in ((uu____3206), (r)))
in LblPos (uu____3201))
in (mk uu____3200 t2.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift1 = (shift + m)
in (

let uu____3234 = (

let uu____3253 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift1))))
in (

let uu____3270 = (aux shift1 body)
in ((qop), (uu____3253), (wopt), (vars), (uu____3270))))
in (mkQuant uu____3234 t1.rng))))
end
| Let (es, body) -> begin
(

let uu____3285 = (FStar_List.fold_left (fun uu____3303 e -> (match (uu____3303) with
| (ix, es1) -> begin
(

let uu____3323 = (

let uu____3326 = (aux shift e)
in (uu____3326)::es1)
in (((shift + (Prims.parse_int "1"))), (uu____3323)))
end)) ((shift), ([])) es)
in (match (uu____3285) with
| (shift1, es_rev) -> begin
(

let uu____3337 = (

let uu____3344 = (aux shift1 body)
in (((FStar_List.rev es_rev)), (uu____3344)))
in (mkLet uu____3337 t1.rng))
end))
end))
in (aux (Prims.parse_int "0") t)))))


let subst : term  ->  fv  ->  term  ->  term = (fun t fv s -> (

let uu____3356 = (abstr ((fv)::[]) t)
in (inst ((s)::[]) uu____3356)))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fv Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____3379 -> (match (uu____3379) with
| (qop, pats, wopt, vars, body) -> begin
(

let uu____3421 = (

let uu____3440 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (

let uu____3457 = (FStar_List.map fv_sort vars)
in (

let uu____3464 = (abstr vars body)
in ((qop), (uu____3440), (wopt), (uu____3457), (uu____3464)))))
in (mkQuant uu____3421))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____3493 r -> (match (uu____3493) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)) r)
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____3557 r -> (match (uu____3557) with
| (pats, wopt, vars, body) -> begin
(

let uu____3589 = (mkQuant' ((Forall), (pats), (wopt), (vars), (body)))
in (uu____3589 r))
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____3612 r -> (match (uu____3612) with
| (pats, vars, body) -> begin
(

let uu____3635 = (mkQuant' ((Forall), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
in (uu____3635 r))
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____3658 r -> (match (uu____3658) with
| (pats, vars, body) -> begin
(

let uu____3681 = (mkQuant' ((Exists), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
in (uu____3681 r))
end))


let mkLet' : ((fv * term) Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____3704 r -> (match (uu____3704) with
| (bindings, body) -> begin
(

let uu____3730 = (FStar_List.split bindings)
in (match (uu____3730) with
| (vars, es) -> begin
(

let uu____3749 = (

let uu____3756 = (abstr vars body)
in ((es), (uu____3756)))
in (mkLet uu____3749 r))
end))
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun uu____3777 -> (match (uu____3777) with
| (nm, vars, s, tm, c) -> begin
(

let uu____3811 = (

let uu____3824 = (FStar_List.map fv_sort vars)
in (

let uu____3831 = (abstr vars tm)
in ((nm), (uu____3824), (s), (uu____3831), (c))))
in DefineFun (uu____3811))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (

let uu____3837 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" uu____3837)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun uu____3846 id1 -> (match (uu____3846) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (

let a = (

let uu____3856 = (

let uu____3857 = (

let uu____3862 = (mkInteger' id1 norng)
in (

let uu____3863 = (

let uu____3864 = (

let uu____3871 = (constr_id_of_sort sort)
in (

let uu____3872 = (

let uu____3875 = (mkApp ((tok_name), ([])) norng)
in (uu____3875)::[])
in ((uu____3871), (uu____3872))))
in (mkApp uu____3864 norng))
in ((uu____3862), (uu____3863))))
in (mkEq uu____3857 norng))
in {assumption_term = uu____3856; assumption_caption = FStar_Pervasives_Native.Some ("fresh token"); assumption_name = a_name; assumption_fact_ids = []})
in Assume (a)))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun uu____3892 -> (match (uu____3892) with
| (name, arg_sorts, sort, id1) -> begin
(

let id2 = (FStar_Util.string_of_int id1)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (

let uu____3924 = (

let uu____3929 = (

let uu____3930 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____3930))
in ((uu____3929), (s)))
in (mkFreeV uu____3924 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (

let uu____3938 = (

let uu____3945 = (constr_id_of_sort sort)
in ((uu____3945), ((capp)::[])))
in (mkApp uu____3938 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (

let a = (

let uu____3950 = (

let uu____3951 = (

let uu____3962 = (

let uu____3963 = (

let uu____3968 = (mkInteger id2 norng)
in ((uu____3968), (cid_app)))
in (mkEq uu____3963 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____3962)))
in (mkForall uu____3951 norng))
in {assumption_term = uu____3950; assumption_caption = FStar_Pervasives_Native.Some ("Consrtructor distinct"); assumption_name = a_name; assumption_fact_ids = []})
in Assume (a))))))))
end))


let injective_constructor : (Prims.string * constructor_field Prims.list * sort)  ->  decls_t = (fun uu____3989 -> (match (uu____3989) with
| (name, fields, sort) -> begin
(

let n_bvars = (FStar_List.length fields)
in (

let bvar_name = (fun i -> (

let uu____4010 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____4010)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (

let uu____4030 = (

let uu____4035 = (bvar_name i)
in ((uu____4035), (s)))
in (mkFreeV uu____4030)))
in (

let bvars = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____4056 -> (match (uu____4056) with
| (uu____4063, s, uu____4065) -> begin
(

let uu____4066 = (bvar i s)
in (uu____4066 norng))
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let uu____4075 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____4103 -> (match (uu____4103) with
| (name1, s, projectible) -> begin
(

let cproj_app = (mkApp ((name1), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((name1), ((sort)::[]), (s), (FStar_Pervasives_Native.Some ("Projector"))))
in (match (projectible) with
| true -> begin
(

let a = (

let uu____4126 = (

let uu____4127 = (

let uu____4138 = (

let uu____4139 = (

let uu____4144 = (

let uu____4145 = (bvar i s)
in (uu____4145 norng))
in ((cproj_app), (uu____4144)))
in (mkEq uu____4139 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____4138)))
in (mkForall uu____4127 norng))
in {assumption_term = uu____4126; assumption_caption = FStar_Pervasives_Native.Some ("Projection inverse"); assumption_name = (Prims.strcat "projection_inverse_" name1); assumption_fact_ids = []})
in (proj_name)::(Assume (a))::[])
end
| uu____4158 -> begin
(proj_name)::[]
end)))
end))))
in (FStar_All.pipe_right uu____4075 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun uu____4167 -> (match (uu____4167) with
| (name, fields, sort, id1, injective) -> begin
(

let injective1 = (injective || true)
in (

let field_sorts = (FStar_All.pipe_right fields (FStar_List.map (fun uu____4195 -> (match (uu____4195) with
| (uu____4202, sort1, uu____4204) -> begin
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

let uu____4222 = (

let uu____4227 = (

let uu____4228 = (

let uu____4235 = (constr_id_of_sort sort)
in ((uu____4235), ((xx)::[])))
in (mkApp uu____4228 norng))
in (

let uu____4238 = (

let uu____4239 = (FStar_Util.string_of_int id1)
in (mkInteger uu____4239 norng))
in ((uu____4227), (uu____4238))))
in (mkEq uu____4222 norng))
in (

let uu____4240 = (

let uu____4255 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____4305 -> (match (uu____4305) with
| (proj, s, projectible) -> begin
(match (projectible) with
| true -> begin
(

let uu____4335 = (mkApp ((proj), ((xx)::[])) norng)
in ((uu____4335), ([])))
end
| uu____4348 -> begin
(

let fi = (

let uu____4354 = (

let uu____4355 = (FStar_Util.string_of_int i)
in (Prims.strcat "f_" uu____4355))
in ((uu____4354), (s)))
in (

let uu____4356 = (mkFreeV fi norng)
in ((uu____4356), ((fi)::[]))))
end)
end))))
in (FStar_All.pipe_right uu____4255 FStar_List.split))
in (match (uu____4240) with
| (proj_terms, ex_vars) -> begin
(

let ex_vars1 = (FStar_List.flatten ex_vars)
in (

let disc_inv_body = (

let uu____4437 = (

let uu____4442 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (uu____4442)))
in (mkEq uu____4437 norng))
in (

let disc_inv_body1 = (match (ex_vars1) with
| [] -> begin
disc_inv_body
end
| uu____4450 -> begin
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
| uu____4490 -> begin
[]
end)
in (

let uu____4491 = (

let uu____4494 = (

let uu____4495 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (uu____4495))
in (uu____4494)::(cdecl)::(cid)::projs)
in (

let uu____4496 = (

let uu____4499 = (

let uu____4502 = (

let uu____4503 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (uu____4503))
in (uu____4502)::[])
in (FStar_List.append ((disc)::[]) uu____4499))
in (FStar_List.append uu____4491 uu____4496)))))))))
end))


let name_binders_inner : Prims.string FStar_Pervasives_Native.option  ->  (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun prefix_opt outer_names start sorts -> (

let uu____4550 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun uu____4605 s -> (match (uu____4605) with
| (names1, binders, n1) -> begin
(

let prefix1 = (match (s) with
| Term_sort -> begin
"@x"
end
| uu____4655 -> begin
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

let uu____4659 = (FStar_Util.string_of_int n1)
in (Prims.strcat prefix2 uu____4659))
in (

let names2 = (((nm), (s)))::names1
in (

let b = (

let uu____4672 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm uu____4672))
in ((names2), ((b)::binders), ((n1 + (Prims.parse_int "1")))))))))
end)) ((outer_names), ([]), (start))))
in (match (uu____4550) with
| (names1, binders, n1) -> begin
((names1), ((FStar_List.rev binders)), (n1))
end)))


let name_macro_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let uu____4749 = (name_binders_inner (FStar_Pervasives_Native.Some ("__")) [] (Prims.parse_int "0") sorts)
in (match (uu____4749) with
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
| uu____5029 -> begin
(

let uu____5030 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "%s.%s" enclosing_name uu____5030))
end);
))))
in (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (uu____5072); freevars = uu____5073; rng = uu____5074})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| uu____5088 -> begin
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

let uu____5128 = (FStar_List.nth names1 i)
in (FStar_All.pipe_right uu____5128 FStar_Pervasives_Native.fst))
end
| FreeV (x) -> begin
(FStar_Pervasives_Native.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(

let uu____5143 = (op_to_string op)
in (

let uu____5144 = (

let uu____5145 = (FStar_List.map (aux1 n1 names1) tms)
in (FStar_All.pipe_right uu____5145 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" uu____5143 uu____5144)))
end
| Labeled (t2, uu____5151, uu____5152) -> begin
(aux1 n1 names1 t2)
end
| LblPos (t2, s) -> begin
(

let uu____5155 = (aux1 n1 names1 t2)
in (FStar_Util.format2 "(! %s :lblpos %s)" uu____5155 s))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let qid = (next_qid ())
in (

let uu____5178 = (name_binders_inner FStar_Pervasives_Native.None names1 n1 sorts)
in (match (uu____5178) with
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
| uu____5227 -> begin
(

let uu____5232 = (FStar_All.pipe_right pats1 (FStar_List.map (fun pats2 -> (

let uu____5248 = (

let uu____5249 = (FStar_List.map (fun p -> (

let uu____5255 = (aux1 n2 names2 p)
in (FStar_Util.format1 "%s" uu____5255))) pats2)
in (FStar_String.concat " " uu____5249))
in (FStar_Util.format1 "\n:pattern (%s)" uu____5248)))))
in (FStar_All.pipe_right uu____5232 (FStar_String.concat "\n")))
end)
in (

let uu____5258 = (

let uu____5261 = (

let uu____5264 = (

let uu____5267 = (aux1 n2 names2 body)
in (

let uu____5268 = (

let uu____5271 = (weightToSmt wopt)
in (uu____5271)::(pats_str)::(qid)::[])
in (uu____5267)::uu____5268))
in (binders1)::uu____5264)
in ((qop_to_string qop))::uu____5261)
in (FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))" uu____5258)))))
end)))
end
| Let (es, body) -> begin
(

let uu____5278 = (FStar_List.fold_left (fun uu____5315 e -> (match (uu____5315) with
| (names0, binders, n0) -> begin
(

let nm = (

let uu____5365 = (FStar_Util.string_of_int n0)
in (Prims.strcat "@lb" uu____5365))
in (

let names01 = (((nm), (Term_sort)))::names0
in (

let b = (

let uu____5378 = (aux1 n1 names1 e)
in (FStar_Util.format2 "(%s %s)" nm uu____5378))
in ((names01), ((b)::binders), ((n0 + (Prims.parse_int "1")))))))
end)) ((names1), ([]), (n1)) es)
in (match (uu____5278) with
| (names2, binders, n2) -> begin
(

let uu____5410 = (aux1 n2 names2 body)
in (FStar_Util.format2 "(let (%s)\n%s)" (FStar_String.concat " " binders) uu____5410))
end))
end)))
and aux = (fun depth n1 names1 t1 -> (

let s = (aux' depth n1 names1 t1)
in (match ((print_ranges && (Prims.op_disEquality t1.rng norng))) with
| true -> begin
(

let uu____5418 = (FStar_Range.string_of_range t1.rng)
in (

let uu____5419 = (FStar_Range.string_of_use_range t1.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____5418 uu____5419 s)))
end
| uu____5420 -> begin
s
end)))
in (aux (Prims.parse_int "0") (Prims.parse_int "0") [] t)))))


let caption_to_string : Prims.string FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___54_5425 -> (match (uu___54_5425) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let uu____5429 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(failwith "Impossible")
end
| (hd1)::[] -> begin
((hd1), (""))
end
| (hd1)::uu____5444 -> begin
((hd1), ("..."))
end)
in (match (uu____5429) with
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

let uu____5475 = (FStar_Options.log_queries ())
in (match (uu____5475) with
| true -> begin
(

let uu____5476 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun uu___55_5480 -> (match (uu___55_5480) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" uu____5476))
end
| uu____5487 -> begin
""
end))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (

let uu____5499 = (caption_to_string c)
in (

let uu____5500 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____5499 f (FStar_String.concat " " l) uu____5500))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let uu____5510 = (name_macro_binders arg_sorts)
in (match (uu____5510) with
| (names1, binders) -> begin
(

let body1 = (

let uu____5542 = (FStar_List.map (fun x -> (mkFreeV x norng)) names1)
in (inst uu____5542 body))
in (

let uu____5555 = (caption_to_string c)
in (

let uu____5556 = (strSort retsort)
in (

let uu____5557 = (termToSmt print_ranges (escape f) body1)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____5555 f (FStar_String.concat " " binders) uu____5556 uu____5557)))))
end))
end
| Assume (a) -> begin
(

let fact_ids_to_string = (fun ids -> (FStar_All.pipe_right ids (FStar_List.map (fun uu___56_5575 -> (match (uu___56_5575) with
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

let uu____5580 = (FStar_Options.log_queries ())
in (match (uu____5580) with
| true -> begin
(

let uu____5581 = (

let uu____5582 = (fact_ids_to_string a.assumption_fact_ids)
in (FStar_String.concat "; " uu____5582))
in (FStar_Util.format1 ";;; Fact-ids: %s\n" uu____5581))
end
| uu____5585 -> begin
""
end))
in (

let n1 = (escape a.assumption_name)
in (

let uu____5587 = (caption_to_string a.assumption_caption)
in (

let uu____5588 = (termToSmt print_ranges n1 a.assumption_term)
in (FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____5587 fids uu____5588 n1))))))
end
| Eval (t) -> begin
(

let uu____5590 = (termToSmt print_ranges "eval" t)
in (FStar_Util.format1 "(eval %s)" uu____5590))
end
| Echo (s) -> begin
(FStar_Util.format1 "(echo \"%s\")" s)
end
| RetainAssumptions (uu____5592) -> begin
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

let uu____5921 = (

let uu____5924 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right uu____5924 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right uu____5921 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mkBvConstructor : Prims.int  ->  decls_t = (fun sz -> (

let uu____5939 = (

let uu____5958 = (

let uu____5959 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____5959))
in (

let uu____5964 = (

let uu____5973 = (

let uu____5980 = (

let uu____5981 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____5981))
in ((uu____5980), (BitVec_sort (sz)), (true)))
in (uu____5973)::[])
in ((uu____5958), (uu____5964), (Term_sort), (((Prims.parse_int "12") + sz)), (true))))
in (FStar_All.pipe_right uu____5939 constructor_to_decl)))


let __range_c : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let mk_Range_const : Prims.unit  ->  term = (fun uu____6063 -> (

let i = (FStar_ST.op_Bang __range_c)
in ((

let uu____6091 = (

let uu____6092 = (FStar_ST.op_Bang __range_c)
in (uu____6092 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals __range_c uu____6091));
(

let uu____6143 = (

let uu____6150 = (

let uu____6153 = (mkInteger' i norng)
in (uu____6153)::[])
in (("Range_const"), (uu____6150)))
in (mkApp uu____6143 norng));
)))


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____6175 = (

let uu____6182 = (

let uu____6185 = (mkInteger' i norng)
in (uu____6185)::[])
in (("Tm_uvar"), (uu____6182)))
in (mkApp uu____6175 r)))


let mk_Term_unit : term = (mkApp (("Tm_unit"), ([])) norng)


let elim_box : Prims.bool  ->  Prims.string  ->  Prims.string  ->  term  ->  term = (fun cond u v1 t -> (match (t.tm) with
| App (Var (v'), (t1)::[]) when ((Prims.op_Equality v1 v') && cond) -> begin
t1
end
| uu____6206 -> begin
(mkApp ((u), ((t)::[])) t.rng)
end))


let maybe_elim_box : Prims.string  ->  Prims.string  ->  term  ->  term = (fun u v1 t -> (

let uu____6218 = (FStar_Options.smtencoding_elim_box ())
in (elim_box uu____6218 u v1 t)))


let boxInt : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxIntFun) (FStar_Pervasives_Native.snd boxIntFun) t))


let unboxInt : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxIntFun) (FStar_Pervasives_Native.fst boxIntFun) t))


let boxBool : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxBoolFun) (FStar_Pervasives_Native.snd boxBoolFun) t))


let unboxBool : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxBoolFun) (FStar_Pervasives_Native.fst boxBoolFun) t))


let boxString : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxStringFun) (FStar_Pervasives_Native.snd boxStringFun) t))


let unboxString : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxStringFun) (FStar_Pervasives_Native.fst boxStringFun) t))


let boxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let uu____6243 = (

let uu____6244 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____6244))
in (

let uu____6249 = (

let uu____6250 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____6250))
in (elim_box true uu____6243 uu____6249 t))))


let unboxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let uu____6261 = (

let uu____6262 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____6262))
in (

let uu____6267 = (

let uu____6268 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____6268))
in (elim_box true uu____6261 uu____6267 t))))


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
| uu____6280 -> begin
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
| uu____6288 -> begin
(FStar_Exn.raise FStar_Util.Impos)
end))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n1) -> begin
(FStar_Util.format1 "(Integer %s)" n1)
end
| BoundV (n1) -> begin
(

let uu____6304 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(BoundV %s)" uu____6304))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv))
end
| App (op, l) -> begin
(

let uu____6316 = (op_to_string op)
in (

let uu____6317 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" uu____6316 uu____6317)))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____6321 = (print_smt_term t1)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 uu____6321))
end
| LblPos (t1, s) -> begin
(

let uu____6324 = (print_smt_term t1)
in (FStar_Util.format2 "(LblPos %s %s)" s uu____6324))
end
| Quant (qop, l, uu____6327, uu____6328, t1) -> begin
(

let uu____6346 = (print_smt_term_list_list l)
in (

let uu____6347 = (print_smt_term t1)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____6346 uu____6347)))
end
| Let (es, body) -> begin
(

let uu____6354 = (print_smt_term_list es)
in (

let uu____6355 = (print_smt_term body)
in (FStar_Util.format2 "(let %s %s)" uu____6354 uu____6355)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (

let uu____6359 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right uu____6359 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l1 -> (

let uu____6378 = (

let uu____6379 = (

let uu____6380 = (print_smt_term_list l1)
in (Prims.strcat uu____6380 " ] "))
in (Prims.strcat "; [ " uu____6379))
in (Prims.strcat s uu____6378))) "" l))


let getBoxedInteger : term  ->  Prims.int FStar_Pervasives_Native.option = (fun t -> (match (t.tm) with
| App (Var (s), (t2)::[]) when (Prims.op_Equality s (FStar_Pervasives_Native.fst boxIntFun)) -> begin
(match (t2.tm) with
| Integer (n1) -> begin
(

let uu____6395 = (FStar_Util.int_of_string n1)
in FStar_Pervasives_Native.Some (uu____6395))
end
| uu____6396 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____6397 -> begin
FStar_Pervasives_Native.None
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2p"), ({tm = App (Var ("Prims.op_Equality"), (uu____6406)::(t1)::(t2)::[]); freevars = uu____6409; rng = uu____6410})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2p"), ({tm = App (Var ("Prims.op_disEquality"), (uu____6423)::(t1)::(t2)::[]); freevars = uu____6426; rng = uu____6427})::[]) -> begin
(

let uu____6440 = (mkEq ((t1), (t2)) norng)
in (mkNot uu____6440 t.rng))
end
| App (Var ("Prims.b2p"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = uu____6443; rng = uu____6444})::[]) -> begin
(

let uu____6457 = (

let uu____6462 = (unboxInt t1)
in (

let uu____6463 = (unboxInt t2)
in ((uu____6462), (uu____6463))))
in (mkLTE uu____6457 t.rng))
end
| App (Var ("Prims.b2p"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = uu____6466; rng = uu____6467})::[]) -> begin
(

let uu____6480 = (

let uu____6485 = (unboxInt t1)
in (

let uu____6486 = (unboxInt t2)
in ((uu____6485), (uu____6486))))
in (mkLT uu____6480 t.rng))
end
| App (Var ("Prims.b2p"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = uu____6489; rng = uu____6490})::[]) -> begin
(

let uu____6503 = (

let uu____6508 = (unboxInt t1)
in (

let uu____6509 = (unboxInt t2)
in ((uu____6508), (uu____6509))))
in (mkGTE uu____6503 t.rng))
end
| App (Var ("Prims.b2p"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = uu____6512; rng = uu____6513})::[]) -> begin
(

let uu____6526 = (

let uu____6531 = (unboxInt t1)
in (

let uu____6532 = (unboxInt t2)
in ((uu____6531), (uu____6532))))
in (mkGT uu____6526 t.rng))
end
| App (Var ("Prims.b2p"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = uu____6535; rng = uu____6536})::[]) -> begin
(

let uu____6549 = (

let uu____6554 = (unboxBool t1)
in (

let uu____6555 = (unboxBool t2)
in ((uu____6554), (uu____6555))))
in (mkAnd uu____6549 t.rng))
end
| App (Var ("Prims.b2p"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = uu____6558; rng = uu____6559})::[]) -> begin
(

let uu____6572 = (

let uu____6577 = (unboxBool t1)
in (

let uu____6578 = (unboxBool t2)
in ((uu____6577), (uu____6578))))
in (mkOr uu____6572 t.rng))
end
| App (Var ("Prims.b2p"), ({tm = App (Var ("Prims.op_Negation"), (t1)::[]); freevars = uu____6580; rng = uu____6581})::[]) -> begin
(

let uu____6594 = (unboxBool t1)
in (mkNot uu____6594 t1.rng))
end
| App (Var ("Prims.b2p"), ({tm = App (Var ("FStar.BV.bvult"), (t0)::(t1)::(t2)::[]); freevars = uu____6598; rng = uu____6599})::[]) when (

let uu____6612 = (getBoxedInteger t0)
in (FStar_Util.is_some uu____6612)) -> begin
(

let sz = (

let uu____6616 = (getBoxedInteger t0)
in (match (uu____6616) with
| FStar_Pervasives_Native.Some (sz) -> begin
sz
end
| uu____6620 -> begin
(failwith "impossible")
end))
in (

let uu____6623 = (

let uu____6628 = (unboxBitVec sz t1)
in (

let uu____6629 = (unboxBitVec sz t2)
in ((uu____6628), (uu____6629))))
in (mkBvUlt uu____6623 t.rng)))
end
| App (Var ("Prims.equals"), (uu____6630)::({tm = App (Var ("FStar.BV.bvult"), (t0)::(t1)::(t2)::[]); freevars = uu____6634; rng = uu____6635})::(uu____6636)::[]) when (

let uu____6649 = (getBoxedInteger t0)
in (FStar_Util.is_some uu____6649)) -> begin
(

let sz = (

let uu____6653 = (getBoxedInteger t0)
in (match (uu____6653) with
| FStar_Pervasives_Native.Some (sz) -> begin
sz
end
| uu____6657 -> begin
(failwith "impossible")
end))
in (

let uu____6660 = (

let uu____6665 = (unboxBitVec sz t1)
in (

let uu____6666 = (unboxBitVec sz t2)
in ((uu____6665), (uu____6666))))
in (mkBvUlt uu____6660 t.rng)))
end
| App (Var ("Prims.b2p"), (t1)::[]) -> begin
(

let uu___57_6670 = (unboxBool t1)
in {tm = uu___57_6670.tm; freevars = uu___57_6670.freevars; rng = t.rng})
end
| uu____6671 -> begin
(mkApp (("Valid"), ((t)::[])) t.rng)
end))


let mk_HasType : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasType"), ((v1)::(t)::[])) t.rng))


let mk_HasTypeZ : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasTypeZ"), ((v1)::(t)::[])) t.rng))


let mk_IsTyped : term  ->  term = (fun v1 -> (mkApp (("IsTyped"), ((v1)::[])) norng))


let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v1 t -> (

let uu____6704 = (FStar_Options.unthrottle_inductives ())
in (match (uu____6704) with
| true -> begin
(mk_HasType v1 t)
end
| uu____6705 -> begin
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

let uu____6777 = (

let uu____6784 = (

let uu____6787 = (mkInteger' i norng)
in (uu____6787)::[])
in (("FString_const"), (uu____6784)))
in (mkApp uu____6777 r)))


let mk_Precedes : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (

let uu____6799 = (mkApp (("Precedes"), ((x1)::(x2)::[])) r)
in (FStar_All.pipe_right uu____6799 mk_Valid)))


let mk_LexCons : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (mkApp (("LexCons"), ((x1)::(x2)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
(mkApp (("ZFuel"), ([])) norng)
end
| uu____6818 -> begin
(

let uu____6819 = (

let uu____6826 = (

let uu____6829 = (n_fuel (n1 - (Prims.parse_int "1")))
in (uu____6829)::[])
in (("SFuel"), (uu____6826)))
in (mkApp uu____6819 norng))
end))


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term FStar_Pervasives_Native.option  ->  term FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  term FStar_Pervasives_Native.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (FStar_Pervasives_Native.Some (p11), FStar_Pervasives_Native.Some (p21)) -> begin
(

let uu____6863 = (mkAnd ((p11), (p21)) r)
in FStar_Pervasives_Native.Some (uu____6863))
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

let uu____6916 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l uu____6916)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____6931 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l uu____6931)))


let mk_haseq : term  ->  term = (fun t -> (

let uu____6939 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid uu____6939)))




