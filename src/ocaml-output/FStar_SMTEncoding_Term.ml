
open Prims
open FStar_Pervasives

let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s 39 (*'*) 95 (*_*)))

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
| uu____50 -> begin
false
end))


let uu___is_Int_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int_sort -> begin
true
end
| uu____61 -> begin
false
end))


let uu___is_String_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| String_sort -> begin
true
end
| uu____72 -> begin
false
end))


let uu___is_Term_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Term_sort -> begin
true
end
| uu____83 -> begin
false
end))


let uu___is_Fuel_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fuel_sort -> begin
true
end
| uu____94 -> begin
false
end))


let uu___is_BitVec_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BitVec_sort (_0) -> begin
true
end
| uu____107 -> begin
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
| uu____134 -> begin
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
| uu____170 -> begin
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
| uu____203 -> begin
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

let uu____231 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ BitVec %s)" uu____231))
end
| Array (s1, s2) -> begin
(

let uu____236 = (strSort s1)
in (

let uu____238 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" uu____236 uu____238)))
end
| Arrow (s1, s2) -> begin
(

let uu____243 = (strSort s1)
in (

let uu____245 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" uu____243 uu____245)))
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
| uu____277 -> begin
false
end))


let uu___is_FalseOp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FalseOp -> begin
true
end
| uu____288 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____299 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____310 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____321 -> begin
false
end))


let uu___is_Imp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Imp -> begin
true
end
| uu____332 -> begin
false
end))


let uu___is_Iff : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iff -> begin
true
end
| uu____343 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____354 -> begin
false
end))


let uu___is_LT : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LT -> begin
true
end
| uu____365 -> begin
false
end))


let uu___is_LTE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LTE -> begin
true
end
| uu____376 -> begin
false
end))


let uu___is_GT : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GT -> begin
true
end
| uu____387 -> begin
false
end))


let uu___is_GTE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GTE -> begin
true
end
| uu____398 -> begin
false
end))


let uu___is_Add : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Add -> begin
true
end
| uu____409 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____420 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____431 -> begin
false
end))


let uu___is_Mul : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mul -> begin
true
end
| uu____442 -> begin
false
end))


let uu___is_Minus : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Minus -> begin
true
end
| uu____453 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____464 -> begin
false
end))


let uu___is_BvAnd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvAnd -> begin
true
end
| uu____475 -> begin
false
end))


let uu___is_BvXor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvXor -> begin
true
end
| uu____486 -> begin
false
end))


let uu___is_BvOr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvOr -> begin
true
end
| uu____497 -> begin
false
end))


let uu___is_BvAdd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvAdd -> begin
true
end
| uu____508 -> begin
false
end))


let uu___is_BvSub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvSub -> begin
true
end
| uu____519 -> begin
false
end))


let uu___is_BvShl : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvShl -> begin
true
end
| uu____530 -> begin
false
end))


let uu___is_BvShr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvShr -> begin
true
end
| uu____541 -> begin
false
end))


let uu___is_BvUdiv : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvUdiv -> begin
true
end
| uu____552 -> begin
false
end))


let uu___is_BvMod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvMod -> begin
true
end
| uu____563 -> begin
false
end))


let uu___is_BvMul : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvMul -> begin
true
end
| uu____574 -> begin
false
end))


let uu___is_BvUlt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvUlt -> begin
true
end
| uu____585 -> begin
false
end))


let uu___is_BvUext : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvUext (_0) -> begin
true
end
| uu____598 -> begin
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
| uu____622 -> begin
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
| uu____644 -> begin
false
end))


let uu___is_ITE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ITE -> begin
true
end
| uu____655 -> begin
false
end))


let uu___is_Var : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Var (_0) -> begin
true
end
| uu____668 -> begin
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
| uu____690 -> begin
false
end))


let uu___is_Exists : qop  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exists -> begin
true
end
| uu____701 -> begin
false
end))

type term' =
| Integer of Prims.string
| BoundV of Prims.int
| FreeV of (Prims.string * sort * Prims.bool)
| App of (op * term Prims.list)
| Quant of (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)
| Let of (term Prims.list * term)
| Labeled of (term * Prims.string * FStar_Range.range)
| LblPos of (term * Prims.string) 
 and term =
{tm : term'; freevars : (Prims.string * sort * Prims.bool) Prims.list FStar_Syntax_Syntax.memo; rng : FStar_Range.range}


let uu___is_Integer : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Integer (_0) -> begin
true
end
| uu____855 -> begin
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
| uu____879 -> begin
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
| uu____910 -> begin
false
end))


let __proj__FreeV__item___0 : term'  ->  (Prims.string * sort * Prims.bool) = (fun projectee -> (match (projectee) with
| FreeV (_0) -> begin
_0
end))


let uu___is_App : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| App (_0) -> begin
true
end
| uu____960 -> begin
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
| uu____1017 -> begin
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
| uu____1100 -> begin
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
| uu____1145 -> begin
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
| uu____1191 -> begin
false
end))


let __proj__LblPos__item___0 : term'  ->  (term * Prims.string) = (fun projectee -> (match (projectee) with
| LblPos (_0) -> begin
_0
end))


let __proj__Mkterm__item__tm : term  ->  term' = (fun projectee -> (match (projectee) with
| {tm = tm; freevars = freevars; rng = rng} -> begin
tm
end))


let __proj__Mkterm__item__freevars : term  ->  (Prims.string * sort * Prims.bool) Prims.list FStar_Syntax_Syntax.memo = (fun projectee -> (match (projectee) with
| {tm = tm; freevars = freevars; rng = rng} -> begin
freevars
end))


let __proj__Mkterm__item__rng : term  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {tm = tm; freevars = freevars; rng = rng} -> begin
rng
end))


type pat =
term


type fv =
(Prims.string * sort * Prims.bool)


type fvs =
(Prims.string * sort * Prims.bool) Prims.list


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
| uu____1415 -> begin
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
| uu____1435 -> begin
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
| uu____1456 -> begin
false
end))


let __proj__Tag__item___0 : fact_db_id  ->  Prims.string = (fun projectee -> (match (projectee) with
| Tag (_0) -> begin
_0
end))

type assumption =
{assumption_term : term; assumption_caption : caption; assumption_name : Prims.string; assumption_fact_ids : fact_db_id Prims.list}


let __proj__Mkassumption__item__assumption_term : assumption  ->  term = (fun projectee -> (match (projectee) with
| {assumption_term = assumption_term; assumption_caption = assumption_caption; assumption_name = assumption_name; assumption_fact_ids = assumption_fact_ids} -> begin
assumption_term
end))


let __proj__Mkassumption__item__assumption_caption : assumption  ->  caption = (fun projectee -> (match (projectee) with
| {assumption_term = assumption_term; assumption_caption = assumption_caption; assumption_name = assumption_name; assumption_fact_ids = assumption_fact_ids} -> begin
assumption_caption
end))


let __proj__Mkassumption__item__assumption_name : assumption  ->  Prims.string = (fun projectee -> (match (projectee) with
| {assumption_term = assumption_term; assumption_caption = assumption_caption; assumption_name = assumption_name; assumption_fact_ids = assumption_fact_ids} -> begin
assumption_name
end))


let __proj__Mkassumption__item__assumption_fact_ids : assumption  ->  fact_db_id Prims.list = (fun projectee -> (match (projectee) with
| {assumption_term = assumption_term; assumption_caption = assumption_caption; assumption_name = assumption_name; assumption_fact_ids = assumption_fact_ids} -> begin
assumption_fact_ids
end))

type decl =
| DefPrelude
| DeclFun of (Prims.string * sort Prims.list * sort * caption)
| DefineFun of (Prims.string * sort Prims.list * sort * term * caption)
| Assume of assumption
| Caption of Prims.string
| Module of (Prims.string * decl Prims.list)
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
| uu____1646 -> begin
false
end))


let uu___is_DeclFun : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DeclFun (_0) -> begin
true
end
| uu____1669 -> begin
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
| uu____1735 -> begin
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
| uu____1794 -> begin
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
| uu____1815 -> begin
false
end))


let __proj__Caption__item___0 : decl  ->  Prims.string = (fun projectee -> (match (projectee) with
| Caption (_0) -> begin
_0
end))


let uu___is_Module : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Module (_0) -> begin
true
end
| uu____1845 -> begin
false
end))


let __proj__Module__item___0 : decl  ->  (Prims.string * decl Prims.list) = (fun projectee -> (match (projectee) with
| Module (_0) -> begin
_0
end))


let uu___is_Eval : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eval (_0) -> begin
true
end
| uu____1886 -> begin
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
| uu____1907 -> begin
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
| uu____1933 -> begin
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
| uu____1961 -> begin
false
end))


let uu___is_Pop : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____1972 -> begin
false
end))


let uu___is_CheckSat : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckSat -> begin
true
end
| uu____1983 -> begin
false
end))


let uu___is_GetUnsatCore : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetUnsatCore -> begin
true
end
| uu____1994 -> begin
false
end))


let uu___is_SetOption : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOption (_0) -> begin
true
end
| uu____2012 -> begin
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
| uu____2049 -> begin
false
end))


let uu___is_GetReasonUnknown : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetReasonUnknown -> begin
true
end
| uu____2060 -> begin
false
end))


type decls_t =
decl Prims.list


type error_label =
(fv * Prims.string * FStar_Range.range)


type error_labels =
error_label Prims.list


let mk_fv : (Prims.string * sort)  ->  fv = (fun uu____2083 -> (match (uu____2083) with
| (x, y) -> begin
((x), (y), (false))
end))


let fv_name : fv  ->  Prims.string = (fun x -> (

let uu____2103 = x
in (match (uu____2103) with
| (nm, uu____2106, uu____2107) -> begin
nm
end)))


let fv_sort : fv  ->  sort = (fun x -> (

let uu____2118 = x
in (match (uu____2118) with
| (uu____2119, sort, uu____2121) -> begin
sort
end)))


let fv_force : fv  ->  Prims.bool = (fun x -> (

let uu____2133 = x
in (match (uu____2133) with
| (uu____2135, uu____2136, force) -> begin
force
end)))


let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> (

let uu____2154 = (fv_name x)
in (

let uu____2156 = (fv_name y)
in (Prims.op_Equality uu____2154 uu____2156))))


let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match (((x.tm), (y.tm))) with
| (FreeV (x1), FreeV (y1)) -> begin
(fv_eq x1 y1)
end
| uu____2190 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun uu___120_2201 -> (match (uu___120_2201) with
| {tm = FreeV (x); freevars = uu____2203; rng = uu____2204} -> begin
(fv_sort x)
end
| uu____2225 -> begin
(failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun uu___121_2232 -> (match (uu___121_2232) with
| {tm = FreeV (fv); freevars = uu____2234; rng = uu____2235} -> begin
fv
end
| uu____2256 -> begin
(failwith "impossible")
end))


let rec freevars : term  ->  (Prims.string * sort * Prims.bool) Prims.list = (fun t -> (match (t.tm) with
| Integer (uu____2284) -> begin
[]
end
| BoundV (uu____2294) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (uu____2329, tms) -> begin
(FStar_List.collect freevars tms)
end
| Quant (uu____2343, uu____2344, uu____2345, uu____2346, t1) -> begin
(freevars t1)
end
| Labeled (t1, uu____2367, uu____2368) -> begin
(freevars t1)
end
| LblPos (t1, uu____2372) -> begin
(freevars t1)
end
| Let (es, body) -> begin
(FStar_List.collect freevars ((body)::es))
end))


let free_variables : term  ->  fvs = (fun t -> (

let uu____2395 = (FStar_ST.op_Bang t.freevars)
in (match (uu____2395) with
| FStar_Pervasives_Native.Some (b) -> begin
b
end
| FStar_Pervasives_Native.None -> begin
(

let fvs = (

let uu____2493 = (freevars t)
in (FStar_Util.remove_dups fv_eq uu____2493))
in ((FStar_ST.op_Colon_Equals t.freevars (FStar_Pervasives_Native.Some (fvs)));
fvs;
))
end)))


let qop_to_string : qop  ->  Prims.string = (fun uu___122_2572 -> (match (uu___122_2572) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun uu___123_2582 -> (match (uu___123_2582) with
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

let uu____2617 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ zero_extend %s)" uu____2617))
end
| NatToBv (n1) -> begin
(

let uu____2622 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ int2bv %s)" uu____2622))
end
| Var (s) -> begin
s
end))


let weightToSmt : Prims.int FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___124_2636 -> (match (uu___124_2636) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (i) -> begin
(

let uu____2646 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" uu____2646))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____2666 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" uu____2666))
end
| FreeV (x) -> begin
(

let uu____2678 = (fv_name x)
in (

let uu____2680 = (

let uu____2682 = (

let uu____2684 = (fv_sort x)
in (strSort uu____2684))
in (Prims.strcat ":" uu____2682))
in (Prims.strcat uu____2678 uu____2680)))
end
| App (op, tms) -> begin
(

let uu____2692 = (

let uu____2694 = (op_to_string op)
in (

let uu____2696 = (

let uu____2698 = (

let uu____2700 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right uu____2700 (FStar_String.concat " ")))
in (Prims.strcat uu____2698 ")"))
in (Prims.strcat uu____2694 uu____2696)))
in (Prims.strcat "(" uu____2692))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____2717 = (hash_of_term t1)
in (

let uu____2719 = (

let uu____2721 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 uu____2721))
in (Prims.strcat uu____2717 uu____2719)))
end
| LblPos (t1, r) -> begin
(

let uu____2727 = (

let uu____2729 = (hash_of_term t1)
in (Prims.strcat uu____2729 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " uu____2727))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let uu____2757 = (

let uu____2759 = (

let uu____2761 = (

let uu____2763 = (

let uu____2765 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right uu____2765 (FStar_String.concat " ")))
in (

let uu____2775 = (

let uu____2777 = (

let uu____2779 = (hash_of_term body)
in (

let uu____2781 = (

let uu____2783 = (

let uu____2785 = (weightToSmt wopt)
in (

let uu____2787 = (

let uu____2789 = (

let uu____2791 = (

let uu____2793 = (FStar_All.pipe_right pats (FStar_List.map (fun pats1 -> (

let uu____2812 = (FStar_List.map hash_of_term pats1)
in (FStar_All.pipe_right uu____2812 (FStar_String.concat " "))))))
in (FStar_All.pipe_right uu____2793 (FStar_String.concat "; ")))
in (Prims.strcat uu____2791 "))"))
in (Prims.strcat " " uu____2789))
in (Prims.strcat uu____2785 uu____2787)))
in (Prims.strcat " " uu____2783))
in (Prims.strcat uu____2779 uu____2781)))
in (Prims.strcat ")(! " uu____2777))
in (Prims.strcat uu____2763 uu____2775)))
in (Prims.strcat " (" uu____2761))
in (Prims.strcat (qop_to_string qop) uu____2759))
in (Prims.strcat "(" uu____2757))
end
| Let (es, body) -> begin
(

let uu____2839 = (

let uu____2841 = (

let uu____2843 = (FStar_List.map hash_of_term es)
in (FStar_All.pipe_right uu____2843 (FStar_String.concat " ")))
in (

let uu____2853 = (

let uu____2855 = (

let uu____2857 = (hash_of_term body)
in (Prims.strcat uu____2857 ")"))
in (Prims.strcat ") " uu____2855))
in (Prims.strcat uu____2841 uu____2853)))
in (Prims.strcat "(let (" uu____2839))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mkBoxFunctions : Prims.string  ->  (Prims.string * Prims.string) = (fun s -> ((s), ((Prims.strcat s "_proj_0"))))


let boxIntFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxInt")


let boxBoolFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxBool")


let boxStringFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxString")


let boxBitVecFun : Prims.int  ->  (Prims.string * Prims.string) = (fun sz -> (

let uu____2918 = (

let uu____2920 = (FStar_Util.string_of_int sz)
in (Prims.strcat "BoxBitVec" uu____2920))
in (mkBoxFunctions uu____2918)))


let isInjective : Prims.string  ->  Prims.bool = (fun s -> (match (((FStar_String.length s) >= (Prims.parse_int "3"))) with
| true -> begin
((

let uu____2937 = (FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3"))
in (Prims.op_Equality uu____2937 "Box")) && (

let uu____2944 = (

let uu____2946 = (FStar_String.list_of_string s)
in (FStar_List.existsML (fun c -> (Prims.op_Equality c 46 (*.*))) uu____2946))
in (not (uu____2944))))
end
| uu____2956 -> begin
false
end))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (

let uu____2970 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {tm = t; freevars = uu____2970; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((TrueOp), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((FalseOp), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____3056 = (

let uu____3057 = (FStar_Util.ensure_decimal i)
in Integer (uu____3057))
in (mk uu____3056 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____3072 = (FStar_Util.string_of_int i)
in (mkInteger uu____3072 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : fv  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun uu____3137 r -> (match (uu____3137) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (TrueOp, uu____3167) -> begin
(mkFalse r)
end
| App (FalseOp, uu____3172) -> begin
(mkTrue r)
end
| uu____3177 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____3193 r -> (match (uu____3193) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____3201), uu____3202) -> begin
t2
end
| (uu____3207, App (TrueOp, uu____3208)) -> begin
t1
end
| (App (FalseOp, uu____3213), uu____3214) -> begin
(mkFalse r)
end
| (uu____3219, App (FalseOp, uu____3220)) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (uu____3237, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), uu____3246) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____3253 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____3273 r -> (match (uu____3273) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____3281), uu____3282) -> begin
(mkTrue r)
end
| (uu____3287, App (TrueOp, uu____3288)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____3293), uu____3294) -> begin
t2
end
| (uu____3299, App (FalseOp, uu____3300)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (uu____3317, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), uu____3326) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____3333 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____3353 r -> (match (uu____3353) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (uu____3361, App (TrueOp, uu____3362)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____3367), uu____3368) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____3373), uu____3374) -> begin
t2
end
| (uu____3379, App (Imp, (t1')::(t2')::[])) -> begin
(

let uu____3384 = (

let uu____3391 = (

let uu____3394 = (mkAnd ((t1), (t1')) r)
in (uu____3394)::(t2')::[])
in ((Imp), (uu____3391)))
in (mkApp' uu____3384 r))
end
| uu____3397 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op uu____3422 r -> (match (uu____3422) with
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


let mkBvShl : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____3582 r -> (match (uu____3582) with
| (t1, t2) -> begin
(

let uu____3591 = (

let uu____3598 = (

let uu____3601 = (

let uu____3604 = (mkNatToBv sz t2 r)
in (uu____3604)::[])
in (t1)::uu____3601)
in ((BvShl), (uu____3598)))
in (mkApp' uu____3591 r))
end))


let mkBvShr : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____3626 r -> (match (uu____3626) with
| (t1, t2) -> begin
(

let uu____3635 = (

let uu____3642 = (

let uu____3645 = (

let uu____3648 = (mkNatToBv sz t2 r)
in (uu____3648)::[])
in (t1)::uu____3645)
in ((BvShr), (uu____3642)))
in (mkApp' uu____3635 r))
end))


let mkBvUdiv : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____3670 r -> (match (uu____3670) with
| (t1, t2) -> begin
(

let uu____3679 = (

let uu____3686 = (

let uu____3689 = (

let uu____3692 = (mkNatToBv sz t2 r)
in (uu____3692)::[])
in (t1)::uu____3689)
in ((BvUdiv), (uu____3686)))
in (mkApp' uu____3679 r))
end))


let mkBvMod : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____3714 r -> (match (uu____3714) with
| (t1, t2) -> begin
(

let uu____3723 = (

let uu____3730 = (

let uu____3733 = (

let uu____3736 = (mkNatToBv sz t2 r)
in (uu____3736)::[])
in (t1)::uu____3733)
in ((BvMod), (uu____3730)))
in (mkApp' uu____3723 r))
end))


let mkBvMul : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____3758 r -> (match (uu____3758) with
| (t1, t2) -> begin
(

let uu____3767 = (

let uu____3774 = (

let uu____3777 = (

let uu____3780 = (mkNatToBv sz t2 r)
in (uu____3780)::[])
in (t1)::uu____3777)
in ((BvMul), (uu____3774)))
in (mkApp' uu____3767 r))
end))


let mkBvUlt : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvUlt)


let mkIff : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Iff)


let mkEq : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____3822 r -> (match (uu____3822) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (Var (f1), (s1)::[]), App (Var (f2), (s2)::[])) when ((Prims.op_Equality f1 f2) && (isInjective f1)) -> begin
(mk_bin_op Eq ((s1), (s2)) r)
end
| uu____3841 -> begin
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


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun uu____3978 r -> (match (uu____3978) with
| (t1, t2, t3) -> begin
(match (t1.tm) with
| App (TrueOp, uu____3989) -> begin
t2
end
| App (FalseOp, uu____3994) -> begin
t3
end
| uu____3999 -> begin
(match (((t2.tm), (t3.tm))) with
| (App (TrueOp, uu____4000), App (TrueOp, uu____4001)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____4010), uu____4011) -> begin
(

let uu____4016 = (

let uu____4021 = (mkNot t1 t1.rng)
in ((uu____4021), (t3)))
in (mkImp uu____4016 r))
end
| (uu____4022, App (TrueOp, uu____4023)) -> begin
(mkImp ((t1), (t2)) r)
end
| (uu____4028, uu____4029) -> begin
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


let check_pattern_ok : term  ->  term FStar_Pervasives_Native.option = (fun t -> (

let rec aux = (fun t1 -> (match (t1.tm) with
| Integer (uu____4085) -> begin
FStar_Pervasives_Native.None
end
| BoundV (uu____4087) -> begin
FStar_Pervasives_Native.None
end
| FreeV (uu____4089) -> begin
FStar_Pervasives_Native.None
end
| Let (tms, tm) -> begin
(aux_l ((tm)::tms))
end
| App (head1, terms) -> begin
(

let head_ok = (match (head1) with
| Var (uu____4113) -> begin
true
end
| TrueOp -> begin
true
end
| FalseOp -> begin
true
end
| Not -> begin
false
end
| And -> begin
false
end
| Or -> begin
false
end
| Imp -> begin
false
end
| Iff -> begin
false
end
| Eq -> begin
false
end
| LT -> begin
true
end
| LTE -> begin
true
end
| GT -> begin
true
end
| GTE -> begin
true
end
| Add -> begin
true
end
| Sub -> begin
true
end
| Div -> begin
true
end
| Mul -> begin
true
end
| Minus -> begin
true
end
| Mod -> begin
true
end
| BvAnd -> begin
false
end
| BvXor -> begin
false
end
| BvOr -> begin
false
end
| BvAdd -> begin
false
end
| BvSub -> begin
false
end
| BvShl -> begin
false
end
| BvShr -> begin
false
end
| BvUdiv -> begin
false
end
| BvMod -> begin
false
end
| BvMul -> begin
false
end
| BvUlt -> begin
false
end
| BvUext (uu____4145) -> begin
false
end
| NatToBv (uu____4148) -> begin
false
end
| BvToNat -> begin
false
end
| ITE -> begin
false
end)
in (match ((not (head_ok))) with
| true -> begin
FStar_Pervasives_Native.Some (t1)
end
| uu____4156 -> begin
(aux_l terms)
end))
end
| Labeled (t2, uu____4159, uu____4160) -> begin
(aux t2)
end
| Quant (uu____4163) -> begin
FStar_Pervasives_Native.Some (t1)
end
| LblPos (uu____4183) -> begin
FStar_Pervasives_Native.Some (t1)
end))
and aux_l = (fun ts -> (match (ts) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (t1)::ts1 -> begin
(

let uu____4198 = (aux t1)
in (match (uu____4198) with
| FStar_Pervasives_Native.Some (t2) -> begin
FStar_Pervasives_Native.Some (t2)
end
| FStar_Pervasives_Native.None -> begin
(aux_l ts1)
end))
end))
in (aux t)))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n1) -> begin
(FStar_Util.format1 "(Integer %s)" n1)
end
| BoundV (n1) -> begin
(

let uu____4233 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(BoundV %s)" uu____4233))
end
| FreeV (fv) -> begin
(

let uu____4245 = (fv_name fv)
in (FStar_Util.format1 "(FreeV %s)" uu____4245))
end
| App (op, l) -> begin
(

let uu____4254 = (op_to_string op)
in (

let uu____4256 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" uu____4254 uu____4256)))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____4264 = (print_smt_term t1)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 uu____4264))
end
| LblPos (t1, s) -> begin
(

let uu____4271 = (print_smt_term t1)
in (FStar_Util.format2 "(LblPos %s %s)" s uu____4271))
end
| Quant (qop, l, uu____4276, uu____4277, t1) -> begin
(

let uu____4297 = (print_smt_term_list_list l)
in (

let uu____4299 = (print_smt_term t1)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4297 uu____4299)))
end
| Let (es, body) -> begin
(

let uu____4308 = (print_smt_term_list es)
in (

let uu____4310 = (print_smt_term body)
in (FStar_Util.format2 "(let %s %s)" uu____4308 uu____4310)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (

let uu____4317 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right uu____4317 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l1 -> (

let uu____4344 = (

let uu____4346 = (

let uu____4348 = (print_smt_term_list l1)
in (Prims.strcat uu____4348 " ] "))
in (Prims.strcat "; [ " uu____4346))
in (Prims.strcat s uu____4344))) "" l))


let mkQuant : FStar_Range.range  ->  Prims.bool  ->  (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  term = (fun r check_pats uu____4388 -> (match (uu____4388) with
| (qop, pats, wopt, vars, body) -> begin
(

let all_pats_ok = (fun pats1 -> (match ((not (check_pats))) with
| true -> begin
pats1
end
| uu____4455 -> begin
(

let uu____4457 = (FStar_Util.find_map pats1 (fun x -> (FStar_Util.find_map x check_pattern_ok)))
in (match (uu____4457) with
| FStar_Pervasives_Native.None -> begin
pats1
end
| FStar_Pervasives_Native.Some (p) -> begin
((

let uu____4472 = (

let uu____4478 = (

let uu____4480 = (print_smt_term p)
in (FStar_Util.format1 "Pattern (%s) contains illegal symbols; dropping it" uu____4480))
in ((FStar_Errors.Warning_SMTPatternMissingBoundVar), (uu____4478)))
in (FStar_Errors.log_issue r uu____4472));
[];
)
end))
end))
in (match ((Prims.op_Equality (FStar_List.length vars) (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____4489 -> begin
(match (body.tm) with
| App (TrueOp, uu____4491) -> begin
body
end
| uu____4496 -> begin
(

let uu____4497 = (

let uu____4498 = (

let uu____4518 = (all_pats_ok pats)
in ((qop), (uu____4518), (wopt), (vars), (body)))
in Quant (uu____4498))
in (mk uu____4497 r))
end)
end))
end))


let mkLet : (term Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____4547 r -> (match (uu____4547) with
| (es, body) -> begin
(match ((Prims.op_Equality (FStar_List.length es) (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____4564 -> begin
(mk (Let (((es), (body)))) r)
end)
end))


let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (

let nvars = (FStar_List.length fvs)
in (

let index_of1 = (fun fv -> (

let uu____4593 = (FStar_Util.try_find_index (fv_eq fv) fvs)
in (match (uu____4593) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((nvars - (i + (Prims.parse_int "1"))))
end)))
in (

let rec aux = (fun ix t1 -> (

let uu____4626 = (FStar_ST.op_Bang t1.freevars)
in (match (uu____4626) with
| FStar_Pervasives_Native.Some ([]) -> begin
t1
end
| uu____4700 -> begin
(match (t1.tm) with
| Integer (uu____4713) -> begin
t1
end
| BoundV (uu____4715) -> begin
t1
end
| FreeV (x) -> begin
(

let uu____4726 = (index_of1 x)
in (match (uu____4726) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (i) -> begin
(mkBoundV (i + ix) t1.rng)
end))
end
| App (op, tms) -> begin
(

let uu____4740 = (

let uu____4747 = (FStar_List.map (aux ix) tms)
in ((op), (uu____4747)))
in (mkApp' uu____4740 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____4757 = (

let uu____4758 = (

let uu____4766 = (aux ix t2)
in ((uu____4766), (r1), (r2)))
in Labeled (uu____4758))
in (mk uu____4757 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____4772 = (

let uu____4773 = (

let uu____4779 = (aux ix t2)
in ((uu____4779), (r)))
in LblPos (uu____4773))
in (mk uu____4772 t2.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n1 = (FStar_List.length vars)
in (

let uu____4805 = (

let uu____4825 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n1)))))
in (

let uu____4846 = (aux (ix + n1) body)
in ((qop), (uu____4825), (wopt), (vars), (uu____4846))))
in (mkQuant t1.rng false uu____4805)))
end
| Let (es, body) -> begin
(

let uu____4867 = (FStar_List.fold_left (fun uu____4887 e -> (match (uu____4887) with
| (ix1, l) -> begin
(

let uu____4911 = (

let uu____4914 = (aux ix1 e)
in (uu____4914)::l)
in (((ix1 + (Prims.parse_int "1"))), (uu____4911)))
end)) ((ix), ([])) es)
in (match (uu____4867) with
| (ix1, es_rev) -> begin
(

let uu____4930 = (

let uu____4937 = (aux ix1 body)
in (((FStar_List.rev es_rev)), (uu____4937)))
in (mkLet uu____4930 t1.rng))
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
| Integer (uu____4973) -> begin
t1
end
| FreeV (uu____4975) -> begin
t1
end
| BoundV (i) -> begin
(match ((((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1))) with
| true -> begin
(FStar_List.nth tms1 (i - shift))
end
| uu____4992 -> begin
t1
end)
end
| App (op, tms2) -> begin
(

let uu____5000 = (

let uu____5007 = (FStar_List.map (aux shift) tms2)
in ((op), (uu____5007)))
in (mkApp' uu____5000 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____5017 = (

let uu____5018 = (

let uu____5026 = (aux shift t2)
in ((uu____5026), (r1), (r2)))
in Labeled (uu____5018))
in (mk uu____5017 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____5032 = (

let uu____5033 = (

let uu____5039 = (aux shift t2)
in ((uu____5039), (r)))
in LblPos (uu____5033))
in (mk uu____5032 t2.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift1 = (shift + m)
in (

let uu____5071 = (

let uu____5091 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift1))))
in (

let uu____5108 = (aux shift1 body)
in ((qop), (uu____5091), (wopt), (vars), (uu____5108))))
in (mkQuant t1.rng false uu____5071))))
end
| Let (es, body) -> begin
(

let uu____5125 = (FStar_List.fold_left (fun uu____5145 e -> (match (uu____5145) with
| (ix, es1) -> begin
(

let uu____5169 = (

let uu____5172 = (aux shift e)
in (uu____5172)::es1)
in (((shift + (Prims.parse_int "1"))), (uu____5169)))
end)) ((shift), ([])) es)
in (match (uu____5125) with
| (shift1, es_rev) -> begin
(

let uu____5188 = (

let uu____5195 = (aux shift1 body)
in (((FStar_List.rev es_rev)), (uu____5195)))
in (mkLet uu____5188 t1.rng))
end))
end))
in (aux (Prims.parse_int "0") t)))))


let subst : term  ->  fv  ->  term  ->  term = (fun t fv s -> (

let uu____5215 = (abstr ((fv)::[]) t)
in (inst ((s)::[]) uu____5215)))


let mkQuant' : FStar_Range.range  ->  (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fv Prims.list * term)  ->  term = (fun r uu____5245 -> (match (uu____5245) with
| (qop, pats, wopt, vars, body) -> begin
(

let uu____5288 = (

let uu____5308 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (

let uu____5325 = (FStar_List.map fv_sort vars)
in (

let uu____5328 = (abstr vars body)
in ((qop), (uu____5308), (wopt), (uu____5325), (uu____5328)))))
in (mkQuant r true uu____5288))
end))


let mkForall : FStar_Range.range  ->  (pat Prims.list Prims.list * fvs * term)  ->  term = (fun r uu____5359 -> (match (uu____5359) with
| (pats, vars, body) -> begin
(mkQuant' r ((Forall), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
end))


let mkForall'' : FStar_Range.range  ->  (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  term = (fun r uu____5418 -> (match (uu____5418) with
| (pats, wopt, sorts, body) -> begin
(mkQuant r true ((Forall), (pats), (wopt), (sorts), (body)))
end))


let mkForall' : FStar_Range.range  ->  (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fvs * term)  ->  term = (fun r uu____5493 -> (match (uu____5493) with
| (pats, wopt, vars, body) -> begin
(mkQuant' r ((Forall), (pats), (wopt), (vars), (body)))
end))


let mkExists : FStar_Range.range  ->  (pat Prims.list Prims.list * fvs * term)  ->  term = (fun r uu____5556 -> (match (uu____5556) with
| (pats, vars, body) -> begin
(mkQuant' r ((Exists), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
end))


let mkLet' : ((fv * term) Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____5607 r -> (match (uu____5607) with
| (bindings, body) -> begin
(

let uu____5633 = (FStar_List.split bindings)
in (match (uu____5633) with
| (vars, es) -> begin
(

let uu____5652 = (

let uu____5659 = (abstr vars body)
in ((es), (uu____5659)))
in (mkLet uu____5652 r))
end))
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let mkDefineFun : (Prims.string * fv Prims.list * sort * term * caption)  ->  decl = (fun uu____5681 -> (match (uu____5681) with
| (nm, vars, s, tm, c) -> begin
(

let uu____5706 = (

let uu____5720 = (FStar_List.map fv_sort vars)
in (

let uu____5723 = (abstr vars tm)
in ((nm), (uu____5720), (s), (uu____5723), (c))))
in DefineFun (uu____5706))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (

let uu____5734 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" uu____5734)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun uu____5752 id1 -> (match (uu____5752) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (

let a = (

let uu____5768 = (

let uu____5769 = (

let uu____5774 = (mkInteger' id1 norng)
in (

let uu____5775 = (

let uu____5776 = (

let uu____5784 = (constr_id_of_sort sort)
in (

let uu____5786 = (

let uu____5789 = (mkApp ((tok_name), ([])) norng)
in (uu____5789)::[])
in ((uu____5784), (uu____5786))))
in (mkApp uu____5776 norng))
in ((uu____5774), (uu____5775))))
in (mkEq uu____5769 norng))
in (

let uu____5796 = (escape a_name)
in {assumption_term = uu____5768; assumption_caption = FStar_Pervasives_Native.Some ("fresh token"); assumption_name = uu____5796; assumption_fact_ids = []}))
in Assume (a)))
end))


let fresh_constructor : FStar_Range.range  ->  (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun rng uu____5822 -> (match (uu____5822) with
| (name, arg_sorts, sort, id1) -> begin
(

let id2 = (FStar_Util.string_of_int id1)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (

let uu____5862 = (

let uu____5863 = (

let uu____5869 = (

let uu____5871 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____5871))
in ((uu____5869), (s)))
in (mk_fv uu____5863))
in (mkFreeV uu____5862 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (

let uu____5899 = (

let uu____5907 = (constr_id_of_sort sort)
in ((uu____5907), ((capp)::[])))
in (mkApp uu____5899 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (

let a = (

let uu____5916 = (

let uu____5917 = (

let uu____5928 = (

let uu____5929 = (

let uu____5934 = (mkInteger id2 norng)
in ((uu____5934), (cid_app)))
in (mkEq uu____5929 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____5928)))
in (mkForall rng uu____5917))
in (

let uu____5943 = (escape a_name)
in {assumption_term = uu____5916; assumption_caption = FStar_Pervasives_Native.Some ("Constructor distinct"); assumption_name = uu____5943; assumption_fact_ids = []}))
in Assume (a))))))))
end))


let injective_constructor : FStar_Range.range  ->  (Prims.string * constructor_field Prims.list * sort)  ->  decls_t = (fun rng uu____5966 -> (match (uu____5966) with
| (name, fields, sort) -> begin
(

let n_bvars = (FStar_List.length fields)
in (

let bvar_name = (fun i -> (

let uu____5995 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____5995)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (

let uu____6030 = (

let uu____6031 = (

let uu____6037 = (bvar_name i)
in ((uu____6037), (s)))
in (mk_fv uu____6031))
in (FStar_All.pipe_left mkFreeV uu____6030)))
in (

let bvars = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____6073 -> (match (uu____6073) with
| (uu____6083, s, uu____6085) -> begin
(

let uu____6090 = (bvar i s)
in (uu____6090 norng))
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let uu____6118 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____6156 -> (match (uu____6156) with
| (name1, s, projectible) -> begin
(

let cproj_app = (mkApp ((name1), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((name1), ((sort)::[]), (s), (FStar_Pervasives_Native.Some ("Projector"))))
in (match (projectible) with
| true -> begin
(

let a = (

let uu____6189 = (

let uu____6190 = (

let uu____6201 = (

let uu____6202 = (

let uu____6207 = (

let uu____6208 = (bvar i s)
in (uu____6208 norng))
in ((cproj_app), (uu____6207)))
in (mkEq uu____6202 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____6201)))
in (mkForall rng uu____6190))
in (

let uu____6221 = (escape (Prims.strcat "projection_inverse_" name1))
in {assumption_term = uu____6189; assumption_caption = FStar_Pervasives_Native.Some ("Projection inverse"); assumption_name = uu____6221; assumption_fact_ids = []}))
in (proj_name)::(Assume (a))::[])
end
| uu____6226 -> begin
(proj_name)::[]
end)))
end))))
in (FStar_All.pipe_right uu____6118 FStar_List.flatten)))))))))
end))


let constructor_to_decl : FStar_Range.range  ->  constructor_t  ->  decls_t = (fun rng uu____6242 -> (match (uu____6242) with
| (name, fields, sort, id1, injective) -> begin
(

let injective1 = (injective || true)
in (

let field_sorts = (FStar_All.pipe_right fields (FStar_List.map (fun uu____6288 -> (match (uu____6288) with
| (uu____6297, sort1, uu____6299) -> begin
sort1
end))))
in (

let cdecl = DeclFun (((name), (field_sorts), (sort), (FStar_Pervasives_Native.Some ("Constructor"))))
in (

let cid = (fresh_constructor rng ((name), (field_sorts), (sort), (id1)))
in (

let disc = (

let disc_name = (Prims.strcat "is-" name)
in (

let xfv = (mk_fv (("x"), (sort)))
in (

let xx = (mkFreeV xfv norng)
in (

let disc_eq = (

let uu____6324 = (

let uu____6329 = (

let uu____6330 = (

let uu____6338 = (constr_id_of_sort sort)
in ((uu____6338), ((xx)::[])))
in (mkApp uu____6330 norng))
in (

let uu____6343 = (

let uu____6344 = (FStar_Util.string_of_int id1)
in (mkInteger uu____6344 norng))
in ((uu____6329), (uu____6343))))
in (mkEq uu____6324 norng))
in (

let uu____6346 = (

let uu____6365 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____6429 -> (match (uu____6429) with
| (proj, s, projectible) -> begin
(match (projectible) with
| true -> begin
(

let uu____6459 = (mkApp ((proj), ((xx)::[])) norng)
in ((uu____6459), ([])))
end
| uu____6465 -> begin
(

let fi = (

let uu____6468 = (

let uu____6474 = (

let uu____6476 = (FStar_Util.string_of_int i)
in (Prims.strcat "f_" uu____6476))
in ((uu____6474), (s)))
in (mk_fv uu____6468))
in (

let uu____6480 = (mkFreeV fi norng)
in ((uu____6480), ((fi)::[]))))
end)
end))))
in (FStar_All.pipe_right uu____6365 FStar_List.split))
in (match (uu____6346) with
| (proj_terms, ex_vars) -> begin
(

let ex_vars1 = (FStar_List.flatten ex_vars)
in (

let disc_inv_body = (

let uu____6577 = (

let uu____6582 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (uu____6582)))
in (mkEq uu____6577 norng))
in (

let disc_inv_body1 = (match (ex_vars1) with
| [] -> begin
disc_inv_body
end
| uu____6595 -> begin
(mkExists norng (([]), (ex_vars1), (disc_inv_body)))
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
(injective_constructor rng ((name), (fields), (sort)))
end
| uu____6628 -> begin
[]
end)
in (

let uu____6630 = (

let uu____6633 = (

let uu____6634 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (uu____6634))
in (uu____6633)::(cdecl)::(cid)::projs)
in (

let uu____6637 = (

let uu____6640 = (

let uu____6643 = (

let uu____6644 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (uu____6644))
in (uu____6643)::[])
in (FStar_List.append ((disc)::[]) uu____6640))
in (FStar_List.append uu____6630 uu____6637)))))))))
end))


let name_binders_inner : Prims.string FStar_Pervasives_Native.option  ->  fv Prims.list  ->  Prims.int  ->  sort Prims.list  ->  (fv Prims.list * Prims.string Prims.list * Prims.int) = (fun prefix_opt outer_names start sorts -> (

let uu____6696 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun uu____6745 s -> (match (uu____6745) with
| (names1, binders, n1) -> begin
(

let prefix1 = (match (s) with
| Term_sort -> begin
"@x"
end
| uu____6790 -> begin
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

let uu____6801 = (FStar_Util.string_of_int n1)
in (Prims.strcat prefix2 uu____6801))
in (

let names2 = (

let uu____6806 = (mk_fv ((nm), (s)))
in (uu____6806)::names1)
in (

let b = (

let uu____6810 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm uu____6810))
in ((names2), ((b)::binders), ((n1 + (Prims.parse_int "1")))))))))
end)) ((outer_names), ([]), (start))))
in (match (uu____6696) with
| (names1, binders, n1) -> begin
((names1), ((FStar_List.rev binders)), (n1))
end)))


let name_macro_binders : sort Prims.list  ->  (fv Prims.list * Prims.string Prims.list) = (fun sorts -> (

let uu____6881 = (name_binders_inner (FStar_Pervasives_Native.Some ("__")) [] (Prims.parse_int "0") sorts)
in (match (uu____6881) with
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
| uu____7043 -> begin
(

let uu____7045 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "%s.%s" enclosing_name uu____7045))
end);
))))
in (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (uu____7091); freevars = uu____7092; rng = uu____7093})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| uu____7114 -> begin
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

let uu____7190 = (FStar_List.nth names1 i)
in (FStar_All.pipe_right uu____7190 fv_name))
end
| FreeV (x) when (fv_force x) -> begin
(

let uu____7201 = (

let uu____7203 = (fv_name x)
in (Prims.strcat uu____7203 " Dummy_value)"))
in (Prims.strcat "(" uu____7201))
end
| FreeV (x) -> begin
(fv_name x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(

let uu____7225 = (op_to_string op)
in (

let uu____7227 = (

let uu____7229 = (FStar_List.map (aux1 n1 names1) tms)
in (FStar_All.pipe_right uu____7229 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" uu____7225 uu____7227)))
end
| Labeled (t2, uu____7241, uu____7242) -> begin
(aux1 n1 names1 t2)
end
| LblPos (t2, s) -> begin
(

let uu____7249 = (aux1 n1 names1 t2)
in (FStar_Util.format2 "(! %s :lblpos %s)" uu____7249 s))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let qid = (next_qid ())
in (

let uu____7277 = (name_binders_inner FStar_Pervasives_Native.None names1 n1 sorts)
in (match (uu____7277) with
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
| uu____7330 -> begin
(

let uu____7335 = (FStar_All.pipe_right pats1 (FStar_List.map (fun pats2 -> (

let uu____7354 = (

let uu____7356 = (FStar_List.map (fun p -> (

let uu____7364 = (aux1 n2 names2 p)
in (FStar_Util.format1 "%s" uu____7364))) pats2)
in (FStar_String.concat " " uu____7356))
in (FStar_Util.format1 "\n:pattern (%s)" uu____7354)))))
in (FStar_All.pipe_right uu____7335 (FStar_String.concat "\n")))
end)
in (

let uu____7374 = (

let uu____7378 = (

let uu____7382 = (

let uu____7386 = (aux1 n2 names2 body)
in (

let uu____7388 = (

let uu____7392 = (weightToSmt wopt)
in (uu____7392)::(pats_str)::(qid)::[])
in (uu____7386)::uu____7388))
in (binders1)::uu____7382)
in ((qop_to_string qop))::uu____7378)
in (FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))" uu____7374)))))
end)))
end
| Let (es, body) -> begin
(

let uu____7408 = (FStar_List.fold_left (fun uu____7441 e -> (match (uu____7441) with
| (names0, binders, n0) -> begin
(

let nm = (

let uu____7484 = (FStar_Util.string_of_int n0)
in (Prims.strcat "@lb" uu____7484))
in (

let names01 = (

let uu____7490 = (mk_fv ((nm), (Term_sort)))
in (uu____7490)::names0)
in (

let b = (

let uu____7494 = (aux1 n1 names1 e)
in (FStar_Util.format2 "(%s %s)" nm uu____7494))
in ((names01), ((b)::binders), ((n0 + (Prims.parse_int "1")))))))
end)) ((names1), ([]), (n1)) es)
in (match (uu____7408) with
| (names2, binders, n2) -> begin
(

let uu____7528 = (aux1 n2 names2 body)
in (FStar_Util.format2 "(let (%s)\n%s)" (FStar_String.concat " " binders) uu____7528))
end))
end)))
and aux = (fun depth n1 names1 t1 -> (

let s = (aux' depth n1 names1 t1)
in (match ((print_ranges && (Prims.op_disEquality t1.rng norng))) with
| true -> begin
(

let uu____7544 = (FStar_Range.string_of_range t1.rng)
in (

let uu____7546 = (FStar_Range.string_of_use_range t1.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____7544 uu____7546 s)))
end
| uu____7549 -> begin
s
end)))
in (aux (Prims.parse_int "0") (Prims.parse_int "0") [] t)))))


let caption_to_string : Prims.bool  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string = (fun print_captions uu___125_7568 -> (match (uu___125_7568) with
| FStar_Pervasives_Native.Some (c) when print_captions -> begin
(

let c1 = (

let uu____7579 = (FStar_All.pipe_right (FStar_String.split ((10)::[]) c) (FStar_List.map FStar_Util.trim_string))
in (FStar_All.pipe_right uu____7579 (FStar_String.concat " ")))
in (Prims.strcat ";;;;;;;;;;;;;;;;" (Prims.strcat c1 "\n")))
end
| uu____7601 -> begin
""
end))


let rec declToSmt' : Prims.bool  ->  Prims.string  ->  decl  ->  Prims.string = (fun print_captions z3options decl -> (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Module (s, decls) -> begin
(

let res = (

let uu____7676 = (FStar_List.map (declToSmt' print_captions z3options) decls)
in (FStar_All.pipe_right uu____7676 (FStar_String.concat "\n")))
in (

let uu____7686 = (FStar_Options.keep_query_captions ())
in (match (uu____7686) with
| true -> begin
(

let uu____7690 = (FStar_Util.string_of_int (FStar_List.length decls))
in (

let uu____7692 = (FStar_Util.string_of_int (FStar_String.length res))
in (FStar_Util.format5 "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)" s res s uu____7690 uu____7692)))
end
| uu____7695 -> begin
res
end)))
end
| Caption (c) -> begin
(match (print_captions) with
| true -> begin
(

let uu____7701 = (

let uu____7703 = (FStar_All.pipe_right (FStar_Util.splitlines c) (FStar_List.map (fun s -> (Prims.strcat "; " (Prims.strcat s "\n")))))
in (FStar_All.pipe_right uu____7703 (FStar_String.concat "")))
in (Prims.strcat "\n" uu____7701))
end
| uu____7726 -> begin
""
end)
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (

let uu____7744 = (caption_to_string print_captions c)
in (

let uu____7746 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____7744 f (FStar_String.concat " " l) uu____7746))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let uu____7761 = (name_macro_binders arg_sorts)
in (match (uu____7761) with
| (names1, binders) -> begin
(

let body1 = (

let uu____7785 = (FStar_List.map (fun x -> (mkFreeV x norng)) names1)
in (inst uu____7785 body))
in (

let uu____7790 = (caption_to_string print_captions c)
in (

let uu____7792 = (strSort retsort)
in (

let uu____7794 = (

let uu____7796 = (escape f)
in (termToSmt print_captions uu____7796 body1))
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____7790 f (FStar_String.concat " " binders) uu____7792 uu____7794)))))
end))
end
| Assume (a) -> begin
(

let fact_ids_to_string = (fun ids -> (FStar_All.pipe_right ids (FStar_List.map (fun uu___126_7823 -> (match (uu___126_7823) with
| Name (n1) -> begin
(

let uu____7826 = (FStar_Ident.text_of_lid n1)
in (Prims.strcat "Name " uu____7826))
end
| Namespace (ns) -> begin
(

let uu____7830 = (FStar_Ident.text_of_lid ns)
in (Prims.strcat "Namespace " uu____7830))
end
| Tag (t) -> begin
(Prims.strcat "Tag " t)
end)))))
in (

let fids = (match (print_captions) with
| true -> begin
(

let uu____7840 = (

let uu____7842 = (fact_ids_to_string a.assumption_fact_ids)
in (FStar_String.concat "; " uu____7842))
in (FStar_Util.format1 ";;; Fact-ids: %s\n" uu____7840))
end
| uu____7848 -> begin
""
end)
in (

let n1 = a.assumption_name
in (

let uu____7853 = (caption_to_string print_captions a.assumption_caption)
in (

let uu____7855 = (termToSmt print_captions n1 a.assumption_term)
in (FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____7853 fids uu____7855 n1))))))
end
| Eval (t) -> begin
(

let uu____7859 = (termToSmt print_captions "eval" t)
in (FStar_Util.format1 "(eval %s)" uu____7859))
end
| Echo (s) -> begin
(FStar_Util.format1 "(echo \"%s\")" s)
end
| RetainAssumptions (uu____7866) -> begin
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
end))
and declToSmt : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (

let uu____7887 = (FStar_Options.keep_query_captions ())
in (declToSmt' uu____7887 z3options decl)))
and declToSmt_no_caps : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (declToSmt' false z3options decl))
and declsToSmt : Prims.string  ->  decl Prims.list  ->  Prims.string = (fun z3options decls -> (

let uu____7898 = (FStar_List.map (declToSmt z3options) decls)
in (FStar_All.pipe_right uu____7898 (FStar_String.concat "\n"))))
and mkPrelude : Prims.string  ->  Prims.string = (fun z3options -> (

let basic = (Prims.strcat z3options "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-sort Dummy_sort)\n(declare-fun Dummy_value () Dummy_sort)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (iff (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(declare-fun Prims.precedes (Term Term Term Term) Term)\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(declare-fun __uu__PartialApp () Term)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))")
in (

let constrs = ((("FString_const"), (((("FString_const_proj_0"), (Int_sort), (true)))::[]), (String_sort), ((Prims.parse_int "0")), (true)))::((("Tm_type"), ([]), (Term_sort), ((Prims.parse_int "2")), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "3")), (false)))::((("Tm_unit"), ([]), (Term_sort), ((Prims.parse_int "6")), (true)))::((((FStar_Pervasives_Native.fst boxIntFun)), (((((FStar_Pervasives_Native.snd boxIntFun)), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "7")), (true)))::((((FStar_Pervasives_Native.fst boxBoolFun)), (((((FStar_Pervasives_Native.snd boxBoolFun)), (Bool_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "8")), (true)))::((((FStar_Pervasives_Native.fst boxStringFun)), (((((FStar_Pervasives_Native.snd boxStringFun)), (String_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "9")), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort), (true)))::((("LexCons_1"), (Term_sort), (true)))::((("LexCons_2"), (Term_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "11")), (true)))::[]
in (

let bcons = (

let uu____8018 = (

let uu____8022 = (FStar_All.pipe_right constrs (FStar_List.collect (constructor_to_decl norng)))
in (FStar_All.pipe_right uu____8022 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right uu____8018 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mkBvConstructor : Prims.int  ->  decls_t = (fun sz -> (

let uu____8051 = (

let uu____8052 = (

let uu____8054 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____8054))
in (

let uu____8063 = (

let uu____8066 = (

let uu____8067 = (

let uu____8069 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____8069))
in ((uu____8067), (BitVec_sort (sz)), (true)))
in (uu____8066)::[])
in ((uu____8052), (uu____8063), (Term_sort), (((Prims.parse_int "12") + sz)), (true))))
in (FStar_All.pipe_right uu____8051 (constructor_to_decl norng))))


let __range_c : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let mk_Range_const : unit  ->  term = (fun uu____8110 -> (

let i = (FStar_ST.op_Bang __range_c)
in ((

let uu____8135 = (

let uu____8137 = (FStar_ST.op_Bang __range_c)
in (uu____8137 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals __range_c uu____8135));
(

let uu____8182 = (

let uu____8190 = (

let uu____8193 = (mkInteger' i norng)
in (uu____8193)::[])
in (("Range_const"), (uu____8190)))
in (mkApp uu____8182 norng));
)))


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____8236 = (

let uu____8244 = (

let uu____8247 = (mkInteger' i norng)
in (uu____8247)::[])
in (("Tm_uvar"), (uu____8244)))
in (mkApp uu____8236 r)))


let mk_Term_unit : term = (mkApp (("Tm_unit"), ([])) norng)


let elim_box : Prims.bool  ->  Prims.string  ->  Prims.string  ->  term  ->  term = (fun cond u v1 t -> (match (t.tm) with
| App (Var (v'), (t1)::[]) when ((Prims.op_Equality v1 v') && cond) -> begin
t1
end
| uu____8290 -> begin
(mkApp ((u), ((t)::[])) t.rng)
end))


let maybe_elim_box : Prims.string  ->  Prims.string  ->  term  ->  term = (fun u v1 t -> (

let uu____8314 = (FStar_Options.smtencoding_elim_box ())
in (elim_box uu____8314 u v1 t)))


let boxInt : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxIntFun) (FStar_Pervasives_Native.snd boxIntFun) t))


let unboxInt : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxIntFun) (FStar_Pervasives_Native.fst boxIntFun) t))


let boxBool : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxBoolFun) (FStar_Pervasives_Native.snd boxBoolFun) t))


let unboxBool : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxBoolFun) (FStar_Pervasives_Native.fst boxBoolFun) t))


let boxString : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxStringFun) (FStar_Pervasives_Native.snd boxStringFun) t))


let unboxString : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxStringFun) (FStar_Pervasives_Native.fst boxStringFun) t))


let boxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let uu____8389 = (

let uu____8391 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____8391))
in (

let uu____8400 = (

let uu____8402 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____8402))
in (elim_box true uu____8389 uu____8400 t))))


let unboxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let uu____8425 = (

let uu____8427 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____8427))
in (

let uu____8436 = (

let uu____8438 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____8438))
in (elim_box true uu____8425 uu____8436 t))))


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
| uu____8461 -> begin
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
| uu____8475 -> begin
(FStar_Exn.raise FStar_Util.Impos)
end))


let getBoxedInteger : term  ->  Prims.int FStar_Pervasives_Native.option = (fun t -> (match (t.tm) with
| App (Var (s), (t2)::[]) when (Prims.op_Equality s (FStar_Pervasives_Native.fst boxIntFun)) -> begin
(match (t2.tm) with
| Integer (n1) -> begin
(

let uu____8501 = (FStar_Util.int_of_string n1)
in FStar_Pervasives_Native.Some (uu____8501))
end
| uu____8504 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____8506 -> begin
FStar_Pervasives_Native.None
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (uu____8524)::(t1)::(t2)::[]); freevars = uu____8527; rng = uu____8528})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (uu____8547)::(t1)::(t2)::[]); freevars = uu____8550; rng = uu____8551})::[]) -> begin
(

let uu____8570 = (mkEq ((t1), (t2)) norng)
in (mkNot uu____8570 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = uu____8573; rng = uu____8574})::[]) -> begin
(

let uu____8593 = (

let uu____8598 = (unboxInt t1)
in (

let uu____8599 = (unboxInt t2)
in ((uu____8598), (uu____8599))))
in (mkLTE uu____8593 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = uu____8602; rng = uu____8603})::[]) -> begin
(

let uu____8622 = (

let uu____8627 = (unboxInt t1)
in (

let uu____8628 = (unboxInt t2)
in ((uu____8627), (uu____8628))))
in (mkLT uu____8622 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = uu____8631; rng = uu____8632})::[]) -> begin
(

let uu____8651 = (

let uu____8656 = (unboxInt t1)
in (

let uu____8657 = (unboxInt t2)
in ((uu____8656), (uu____8657))))
in (mkGTE uu____8651 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = uu____8660; rng = uu____8661})::[]) -> begin
(

let uu____8680 = (

let uu____8685 = (unboxInt t1)
in (

let uu____8686 = (unboxInt t2)
in ((uu____8685), (uu____8686))))
in (mkGT uu____8680 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = uu____8689; rng = uu____8690})::[]) -> begin
(

let uu____8709 = (

let uu____8714 = (unboxBool t1)
in (

let uu____8715 = (unboxBool t2)
in ((uu____8714), (uu____8715))))
in (mkAnd uu____8709 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = uu____8718; rng = uu____8719})::[]) -> begin
(

let uu____8738 = (

let uu____8743 = (unboxBool t1)
in (

let uu____8744 = (unboxBool t2)
in ((uu____8743), (uu____8744))))
in (mkOr uu____8738 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t1)::[]); freevars = uu____8746; rng = uu____8747})::[]) -> begin
(

let uu____8766 = (unboxBool t1)
in (mkNot uu____8766 t1.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("FStar.BV.bvult"), (t0)::(t1)::(t2)::[]); freevars = uu____8770; rng = uu____8771})::[]) when (

let uu____8790 = (getBoxedInteger t0)
in (FStar_Util.is_some uu____8790)) -> begin
(

let sz = (

let uu____8797 = (getBoxedInteger t0)
in (match (uu____8797) with
| FStar_Pervasives_Native.Some (sz) -> begin
sz
end
| uu____8805 -> begin
(failwith "impossible")
end))
in (

let uu____8811 = (

let uu____8816 = (unboxBitVec sz t1)
in (

let uu____8817 = (unboxBitVec sz t2)
in ((uu____8816), (uu____8817))))
in (mkBvUlt uu____8811 t.rng)))
end
| App (Var ("Prims.equals"), (uu____8818)::({tm = App (Var ("FStar.BV.bvult"), (t0)::(t1)::(t2)::[]); freevars = uu____8822; rng = uu____8823})::(uu____8824)::[]) when (

let uu____8843 = (getBoxedInteger t0)
in (FStar_Util.is_some uu____8843)) -> begin
(

let sz = (

let uu____8850 = (getBoxedInteger t0)
in (match (uu____8850) with
| FStar_Pervasives_Native.Some (sz) -> begin
sz
end
| uu____8858 -> begin
(failwith "impossible")
end))
in (

let uu____8864 = (

let uu____8869 = (unboxBitVec sz t1)
in (

let uu____8870 = (unboxBitVec sz t2)
in ((uu____8869), (uu____8870))))
in (mkBvUlt uu____8864 t.rng)))
end
| App (Var ("Prims.b2t"), (t1)::[]) -> begin
(

let uu___127_8875 = (unboxBool t1)
in {tm = uu___127_8875.tm; freevars = uu___127_8875.freevars; rng = t.rng})
end
| uu____8876 -> begin
(mkApp (("Valid"), ((t)::[])) t.rng)
end))


let mk_HasType : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasType"), ((v1)::(t)::[])) t.rng))


let mk_HasTypeZ : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasTypeZ"), ((v1)::(t)::[])) t.rng))


let mk_IsTyped : term  ->  term = (fun v1 -> (mkApp (("IsTyped"), ((v1)::[])) norng))


let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v1 t -> (

let uu____8937 = (FStar_Options.unthrottle_inductives ())
in (match (uu____8937) with
| true -> begin
(mk_HasType v1 t)
end
| uu____8940 -> begin
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

let uu____9070 = (

let uu____9071 = (mkApp (("__uu__PartialApp"), ([])) t.rng)
in (mk_ApplyTT uu____9071 t t.rng))
in (FStar_All.pipe_right uu____9070 mk_Valid)))


let mk_String_const : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____9089 = (

let uu____9097 = (

let uu____9100 = (mkInteger' i norng)
in (uu____9100)::[])
in (("FString_const"), (uu____9097)))
in (mkApp uu____9089 r)))


let mk_Precedes : term  ->  term  ->  term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 x3 x4 r -> (

let uu____9131 = (mkApp (("Prims.precedes"), ((x1)::(x2)::(x3)::(x4)::[])) r)
in (FStar_All.pipe_right uu____9131 mk_Valid)))


let mk_LexCons : term  ->  term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 x3 r -> (mkApp (("LexCons"), ((x1)::(x2)::(x3)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
(mkApp (("ZFuel"), ([])) norng)
end
| uu____9176 -> begin
(

let uu____9178 = (

let uu____9186 = (

let uu____9189 = (n_fuel (n1 - (Prims.parse_int "1")))
in (uu____9189)::[])
in (("SFuel"), (uu____9186)))
in (mkApp uu____9178 norng))
end))


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term FStar_Pervasives_Native.option  ->  term FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  term FStar_Pervasives_Native.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (FStar_Pervasives_Native.Some (p11), FStar_Pervasives_Native.Some (p21)) -> begin
(

let uu____9237 = (mkAnd ((p11), (p21)) r)
in FStar_Pervasives_Native.Some (uu____9237))
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

let uu____9300 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l uu____9300)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____9320 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l uu____9320)))


let mk_haseq : term  ->  term = (fun t -> (

let uu____9331 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid uu____9331)))


let dummy_sort : sort = Sort ("Dummy_sort")




