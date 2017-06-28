
open Prims
open FStar_Pervasives
type sort =
| Bool_sort
| Int_sort
| String_sort
| Ref_sort
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
| uu____25 -> begin
false
end))


let uu___is_Int_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int_sort -> begin
true
end
| uu____30 -> begin
false
end))


let uu___is_String_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| String_sort -> begin
true
end
| uu____35 -> begin
false
end))


let uu___is_Ref_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Ref_sort -> begin
true
end
| uu____40 -> begin
false
end))


let uu___is_Term_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Term_sort -> begin
true
end
| uu____45 -> begin
false
end))


let uu___is_Fuel_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fuel_sort -> begin
true
end
| uu____50 -> begin
false
end))


let uu___is_BitVec_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BitVec_sort (_0) -> begin
true
end
| uu____56 -> begin
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
| uu____72 -> begin
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
| uu____94 -> begin
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
| uu____114 -> begin
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
| Ref_sort -> begin
"Ref"
end
| Fuel_sort -> begin
"Fuel"
end
| BitVec_sort (n1) -> begin
(

let uu____128 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ BitVec %s)" uu____128))
end
| Array (s1, s2) -> begin
(

let uu____131 = (strSort s1)
in (

let uu____132 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" uu____131 uu____132)))
end
| Arrow (s1, s2) -> begin
(

let uu____135 = (strSort s1)
in (

let uu____136 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" uu____135 uu____136)))
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
| NatToBv of Prims.int
| ITE
| Var of Prims.string


let uu___is_TrueOp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TrueOp -> begin
true
end
| uu____150 -> begin
false
end))


let uu___is_FalseOp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FalseOp -> begin
true
end
| uu____155 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____160 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____165 -> begin
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
| uu____175 -> begin
false
end))


let uu___is_Iff : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iff -> begin
true
end
| uu____180 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____185 -> begin
false
end))


let uu___is_LT : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LT -> begin
true
end
| uu____190 -> begin
false
end))


let uu___is_LTE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LTE -> begin
true
end
| uu____195 -> begin
false
end))


let uu___is_GT : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GT -> begin
true
end
| uu____200 -> begin
false
end))


let uu___is_GTE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GTE -> begin
true
end
| uu____205 -> begin
false
end))


let uu___is_Add : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Add -> begin
true
end
| uu____210 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____215 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____220 -> begin
false
end))


let uu___is_Mul : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mul -> begin
true
end
| uu____225 -> begin
false
end))


let uu___is_Minus : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Minus -> begin
true
end
| uu____230 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____235 -> begin
false
end))


let uu___is_BvAnd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvAnd -> begin
true
end
| uu____240 -> begin
false
end))


let uu___is_BvXor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvXor -> begin
true
end
| uu____245 -> begin
false
end))


let uu___is_BvOr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvOr -> begin
true
end
| uu____250 -> begin
false
end))


let uu___is_BvShl : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvShl -> begin
true
end
| uu____255 -> begin
false
end))


let uu___is_BvShr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvShr -> begin
true
end
| uu____260 -> begin
false
end))


let uu___is_BvUdiv : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvUdiv -> begin
true
end
| uu____265 -> begin
false
end))


let uu___is_BvMod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvMod -> begin
true
end
| uu____270 -> begin
false
end))


let uu___is_NatToBv : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NatToBv (_0) -> begin
true
end
| uu____276 -> begin
false
end))


let __proj__NatToBv__item___0 : op  ->  Prims.int = (fun projectee -> (match (projectee) with
| NatToBv (_0) -> begin
_0
end))


let uu___is_ITE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ITE -> begin
true
end
| uu____289 -> begin
false
end))


let uu___is_Var : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Var (_0) -> begin
true
end
| uu____295 -> begin
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
| uu____308 -> begin
false
end))


let uu___is_Exists : qop  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exists -> begin
true
end
| uu____313 -> begin
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
| uu____390 -> begin
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
| uu____404 -> begin
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
| uu____420 -> begin
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
| uu____443 -> begin
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
| uu____475 -> begin
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
| uu____519 -> begin
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
| uu____545 -> begin
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
| uu____570 -> begin
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
| uu____665 -> begin
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
| uu____679 -> begin
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
| uu____693 -> begin
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
| uu____807 -> begin
false
end))


let uu___is_DeclFun : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DeclFun (_0) -> begin
true
end
| uu____818 -> begin
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
| uu____853 -> begin
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
| uu____885 -> begin
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
| uu____899 -> begin
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
| uu____913 -> begin
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
| uu____927 -> begin
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
| uu____942 -> begin
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
| uu____958 -> begin
false
end))


let uu___is_Pop : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____963 -> begin
false
end))


let uu___is_CheckSat : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckSat -> begin
true
end
| uu____968 -> begin
false
end))


let uu___is_GetUnsatCore : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetUnsatCore -> begin
true
end
| uu____973 -> begin
false
end))


let uu___is_SetOption : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOption (_0) -> begin
true
end
| uu____981 -> begin
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
| uu____1000 -> begin
false
end))


let uu___is_GetReasonUnknown : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetReasonUnknown -> begin
true
end
| uu____1005 -> begin
false
end))


type decls_t =
decl Prims.list


type error_label =
(fv * Prims.string * FStar_Range.range)


type error_labels =
error_label Prims.list


let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> ((FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst y)))


let fv_sort = (fun x -> (FStar_Pervasives_Native.snd x))


let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match (((x.tm), (y.tm))) with
| (FreeV (x1), FreeV (y1)) -> begin
(fv_eq x1 y1)
end
| uu____1049 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun uu___87_1055 -> (match (uu___87_1055) with
| {tm = FreeV (x); freevars = uu____1057; rng = uu____1058} -> begin
(fv_sort x)
end
| uu____1065 -> begin
(failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun uu___88_1069 -> (match (uu___88_1069) with
| {tm = FreeV (fv); freevars = uu____1071; rng = uu____1072} -> begin
fv
end
| uu____1079 -> begin
(failwith "impossible")
end))


let rec freevars : term  ->  (Prims.string * sort) Prims.list = (fun t -> (match (t.tm) with
| Integer (uu____1090) -> begin
[]
end
| BoundV (uu____1093) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (uu____1103, tms) -> begin
(FStar_List.collect freevars tms)
end
| Quant (uu____1109, uu____1110, uu____1111, uu____1112, t1) -> begin
(freevars t1)
end
| Labeled (t1, uu____1123, uu____1124) -> begin
(freevars t1)
end
| LblPos (t1, uu____1126) -> begin
(freevars t1)
end
| Let (es, body) -> begin
(FStar_List.collect freevars ((body)::es))
end))


let free_variables : term  ->  fvs = (fun t -> (

let uu____1137 = (FStar_ST.read t.freevars)
in (match (uu____1137) with
| FStar_Pervasives_Native.Some (b) -> begin
b
end
| FStar_Pervasives_Native.None -> begin
(

let fvs = (

let uu____1160 = (freevars t)
in (FStar_Util.remove_dups fv_eq uu____1160))
in ((FStar_ST.write t.freevars (FStar_Pervasives_Native.Some (fvs)));
fvs;
))
end)))


let qop_to_string : qop  ->  Prims.string = (fun uu___89_1173 -> (match (uu___89_1173) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun uu___90_1177 -> (match (uu___90_1177) with
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
| NatToBv (n1) -> begin
(

let uu____1179 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ int2bv %s)" uu____1179))
end
| Var (s) -> begin
s
end))


let weightToSmt : Prims.int FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___91_1185 -> (match (uu___91_1185) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (i) -> begin
(

let uu____1188 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" uu____1188))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____1196 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" uu____1196))
end
| FreeV (x) -> begin
(

let uu____1200 = (

let uu____1201 = (strSort (FStar_Pervasives_Native.snd x))
in (Prims.strcat ":" uu____1201))
in (Prims.strcat (FStar_Pervasives_Native.fst x) uu____1200))
end
| App (op, tms) -> begin
(

let uu____1206 = (

let uu____1207 = (op_to_string op)
in (

let uu____1208 = (

let uu____1209 = (

let uu____1210 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right uu____1210 (FStar_String.concat " ")))
in (Prims.strcat uu____1209 ")"))
in (Prims.strcat uu____1207 uu____1208)))
in (Prims.strcat "(" uu____1206))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____1216 = (hash_of_term t1)
in (

let uu____1217 = (

let uu____1218 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 uu____1218))
in (Prims.strcat uu____1216 uu____1217)))
end
| LblPos (t1, r) -> begin
(

let uu____1221 = (

let uu____1222 = (hash_of_term t1)
in (Prims.strcat uu____1222 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " uu____1221))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let uu____1236 = (

let uu____1237 = (

let uu____1238 = (

let uu____1239 = (

let uu____1240 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right uu____1240 (FStar_String.concat " ")))
in (

let uu____1243 = (

let uu____1244 = (

let uu____1245 = (hash_of_term body)
in (

let uu____1246 = (

let uu____1247 = (

let uu____1248 = (weightToSmt wopt)
in (

let uu____1249 = (

let uu____1250 = (

let uu____1251 = (

let uu____1252 = (FStar_All.pipe_right pats (FStar_List.map (fun pats1 -> (

let uu____1262 = (FStar_List.map hash_of_term pats1)
in (FStar_All.pipe_right uu____1262 (FStar_String.concat " "))))))
in (FStar_All.pipe_right uu____1252 (FStar_String.concat "; ")))
in (Prims.strcat uu____1251 "))"))
in (Prims.strcat " " uu____1250))
in (Prims.strcat uu____1248 uu____1249)))
in (Prims.strcat " " uu____1247))
in (Prims.strcat uu____1245 uu____1246)))
in (Prims.strcat ")(! " uu____1244))
in (Prims.strcat uu____1239 uu____1243)))
in (Prims.strcat " (" uu____1238))
in (Prims.strcat (qop_to_string qop) uu____1237))
in (Prims.strcat "(" uu____1236))
end
| Let (es, body) -> begin
(

let uu____1270 = (

let uu____1271 = (

let uu____1272 = (FStar_List.map hash_of_term es)
in (FStar_All.pipe_right uu____1272 (FStar_String.concat " ")))
in (

let uu____1275 = (

let uu____1276 = (

let uu____1277 = (hash_of_term body)
in (Prims.strcat uu____1277 ")"))
in (Prims.strcat ") " uu____1276))
in (Prims.strcat uu____1271 uu____1275)))
in (Prims.strcat "(let (" uu____1270))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (

let uu____1287 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {tm = t; freevars = uu____1287; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((TrueOp), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((FalseOp), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____1320 = (

let uu____1321 = (FStar_Util.ensure_decimal i)
in Integer (uu____1321))
in (mk uu____1320 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____1330 = (FStar_Util.string_of_int i)
in (mkInteger uu____1330 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun uu____1374 r -> (match (uu____1374) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (TrueOp, uu____1392) -> begin
(mkFalse r)
end
| App (FalseOp, uu____1395) -> begin
(mkTrue r)
end
| uu____1398 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1408 r -> (match (uu____1408) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____1414), uu____1415) -> begin
t2
end
| (uu____1418, App (TrueOp, uu____1419)) -> begin
t1
end
| (App (FalseOp, uu____1422), uu____1423) -> begin
(mkFalse r)
end
| (uu____1426, App (FalseOp, uu____1427)) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (uu____1437, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), uu____1443) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____1447 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1459 r -> (match (uu____1459) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____1465), uu____1466) -> begin
(mkTrue r)
end
| (uu____1469, App (TrueOp, uu____1470)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____1473), uu____1474) -> begin
t2
end
| (uu____1477, App (FalseOp, uu____1478)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (uu____1488, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), uu____1494) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____1498 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1510 r -> (match (uu____1510) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (uu____1516, App (TrueOp, uu____1517)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____1520), uu____1521) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____1524), uu____1525) -> begin
t2
end
| (uu____1528, App (Imp, (t1')::(t2')::[])) -> begin
(

let uu____1532 = (

let uu____1536 = (

let uu____1538 = (mkAnd ((t1), (t1')) r)
in (uu____1538)::(t2')::[])
in ((Imp), (uu____1536)))
in (mkApp' uu____1532 r))
end
| uu____1540 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op uu____1556 r -> (match (uu____1556) with
| (t1, t2) -> begin
(mkApp' ((op), ((t1)::(t2)::[])) r)
end))


let mkMinus : term  ->  FStar_Range.range  ->  term = (fun t r -> (mkApp' ((Minus), ((t)::[])) r))


let mkNatToBv : Prims.int  ->  term  ->  FStar_Range.range  ->  term = (fun sz t r -> (mkApp' ((NatToBv (sz)), ((t)::[])) r))


let mkBvAnd : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvAnd)


let mkBvXor : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvXor)


let mkBvOr : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvOr)


let mkBvShl : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____1621 r -> (match (uu____1621) with
| (t1, t2) -> begin
(

let uu____1627 = (

let uu____1631 = (

let uu____1633 = (

let uu____1635 = (mkNatToBv sz t2 r)
in (uu____1635)::[])
in (t1)::uu____1633)
in ((BvShl), (uu____1631)))
in (mkApp' uu____1627 r))
end))


let mkBvShr : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____1649 r -> (match (uu____1649) with
| (t1, t2) -> begin
(

let uu____1655 = (

let uu____1659 = (

let uu____1661 = (

let uu____1663 = (mkNatToBv sz t2 r)
in (uu____1663)::[])
in (t1)::uu____1661)
in ((BvShr), (uu____1659)))
in (mkApp' uu____1655 r))
end))


let mkBvUdiv : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvUdiv)


let mkBvMod : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvMod)


let mkIff : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Iff)


let mkEq : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Eq)


let mkLT : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op LT)


let mkLTE : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op LTE)


let mkGT : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op GT)


let mkGTE : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op GTE)


let mkAdd : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Add)


let mkSub : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Sub)


let mkDiv : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Div)


let mkMul : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Mul)


let mkMod : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Mod)


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun uu____1778 r -> (match (uu____1778) with
| (t1, t2, t3) -> begin
(match (t1.tm) with
| App (TrueOp, uu____1786) -> begin
t2
end
| App (FalseOp, uu____1789) -> begin
t3
end
| uu____1792 -> begin
(match (((t2.tm), (t3.tm))) with
| (App (TrueOp, uu____1793), App (TrueOp, uu____1794)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____1799), uu____1800) -> begin
(

let uu____1803 = (

let uu____1806 = (mkNot t1 t1.rng)
in ((uu____1806), (t3)))
in (mkImp uu____1803 r))
end
| (uu____1807, App (TrueOp, uu____1808)) -> begin
(mkImp ((t1), (t2)) r)
end
| (uu____1811, uu____1812) -> begin
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


let mkQuant : (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1846 r -> (match (uu____1846) with
| (qop, pats, wopt, vars, body) -> begin
(match (((FStar_List.length vars) = (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____1874 -> begin
(match (body.tm) with
| App (TrueOp, uu____1875) -> begin
body
end
| uu____1878 -> begin
(mk (Quant (((qop), (pats), (wopt), (vars), (body)))) r)
end)
end)
end))


let mkLet : (term Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1892 r -> (match (uu____1892) with
| (es, body) -> begin
(match (((FStar_List.length es) = (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____1905 -> begin
(mk (Let (((es), (body)))) r)
end)
end))


let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (

let nvars = (FStar_List.length fvs)
in (

let index_of = (fun fv -> (

let uu____1925 = (FStar_Util.try_find_index (fv_eq fv) fvs)
in (match (uu____1925) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((nvars - (i + (Prims.parse_int "1"))))
end)))
in (

let rec aux = (fun ix t1 -> (

let uu____1942 = (FStar_ST.read t1.freevars)
in (match (uu____1942) with
| FStar_Pervasives_Native.Some ([]) -> begin
t1
end
| uu____1958 -> begin
(match (t1.tm) with
| Integer (uu____1963) -> begin
t1
end
| BoundV (uu____1964) -> begin
t1
end
| FreeV (x) -> begin
(

let uu____1968 = (index_of x)
in (match (uu____1968) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (i) -> begin
(mkBoundV (i + ix) t1.rng)
end))
end
| App (op, tms) -> begin
(

let uu____1975 = (

let uu____1979 = (FStar_List.map (aux ix) tms)
in ((op), (uu____1979)))
in (mkApp' uu____1975 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____1985 = (

let uu____1986 = (

let uu____1990 = (aux ix t2)
in ((uu____1990), (r1), (r2)))
in Labeled (uu____1986))
in (mk uu____1985 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____1993 = (

let uu____1994 = (

let uu____1997 = (aux ix t2)
in ((uu____1997), (r)))
in LblPos (uu____1994))
in (mk uu____1993 t2.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n1 = (FStar_List.length vars)
in (

let uu____2014 = (

let uu____2024 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n1)))))
in (

let uu____2037 = (aux (ix + n1) body)
in ((qop), (uu____2024), (wopt), (vars), (uu____2037))))
in (mkQuant uu____2014 t1.rng)))
end
| Let (es, body) -> begin
(

let uu____2050 = (FStar_List.fold_left (fun uu____2062 e -> (match (uu____2062) with
| (ix1, l) -> begin
(

let uu____2074 = (

let uu____2076 = (aux ix1 e)
in (uu____2076)::l)
in (((ix1 + (Prims.parse_int "1"))), (uu____2074)))
end)) ((ix), ([])) es)
in (match (uu____2050) with
| (ix1, es_rev) -> begin
(

let uu____2083 = (

let uu____2087 = (aux ix1 body)
in (((FStar_List.rev es_rev)), (uu____2087)))
in (mkLet uu____2083 t1.rng))
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
| Integer (uu____2111) -> begin
t1
end
| FreeV (uu____2112) -> begin
t1
end
| BoundV (i) -> begin
(match ((((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1))) with
| true -> begin
(FStar_List.nth tms1 (i - shift))
end
| uu____2120 -> begin
t1
end)
end
| App (op, tms2) -> begin
(

let uu____2125 = (

let uu____2129 = (FStar_List.map (aux shift) tms2)
in ((op), (uu____2129)))
in (mkApp' uu____2125 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____2135 = (

let uu____2136 = (

let uu____2140 = (aux shift t2)
in ((uu____2140), (r1), (r2)))
in Labeled (uu____2136))
in (mk uu____2135 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____2143 = (

let uu____2144 = (

let uu____2147 = (aux shift t2)
in ((uu____2147), (r)))
in LblPos (uu____2144))
in (mk uu____2143 t2.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift1 = (shift + m)
in (

let uu____2169 = (

let uu____2179 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift1))))
in (

let uu____2188 = (aux shift1 body)
in ((qop), (uu____2179), (wopt), (vars), (uu____2188))))
in (mkQuant uu____2169 t1.rng))))
end
| Let (es, body) -> begin
(

let uu____2197 = (FStar_List.fold_left (fun uu____2209 e -> (match (uu____2209) with
| (ix, es1) -> begin
(

let uu____2221 = (

let uu____2223 = (aux shift e)
in (uu____2223)::es1)
in (((shift + (Prims.parse_int "1"))), (uu____2221)))
end)) ((shift), ([])) es)
in (match (uu____2197) with
| (shift1, es_rev) -> begin
(

let uu____2230 = (

let uu____2234 = (aux shift1 body)
in (((FStar_List.rev es_rev)), (uu____2234)))
in (mkLet uu____2230 t1.rng))
end))
end))
in (aux (Prims.parse_int "0") t)))))


let subst : term  ->  fv  ->  term  ->  term = (fun t fv s -> (

let uu____2248 = (abstr ((fv)::[]) t)
in (inst ((s)::[]) uu____2248)))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fv Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____2263 -> (match (uu____2263) with
| (qop, pats, wopt, vars, body) -> begin
(

let uu____2288 = (

let uu____2298 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (

let uu____2307 = (FStar_List.map fv_sort vars)
in (

let uu____2311 = (abstr vars body)
in ((qop), (uu____2298), (wopt), (uu____2307), (uu____2311)))))
in (mkQuant uu____2288))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____2330 r -> (match (uu____2330) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)) r)
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____2369 r -> (match (uu____2369) with
| (pats, wopt, vars, body) -> begin
(

let uu____2388 = (mkQuant' ((Forall), (pats), (wopt), (vars), (body)))
in (uu____2388 r))
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____2405 r -> (match (uu____2405) with
| (pats, vars, body) -> begin
(

let uu____2419 = (mkQuant' ((Forall), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
in (uu____2419 r))
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____2436 r -> (match (uu____2436) with
| (pats, vars, body) -> begin
(

let uu____2450 = (mkQuant' ((Exists), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
in (uu____2450 r))
end))


let mkLet' : ((fv * term) Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____2467 r -> (match (uu____2467) with
| (bindings, body) -> begin
(

let uu____2482 = (FStar_List.split bindings)
in (match (uu____2482) with
| (vars, es) -> begin
(

let uu____2493 = (

let uu____2497 = (abstr vars body)
in ((es), (uu____2497)))
in (mkLet uu____2493 r))
end))
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun uu____2510 -> (match (uu____2510) with
| (nm, vars, s, tm, c) -> begin
(

let uu____2530 = (

let uu____2537 = (FStar_List.map fv_sort vars)
in (

let uu____2541 = (abstr vars tm)
in ((nm), (uu____2537), (s), (uu____2541), (c))))
in DefineFun (uu____2530))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (

let uu____2547 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" uu____2547)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun uu____2556 id -> (match (uu____2556) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (

let a = (

let uu____2564 = (

let uu____2565 = (

let uu____2568 = (mkInteger' id norng)
in (

let uu____2569 = (

let uu____2570 = (

let uu____2574 = (constr_id_of_sort sort)
in (

let uu____2575 = (

let uu____2577 = (mkApp ((tok_name), ([])) norng)
in (uu____2577)::[])
in ((uu____2574), (uu____2575))))
in (mkApp uu____2570 norng))
in ((uu____2568), (uu____2569))))
in (mkEq uu____2565 norng))
in {assumption_term = uu____2564; assumption_caption = FStar_Pervasives_Native.Some ("fresh token"); assumption_name = a_name; assumption_fact_ids = []})
in Assume (a)))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun uu____2588 -> (match (uu____2588) with
| (name, arg_sorts, sort, id) -> begin
(

let id1 = (FStar_Util.string_of_int id)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (

let uu____2610 = (

let uu____2613 = (

let uu____2614 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____2614))
in ((uu____2613), (s)))
in (mkFreeV uu____2610 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (

let uu____2620 = (

let uu____2624 = (constr_id_of_sort sort)
in ((uu____2624), ((capp)::[])))
in (mkApp uu____2620 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (

let a = (

let uu____2628 = (

let uu____2629 = (

let uu____2635 = (

let uu____2636 = (

let uu____2639 = (mkInteger id1 norng)
in ((uu____2639), (cid_app)))
in (mkEq uu____2636 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____2635)))
in (mkForall uu____2629 norng))
in {assumption_term = uu____2628; assumption_caption = FStar_Pervasives_Native.Some ("Consrtructor distinct"); assumption_name = a_name; assumption_fact_ids = []})
in Assume (a))))))))
end))


let injective_constructor : (Prims.string * constructor_field Prims.list * sort)  ->  decls_t = (fun uu____2652 -> (match (uu____2652) with
| (name, fields, sort) -> begin
(

let n_bvars = (FStar_List.length fields)
in (

let bvar_name = (fun i -> (

let uu____2669 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____2669)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (

let uu____2689 = (

let uu____2692 = (bvar_name i)
in ((uu____2692), (s)))
in (mkFreeV uu____2689)))
in (

let bvars = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____2707 -> (match (uu____2707) with
| (uu____2711, s, uu____2713) -> begin
(

let uu____2714 = (bvar i s)
in (uu____2714 norng))
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let uu____2721 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____2740 -> (match (uu____2740) with
| (name1, s, projectible) -> begin
(

let cproj_app = (mkApp ((name1), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((name1), ((sort)::[]), (s), (FStar_Pervasives_Native.Some ("Projector"))))
in (match (projectible) with
| true -> begin
(

let a = (

let uu____2755 = (

let uu____2756 = (

let uu____2762 = (

let uu____2763 = (

let uu____2766 = (

let uu____2767 = (bvar i s)
in (uu____2767 norng))
in ((cproj_app), (uu____2766)))
in (mkEq uu____2763 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____2762)))
in (mkForall uu____2756 norng))
in {assumption_term = uu____2755; assumption_caption = FStar_Pervasives_Native.Some ("Projection inverse"); assumption_name = (Prims.strcat "projection_inverse_" name1); assumption_fact_ids = []})
in (proj_name)::(Assume (a))::[])
end
| uu____2775 -> begin
(proj_name)::[]
end)))
end))))
in (FStar_All.pipe_right uu____2721 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun uu____2782 -> (match (uu____2782) with
| (name, fields, sort, id, injective) -> begin
(

let injective1 = (injective || true)
in (

let field_sorts = (FStar_All.pipe_right fields (FStar_List.map (fun uu____2802 -> (match (uu____2802) with
| (uu____2806, sort1, uu____2808) -> begin
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

let uu____2821 = (

let uu____2824 = (

let uu____2825 = (

let uu____2829 = (constr_id_of_sort sort)
in ((uu____2829), ((xx)::[])))
in (mkApp uu____2825 norng))
in (

let uu____2831 = (

let uu____2832 = (FStar_Util.string_of_int id)
in (mkInteger uu____2832 norng))
in ((uu____2824), (uu____2831))))
in (mkEq uu____2821 norng))
in (

let uu____2833 = (

let uu____2841 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____2870 -> (match (uu____2870) with
| (proj, s, projectible) -> begin
(match (projectible) with
| true -> begin
(

let uu____2887 = (mkApp ((proj), ((xx)::[])) norng)
in ((uu____2887), ([])))
end
| uu____2894 -> begin
(

let fi = (

let uu____2898 = (

let uu____2899 = (FStar_Util.string_of_int i)
in (Prims.strcat "f_" uu____2899))
in ((uu____2898), (s)))
in (

let uu____2900 = (mkFreeV fi norng)
in ((uu____2900), ((fi)::[]))))
end)
end))))
in (FStar_All.pipe_right uu____2841 FStar_List.split))
in (match (uu____2833) with
| (proj_terms, ex_vars) -> begin
(

let ex_vars1 = (FStar_List.flatten ex_vars)
in (

let disc_inv_body = (

let uu____2943 = (

let uu____2946 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (uu____2946)))
in (mkEq uu____2943 norng))
in (

let disc_inv_body1 = (match (ex_vars1) with
| [] -> begin
disc_inv_body
end
| uu____2951 -> begin
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
| uu____2973 -> begin
[]
end)
in (

let uu____2974 = (

let uu____2976 = (

let uu____2977 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (uu____2977))
in (uu____2976)::(cdecl)::(cid)::projs)
in (

let uu____2978 = (

let uu____2980 = (

let uu____2982 = (

let uu____2983 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (uu____2983))
in (uu____2982)::[])
in (FStar_List.append ((disc)::[]) uu____2980))
in (FStar_List.append uu____2974 uu____2978)))))))))
end))


let name_binders_inner : Prims.string FStar_Pervasives_Native.option  ->  (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun prefix_opt outer_names start sorts -> (

let uu____3017 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun uu____3050 s -> (match (uu____3050) with
| (names1, binders, n1) -> begin
(

let prefix1 = (match (s) with
| Term_sort -> begin
"@x"
end
| uu____3078 -> begin
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

let uu____3082 = (FStar_Util.string_of_int n1)
in (Prims.strcat prefix2 uu____3082))
in (

let names2 = (((nm), (s)))::names1
in (

let b = (

let uu____3090 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm uu____3090))
in ((names2), ((b)::binders), ((n1 + (Prims.parse_int "1")))))))))
end)) ((outer_names), ([]), (start))))
in (match (uu____3017) with
| (names1, binders, n1) -> begin
((names1), ((FStar_List.rev binders)), (n1))
end)))


let name_macro_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let uu____3133 = (name_binders_inner (FStar_Pervasives_Native.Some ("__")) [] (Prims.parse_int "0") sorts)
in (match (uu____3133) with
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
| uu____3188 -> begin
(

let uu____3189 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "%s.%s" enclosing_name uu____3189))
end);
))))
in (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (uu____3216); freevars = uu____3217; rng = uu____3218})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| uu____3226 -> begin
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

let uu____3262 = (FStar_List.nth names1 i)
in (FStar_All.pipe_right uu____3262 FStar_Pervasives_Native.fst))
end
| FreeV (x) -> begin
(FStar_Pervasives_Native.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(

let uu____3272 = (op_to_string op)
in (

let uu____3273 = (

let uu____3274 = (FStar_List.map (aux1 n1 names1) tms)
in (FStar_All.pipe_right uu____3274 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" uu____3272 uu____3273)))
end
| Labeled (t2, uu____3278, uu____3279) -> begin
(aux1 n1 names1 t2)
end
| LblPos (t2, s) -> begin
(

let uu____3282 = (aux1 n1 names1 t2)
in (FStar_Util.format2 "(! %s :lblpos %s)" uu____3282 s))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let qid = (next_qid ())
in (

let uu____3297 = (name_binders_inner FStar_Pervasives_Native.None names1 n1 sorts)
in (match (uu____3297) with
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
| uu____3325 -> begin
(

let uu____3328 = (FStar_All.pipe_right pats1 (FStar_List.map (fun pats2 -> (

let uu____3338 = (

let uu____3339 = (FStar_List.map (fun p -> (

let uu____3344 = (aux1 n2 names2 p)
in (FStar_Util.format1 "%s" uu____3344))) pats2)
in (FStar_String.concat " " uu____3339))
in (FStar_Util.format1 "\n:pattern (%s)" uu____3338)))))
in (FStar_All.pipe_right uu____3328 (FStar_String.concat "\n")))
end)
in (

let uu____3346 = (

let uu____3348 = (

let uu____3350 = (

let uu____3352 = (aux1 n2 names2 body)
in (

let uu____3353 = (

let uu____3355 = (weightToSmt wopt)
in (uu____3355)::(pats_str)::(qid)::[])
in (uu____3352)::uu____3353))
in (binders1)::uu____3350)
in ((qop_to_string qop))::uu____3348)
in (FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))" uu____3346)))))
end)))
end
| Let (es, body) -> begin
(

let uu____3360 = (FStar_List.fold_left (fun uu____3383 e -> (match (uu____3383) with
| (names0, binders, n0) -> begin
(

let nm = (

let uu____3411 = (FStar_Util.string_of_int n0)
in (Prims.strcat "@lb" uu____3411))
in (

let names01 = (((nm), (Term_sort)))::names0
in (

let b = (

let uu____3419 = (aux1 n1 names1 e)
in (FStar_Util.format2 "(%s %s)" nm uu____3419))
in ((names01), ((b)::binders), ((n0 + (Prims.parse_int "1")))))))
end)) ((names1), ([]), (n1)) es)
in (match (uu____3360) with
| (names2, binders, n2) -> begin
(

let uu____3437 = (aux1 n2 names2 body)
in (FStar_Util.format2 "(let (%s)\n%s)" (FStar_String.concat " " binders) uu____3437))
end))
end)))
and aux = (fun depth n1 names1 t1 -> (

let s = (aux' depth n1 names1 t1)
in (match ((t1.rng <> norng)) with
| true -> begin
(

let uu____3444 = (FStar_Range.string_of_range t1.rng)
in (

let uu____3445 = (FStar_Range.string_of_use_range t1.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____3444 uu____3445 s)))
end
| uu____3446 -> begin
s
end)))
in (aux (Prims.parse_int "0") (Prims.parse_int "0") [] t)))))


let caption_to_string : Prims.string FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___92_3451 -> (match (uu___92_3451) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let uu____3454 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(failwith "Impossible")
end
| (hd1)::[] -> begin
((hd1), (""))
end
| (hd1)::uu____3463 -> begin
((hd1), ("..."))
end)
in (match (uu____3454) with
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

let uu____3480 = (FStar_Options.log_queries ())
in (match (uu____3480) with
| true -> begin
(

let uu____3481 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun uu___93_3484 -> (match (uu___93_3484) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" uu____3481))
end
| uu____3489 -> begin
""
end))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (

let uu____3498 = (caption_to_string c)
in (

let uu____3499 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____3498 f (FStar_String.concat " " l) uu____3499))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let uu____3507 = (name_macro_binders arg_sorts)
in (match (uu____3507) with
| (names1, binders) -> begin
(

let body1 = (

let uu____3525 = (FStar_List.map (fun x -> (mkFreeV x norng)) names1)
in (inst uu____3525 body))
in (

let uu____3533 = (caption_to_string c)
in (

let uu____3534 = (strSort retsort)
in (

let uu____3535 = (termToSmt (escape f) body1)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____3533 f (FStar_String.concat " " binders) uu____3534 uu____3535)))))
end))
end
| Assume (a) -> begin
(

let fact_ids_to_string = (fun ids -> (FStar_All.pipe_right ids (FStar_List.map (fun uu___94_3548 -> (match (uu___94_3548) with
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

let uu____3553 = (FStar_Options.log_queries ())
in (match (uu____3553) with
| true -> begin
(

let uu____3554 = (

let uu____3555 = (fact_ids_to_string a.assumption_fact_ids)
in (FStar_String.concat "; " uu____3555))
in (FStar_Util.format1 ";;; Fact-ids: %s\n" uu____3554))
end
| uu____3557 -> begin
""
end))
in (

let n1 = (escape a.assumption_name)
in (

let uu____3559 = (caption_to_string a.assumption_caption)
in (

let uu____3560 = (termToSmt n1 a.assumption_term)
in (FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____3559 fids uu____3560 n1))))))
end
| Eval (t) -> begin
(

let uu____3562 = (termToSmt "eval" t)
in (FStar_Util.format1 "(eval %s)" uu____3562))
end
| Echo (s) -> begin
(FStar_Util.format1 "(echo \"%s\")" s)
end
| RetainAssumptions (uu____3564) -> begin
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

let basic = (Prims.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))")
in (

let constrs = ((("FString_const"), (((("FString_const_proj_0"), (Int_sort), (true)))::[]), (String_sort), ((Prims.parse_int "0")), (true)))::((("Tm_type"), ([]), (Term_sort), ((Prims.parse_int "2")), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "3")), (false)))::((("Tm_uvar"), (((("Tm_uvar_fst"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "5")), (true)))::((("Tm_unit"), ([]), (Term_sort), ((Prims.parse_int "6")), (true)))::((("BoxInt"), (((("BoxInt_proj_0"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "7")), (true)))::((("BoxBool"), (((("BoxBool_proj_0"), (Bool_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "8")), (true)))::((("BoxString"), (((("BoxString_proj_0"), (String_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "9")), (true)))::((("BoxRef"), (((("BoxRef_proj_0"), (Ref_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "10")), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort), (true)))::((("LexCons_1"), (Term_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "11")), (true)))::[]
in (

let bcons = (

let uu____3768 = (

let uu____3770 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right uu____3770 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right uu____3768 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mkBvConstructor : Prims.int  ->  decls_t = (fun sz -> (

let uu____3781 = (

let uu____3791 = (

let uu____3792 = (FStar_Util.string_of_int sz)
in (FStar_Util.format1 "BoxBitVec%s" uu____3792))
in (

let uu____3793 = (

let uu____3798 = (

let uu____3802 = (

let uu____3803 = (FStar_Util.string_of_int sz)
in (FStar_Util.format1 "BoxBitVec%s_proj_0" uu____3803))
in ((uu____3802), (BitVec_sort (sz)), (true)))
in (uu____3798)::[])
in ((uu____3791), (uu____3793), (Term_sort), (((Prims.parse_int "12") + sz)), (true))))
in (FStar_All.pipe_right uu____3781 constructor_to_decl)))


let mk_Range_const : term = (mkApp (("Range_const"), ([])) norng)


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____3846 = (

let uu____3850 = (

let uu____3852 = (mkInteger' i norng)
in (uu____3852)::[])
in (("Tm_uvar"), (uu____3850)))
in (mkApp uu____3846 r)))


let mk_Term_unit : term = (mkApp (("Tm_unit"), ([])) norng)


let elim_box : Prims.bool  ->  Prims.string  ->  Prims.string  ->  term  ->  term = (fun cond u v1 t -> (match (t.tm) with
| App (Var (v'), (t1)::[]) when ((v1 = v') && cond) -> begin
t1
end
| uu____3874 -> begin
(mkApp ((u), ((t)::[])) t.rng)
end))


let maybe_elim_box : Prims.string  ->  Prims.string  ->  term  ->  term = (fun u v1 t -> (

let uu____3888 = (FStar_Options.smtencoding_elim_box ())
in (elim_box uu____3888 u v1 t)))


let boxInt : term  ->  term = (fun t -> (maybe_elim_box "BoxInt" "BoxInt_proj_0" t))


let unboxInt : term  ->  term = (fun t -> (maybe_elim_box "BoxInt_proj_0" "BoxInt" t))


let boxBool : term  ->  term = (fun t -> (maybe_elim_box "BoxBool" "BoxBool_proj_0" t))


let unboxBool : term  ->  term = (fun t -> (maybe_elim_box "BoxBool_proj_0" "BoxBool" t))


let boxString : term  ->  term = (fun t -> (maybe_elim_box "BoxString" "BoxString_proj_0" t))


let unboxString : term  ->  term = (fun t -> (maybe_elim_box "BoxString_proj_0" "BoxString" t))


let boxRef : term  ->  term = (fun t -> (maybe_elim_box "BoxRef" "BoxRef_proj_0" t))


let unboxRef : term  ->  term = (fun t -> (maybe_elim_box "BoxRef_proj_0" "BoxRef" t))


let boxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let boxOfSize = (

let uu____3930 = (FStar_Util.string_of_int sz)
in (FStar_Util.format1 "BoxBitVec%s" uu____3930))
in (elim_box true boxOfSize (Prims.strcat boxOfSize "_proj_0") t)))


let unboxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let boxOfSize = (

let uu____3940 = (FStar_Util.string_of_int sz)
in (FStar_Util.format1 "BoxBitVec%s" uu____3940))
in (elim_box true (Prims.strcat boxOfSize "_proj_0") boxOfSize t)))


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
| Ref_sort -> begin
(boxRef t)
end
| BitVec_sort (sz) -> begin
(boxBitVec sz t)
end
| uu____3950 -> begin
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
| Ref_sort -> begin
(unboxRef t)
end
| BitVec_sort (sz) -> begin
(unboxBitVec sz t)
end
| uu____3960 -> begin
(FStar_Pervasives.raise FStar_Util.Impos)
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (uu____3970)::(t1)::(t2)::[]); freevars = uu____3973; rng = uu____3974})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (uu____3981)::(t1)::(t2)::[]); freevars = uu____3984; rng = uu____3985})::[]) -> begin
(

let uu____3992 = (mkEq ((t1), (t2)) norng)
in (mkNot uu____3992 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = uu____3995; rng = uu____3996})::[]) -> begin
(

let uu____4003 = (

let uu____4006 = (unboxInt t1)
in (

let uu____4007 = (unboxInt t2)
in ((uu____4006), (uu____4007))))
in (mkLTE uu____4003 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = uu____4010; rng = uu____4011})::[]) -> begin
(

let uu____4018 = (

let uu____4021 = (unboxInt t1)
in (

let uu____4022 = (unboxInt t2)
in ((uu____4021), (uu____4022))))
in (mkLT uu____4018 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = uu____4025; rng = uu____4026})::[]) -> begin
(

let uu____4033 = (

let uu____4036 = (unboxInt t1)
in (

let uu____4037 = (unboxInt t2)
in ((uu____4036), (uu____4037))))
in (mkGTE uu____4033 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = uu____4040; rng = uu____4041})::[]) -> begin
(

let uu____4048 = (

let uu____4051 = (unboxInt t1)
in (

let uu____4052 = (unboxInt t2)
in ((uu____4051), (uu____4052))))
in (mkGT uu____4048 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = uu____4055; rng = uu____4056})::[]) -> begin
(

let uu____4063 = (

let uu____4066 = (unboxBool t1)
in (

let uu____4067 = (unboxBool t2)
in ((uu____4066), (uu____4067))))
in (mkAnd uu____4063 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = uu____4070; rng = uu____4071})::[]) -> begin
(

let uu____4078 = (

let uu____4081 = (unboxBool t1)
in (

let uu____4082 = (unboxBool t2)
in ((uu____4081), (uu____4082))))
in (mkOr uu____4078 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t1)::[]); freevars = uu____4084; rng = uu____4085})::[]) -> begin
(

let uu____4092 = (unboxBool t1)
in (mkNot uu____4092 t1.rng))
end
| App (Var ("Prims.b2t"), (t1)::[]) -> begin
(

let uu___95_4095 = (unboxBool t1)
in {tm = uu___95_4095.tm; freevars = uu___95_4095.freevars; rng = t.rng})
end
| uu____4098 -> begin
(mkApp (("Valid"), ((t)::[])) t.rng)
end))


let mk_HasType : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasType"), ((v1)::(t)::[])) t.rng))


let mk_HasTypeZ : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasTypeZ"), ((v1)::(t)::[])) t.rng))


let mk_IsTyped : term  ->  term = (fun v1 -> (mkApp (("IsTyped"), ((v1)::[])) norng))


let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v1 t -> (

let uu____4135 = (FStar_Options.unthrottle_inductives ())
in (match (uu____4135) with
| true -> begin
(mk_HasType v1 t)
end
| uu____4136 -> begin
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

let uu____4217 = (

let uu____4221 = (

let uu____4223 = (mkInteger' i norng)
in (uu____4223)::[])
in (("FString_const"), (uu____4221)))
in (mkApp uu____4217 r)))


let mk_Precedes : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (

let uu____4237 = (mkApp (("Precedes"), ((x1)::(x2)::[])) r)
in (FStar_All.pipe_right uu____4237 mk_Valid)))


let mk_LexCons : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (mkApp (("LexCons"), ((x1)::(x2)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n1 -> (match ((n1 = (Prims.parse_int "0"))) with
| true -> begin
(mkApp (("ZFuel"), ([])) norng)
end
| uu____4257 -> begin
(

let uu____4258 = (

let uu____4262 = (

let uu____4264 = (n_fuel (n1 - (Prims.parse_int "1")))
in (uu____4264)::[])
in (("SFuel"), (uu____4262)))
in (mkApp uu____4258 norng))
end))


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term FStar_Pervasives_Native.option  ->  term FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  term FStar_Pervasives_Native.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (FStar_Pervasives_Native.Some (p11), FStar_Pervasives_Native.Some (p21)) -> begin
(

let uu____4290 = (mkAnd ((p11), (p21)) r)
in FStar_Pervasives_Native.Some (uu____4290))
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

let uu____4330 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l uu____4330)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____4345 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l uu____4345)))


let mk_haseq : term  ->  term = (fun t -> (

let uu____4354 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid uu____4354)))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n1) -> begin
(FStar_Util.format1 "(Integer %s)" n1)
end
| BoundV (n1) -> begin
(

let uu____4368 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(BoundV %s)" uu____4368))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv))
end
| App (op, l) -> begin
(

let uu____4376 = (op_to_string op)
in (

let uu____4377 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" uu____4376 uu____4377)))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____4381 = (print_smt_term t1)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 uu____4381))
end
| LblPos (t1, s) -> begin
(

let uu____4384 = (print_smt_term t1)
in (FStar_Util.format2 "(LblPos %s %s)" s uu____4384))
end
| Quant (qop, l, uu____4387, uu____4388, t1) -> begin
(

let uu____4398 = (print_smt_term_list_list l)
in (

let uu____4399 = (print_smt_term t1)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4398 uu____4399)))
end
| Let (es, body) -> begin
(

let uu____4404 = (print_smt_term_list es)
in (

let uu____4405 = (print_smt_term body)
in (FStar_Util.format2 "(let %s %s)" uu____4404 uu____4405)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (

let uu____4408 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right uu____4408 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l1 -> (

let uu____4421 = (

let uu____4422 = (

let uu____4423 = (print_smt_term_list l1)
in (Prims.strcat uu____4423 " ] "))
in (Prims.strcat "; [ " uu____4422))
in (Prims.strcat s uu____4421))) "" l))




