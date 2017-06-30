
open Prims
open FStar_Pervasives
type sort =
| Bool_sort
| Int_sort
| String_sort
| Ref_sort
| Term_sort
| Fuel_sort
| Array of (sort * sort)
| Arrow of (sort * sort)
| Sort of Prims.string


let uu___is_Bool_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool_sort -> begin
true
end
| uu____20 -> begin
false
end))


let uu___is_Int_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int_sort -> begin
true
end
| uu____24 -> begin
false
end))


let uu___is_String_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| String_sort -> begin
true
end
| uu____28 -> begin
false
end))


let uu___is_Ref_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Ref_sort -> begin
true
end
| uu____32 -> begin
false
end))


let uu___is_Term_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Term_sort -> begin
true
end
| uu____36 -> begin
false
end))


let uu___is_Fuel_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fuel_sort -> begin
true
end
| uu____40 -> begin
false
end))


let uu___is_Array : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Array (_0) -> begin
true
end
| uu____47 -> begin
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
| uu____67 -> begin
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
| uu____85 -> begin
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
| Array (s1, s2) -> begin
(

let uu____98 = (strSort s1)
in (

let uu____99 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" uu____98 uu____99)))
end
| Arrow (s1, s2) -> begin
(

let uu____102 = (strSort s1)
in (

let uu____103 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" uu____102 uu____103)))
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
| ITE
| Var of Prims.string


let uu___is_TrueOp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TrueOp -> begin
true
end
| uu____112 -> begin
false
end))


let uu___is_FalseOp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FalseOp -> begin
true
end
| uu____116 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____120 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____124 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____128 -> begin
false
end))


let uu___is_Imp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Imp -> begin
true
end
| uu____132 -> begin
false
end))


let uu___is_Iff : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iff -> begin
true
end
| uu____136 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____140 -> begin
false
end))


let uu___is_LT : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LT -> begin
true
end
| uu____144 -> begin
false
end))


let uu___is_LTE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LTE -> begin
true
end
| uu____148 -> begin
false
end))


let uu___is_GT : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GT -> begin
true
end
| uu____152 -> begin
false
end))


let uu___is_GTE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GTE -> begin
true
end
| uu____156 -> begin
false
end))


let uu___is_Add : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Add -> begin
true
end
| uu____160 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____164 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____168 -> begin
false
end))


let uu___is_Mul : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mul -> begin
true
end
| uu____172 -> begin
false
end))


let uu___is_Minus : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Minus -> begin
true
end
| uu____176 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____180 -> begin
false
end))


let uu___is_ITE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ITE -> begin
true
end
| uu____184 -> begin
false
end))


let uu___is_Var : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Var (_0) -> begin
true
end
| uu____189 -> begin
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
| uu____200 -> begin
false
end))


let uu___is_Exists : qop  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exists -> begin
true
end
| uu____204 -> begin
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
| uu____280 -> begin
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
| uu____292 -> begin
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
| uu____306 -> begin
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
| uu____327 -> begin
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
| uu____357 -> begin
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
| uu____399 -> begin
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
| uu____423 -> begin
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
| uu____446 -> begin
false
end))


let __proj__LblPos__item___0 : term'  ->  (term * Prims.string) = (fun projectee -> (match (projectee) with
| LblPos (_0) -> begin
_0
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
| uu____517 -> begin
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
| uu____529 -> begin
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
| uu____541 -> begin
false
end))


let __proj__Tag__item___0 : fact_db_id  ->  Prims.string = (fun projectee -> (match (projectee) with
| Tag (_0) -> begin
_0
end))

type assumption =
{assumption_term : term; assumption_caption : caption; assumption_name : Prims.string; assumption_fact_ids : fact_db_id Prims.list}

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
| uu____633 -> begin
false
end))


let uu___is_DeclFun : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DeclFun (_0) -> begin
true
end
| uu____643 -> begin
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
| uu____676 -> begin
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
| uu____706 -> begin
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
| uu____718 -> begin
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
| uu____730 -> begin
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
| uu____742 -> begin
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
| uu____755 -> begin
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
| uu____769 -> begin
false
end))


let uu___is_Pop : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____773 -> begin
false
end))


let uu___is_CheckSat : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckSat -> begin
true
end
| uu____777 -> begin
false
end))


let uu___is_GetUnsatCore : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetUnsatCore -> begin
true
end
| uu____781 -> begin
false
end))


let uu___is_SetOption : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOption (_0) -> begin
true
end
| uu____788 -> begin
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
| uu____805 -> begin
false
end))


let uu___is_GetReasonUnknown : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetReasonUnknown -> begin
true
end
| uu____809 -> begin
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
| uu____846 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun uu___85_851 -> (match (uu___85_851) with
| {tm = FreeV (x); freevars = uu____853; rng = uu____854} -> begin
(fv_sort x)
end
| uu____861 -> begin
(failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun uu___86_864 -> (match (uu___86_864) with
| {tm = FreeV (fv); freevars = uu____866; rng = uu____867} -> begin
fv
end
| uu____874 -> begin
(failwith "impossible")
end))


let rec freevars : term  ->  (Prims.string * sort) Prims.list = (fun t -> (match (t.tm) with
| Integer (uu____884) -> begin
[]
end
| BoundV (uu____887) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (uu____897, tms) -> begin
(FStar_List.collect freevars tms)
end
| Quant (uu____903, uu____904, uu____905, uu____906, t1) -> begin
(freevars t1)
end
| Labeled (t1, uu____917, uu____918) -> begin
(freevars t1)
end
| LblPos (t1, uu____920) -> begin
(freevars t1)
end
| Let (es, body) -> begin
(FStar_List.collect freevars ((body)::es))
end))


let free_variables : term  ->  fvs = (fun t -> (

let uu____930 = (FStar_ST.read t.freevars)
in (match (uu____930) with
| FStar_Pervasives_Native.Some (b) -> begin
b
end
| FStar_Pervasives_Native.None -> begin
(

let fvs = (

let uu____953 = (freevars t)
in (FStar_Util.remove_dups fv_eq uu____953))
in ((FStar_ST.write t.freevars (FStar_Pervasives_Native.Some (fvs)));
fvs;
))
end)))


let qop_to_string : qop  ->  Prims.string = (fun uu___87_965 -> (match (uu___87_965) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun uu___88_968 -> (match (uu___88_968) with
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
| Var (s) -> begin
s
end))


let weightToSmt : Prims.int FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___89_973 -> (match (uu___89_973) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (i) -> begin
(

let uu____976 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" uu____976))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____984 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" uu____984))
end
| FreeV (x) -> begin
(

let uu____988 = (

let uu____989 = (strSort (FStar_Pervasives_Native.snd x))
in (Prims.strcat ":" uu____989))
in (Prims.strcat (FStar_Pervasives_Native.fst x) uu____988))
end
| App (op, tms) -> begin
(

let uu____994 = (

let uu____995 = (

let uu____996 = (

let uu____997 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right uu____997 (FStar_String.concat " ")))
in (Prims.strcat uu____996 ")"))
in (Prims.strcat (op_to_string op) uu____995))
in (Prims.strcat "(" uu____994))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____1003 = (hash_of_term t1)
in (

let uu____1004 = (

let uu____1005 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 uu____1005))
in (Prims.strcat uu____1003 uu____1004)))
end
| LblPos (t1, r) -> begin
(

let uu____1008 = (

let uu____1009 = (hash_of_term t1)
in (Prims.strcat uu____1009 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " uu____1008))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let uu____1023 = (

let uu____1024 = (

let uu____1025 = (

let uu____1026 = (

let uu____1027 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right uu____1027 (FStar_String.concat " ")))
in (

let uu____1030 = (

let uu____1031 = (

let uu____1032 = (hash_of_term body)
in (

let uu____1033 = (

let uu____1034 = (

let uu____1035 = (weightToSmt wopt)
in (

let uu____1036 = (

let uu____1037 = (

let uu____1038 = (

let uu____1039 = (FStar_All.pipe_right pats (FStar_List.map (fun pats1 -> (

let uu____1047 = (FStar_List.map hash_of_term pats1)
in (FStar_All.pipe_right uu____1047 (FStar_String.concat " "))))))
in (FStar_All.pipe_right uu____1039 (FStar_String.concat "; ")))
in (Prims.strcat uu____1038 "))"))
in (Prims.strcat " " uu____1037))
in (Prims.strcat uu____1035 uu____1036)))
in (Prims.strcat " " uu____1034))
in (Prims.strcat uu____1032 uu____1033)))
in (Prims.strcat ")(! " uu____1031))
in (Prims.strcat uu____1026 uu____1030)))
in (Prims.strcat " (" uu____1025))
in (Prims.strcat (qop_to_string qop) uu____1024))
in (Prims.strcat "(" uu____1023))
end
| Let (es, body) -> begin
(

let uu____1055 = (

let uu____1056 = (

let uu____1057 = (FStar_List.map hash_of_term es)
in (FStar_All.pipe_right uu____1057 (FStar_String.concat " ")))
in (

let uu____1060 = (

let uu____1061 = (

let uu____1062 = (hash_of_term body)
in (Prims.strcat uu____1062 ")"))
in (Prims.strcat ") " uu____1061))
in (Prims.strcat uu____1056 uu____1060)))
in (Prims.strcat "(let (" uu____1055))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (

let uu____1070 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {tm = t; freevars = uu____1070; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((TrueOp), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((FalseOp), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____1099 = (

let uu____1100 = (FStar_Util.ensure_decimal i)
in Integer (uu____1100))
in (mk uu____1099 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____1107 = (FStar_Util.string_of_int i)
in (mkInteger uu____1107 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun uu____1143 r -> (match (uu____1143) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (TrueOp, uu____1159) -> begin
(mkFalse r)
end
| App (FalseOp, uu____1162) -> begin
(mkTrue r)
end
| uu____1165 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1173 r -> (match (uu____1173) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____1179), uu____1180) -> begin
t2
end
| (uu____1183, App (TrueOp, uu____1184)) -> begin
t1
end
| (App (FalseOp, uu____1187), uu____1188) -> begin
(mkFalse r)
end
| (uu____1191, App (FalseOp, uu____1192)) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (uu____1202, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), uu____1208) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____1212 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1222 r -> (match (uu____1222) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____1228), uu____1229) -> begin
(mkTrue r)
end
| (uu____1232, App (TrueOp, uu____1233)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____1236), uu____1237) -> begin
t2
end
| (uu____1240, App (FalseOp, uu____1241)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (uu____1251, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), uu____1257) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____1261 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1271 r -> (match (uu____1271) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (uu____1277, App (TrueOp, uu____1278)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____1281), uu____1282) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____1285), uu____1286) -> begin
t2
end
| (uu____1289, App (Imp, (t1')::(t2')::[])) -> begin
(

let uu____1293 = (

let uu____1297 = (

let uu____1299 = (mkAnd ((t1), (t1')) r)
in (uu____1299)::(t2')::[])
in ((Imp), (uu____1297)))
in (mkApp' uu____1293 r))
end
| uu____1301 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op uu____1314 r -> (match (uu____1314) with
| (t1, t2) -> begin
(mkApp' ((op), ((t1)::(t2)::[])) r)
end))


let mkMinus : term  ->  FStar_Range.range  ->  term = (fun t r -> (mkApp' ((Minus), ((t)::[])) r))


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


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun uu____1401 r -> (match (uu____1401) with
| (t1, t2, t3) -> begin
(match (t1.tm) with
| App (TrueOp, uu____1409) -> begin
t2
end
| App (FalseOp, uu____1412) -> begin
t3
end
| uu____1415 -> begin
(match (((t2.tm), (t3.tm))) with
| (App (TrueOp, uu____1416), App (TrueOp, uu____1417)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____1422), uu____1423) -> begin
(

let uu____1426 = (

let uu____1429 = (mkNot t1 t1.rng)
in ((uu____1429), (t3)))
in (mkImp uu____1426 r))
end
| (uu____1430, App (TrueOp, uu____1431)) -> begin
(mkImp ((t1), (t2)) r)
end
| (uu____1434, uu____1435) -> begin
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


let mkQuant : (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1463 r -> (match (uu____1463) with
| (qop, pats, wopt, vars, body) -> begin
(match (((FStar_List.length vars) = (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____1489 -> begin
(match (body.tm) with
| App (TrueOp, uu____1490) -> begin
body
end
| uu____1493 -> begin
(mk (Quant (((qop), (pats), (wopt), (vars), (body)))) r)
end)
end)
end))


let mkLet : (term Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1505 r -> (match (uu____1505) with
| (es, body) -> begin
(match (((FStar_List.length es) = (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____1516 -> begin
(mk (Let (((es), (body)))) r)
end)
end))


let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (

let nvars = (FStar_List.length fvs)
in (

let index_of = (fun fv -> (

let uu____1533 = (FStar_Util.try_find_index (fv_eq fv) fvs)
in (match (uu____1533) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((nvars - (i + (Prims.parse_int "1"))))
end)))
in (

let rec aux = (fun ix t1 -> (

let uu____1547 = (FStar_ST.read t1.freevars)
in (match (uu____1547) with
| FStar_Pervasives_Native.Some ([]) -> begin
t1
end
| uu____1563 -> begin
(match (t1.tm) with
| Integer (uu____1568) -> begin
t1
end
| BoundV (uu____1569) -> begin
t1
end
| FreeV (x) -> begin
(

let uu____1573 = (index_of x)
in (match (uu____1573) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (i) -> begin
(mkBoundV (i + ix) t1.rng)
end))
end
| App (op, tms) -> begin
(

let uu____1580 = (

let uu____1584 = (FStar_List.map (aux ix) tms)
in ((op), (uu____1584)))
in (mkApp' uu____1580 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____1590 = (

let uu____1591 = (

let uu____1595 = (aux ix t2)
in ((uu____1595), (r1), (r2)))
in Labeled (uu____1591))
in (mk uu____1590 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____1598 = (

let uu____1599 = (

let uu____1602 = (aux ix t2)
in ((uu____1602), (r)))
in LblPos (uu____1599))
in (mk uu____1598 t2.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n1 = (FStar_List.length vars)
in (

let uu____1618 = (

let uu____1628 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n1)))))
in (

let uu____1639 = (aux (ix + n1) body)
in ((qop), (uu____1628), (wopt), (vars), (uu____1639))))
in (mkQuant uu____1618 t1.rng)))
end
| Let (es, body) -> begin
(

let uu____1650 = (FStar_List.fold_left (fun uu____1657 e -> (match (uu____1657) with
| (ix1, l) -> begin
(

let uu____1669 = (

let uu____1671 = (aux ix1 e)
in (uu____1671)::l)
in (((ix1 + (Prims.parse_int "1"))), (uu____1669)))
end)) ((ix), ([])) es)
in (match (uu____1650) with
| (ix1, es_rev) -> begin
(

let uu____1678 = (

let uu____1682 = (aux ix1 body)
in (((FStar_List.rev es_rev)), (uu____1682)))
in (mkLet uu____1678 t1.rng))
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
| Integer (uu____1703) -> begin
t1
end
| FreeV (uu____1704) -> begin
t1
end
| BoundV (i) -> begin
(match ((((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1))) with
| true -> begin
(FStar_List.nth tms1 (i - shift))
end
| uu____1710 -> begin
t1
end)
end
| App (op, tms2) -> begin
(

let uu____1715 = (

let uu____1719 = (FStar_List.map (aux shift) tms2)
in ((op), (uu____1719)))
in (mkApp' uu____1715 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____1725 = (

let uu____1726 = (

let uu____1730 = (aux shift t2)
in ((uu____1730), (r1), (r2)))
in Labeled (uu____1726))
in (mk uu____1725 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____1733 = (

let uu____1734 = (

let uu____1737 = (aux shift t2)
in ((uu____1737), (r)))
in LblPos (uu____1734))
in (mk uu____1733 t2.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift1 = (shift + m)
in (

let uu____1756 = (

let uu____1766 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift1))))
in (

let uu____1775 = (aux shift1 body)
in ((qop), (uu____1766), (wopt), (vars), (uu____1775))))
in (mkQuant uu____1756 t1.rng))))
end
| Let (es, body) -> begin
(

let uu____1784 = (FStar_List.fold_left (fun uu____1791 e -> (match (uu____1791) with
| (ix, es1) -> begin
(

let uu____1803 = (

let uu____1805 = (aux shift e)
in (uu____1805)::es1)
in (((shift + (Prims.parse_int "1"))), (uu____1803)))
end)) ((shift), ([])) es)
in (match (uu____1784) with
| (shift1, es_rev) -> begin
(

let uu____1812 = (

let uu____1816 = (aux shift1 body)
in (((FStar_List.rev es_rev)), (uu____1816)))
in (mkLet uu____1812 t1.rng))
end))
end))
in (aux (Prims.parse_int "0") t)))))


let subst : term  ->  fv  ->  term  ->  term = (fun t fv s -> (

let uu____1827 = (abstr ((fv)::[]) t)
in (inst ((s)::[]) uu____1827)))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fv Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1841 -> (match (uu____1841) with
| (qop, pats, wopt, vars, body) -> begin
(

let uu____1866 = (

let uu____1876 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (

let uu____1885 = (FStar_List.map fv_sort vars)
in (

let uu____1889 = (abstr vars body)
in ((qop), (uu____1876), (wopt), (uu____1885), (uu____1889)))))
in (mkQuant uu____1866))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1906 r -> (match (uu____1906) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)) r)
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____1943 r -> (match (uu____1943) with
| (pats, wopt, vars, body) -> begin
(

let uu____1962 = (mkQuant' ((Forall), (pats), (wopt), (vars), (body)))
in (uu____1962 r))
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____1977 r -> (match (uu____1977) with
| (pats, vars, body) -> begin
(

let uu____1991 = (mkQuant' ((Forall), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
in (uu____1991 r))
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____2006 r -> (match (uu____2006) with
| (pats, vars, body) -> begin
(

let uu____2020 = (mkQuant' ((Exists), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
in (uu____2020 r))
end))


let mkLet' : ((fv * term) Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____2035 r -> (match (uu____2035) with
| (bindings, body) -> begin
(

let uu____2050 = (FStar_List.split bindings)
in (match (uu____2050) with
| (vars, es) -> begin
(

let uu____2061 = (

let uu____2065 = (abstr vars body)
in ((es), (uu____2065)))
in (mkLet uu____2061 r))
end))
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun uu____2077 -> (match (uu____2077) with
| (nm, vars, s, tm, c) -> begin
(

let uu____2097 = (

let uu____2104 = (FStar_List.map fv_sort vars)
in (

let uu____2108 = (abstr vars tm)
in ((nm), (uu____2104), (s), (uu____2108), (c))))
in DefineFun (uu____2097))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (

let uu____2113 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" uu____2113)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun uu____2120 id -> (match (uu____2120) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (

let a = (

let uu____2128 = (

let uu____2129 = (

let uu____2132 = (mkInteger' id norng)
in (

let uu____2133 = (

let uu____2134 = (

let uu____2138 = (constr_id_of_sort sort)
in (

let uu____2139 = (

let uu____2141 = (mkApp ((tok_name), ([])) norng)
in (uu____2141)::[])
in ((uu____2138), (uu____2139))))
in (mkApp uu____2134 norng))
in ((uu____2132), (uu____2133))))
in (mkEq uu____2129 norng))
in {assumption_term = uu____2128; assumption_caption = FStar_Pervasives_Native.Some ("fresh token"); assumption_name = a_name; assumption_fact_ids = []})
in Assume (a)))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun uu____2151 -> (match (uu____2151) with
| (name, arg_sorts, sort, id) -> begin
(

let id1 = (FStar_Util.string_of_int id)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (

let uu____2170 = (

let uu____2173 = (

let uu____2174 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____2174))
in ((uu____2173), (s)))
in (mkFreeV uu____2170 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (

let uu____2180 = (

let uu____2184 = (constr_id_of_sort sort)
in ((uu____2184), ((capp)::[])))
in (mkApp uu____2180 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (

let a = (

let uu____2188 = (

let uu____2189 = (

let uu____2195 = (

let uu____2196 = (

let uu____2199 = (mkInteger id1 norng)
in ((uu____2199), (cid_app)))
in (mkEq uu____2196 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____2195)))
in (mkForall uu____2189 norng))
in {assumption_term = uu____2188; assumption_caption = FStar_Pervasives_Native.Some ("Consrtructor distinct"); assumption_name = a_name; assumption_fact_ids = []})
in Assume (a))))))))
end))


let injective_constructor : (Prims.string * constructor_field Prims.list * sort)  ->  decls_t = (fun uu____2211 -> (match (uu____2211) with
| (name, fields, sort) -> begin
(

let n_bvars = (FStar_List.length fields)
in (

let bvar_name = (fun i -> (

let uu____2227 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____2227)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (

let uu____2244 = (

let uu____2247 = (bvar_name i)
in ((uu____2247), (s)))
in (mkFreeV uu____2244)))
in (

let bvars = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____2256 -> (match (uu____2256) with
| (uu____2260, s, uu____2262) -> begin
(

let uu____2263 = (bvar i s)
in (uu____2263 norng))
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let uu____2270 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____2281 -> (match (uu____2281) with
| (name1, s, projectible) -> begin
(

let cproj_app = (mkApp ((name1), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((name1), ((sort)::[]), (s), (FStar_Pervasives_Native.Some ("Projector"))))
in (match (projectible) with
| true -> begin
(

let a = (

let uu____2296 = (

let uu____2297 = (

let uu____2303 = (

let uu____2304 = (

let uu____2307 = (

let uu____2308 = (bvar i s)
in (uu____2308 norng))
in ((cproj_app), (uu____2307)))
in (mkEq uu____2304 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____2303)))
in (mkForall uu____2297 norng))
in {assumption_term = uu____2296; assumption_caption = FStar_Pervasives_Native.Some ("Projection inverse"); assumption_name = (Prims.strcat "projection_inverse_" name1); assumption_fact_ids = []})
in (proj_name)::(Assume (a))::[])
end
| uu____2316 -> begin
(proj_name)::[]
end)))
end))))
in (FStar_All.pipe_right uu____2270 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun uu____2322 -> (match (uu____2322) with
| (name, fields, sort, id, injective) -> begin
(

let injective1 = (injective || true)
in (

let field_sorts = (FStar_All.pipe_right fields (FStar_List.map (fun uu____2338 -> (match (uu____2338) with
| (uu____2342, sort1, uu____2344) -> begin
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

let uu____2357 = (

let uu____2360 = (

let uu____2361 = (

let uu____2365 = (constr_id_of_sort sort)
in ((uu____2365), ((xx)::[])))
in (mkApp uu____2361 norng))
in (

let uu____2367 = (

let uu____2368 = (FStar_Util.string_of_int id)
in (mkInteger uu____2368 norng))
in ((uu____2360), (uu____2367))))
in (mkEq uu____2357 norng))
in (

let uu____2369 = (

let uu____2377 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____2400 -> (match (uu____2400) with
| (proj, s, projectible) -> begin
(match (projectible) with
| true -> begin
(

let uu____2417 = (mkApp ((proj), ((xx)::[])) norng)
in ((uu____2417), ([])))
end
| uu____2424 -> begin
(

let fi = (

let uu____2428 = (

let uu____2429 = (FStar_Util.string_of_int i)
in (Prims.strcat "f_" uu____2429))
in ((uu____2428), (s)))
in (

let uu____2430 = (mkFreeV fi norng)
in ((uu____2430), ((fi)::[]))))
end)
end))))
in (FStar_All.pipe_right uu____2377 FStar_List.split))
in (match (uu____2369) with
| (proj_terms, ex_vars) -> begin
(

let ex_vars1 = (FStar_List.flatten ex_vars)
in (

let disc_inv_body = (

let uu____2473 = (

let uu____2476 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (uu____2476)))
in (mkEq uu____2473 norng))
in (

let disc_inv_body1 = (match (ex_vars1) with
| [] -> begin
disc_inv_body
end
| uu____2481 -> begin
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
| uu____2503 -> begin
[]
end)
in (

let uu____2504 = (

let uu____2506 = (

let uu____2507 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (uu____2507))
in (uu____2506)::(cdecl)::(cid)::projs)
in (

let uu____2508 = (

let uu____2510 = (

let uu____2512 = (

let uu____2513 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (uu____2513))
in (uu____2512)::[])
in (FStar_List.append ((disc)::[]) uu____2510))
in (FStar_List.append uu____2504 uu____2508)))))))))
end))


let name_binders_inner : Prims.string FStar_Pervasives_Native.option  ->  (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun prefix_opt outer_names start sorts -> (

let uu____2543 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun uu____2566 s -> (match (uu____2566) with
| (names, binders, n1) -> begin
(

let prefix1 = (match (s) with
| Term_sort -> begin
"@x"
end
| uu____2594 -> begin
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

let uu____2598 = (FStar_Util.string_of_int n1)
in (Prims.strcat prefix2 uu____2598))
in (

let names1 = (((nm), (s)))::names
in (

let b = (

let uu____2606 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm uu____2606))
in ((names1), ((b)::binders), ((n1 + (Prims.parse_int "1")))))))))
end)) ((outer_names), ([]), (start))))
in (match (uu____2543) with
| (names, binders, n1) -> begin
((names), ((FStar_List.rev binders)), (n1))
end)))


let name_macro_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let uu____2648 = (name_binders_inner (FStar_Pervasives_Native.Some ("__")) [] (Prims.parse_int "0") sorts)
in (match (uu____2648) with
| (names, binders, n1) -> begin
(((FStar_List.rev names)), (binders))
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
| uu____2701 -> begin
(

let uu____2702 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "%s.%s" enclosing_name uu____2702))
end);
))))
in (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (uu____2724); freevars = uu____2725; rng = uu____2726})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| uu____2734 -> begin
tm
end))))))))
in (

let rec aux' = (fun depth n1 names t1 -> (

let aux1 = (aux (depth + (Prims.parse_int "1")))
in (match (t1.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____2770 = (FStar_List.nth names i)
in (FStar_All.pipe_right uu____2770 FStar_Pervasives_Native.fst))
end
| FreeV (x) -> begin
(FStar_Pervasives_Native.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(

let uu____2780 = (

let uu____2781 = (FStar_List.map (aux1 n1 names) tms)
in (FStar_All.pipe_right uu____2781 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) uu____2780))
end
| Labeled (t2, uu____2785, uu____2786) -> begin
(aux1 n1 names t2)
end
| LblPos (t2, s) -> begin
(

let uu____2789 = (aux1 n1 names t2)
in (FStar_Util.format2 "(! %s :lblpos %s)" uu____2789 s))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let qid = (next_qid ())
in (

let uu____2804 = (name_binders_inner FStar_Pervasives_Native.None names n1 sorts)
in (match (uu____2804) with
| (names1, binders, n2) -> begin
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
| uu____2832 -> begin
(

let uu____2835 = (FStar_All.pipe_right pats1 (FStar_List.map (fun pats2 -> (

let uu____2843 = (

let uu____2844 = (FStar_List.map (fun p -> (

let uu____2847 = (aux1 n2 names1 p)
in (FStar_Util.format1 "%s" uu____2847))) pats2)
in (FStar_String.concat " " uu____2844))
in (FStar_Util.format1 "\n:pattern (%s)" uu____2843)))))
in (FStar_All.pipe_right uu____2835 (FStar_String.concat "\n")))
end)
in (

let uu____2849 = (

let uu____2851 = (

let uu____2853 = (

let uu____2855 = (aux1 n2 names1 body)
in (

let uu____2856 = (

let uu____2858 = (weightToSmt wopt)
in (uu____2858)::(pats_str)::(qid)::[])
in (uu____2855)::uu____2856))
in (binders1)::uu____2853)
in ((qop_to_string qop))::uu____2851)
in (FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))" uu____2849)))))
end)))
end
| Let (es, body) -> begin
(

let uu____2863 = (FStar_List.fold_left (fun uu____2878 e -> (match (uu____2878) with
| (names0, binders, n0) -> begin
(

let nm = (

let uu____2906 = (FStar_Util.string_of_int n0)
in (Prims.strcat "@lb" uu____2906))
in (

let names01 = (((nm), (Term_sort)))::names0
in (

let b = (

let uu____2914 = (aux1 n1 names e)
in (FStar_Util.format2 "(%s %s)" nm uu____2914))
in ((names01), ((b)::binders), ((n0 + (Prims.parse_int "1")))))))
end)) ((names), ([]), (n1)) es)
in (match (uu____2863) with
| (names1, binders, n2) -> begin
(

let uu____2932 = (aux1 n2 names1 body)
in (FStar_Util.format2 "(let (%s)\n%s)" (FStar_String.concat " " binders) uu____2932))
end))
end)))
and aux = (fun depth n1 names t1 -> (

let s = (aux' depth n1 names t1)
in (match ((t1.rng <> norng)) with
| true -> begin
(

let uu____2939 = (FStar_Range.string_of_range t1.rng)
in (

let uu____2940 = (FStar_Range.string_of_use_range t1.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____2939 uu____2940 s)))
end
| uu____2941 -> begin
s
end)))
in (aux (Prims.parse_int "0") (Prims.parse_int "0") [] t)))))


let caption_to_string : Prims.string FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___90_2945 -> (match (uu___90_2945) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let uu____2948 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(failwith "Impossible")
end
| (hd1)::[] -> begin
((hd1), (""))
end
| (hd1)::uu____2957 -> begin
((hd1), ("..."))
end)
in (match (uu____2948) with
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

let uu____2974 = (FStar_Options.log_queries ())
in (match (uu____2974) with
| true -> begin
(

let uu____2975 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun uu___91_2977 -> (match (uu___91_2977) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" uu____2975))
end
| uu____2982 -> begin
""
end))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (

let uu____2991 = (caption_to_string c)
in (

let uu____2992 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____2991 f (FStar_String.concat " " l) uu____2992))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let uu____3000 = (name_macro_binders arg_sorts)
in (match (uu____3000) with
| (names, binders) -> begin
(

let body1 = (

let uu____3018 = (FStar_List.map (fun x -> (mkFreeV x norng)) names)
in (inst uu____3018 body))
in (

let uu____3025 = (caption_to_string c)
in (

let uu____3026 = (strSort retsort)
in (

let uu____3027 = (termToSmt (escape f) body1)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____3025 f (FStar_String.concat " " binders) uu____3026 uu____3027)))))
end))
end
| Assume (a) -> begin
(

let fact_ids_to_string = (fun ids -> (FStar_All.pipe_right ids (FStar_List.map (fun uu___92_3038 -> (match (uu___92_3038) with
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

let uu____3043 = (FStar_Options.log_queries ())
in (match (uu____3043) with
| true -> begin
(

let uu____3044 = (

let uu____3045 = (fact_ids_to_string a.assumption_fact_ids)
in (FStar_String.concat "; " uu____3045))
in (FStar_Util.format1 ";;; Fact-ids: %s\n" uu____3044))
end
| uu____3047 -> begin
""
end))
in (

let n1 = (escape a.assumption_name)
in (

let uu____3049 = (caption_to_string a.assumption_caption)
in (

let uu____3050 = (termToSmt n1 a.assumption_term)
in (FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____3049 fids uu____3050 n1))))))
end
| Eval (t) -> begin
(

let uu____3052 = (termToSmt "eval" t)
in (FStar_Util.format1 "(eval %s)" uu____3052))
end
| Echo (s) -> begin
(FStar_Util.format1 "(echo \"%s\")" s)
end
| RetainAssumptions (uu____3054) -> begin
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

let basic = (Prims.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))")
in (

let constrs = ((("FString_const"), (((("FString_const_proj_0"), (Int_sort), (true)))::[]), (String_sort), ((Prims.parse_int "0")), (true)))::((("Tm_type"), ([]), (Term_sort), ((Prims.parse_int "2")), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "3")), (false)))::((("Tm_unit"), ([]), (Term_sort), ((Prims.parse_int "6")), (true)))::((("BoxInt"), (((("BoxInt_proj_0"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "7")), (true)))::((("BoxBool"), (((("BoxBool_proj_0"), (Bool_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "8")), (true)))::((("BoxString"), (((("BoxString_proj_0"), (String_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "9")), (true)))::((("BoxRef"), (((("BoxRef_proj_0"), (Ref_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "10")), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort), (true)))::((("LexCons_1"), (Term_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "11")), (true)))::[]
in (

let bcons = (

let uu____3239 = (

let uu____3241 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right uu____3241 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right uu____3239 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mk_Range_const : term = (mkApp (("Range_const"), ([])) norng)


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____3266 = (

let uu____3270 = (

let uu____3272 = (mkInteger' i norng)
in (uu____3272)::[])
in (("Tm_uvar"), (uu____3270)))
in (mkApp uu____3266 r)))


let mk_Term_unit : term = (mkApp (("Tm_unit"), ([])) norng)


let maybe_elim_box : Prims.string  ->  Prims.string  ->  term  ->  term = (fun u v1 t -> (match (t.tm) with
| App (Var (v'), (t1)::[]) when ((v1 = v') && (FStar_Options.smtencoding_elim_box ())) -> begin
t1
end
| uu____3287 -> begin
(mkApp ((u), ((t)::[])) t.rng)
end))


let boxInt : term  ->  term = (fun t -> (maybe_elim_box "BoxInt" "BoxInt_proj_0" t))


let unboxInt : term  ->  term = (fun t -> (maybe_elim_box "BoxInt_proj_0" "BoxInt" t))


let boxBool : term  ->  term = (fun t -> (maybe_elim_box "BoxBool" "BoxBool_proj_0" t))


let unboxBool : term  ->  term = (fun t -> (maybe_elim_box "BoxBool_proj_0" "BoxBool" t))


let boxString : term  ->  term = (fun t -> (maybe_elim_box "BoxString" "BoxString_proj_0" t))


let unboxString : term  ->  term = (fun t -> (maybe_elim_box "BoxString_proj_0" "BoxString" t))


let boxRef : term  ->  term = (fun t -> (maybe_elim_box "BoxRef" "BoxRef_proj_0" t))


let unboxRef : term  ->  term = (fun t -> (maybe_elim_box "BoxRef_proj_0" "BoxRef" t))


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
| uu____3319 -> begin
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
| uu____3326 -> begin
(FStar_Pervasives.raise FStar_Util.Impos)
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (uu____3334)::(t1)::(t2)::[]); freevars = uu____3337; rng = uu____3338})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (uu____3345)::(t1)::(t2)::[]); freevars = uu____3348; rng = uu____3349})::[]) -> begin
(

let uu____3356 = (mkEq ((t1), (t2)) norng)
in (mkNot uu____3356 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = uu____3359; rng = uu____3360})::[]) -> begin
(

let uu____3367 = (

let uu____3370 = (unboxInt t1)
in (

let uu____3371 = (unboxInt t2)
in ((uu____3370), (uu____3371))))
in (mkLTE uu____3367 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = uu____3374; rng = uu____3375})::[]) -> begin
(

let uu____3382 = (

let uu____3385 = (unboxInt t1)
in (

let uu____3386 = (unboxInt t2)
in ((uu____3385), (uu____3386))))
in (mkLT uu____3382 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = uu____3389; rng = uu____3390})::[]) -> begin
(

let uu____3397 = (

let uu____3400 = (unboxInt t1)
in (

let uu____3401 = (unboxInt t2)
in ((uu____3400), (uu____3401))))
in (mkGTE uu____3397 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = uu____3404; rng = uu____3405})::[]) -> begin
(

let uu____3412 = (

let uu____3415 = (unboxInt t1)
in (

let uu____3416 = (unboxInt t2)
in ((uu____3415), (uu____3416))))
in (mkGT uu____3412 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = uu____3419; rng = uu____3420})::[]) -> begin
(

let uu____3427 = (

let uu____3430 = (unboxBool t1)
in (

let uu____3431 = (unboxBool t2)
in ((uu____3430), (uu____3431))))
in (mkAnd uu____3427 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = uu____3434; rng = uu____3435})::[]) -> begin
(

let uu____3442 = (

let uu____3445 = (unboxBool t1)
in (

let uu____3446 = (unboxBool t2)
in ((uu____3445), (uu____3446))))
in (mkOr uu____3442 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t1)::[]); freevars = uu____3448; rng = uu____3449})::[]) -> begin
(

let uu____3456 = (unboxBool t1)
in (mkNot uu____3456 t1.rng))
end
| App (Var ("Prims.b2t"), (t1)::[]) -> begin
(

let uu___93_3459 = (unboxBool t1)
in {tm = uu___93_3459.tm; freevars = uu___93_3459.freevars; rng = t.rng})
end
| uu____3462 -> begin
(mkApp (("Valid"), ((t)::[])) t.rng)
end))


let mk_HasType : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasType"), ((v1)::(t)::[])) t.rng))


let mk_HasTypeZ : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasTypeZ"), ((v1)::(t)::[])) t.rng))


let mk_IsTyped : term  ->  term = (fun v1 -> (mkApp (("IsTyped"), ((v1)::[])) norng))


let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v1 t -> (

let uu____3491 = (FStar_Options.unthrottle_inductives ())
in (match (uu____3491) with
| true -> begin
(mk_HasType v1 t)
end
| uu____3492 -> begin
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

let uu____3555 = (

let uu____3559 = (

let uu____3561 = (mkInteger' i norng)
in (uu____3561)::[])
in (("FString_const"), (uu____3559)))
in (mkApp uu____3555 r)))


let mk_Precedes : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (

let uu____3572 = (mkApp (("Precedes"), ((x1)::(x2)::[])) r)
in (FStar_All.pipe_right uu____3572 mk_Valid)))


let mk_LexCons : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (mkApp (("LexCons"), ((x1)::(x2)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n1 -> (match ((n1 = (Prims.parse_int "0"))) with
| true -> begin
(mkApp (("ZFuel"), ([])) norng)
end
| uu____3588 -> begin
(

let uu____3589 = (

let uu____3593 = (

let uu____3595 = (n_fuel (n1 - (Prims.parse_int "1")))
in (uu____3595)::[])
in (("SFuel"), (uu____3593)))
in (mkApp uu____3589 norng))
end))


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term FStar_Pervasives_Native.option  ->  term FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  term FStar_Pervasives_Native.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (FStar_Pervasives_Native.Some (p11), FStar_Pervasives_Native.Some (p21)) -> begin
(

let uu____3618 = (mkAnd ((p11), (p21)) r)
in FStar_Pervasives_Native.Some (uu____3618))
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

let uu____3652 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l uu____3652)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____3663 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l uu____3663)))


let mk_haseq : term  ->  term = (fun t -> (

let uu____3669 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid uu____3669)))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n1) -> begin
(FStar_Util.format1 "(Integer %s)" n1)
end
| BoundV (n1) -> begin
(

let uu____3683 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(BoundV %s)" uu____3683))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv))
end
| App (op, l) -> begin
(

let uu____3691 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) uu____3691))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____3695 = (print_smt_term t1)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 uu____3695))
end
| LblPos (t1, s) -> begin
(

let uu____3698 = (print_smt_term t1)
in (FStar_Util.format2 "(LblPos %s %s)" s uu____3698))
end
| Quant (qop, l, uu____3701, uu____3702, t1) -> begin
(

let uu____3712 = (print_smt_term_list_list l)
in (

let uu____3713 = (print_smt_term t1)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____3712 uu____3713)))
end
| Let (es, body) -> begin
(

let uu____3718 = (print_smt_term_list es)
in (

let uu____3719 = (print_smt_term body)
in (FStar_Util.format2 "(let %s %s)" uu____3718 uu____3719)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (

let uu____3722 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right uu____3722 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l1 -> (

let uu____3732 = (

let uu____3733 = (

let uu____3734 = (print_smt_term_list l1)
in (Prims.strcat uu____3734 " ] "))
in (Prims.strcat "; [ " uu____3733))
in (Prims.strcat s uu____3732))) "" l))




