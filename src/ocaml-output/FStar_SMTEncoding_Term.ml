
open Prims
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
| uu____17 -> begin
false
end))


let uu___is_Int_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int_sort -> begin
true
end
| uu____21 -> begin
false
end))


let uu___is_String_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| String_sort -> begin
true
end
| uu____25 -> begin
false
end))


let uu___is_Ref_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Ref_sort -> begin
true
end
| uu____29 -> begin
false
end))


let uu___is_Term_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Term_sort -> begin
true
end
| uu____33 -> begin
false
end))


let uu___is_Fuel_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fuel_sort -> begin
true
end
| uu____37 -> begin
false
end))


let uu___is_Array : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Array (_0) -> begin
true
end
| uu____44 -> begin
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
| uu____64 -> begin
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
| uu____82 -> begin
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

let uu____95 = (strSort s1)
in (

let uu____96 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" uu____95 uu____96)))
end
| Arrow (s1, s2) -> begin
(

let uu____99 = (strSort s1)
in (

let uu____100 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" uu____99 uu____100)))
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
| uu____108 -> begin
false
end))


let uu___is_FalseOp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FalseOp -> begin
true
end
| uu____112 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____116 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____120 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____124 -> begin
false
end))


let uu___is_Imp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Imp -> begin
true
end
| uu____128 -> begin
false
end))


let uu___is_Iff : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iff -> begin
true
end
| uu____132 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____136 -> begin
false
end))


let uu___is_LT : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LT -> begin
true
end
| uu____140 -> begin
false
end))


let uu___is_LTE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LTE -> begin
true
end
| uu____144 -> begin
false
end))


let uu___is_GT : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GT -> begin
true
end
| uu____148 -> begin
false
end))


let uu___is_GTE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GTE -> begin
true
end
| uu____152 -> begin
false
end))


let uu___is_Add : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Add -> begin
true
end
| uu____156 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____160 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____164 -> begin
false
end))


let uu___is_Mul : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mul -> begin
true
end
| uu____168 -> begin
false
end))


let uu___is_Minus : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Minus -> begin
true
end
| uu____172 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____176 -> begin
false
end))


let uu___is_ITE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ITE -> begin
true
end
| uu____180 -> begin
false
end))


let uu___is_Var : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Var (_0) -> begin
true
end
| uu____185 -> begin
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
| uu____196 -> begin
false
end))


let uu___is_Exists : qop  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exists -> begin
true
end
| uu____200 -> begin
false
end))

type term' =
| Integer of Prims.string
| BoundV of Prims.int
| FreeV of (Prims.string * sort)
| App of (op * term Prims.list)
| Quant of (qop * term Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)
| Labeled of (term * Prims.string * FStar_Range.range)
| LblPos of (term * Prims.string) 
 and term =
{tm : term'; freevars : (Prims.string * sort) Prims.list FStar_Syntax_Syntax.memo; rng : FStar_Range.range}


let uu___is_Integer : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Integer (_0) -> begin
true
end
| uu____259 -> begin
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
| uu____271 -> begin
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
| uu____285 -> begin
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
| uu____306 -> begin
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
| uu____336 -> begin
false
end))


let __proj__Quant__item___0 : term'  ->  (qop * term Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term) = (fun projectee -> (match (projectee) with
| Quant (_0) -> begin
_0
end))


let uu___is_Labeled : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Labeled (_0) -> begin
true
end
| uu____378 -> begin
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
| uu____401 -> begin
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
Prims.string Prims.option


type binders =
(Prims.string * sort) Prims.list


type projector =
(Prims.string * sort)


type constructor_t =
(Prims.string * projector Prims.list * sort * Prims.int * Prims.bool)


type constructors =
constructor_t Prims.list

type decl =
| DefPrelude
| DeclFun of (Prims.string * sort Prims.list * sort * caption)
| DefineFun of (Prims.string * sort Prims.list * sort * term * caption)
| Assume of (term * caption * Prims.string Prims.option)
| Caption of Prims.string
| Eval of term
| Echo of Prims.string
| Push
| Pop
| CheckSat
| GetUnsatCore
| SetOption of (Prims.string * Prims.string)
| PrintStats


let uu___is_DefPrelude : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DefPrelude -> begin
true
end
| uu____496 -> begin
false
end))


let uu___is_DeclFun : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DeclFun (_0) -> begin
true
end
| uu____506 -> begin
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
| uu____539 -> begin
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
| uu____573 -> begin
false
end))


let __proj__Assume__item___0 : decl  ->  (term * caption * Prims.string Prims.option) = (fun projectee -> (match (projectee) with
| Assume (_0) -> begin
_0
end))


let uu___is_Caption : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Caption (_0) -> begin
true
end
| uu____597 -> begin
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
| uu____609 -> begin
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
| uu____621 -> begin
false
end))


let __proj__Echo__item___0 : decl  ->  Prims.string = (fun projectee -> (match (projectee) with
| Echo (_0) -> begin
_0
end))


let uu___is_Push : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push -> begin
true
end
| uu____632 -> begin
false
end))


let uu___is_Pop : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____636 -> begin
false
end))


let uu___is_CheckSat : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckSat -> begin
true
end
| uu____640 -> begin
false
end))


let uu___is_GetUnsatCore : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetUnsatCore -> begin
true
end
| uu____644 -> begin
false
end))


let uu___is_SetOption : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOption (_0) -> begin
true
end
| uu____651 -> begin
false
end))


let __proj__SetOption__item___0 : decl  ->  (Prims.string * Prims.string) = (fun projectee -> (match (projectee) with
| SetOption (_0) -> begin
_0
end))


let uu___is_PrintStats : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PrintStats -> begin
true
end
| uu____668 -> begin
false
end))


type decls_t =
decl Prims.list


type error_label =
(fv * Prims.string * FStar_Range.range)


type error_labels =
error_label Prims.list


let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> ((Prims.fst x) = (Prims.fst y)))


let fv_sort = (fun x -> (Prims.snd x))


let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match (((x.tm), (y.tm))) with
| (FreeV (x), FreeV (y)) -> begin
(fv_eq x y)
end
| uu____705 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun uu___83_710 -> (match (uu___83_710) with
| {tm = FreeV (x); freevars = uu____712; rng = uu____713} -> begin
(fv_sort x)
end
| uu____720 -> begin
(failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun uu___84_723 -> (match (uu___84_723) with
| {tm = FreeV (fv); freevars = uu____725; rng = uu____726} -> begin
fv
end
| uu____733 -> begin
(failwith "impossible")
end))


let rec freevars : term  ->  (Prims.string * sort) Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (uu____754, tms) -> begin
(FStar_List.collect freevars tms)
end
| (Quant (_, _, _, _, t)) | (Labeled (t, _, _)) | (LblPos (t, _)) -> begin
(freevars t)
end))


let free_variables : term  ->  fvs = (fun t -> (

let uu____775 = (FStar_ST.read t.freevars)
in (match (uu____775) with
| Some (b) -> begin
b
end
| None -> begin
(

let fvs = (

let uu____798 = (freevars t)
in (FStar_Util.remove_dups fv_eq uu____798))
in ((FStar_ST.write t.freevars (Some (fvs)));
fvs;
))
end)))


let qop_to_string : qop  ->  Prims.string = (fun uu___85_810 -> (match (uu___85_810) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun uu___86_813 -> (match (uu___86_813) with
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


let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun uu___87_818 -> (match (uu___87_818) with
| None -> begin
""
end
| Some (i) -> begin
(

let uu____821 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" uu____821))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____829 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" uu____829))
end
| FreeV (x) -> begin
(

let uu____833 = (

let uu____834 = (strSort (Prims.snd x))
in (Prims.strcat ":" uu____834))
in (Prims.strcat (Prims.fst x) uu____833))
end
| App (op, tms) -> begin
(

let uu____839 = (

let uu____840 = (

let uu____841 = (

let uu____842 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right uu____842 (FStar_String.concat " ")))
in (Prims.strcat uu____841 ")"))
in (Prims.strcat (op_to_string op) uu____840))
in (Prims.strcat "(" uu____839))
end
| Labeled (t, r1, r2) -> begin
(

let uu____848 = (hash_of_term t)
in (

let uu____849 = (

let uu____850 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 uu____850))
in (Prims.strcat uu____848 uu____849)))
end
| LblPos (t, r) -> begin
(

let uu____853 = (

let uu____854 = (hash_of_term t)
in (Prims.strcat uu____854 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " uu____853))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let uu____868 = (

let uu____869 = (

let uu____870 = (

let uu____871 = (

let uu____872 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right uu____872 (FStar_String.concat " ")))
in (

let uu____875 = (

let uu____876 = (

let uu____877 = (hash_of_term body)
in (

let uu____878 = (

let uu____879 = (

let uu____880 = (weightToSmt wopt)
in (

let uu____881 = (

let uu____882 = (

let uu____883 = (

let uu____884 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (

let uu____892 = (FStar_List.map hash_of_term pats)
in (FStar_All.pipe_right uu____892 (FStar_String.concat " "))))))
in (FStar_All.pipe_right uu____884 (FStar_String.concat "; ")))
in (Prims.strcat uu____883 "))"))
in (Prims.strcat " " uu____882))
in (Prims.strcat uu____880 uu____881)))
in (Prims.strcat " " uu____879))
in (Prims.strcat uu____877 uu____878)))
in (Prims.strcat ")(! " uu____876))
in (Prims.strcat uu____871 uu____875)))
in (Prims.strcat " (" uu____870))
in (Prims.strcat (qop_to_string qop) uu____869))
in (Prims.strcat "(" uu____868))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (

let uu____903 = (FStar_Util.mk_ref None)
in {tm = t; freevars = uu____903; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((TrueOp), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((FalseOp), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____932 = (

let uu____933 = (FStar_Util.ensure_decimal i)
in Integer (uu____933))
in (mk uu____932 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____940 = (FStar_Util.string_of_int i)
in (mkInteger uu____940 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun uu____976 r -> (match (uu____976) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (TrueOp, uu____992) -> begin
(mkFalse r)
end
| App (FalseOp, uu____995) -> begin
(mkTrue r)
end
| uu____998 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1006 r -> (match (uu____1006) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____1012), uu____1013) -> begin
t2
end
| (uu____1016, App (TrueOp, uu____1017)) -> begin
t1
end
| ((App (FalseOp, _), _)) | ((_, App (FalseOp, _))) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (uu____1033, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), uu____1039) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____1043 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1053 r -> (match (uu____1053) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((App (TrueOp, _), _)) | ((_, App (TrueOp, _))) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____1065), uu____1066) -> begin
t2
end
| (uu____1069, App (FalseOp, uu____1070)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (uu____1080, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), uu____1086) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____1090 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1100 r -> (match (uu____1100) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((_, App (TrueOp, _))) | ((App (FalseOp, _), _)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____1112), uu____1113) -> begin
t2
end
| (uu____1116, App (Imp, (t1')::(t2')::[])) -> begin
(

let uu____1120 = (

let uu____1124 = (

let uu____1126 = (mkAnd ((t1), (t1')) r)
in (uu____1126)::(t2')::[])
in ((Imp), (uu____1124)))
in (mkApp' uu____1120 r))
end
| uu____1128 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op uu____1141 r -> (match (uu____1141) with
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


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun uu____1228 r -> (match (uu____1228) with
| (t1, t2, t3) -> begin
(match (t1.tm) with
| App (TrueOp, uu____1236) -> begin
t2
end
| App (FalseOp, uu____1239) -> begin
t3
end
| uu____1242 -> begin
(match (((t2.tm), (t3.tm))) with
| (App (TrueOp, uu____1243), App (TrueOp, uu____1244)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____1249), uu____1250) -> begin
(

let uu____1253 = (

let uu____1256 = (mkNot t1 t1.rng)
in ((uu____1256), (t3)))
in (mkImp uu____1253 r))
end
| (uu____1257, App (TrueOp, uu____1258)) -> begin
(mkImp ((t1), (t2)) r)
end
| (uu____1261, uu____1262) -> begin
(mkApp' ((ITE), ((t1)::(t2)::(t3)::[])) r)
end)
end)
end))


let mkCases : term Prims.list  ->  FStar_Range.range  ->  term = (fun t r -> (match (t) with
| [] -> begin
(failwith "Impos")
end
| (hd)::tl -> begin
(FStar_List.fold_left (fun out t -> (mkAnd ((out), (t)) r)) hd tl)
end))


let mkQuant : (qop * term Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1290 r -> (match (uu____1290) with
| (qop, pats, wopt, vars, body) -> begin
(match (((FStar_List.length vars) = (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____1316 -> begin
(match (body.tm) with
| App (TrueOp, uu____1317) -> begin
body
end
| uu____1320 -> begin
(mk (Quant (((qop), (pats), (wopt), (vars), (body)))) r)
end)
end)
end))


let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (

let nvars = (FStar_List.length fvs)
in (

let index_of = (fun fv -> (

let uu____1340 = (FStar_Util.try_find_index (fv_eq fv) fvs)
in (match (uu____1340) with
| None -> begin
None
end
| Some (i) -> begin
Some ((nvars - (i + (Prims.parse_int "1"))))
end)))
in (

let rec aux = (fun ix t -> (

let uu____1354 = (FStar_ST.read t.freevars)
in (match (uu____1354) with
| Some ([]) -> begin
t
end
| uu____1370 -> begin
(match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
t
end
| FreeV (x) -> begin
(

let uu____1380 = (index_of x)
in (match (uu____1380) with
| None -> begin
t
end
| Some (i) -> begin
(mkBoundV (i + ix) t.rng)
end))
end
| App (op, tms) -> begin
(

let uu____1387 = (

let uu____1391 = (FStar_List.map (aux ix) tms)
in ((op), (uu____1391)))
in (mkApp' uu____1387 t.rng))
end
| Labeled (t, r1, r2) -> begin
(

let uu____1397 = (

let uu____1398 = (

let uu____1402 = (aux ix t)
in ((uu____1402), (r1), (r2)))
in Labeled (uu____1398))
in (mk uu____1397 t.rng))
end
| LblPos (t, r) -> begin
(

let uu____1405 = (

let uu____1406 = (

let uu____1409 = (aux ix t)
in ((uu____1409), (r)))
in LblPos (uu____1406))
in (mk uu____1405 t.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n = (FStar_List.length vars)
in (

let uu____1425 = (

let uu____1435 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (

let uu____1446 = (aux (ix + n) body)
in ((qop), (uu____1435), (wopt), (vars), (uu____1446))))
in (mkQuant uu____1425 t.rng)))
end)
end)))
in (aux (Prims.parse_int "0") t)))))


let inst : term Prims.list  ->  term  ->  term = (fun tms t -> (

let tms = (FStar_List.rev tms)
in (

let n = (FStar_List.length tms)
in (

let rec aux = (fun shift t -> (match (t.tm) with
| (Integer (_)) | (FreeV (_)) -> begin
t
end
| BoundV (i) -> begin
(match ((((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n))) with
| true -> begin
(FStar_List.nth tms (i - shift))
end
| uu____1477 -> begin
t
end)
end
| App (op, tms) -> begin
(

let uu____1482 = (

let uu____1486 = (FStar_List.map (aux shift) tms)
in ((op), (uu____1486)))
in (mkApp' uu____1482 t.rng))
end
| Labeled (t, r1, r2) -> begin
(

let uu____1492 = (

let uu____1493 = (

let uu____1497 = (aux shift t)
in ((uu____1497), (r1), (r2)))
in Labeled (uu____1493))
in (mk uu____1492 t.rng))
end
| LblPos (t, r) -> begin
(

let uu____1500 = (

let uu____1501 = (

let uu____1504 = (aux shift t)
in ((uu____1504), (r)))
in LblPos (uu____1501))
in (mk uu____1500 t.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift = (shift + m)
in (

let uu____1523 = (

let uu____1533 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (

let uu____1542 = (aux shift body)
in ((qop), (uu____1533), (wopt), (vars), (uu____1542))))
in (mkQuant uu____1523 t.rng))))
end))
in (aux (Prims.parse_int "0") t)))))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1560 -> (match (uu____1560) with
| (qop, pats, wopt, vars, body) -> begin
(

let uu____1585 = (

let uu____1595 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (

let uu____1604 = (FStar_List.map fv_sort vars)
in (

let uu____1608 = (abstr vars body)
in ((qop), (uu____1595), (wopt), (uu____1604), (uu____1608)))))
in (mkQuant uu____1585))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1625 r -> (match (uu____1625) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)) r)
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____1662 r -> (match (uu____1662) with
| (pats, wopt, vars, body) -> begin
(

let uu____1681 = (mkQuant' ((Forall), (pats), (wopt), (vars), (body)))
in (uu____1681 r))
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____1696 r -> (match (uu____1696) with
| (pats, vars, body) -> begin
(

let uu____1710 = (mkQuant' ((Forall), (pats), (None), (vars), (body)))
in (uu____1710 r))
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____1725 r -> (match (uu____1725) with
| (pats, vars, body) -> begin
(

let uu____1739 = (mkQuant' ((Exists), (pats), (None), (vars), (body)))
in (uu____1739 r))
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun uu____1755 -> (match (uu____1755) with
| (nm, vars, s, tm, c) -> begin
(

let uu____1775 = (

let uu____1782 = (FStar_List.map fv_sort vars)
in (

let uu____1786 = (abstr vars tm)
in ((nm), (uu____1782), (s), (uu____1786), (c))))
in DefineFun (uu____1775))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (

let uu____1791 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" uu____1791)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun uu____1798 id -> (match (uu____1798) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (

let uu____1805 = (

let uu____1810 = (

let uu____1811 = (

let uu____1814 = (mkInteger' id norng)
in (

let uu____1815 = (

let uu____1816 = (

let uu____1820 = (constr_id_of_sort sort)
in (

let uu____1821 = (

let uu____1823 = (mkApp ((tok_name), ([])) norng)
in (uu____1823)::[])
in ((uu____1820), (uu____1821))))
in (mkApp uu____1816 norng))
in ((uu____1814), (uu____1815))))
in (mkEq uu____1811 norng))
in ((uu____1810), (Some ("fresh token")), (Some (a_name))))
in Assume (uu____1805)))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun uu____1835 -> (match (uu____1835) with
| (name, arg_sorts, sort, id) -> begin
(

let id = (FStar_Util.string_of_int id)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (

let uu____1854 = (

let uu____1857 = (

let uu____1858 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____1858))
in ((uu____1857), (s)))
in (mkFreeV uu____1854 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (

let uu____1864 = (

let uu____1868 = (constr_id_of_sort sort)
in ((uu____1868), ((capp)::[])))
in (mkApp uu____1864 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (

let uu____1871 = (

let uu____1876 = (

let uu____1877 = (

let uu____1883 = (

let uu____1884 = (

let uu____1887 = (mkInteger id norng)
in ((uu____1887), (cid_app)))
in (mkEq uu____1884 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____1883)))
in (mkForall uu____1877 norng))
in ((uu____1876), (Some ("Constructor distinct")), (Some (a_name))))
in Assume (uu____1871))))))))
end))


let injective_constructor : (Prims.string * (Prims.string * sort) Prims.list * sort)  ->  decls_t = (fun uu____1903 -> (match (uu____1903) with
| (name, projectors, sort) -> begin
(

let n_bvars = (FStar_List.length projectors)
in (

let bvar_name = (fun i -> (

let uu____1927 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____1927)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (

let uu____1944 = (

let uu____1947 = (bvar_name i)
in ((uu____1947), (s)))
in (mkFreeV uu____1944)))
in (

let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i uu____1957 -> (match (uu____1957) with
| (uu____1960, s) -> begin
(

let uu____1962 = (bvar i s)
in (uu____1962 norng))
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let uu____1969 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i uu____1981 -> (match (uu____1981) with
| (name, s) -> begin
(

let cproj_app = (mkApp ((name), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((name), ((sort)::[]), (s), (Some ("Projector"))))
in (

let a_name = (Prims.strcat "projection_inverse_" name)
in (

let uu____1993 = (

let uu____1995 = (

let uu____1996 = (

let uu____2001 = (

let uu____2002 = (

let uu____2008 = (

let uu____2009 = (

let uu____2012 = (

let uu____2013 = (bvar i s)
in (uu____2013 norng))
in ((cproj_app), (uu____2012)))
in (mkEq uu____2009 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____2008)))
in (mkForall uu____2002 norng))
in ((uu____2001), (Some ("Projection inverse")), (Some (a_name))))
in Assume (uu____1996))
in (uu____1995)::[])
in (proj_name)::uu____1993))))
end))))
in (FStar_All.pipe_right uu____1969 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun uu____2028 -> (match (uu____2028) with
| (name, projectors, sort, id, injective) -> begin
(

let injective = (injective || true)
in (

let cdecl = (

let uu____2038 = (

let uu____2044 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (uu____2044), (sort), (Some ("Constructor"))))
in DeclFun (uu____2038))
in (

let cid = (

let uu____2053 = (

let uu____2059 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (uu____2059), (sort), (id)))
in (fresh_constructor uu____2053))
in (

let disc = (

let disc_name = (Prims.strcat "is-" name)
in (

let xfv = (("x"), (sort))
in (

let xx = (mkFreeV xfv norng)
in (

let disc_eq = (

let uu____2073 = (

let uu____2076 = (

let uu____2077 = (

let uu____2081 = (constr_id_of_sort sort)
in ((uu____2081), ((xx)::[])))
in (mkApp uu____2077 norng))
in (

let uu____2083 = (

let uu____2084 = (FStar_Util.string_of_int id)
in (mkInteger uu____2084 norng))
in ((uu____2076), (uu____2083))))
in (mkEq uu____2073 norng))
in (

let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun uu____2091 -> (match (uu____2091) with
| (proj, s) -> begin
(mkApp ((proj), ((xx)::[])) norng)
end))))
in (

let disc_inv_body = (

let uu____2098 = (

let uu____2101 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (uu____2101)))
in (mkEq uu____2098 norng))
in (

let disc_ax = (mkAnd ((disc_eq), (disc_inv_body)) norng)
in (mkDefineFun ((disc_name), ((xfv)::[]), (Bool_sort), (disc_ax), (Some ("Discriminator definition")))))))))))
in (

let projs = (match (injective) with
| true -> begin
(injective_constructor ((name), (projectors), (sort)))
end
| uu____2114 -> begin
[]
end)
in (

let uu____2115 = (

let uu____2117 = (

let uu____2118 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (uu____2118))
in (uu____2117)::(cdecl)::(cid)::projs)
in (

let uu____2119 = (

let uu____2121 = (

let uu____2123 = (

let uu____2124 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (uu____2124))
in (uu____2123)::[])
in (FStar_List.append ((disc)::[]) uu____2121))
in (FStar_List.append uu____2115 uu____2119))))))))
end))


let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (

let uu____2149 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun uu____2172 s -> (match (uu____2172) with
| (names, binders, n) -> begin
(

let prefix = (match (s) with
| Term_sort -> begin
"@x"
end
| uu____2200 -> begin
"@u"
end)
in (

let nm = (

let uu____2202 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix uu____2202))
in (

let names = (((nm), (s)))::names
in (

let b = (

let uu____2210 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm uu____2210))
in ((names), ((b)::binders), ((n + (Prims.parse_int "1"))))))))
end)) ((outer_names), ([]), (start))))
in (match (uu____2149) with
| (names, binders, n) -> begin
((names), ((FStar_List.rev binders)), (n))
end)))


let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let uu____2252 = (name_binders_inner [] (Prims.parse_int "0") sorts)
in (match (uu____2252) with
| (names, binders, n) -> begin
(((FStar_List.rev names)), (binders))
end)))


let termToSmt : term  ->  Prims.string = (fun t -> (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (uu____2309); freevars = uu____2310; rng = uu____2311})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| uu____2319 -> begin
tm
end))))))))
in (

let rec aux' = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____2342 = (FStar_List.nth names i)
in (FStar_All.pipe_right uu____2342 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(

let uu____2352 = (

let uu____2353 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right uu____2353 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) uu____2352))
end
| Labeled (t, uu____2357, uu____2358) -> begin
(aux n names t)
end
| LblPos (t, s) -> begin
(

let uu____2361 = (aux n names t)
in (FStar_Util.format2 "(! %s :lblpos %s)" uu____2361 s))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let uu____2375 = (name_binders_inner names n sorts)
in (match (uu____2375) with
| (names, binders, n) -> begin
(

let binders = (FStar_All.pipe_right binders (FStar_String.concat " "))
in (

let pats = (remove_guard_free pats)
in (

let pats_str = (match (pats) with
| (([])::[]) | ([]) -> begin
""
end
| uu____2403 -> begin
(

let uu____2406 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (

let uu____2414 = (

let uu____2415 = (FStar_List.map (fun p -> (

let uu____2418 = (aux n names p)
in (FStar_Util.format1 "%s" uu____2418))) pats)
in (FStar_String.concat " " uu____2415))
in (FStar_Util.format1 "\n:pattern (%s)" uu____2414)))))
in (FStar_All.pipe_right uu____2406 (FStar_String.concat "\n")))
end)
in (match (((pats), (wopt))) with
| ((([])::[], None)) | (([], None)) -> begin
(

let uu____2432 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders uu____2432))
end
| uu____2433 -> begin
(

let uu____2439 = (aux n names body)
in (

let uu____2440 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders uu____2439 uu____2440 pats_str)))
end))))
end))
end))
and aux = (fun n names t -> (

let s = (aux' n names t)
in (match ((t.rng <> norng)) with
| true -> begin
(

let uu____2446 = (FStar_Range.string_of_range t.rng)
in (

let uu____2447 = (FStar_Range.string_of_use_range t.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____2446 uu____2447 s)))
end
| uu____2448 -> begin
s
end)))
in (aux (Prims.parse_int "0") [] t))))


let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun uu___88_2452 -> (match (uu___88_2452) with
| None -> begin
""
end
| Some (c) -> begin
(

let uu____2455 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(failwith "Impossible")
end
| (hd)::[] -> begin
((hd), (""))
end
| (hd)::uu____2464 -> begin
((hd), ("..."))
end)
in (match (uu____2455) with
| (hd, suffix) -> begin
(FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd suffix)
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

let uu____2481 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun uu___89_2483 -> (match (uu___89_2483) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" uu____2481))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (

let uu____2496 = (caption_to_string c)
in (

let uu____2497 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____2496 f (FStar_String.concat " " l) uu____2497))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let uu____2505 = (name_binders arg_sorts)
in (match (uu____2505) with
| (names, binders) -> begin
(

let body = (

let uu____2523 = (FStar_List.map (fun x -> (mkFreeV x norng)) names)
in (inst uu____2523 body))
in (

let uu____2530 = (caption_to_string c)
in (

let uu____2531 = (strSort retsort)
in (

let uu____2532 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____2530 f (FStar_String.concat " " binders) uu____2531 uu____2532)))))
end))
end
| Assume (t, c, Some (n)) -> begin
(

let uu____2537 = (caption_to_string c)
in (

let uu____2538 = (termToSmt t)
in (FStar_Util.format3 "%s(assert (!\n%s\n:named %s))" uu____2537 uu____2538 (escape n))))
end
| Assume (t, c, None) -> begin
(

let uu____2542 = (caption_to_string c)
in (

let uu____2543 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" uu____2542 uu____2543)))
end
| Eval (t) -> begin
(

let uu____2545 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" uu____2545))
end
| Echo (s) -> begin
(FStar_Util.format1 "(echo \"%s\")" s)
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
| SetOption (s, v) -> begin
(FStar_Util.format2 "(set-option :%s %s)" s v)
end
| PrintStats -> begin
"(get-info :all-statistics)"
end)))
and mkPrelude : Prims.string  ->  Prims.string = (fun z3options -> (

let basic = (Prims.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n")
in (

let constrs = ((("FString_const"), (((("FString_const_proj_0"), (Int_sort)))::[]), (String_sort), ((Prims.parse_int "0")), (true)))::((("Tm_type"), ([]), (Term_sort), ((Prims.parse_int "2")), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort)))::[]), (Term_sort), ((Prims.parse_int "3")), (false)))::((("Tm_uvar"), (((("Tm_uvar_fst"), (Int_sort)))::[]), (Term_sort), ((Prims.parse_int "5")), (true)))::((("Tm_unit"), ([]), (Term_sort), ((Prims.parse_int "6")), (true)))::((("BoxInt"), (((("BoxInt_proj_0"), (Int_sort)))::[]), (Term_sort), ((Prims.parse_int "7")), (true)))::((("BoxBool"), (((("BoxBool_proj_0"), (Bool_sort)))::[]), (Term_sort), ((Prims.parse_int "8")), (true)))::((("BoxString"), (((("BoxString_proj_0"), (String_sort)))::[]), (Term_sort), ((Prims.parse_int "9")), (true)))::((("BoxRef"), (((("BoxRef_proj_0"), (Ref_sort)))::[]), (Term_sort), ((Prims.parse_int "10")), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort)))::((("LexCons_1"), (Term_sort)))::[]), (Term_sort), ((Prims.parse_int "11")), (true)))::[]
in (

let bcons = (

let uu____2709 = (

let uu____2711 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right uu____2711 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right uu____2709 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mk_Range_const : term = (mkApp (("Range_const"), ([])) norng)


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____2736 = (

let uu____2740 = (

let uu____2742 = (mkInteger' i norng)
in (uu____2742)::[])
in (("Tm_uvar"), (uu____2740)))
in (mkApp uu____2736 r)))


let mk_Term_unit : term = (mkApp (("Tm_unit"), ([])) norng)


let boxInt : term  ->  term = (fun t -> (mkApp (("BoxInt"), ((t)::[])) t.rng))


let unboxInt : term  ->  term = (fun t -> (mkApp (("BoxInt_proj_0"), ((t)::[])) t.rng))


let boxBool : term  ->  term = (fun t -> (mkApp (("BoxBool"), ((t)::[])) t.rng))


let unboxBool : term  ->  term = (fun t -> (mkApp (("BoxBool_proj_0"), ((t)::[])) t.rng))


let boxString : term  ->  term = (fun t -> (mkApp (("BoxString"), ((t)::[])) t.rng))


let unboxString : term  ->  term = (fun t -> (mkApp (("BoxString_proj_0"), ((t)::[])) t.rng))


let boxRef : term  ->  term = (fun t -> (mkApp (("BoxRef"), ((t)::[])) t.rng))


let unboxRef : term  ->  term = (fun t -> (mkApp (("BoxRef_proj_0"), ((t)::[])) t.rng))


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
| uu____2783 -> begin
(Prims.raise FStar_Util.Impos)
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
| uu____2790 -> begin
(Prims.raise FStar_Util.Impos)
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (uu____2798)::(t1)::(t2)::[]); freevars = uu____2801; rng = uu____2802})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (uu____2809)::(t1)::(t2)::[]); freevars = uu____2812; rng = uu____2813})::[]) -> begin
(

let uu____2820 = (mkEq ((t1), (t2)) norng)
in (mkNot uu____2820 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = uu____2823; rng = uu____2824})::[]) -> begin
(

let uu____2831 = (

let uu____2834 = (unboxInt t1)
in (

let uu____2835 = (unboxInt t2)
in ((uu____2834), (uu____2835))))
in (mkLTE uu____2831 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = uu____2838; rng = uu____2839})::[]) -> begin
(

let uu____2846 = (

let uu____2849 = (unboxInt t1)
in (

let uu____2850 = (unboxInt t2)
in ((uu____2849), (uu____2850))))
in (mkLT uu____2846 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = uu____2853; rng = uu____2854})::[]) -> begin
(

let uu____2861 = (

let uu____2864 = (unboxInt t1)
in (

let uu____2865 = (unboxInt t2)
in ((uu____2864), (uu____2865))))
in (mkGTE uu____2861 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = uu____2868; rng = uu____2869})::[]) -> begin
(

let uu____2876 = (

let uu____2879 = (unboxInt t1)
in (

let uu____2880 = (unboxInt t2)
in ((uu____2879), (uu____2880))))
in (mkGT uu____2876 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = uu____2883; rng = uu____2884})::[]) -> begin
(

let uu____2891 = (

let uu____2894 = (unboxBool t1)
in (

let uu____2895 = (unboxBool t2)
in ((uu____2894), (uu____2895))))
in (mkAnd uu____2891 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = uu____2898; rng = uu____2899})::[]) -> begin
(

let uu____2906 = (

let uu____2909 = (unboxBool t1)
in (

let uu____2910 = (unboxBool t2)
in ((uu____2909), (uu____2910))))
in (mkOr uu____2906 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t)::[]); freevars = uu____2912; rng = uu____2913})::[]) -> begin
(

let uu____2920 = (unboxBool t)
in (mkNot uu____2920 t.rng))
end
| App (Var ("Prims.b2t"), (t1)::[]) -> begin
(

let uu___90_2923 = (unboxBool t1)
in {tm = uu___90_2923.tm; freevars = uu___90_2923.freevars; rng = t.rng})
end
| uu____2926 -> begin
(mkApp (("Valid"), ((t)::[])) t.rng)
end))


let mk_HasType : term  ->  term  ->  term = (fun v t -> (mkApp (("HasType"), ((v)::(t)::[])) t.rng))


let mk_HasTypeZ : term  ->  term  ->  term = (fun v t -> (mkApp (("HasTypeZ"), ((v)::(t)::[])) t.rng))


let mk_IsTyped : term  ->  term = (fun v -> (mkApp (("IsTyped"), ((v)::[])) norng))


let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v t -> (

let uu____2955 = (FStar_Options.unthrottle_inductives ())
in (match (uu____2955) with
| true -> begin
(mk_HasType v t)
end
| uu____2956 -> begin
(mkApp (("HasTypeFuel"), ((f)::(v)::(t)::[])) t.rng)
end)))


let mk_HasTypeWithFuel : term Prims.option  ->  term  ->  term  ->  term = (fun f v t -> (match (f) with
| None -> begin
(mk_HasType v t)
end
| Some (f) -> begin
(mk_HasTypeFuel f v t)
end))


let mk_Destruct : term  ->  FStar_Range.range  ->  term = (fun v -> (mkApp (("Destruct"), ((v)::[]))))


let mk_Rank : term  ->  FStar_Range.range  ->  term = (fun x -> (mkApp (("Rank"), ((x)::[]))))


let mk_tester : Prims.string  ->  term  ->  term = (fun n t -> (mkApp (((Prims.strcat "is-" n)), ((t)::[])) t.rng))


let mk_ApplyTF : term  ->  term  ->  term = (fun t t' -> (mkApp (("ApplyTF"), ((t)::(t')::[])) t.rng))


let mk_ApplyTT : term  ->  term  ->  FStar_Range.range  ->  term = (fun t t' r -> (mkApp (("ApplyTT"), ((t)::(t')::[])) r))


let mk_String_const : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____3012 = (

let uu____3016 = (

let uu____3018 = (mkInteger' i norng)
in (uu____3018)::[])
in (("FString_const"), (uu____3016)))
in (mkApp uu____3012 r)))


let mk_Precedes : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (

let uu____3029 = (mkApp (("Precedes"), ((x1)::(x2)::[])) r)
in (FStar_All.pipe_right uu____3029 mk_Valid)))


let mk_LexCons : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (mkApp (("LexCons"), ((x1)::(x2)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n -> (match ((n = (Prims.parse_int "0"))) with
| true -> begin
(mkApp (("ZFuel"), ([])) norng)
end
| uu____3045 -> begin
(

let uu____3046 = (

let uu____3050 = (

let uu____3052 = (n_fuel (n - (Prims.parse_int "1")))
in (uu____3052)::[])
in (("SFuel"), (uu____3050)))
in (mkApp uu____3046 norng))
end))


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term Prims.option  ->  term Prims.option  ->  FStar_Range.range  ->  term Prims.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (Some (p1), Some (p2)) -> begin
(

let uu____3075 = (mkAnd ((p1), (p2)) r)
in Some (uu____3075))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))


let mk_and_opt_l : term Prims.option Prims.list  ->  FStar_Range.range  ->  term Prims.option = (fun pl r -> (FStar_List.fold_right (fun p out -> (mk_and_opt p out r)) pl None))


let mk_and_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____3108 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l uu____3108)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____3119 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l uu____3119)))


let mk_haseq : term  ->  term = (fun t -> (

let uu____3125 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid uu____3125)))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "(Integer %s)" n)
end
| BoundV (n) -> begin
(

let uu____3139 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "(BoundV %s)" uu____3139))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (Prims.fst fv))
end
| App (op, l) -> begin
(

let uu____3147 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) uu____3147))
end
| Labeled (t, r1, r2) -> begin
(

let uu____3151 = (print_smt_term t)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 uu____3151))
end
| LblPos (t, s) -> begin
(

let uu____3154 = (print_smt_term t)
in (FStar_Util.format2 "(LblPos %s %s)" s uu____3154))
end
| Quant (qop, l, uu____3157, uu____3158, t) -> begin
(

let uu____3168 = (print_smt_term_list_list l)
in (

let uu____3169 = (print_smt_term t)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____3168 uu____3169)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (

let uu____3172 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right uu____3172 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (

let uu____3182 = (

let uu____3183 = (

let uu____3184 = (print_smt_term_list l)
in (Prims.strcat uu____3184 " ] "))
in (Prims.strcat "; [ " uu____3183))
in (Prims.strcat s uu____3182))) "" l))




