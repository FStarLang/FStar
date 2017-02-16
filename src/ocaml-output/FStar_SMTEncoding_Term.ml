
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
| Let of (term Prims.list * term)
| Labeled of (term * Prims.string * FStar_Range.range)
| LblPos of (term * Prims.string) 
 and term =
{tm : term'; freevars : (Prims.string * sort) Prims.list FStar_Syntax_Syntax.memo; rng : FStar_Range.range}


let uu___is_Integer : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Integer (_0) -> begin
true
end
| uu____265 -> begin
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
| uu____277 -> begin
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
| uu____291 -> begin
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
| uu____312 -> begin
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
| uu____342 -> begin
false
end))


let __proj__Quant__item___0 : term'  ->  (qop * term Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term) = (fun projectee -> (match (projectee) with
| Quant (_0) -> begin
_0
end))


let uu___is_Let : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Let (_0) -> begin
true
end
| uu____384 -> begin
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
| uu____408 -> begin
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
| uu____431 -> begin
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
| uu____526 -> begin
false
end))


let uu___is_DeclFun : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DeclFun (_0) -> begin
true
end
| uu____536 -> begin
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
| uu____569 -> begin
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
| uu____603 -> begin
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
| uu____627 -> begin
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
| uu____639 -> begin
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
| uu____651 -> begin
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
| uu____662 -> begin
false
end))


let uu___is_Pop : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____666 -> begin
false
end))


let uu___is_CheckSat : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckSat -> begin
true
end
| uu____670 -> begin
false
end))


let uu___is_GetUnsatCore : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetUnsatCore -> begin
true
end
| uu____674 -> begin
false
end))


let uu___is_SetOption : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOption (_0) -> begin
true
end
| uu____681 -> begin
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
| uu____698 -> begin
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
| uu____735 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun uu___83_740 -> (match (uu___83_740) with
| {tm = FreeV (x); freevars = uu____742; rng = uu____743} -> begin
(fv_sort x)
end
| uu____750 -> begin
(failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun uu___84_753 -> (match (uu___84_753) with
| {tm = FreeV (fv); freevars = uu____755; rng = uu____756} -> begin
fv
end
| uu____763 -> begin
(failwith "impossible")
end))


let rec freevars : term  ->  (Prims.string * sort) Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (uu____784, tms) -> begin
(FStar_List.collect freevars tms)
end
| (Quant (_, _, _, _, t)) | (Labeled (t, _, _)) | (LblPos (t, _)) -> begin
(freevars t)
end
| Let (es, body) -> begin
(FStar_List.collect freevars ((body)::es))
end))


let free_variables : term  ->  fvs = (fun t -> (

let uu____811 = (FStar_ST.read t.freevars)
in (match (uu____811) with
| Some (b) -> begin
b
end
| None -> begin
(

let fvs = (

let uu____834 = (freevars t)
in (FStar_Util.remove_dups fv_eq uu____834))
in ((FStar_ST.write t.freevars (Some (fvs)));
fvs;
))
end)))


let qop_to_string : qop  ->  Prims.string = (fun uu___85_846 -> (match (uu___85_846) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun uu___86_849 -> (match (uu___86_849) with
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


let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun uu___87_854 -> (match (uu___87_854) with
| None -> begin
""
end
| Some (i) -> begin
(

let uu____857 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" uu____857))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____865 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" uu____865))
end
| FreeV (x) -> begin
(

let uu____869 = (

let uu____870 = (strSort (Prims.snd x))
in (Prims.strcat ":" uu____870))
in (Prims.strcat (Prims.fst x) uu____869))
end
| App (op, tms) -> begin
(

let uu____875 = (

let uu____876 = (

let uu____877 = (

let uu____878 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right uu____878 (FStar_String.concat " ")))
in (Prims.strcat uu____877 ")"))
in (Prims.strcat (op_to_string op) uu____876))
in (Prims.strcat "(" uu____875))
end
| Labeled (t, r1, r2) -> begin
(

let uu____884 = (hash_of_term t)
in (

let uu____885 = (

let uu____886 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 uu____886))
in (Prims.strcat uu____884 uu____885)))
end
| LblPos (t, r) -> begin
(

let uu____889 = (

let uu____890 = (hash_of_term t)
in (Prims.strcat uu____890 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " uu____889))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let uu____904 = (

let uu____905 = (

let uu____906 = (

let uu____907 = (

let uu____908 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right uu____908 (FStar_String.concat " ")))
in (

let uu____911 = (

let uu____912 = (

let uu____913 = (hash_of_term body)
in (

let uu____914 = (

let uu____915 = (

let uu____916 = (weightToSmt wopt)
in (

let uu____917 = (

let uu____918 = (

let uu____919 = (

let uu____920 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (

let uu____928 = (FStar_List.map hash_of_term pats)
in (FStar_All.pipe_right uu____928 (FStar_String.concat " "))))))
in (FStar_All.pipe_right uu____920 (FStar_String.concat "; ")))
in (Prims.strcat uu____919 "))"))
in (Prims.strcat " " uu____918))
in (Prims.strcat uu____916 uu____917)))
in (Prims.strcat " " uu____915))
in (Prims.strcat uu____913 uu____914)))
in (Prims.strcat ")(! " uu____912))
in (Prims.strcat uu____907 uu____911)))
in (Prims.strcat " (" uu____906))
in (Prims.strcat (qop_to_string qop) uu____905))
in (Prims.strcat "(" uu____904))
end
| Let (es, body) -> begin
(

let uu____936 = (

let uu____937 = (

let uu____938 = (FStar_List.map hash_of_term es)
in (FStar_All.pipe_right uu____938 (FStar_String.concat " ")))
in (

let uu____941 = (

let uu____942 = (

let uu____943 = (hash_of_term body)
in (Prims.strcat uu____943 ")"))
in (Prims.strcat ") " uu____942))
in (Prims.strcat uu____937 uu____941)))
in (Prims.strcat "(let (" uu____936))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (

let uu____951 = (FStar_Util.mk_ref None)
in {tm = t; freevars = uu____951; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((TrueOp), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((FalseOp), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____980 = (

let uu____981 = (FStar_Util.ensure_decimal i)
in Integer (uu____981))
in (mk uu____980 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____988 = (FStar_Util.string_of_int i)
in (mkInteger uu____988 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun uu____1024 r -> (match (uu____1024) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (TrueOp, uu____1040) -> begin
(mkFalse r)
end
| App (FalseOp, uu____1043) -> begin
(mkTrue r)
end
| uu____1046 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1054 r -> (match (uu____1054) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____1060), uu____1061) -> begin
t2
end
| (uu____1064, App (TrueOp, uu____1065)) -> begin
t1
end
| ((App (FalseOp, _), _)) | ((_, App (FalseOp, _))) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (uu____1081, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), uu____1087) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____1091 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1101 r -> (match (uu____1101) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((App (TrueOp, _), _)) | ((_, App (TrueOp, _))) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____1113), uu____1114) -> begin
t2
end
| (uu____1117, App (FalseOp, uu____1118)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (uu____1128, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), uu____1134) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____1138 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1148 r -> (match (uu____1148) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((_, App (TrueOp, _))) | ((App (FalseOp, _), _)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____1160), uu____1161) -> begin
t2
end
| (uu____1164, App (Imp, (t1')::(t2')::[])) -> begin
(

let uu____1168 = (

let uu____1172 = (

let uu____1174 = (mkAnd ((t1), (t1')) r)
in (uu____1174)::(t2')::[])
in ((Imp), (uu____1172)))
in (mkApp' uu____1168 r))
end
| uu____1176 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op uu____1189 r -> (match (uu____1189) with
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


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun uu____1276 r -> (match (uu____1276) with
| (t1, t2, t3) -> begin
(match (t1.tm) with
| App (TrueOp, uu____1284) -> begin
t2
end
| App (FalseOp, uu____1287) -> begin
t3
end
| uu____1290 -> begin
(match (((t2.tm), (t3.tm))) with
| (App (TrueOp, uu____1291), App (TrueOp, uu____1292)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____1297), uu____1298) -> begin
(

let uu____1301 = (

let uu____1304 = (mkNot t1 t1.rng)
in ((uu____1304), (t3)))
in (mkImp uu____1301 r))
end
| (uu____1305, App (TrueOp, uu____1306)) -> begin
(mkImp ((t1), (t2)) r)
end
| (uu____1309, uu____1310) -> begin
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


let mkQuant : (qop * term Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1338 r -> (match (uu____1338) with
| (qop, pats, wopt, vars, body) -> begin
(match (((FStar_List.length vars) = (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____1364 -> begin
(match (body.tm) with
| App (TrueOp, uu____1365) -> begin
body
end
| uu____1368 -> begin
(mk (Quant (((qop), (pats), (wopt), (vars), (body)))) r)
end)
end)
end))


let mkLet : (term Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1380 r -> (match (uu____1380) with
| (es, body) -> begin
(match (((FStar_List.length es) = (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____1391 -> begin
(mk (Let (((es), (body)))) r)
end)
end))


let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (

let nvars = (FStar_List.length fvs)
in (

let index_of = (fun fv -> (

let uu____1408 = (FStar_Util.try_find_index (fv_eq fv) fvs)
in (match (uu____1408) with
| None -> begin
None
end
| Some (i) -> begin
Some ((nvars - (i + (Prims.parse_int "1"))))
end)))
in (

let rec aux = (fun ix t -> (

let uu____1422 = (FStar_ST.read t.freevars)
in (match (uu____1422) with
| Some ([]) -> begin
t
end
| uu____1438 -> begin
(match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
t
end
| FreeV (x) -> begin
(

let uu____1448 = (index_of x)
in (match (uu____1448) with
| None -> begin
t
end
| Some (i) -> begin
(mkBoundV (i + ix) t.rng)
end))
end
| App (op, tms) -> begin
(

let uu____1455 = (

let uu____1459 = (FStar_List.map (aux ix) tms)
in ((op), (uu____1459)))
in (mkApp' uu____1455 t.rng))
end
| Labeled (t, r1, r2) -> begin
(

let uu____1465 = (

let uu____1466 = (

let uu____1470 = (aux ix t)
in ((uu____1470), (r1), (r2)))
in Labeled (uu____1466))
in (mk uu____1465 t.rng))
end
| LblPos (t, r) -> begin
(

let uu____1473 = (

let uu____1474 = (

let uu____1477 = (aux ix t)
in ((uu____1477), (r)))
in LblPos (uu____1474))
in (mk uu____1473 t.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n = (FStar_List.length vars)
in (

let uu____1493 = (

let uu____1503 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (

let uu____1514 = (aux (ix + n) body)
in ((qop), (uu____1503), (wopt), (vars), (uu____1514))))
in (mkQuant uu____1493 t.rng)))
end
| Let (es, body) -> begin
(

let uu____1525 = (FStar_List.fold_left (fun uu____1532 e -> (match (uu____1532) with
| (ix, l) -> begin
(

let uu____1544 = (

let uu____1546 = (aux ix e)
in (uu____1546)::l)
in (((ix + (Prims.parse_int "1"))), (uu____1544)))
end)) ((ix), ([])) es)
in (match (uu____1525) with
| (ix, es_rev) -> begin
(

let uu____1553 = (

let uu____1557 = (aux ix body)
in (((FStar_List.rev es_rev)), (uu____1557)))
in (mkLet uu____1553 t.rng))
end))
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
| uu____1583 -> begin
t
end)
end
| App (op, tms) -> begin
(

let uu____1588 = (

let uu____1592 = (FStar_List.map (aux shift) tms)
in ((op), (uu____1592)))
in (mkApp' uu____1588 t.rng))
end
| Labeled (t, r1, r2) -> begin
(

let uu____1598 = (

let uu____1599 = (

let uu____1603 = (aux shift t)
in ((uu____1603), (r1), (r2)))
in Labeled (uu____1599))
in (mk uu____1598 t.rng))
end
| LblPos (t, r) -> begin
(

let uu____1606 = (

let uu____1607 = (

let uu____1610 = (aux shift t)
in ((uu____1610), (r)))
in LblPos (uu____1607))
in (mk uu____1606 t.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift = (shift + m)
in (

let uu____1629 = (

let uu____1639 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (

let uu____1648 = (aux shift body)
in ((qop), (uu____1639), (wopt), (vars), (uu____1648))))
in (mkQuant uu____1629 t.rng))))
end
| Let (es, body) -> begin
(

let uu____1657 = (FStar_List.fold_left (fun uu____1664 e -> (match (uu____1664) with
| (ix, es) -> begin
(

let uu____1676 = (

let uu____1678 = (aux shift e)
in (uu____1678)::es)
in (((shift + (Prims.parse_int "1"))), (uu____1676)))
end)) ((shift), ([])) es)
in (match (uu____1657) with
| (shift, es_rev) -> begin
(

let uu____1685 = (

let uu____1689 = (aux shift body)
in (((FStar_List.rev es_rev)), (uu____1689)))
in (mkLet uu____1685 t.rng))
end))
end))
in (aux (Prims.parse_int "0") t)))))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1704 -> (match (uu____1704) with
| (qop, pats, wopt, vars, body) -> begin
(

let uu____1729 = (

let uu____1739 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (

let uu____1748 = (FStar_List.map fv_sort vars)
in (

let uu____1752 = (abstr vars body)
in ((qop), (uu____1739), (wopt), (uu____1748), (uu____1752)))))
in (mkQuant uu____1729))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1769 r -> (match (uu____1769) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)) r)
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____1806 r -> (match (uu____1806) with
| (pats, wopt, vars, body) -> begin
(

let uu____1825 = (mkQuant' ((Forall), (pats), (wopt), (vars), (body)))
in (uu____1825 r))
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____1840 r -> (match (uu____1840) with
| (pats, vars, body) -> begin
(

let uu____1854 = (mkQuant' ((Forall), (pats), (None), (vars), (body)))
in (uu____1854 r))
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____1869 r -> (match (uu____1869) with
| (pats, vars, body) -> begin
(

let uu____1883 = (mkQuant' ((Exists), (pats), (None), (vars), (body)))
in (uu____1883 r))
end))


let mkLet' : ((fv * term) Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1898 r -> (match (uu____1898) with
| (bindings, body) -> begin
(

let uu____1913 = (FStar_List.split bindings)
in (match (uu____1913) with
| (vars, es) -> begin
(

let uu____1924 = (

let uu____1928 = (abstr vars body)
in ((es), (uu____1928)))
in (mkLet uu____1924 r))
end))
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun uu____1940 -> (match (uu____1940) with
| (nm, vars, s, tm, c) -> begin
(

let uu____1960 = (

let uu____1967 = (FStar_List.map fv_sort vars)
in (

let uu____1971 = (abstr vars tm)
in ((nm), (uu____1967), (s), (uu____1971), (c))))
in DefineFun (uu____1960))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (

let uu____1976 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" uu____1976)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun uu____1983 id -> (match (uu____1983) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (

let uu____1990 = (

let uu____1995 = (

let uu____1996 = (

let uu____1999 = (mkInteger' id norng)
in (

let uu____2000 = (

let uu____2001 = (

let uu____2005 = (constr_id_of_sort sort)
in (

let uu____2006 = (

let uu____2008 = (mkApp ((tok_name), ([])) norng)
in (uu____2008)::[])
in ((uu____2005), (uu____2006))))
in (mkApp uu____2001 norng))
in ((uu____1999), (uu____2000))))
in (mkEq uu____1996 norng))
in ((uu____1995), (Some ("fresh token")), (Some (a_name))))
in Assume (uu____1990)))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun uu____2020 -> (match (uu____2020) with
| (name, arg_sorts, sort, id) -> begin
(

let id = (FStar_Util.string_of_int id)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (

let uu____2039 = (

let uu____2042 = (

let uu____2043 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____2043))
in ((uu____2042), (s)))
in (mkFreeV uu____2039 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (

let uu____2049 = (

let uu____2053 = (constr_id_of_sort sort)
in ((uu____2053), ((capp)::[])))
in (mkApp uu____2049 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (

let uu____2056 = (

let uu____2061 = (

let uu____2062 = (

let uu____2068 = (

let uu____2069 = (

let uu____2072 = (mkInteger id norng)
in ((uu____2072), (cid_app)))
in (mkEq uu____2069 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____2068)))
in (mkForall uu____2062 norng))
in ((uu____2061), (Some ("Constructor distinct")), (Some (a_name))))
in Assume (uu____2056))))))))
end))


let injective_constructor : (Prims.string * (Prims.string * sort) Prims.list * sort)  ->  decls_t = (fun uu____2088 -> (match (uu____2088) with
| (name, projectors, sort) -> begin
(

let n_bvars = (FStar_List.length projectors)
in (

let bvar_name = (fun i -> (

let uu____2112 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____2112)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (

let uu____2129 = (

let uu____2132 = (bvar_name i)
in ((uu____2132), (s)))
in (mkFreeV uu____2129)))
in (

let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i uu____2142 -> (match (uu____2142) with
| (uu____2145, s) -> begin
(

let uu____2147 = (bvar i s)
in (uu____2147 norng))
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let uu____2154 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i uu____2166 -> (match (uu____2166) with
| (name, s) -> begin
(

let cproj_app = (mkApp ((name), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((name), ((sort)::[]), (s), (Some ("Projector"))))
in (

let a_name = (Prims.strcat "projection_inverse_" name)
in (

let uu____2178 = (

let uu____2180 = (

let uu____2181 = (

let uu____2186 = (

let uu____2187 = (

let uu____2193 = (

let uu____2194 = (

let uu____2197 = (

let uu____2198 = (bvar i s)
in (uu____2198 norng))
in ((cproj_app), (uu____2197)))
in (mkEq uu____2194 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____2193)))
in (mkForall uu____2187 norng))
in ((uu____2186), (Some ("Projection inverse")), (Some (a_name))))
in Assume (uu____2181))
in (uu____2180)::[])
in (proj_name)::uu____2178))))
end))))
in (FStar_All.pipe_right uu____2154 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun uu____2213 -> (match (uu____2213) with
| (name, projectors, sort, id, injective) -> begin
(

let injective = (injective || true)
in (

let cdecl = (

let uu____2223 = (

let uu____2229 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (uu____2229), (sort), (Some ("Constructor"))))
in DeclFun (uu____2223))
in (

let cid = (

let uu____2238 = (

let uu____2244 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (uu____2244), (sort), (id)))
in (fresh_constructor uu____2238))
in (

let disc = (

let disc_name = (Prims.strcat "is-" name)
in (

let xfv = (("x"), (sort))
in (

let xx = (mkFreeV xfv norng)
in (

let disc_eq = (

let uu____2258 = (

let uu____2261 = (

let uu____2262 = (

let uu____2266 = (constr_id_of_sort sort)
in ((uu____2266), ((xx)::[])))
in (mkApp uu____2262 norng))
in (

let uu____2268 = (

let uu____2269 = (FStar_Util.string_of_int id)
in (mkInteger uu____2269 norng))
in ((uu____2261), (uu____2268))))
in (mkEq uu____2258 norng))
in (

let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun uu____2276 -> (match (uu____2276) with
| (proj, s) -> begin
(mkApp ((proj), ((xx)::[])) norng)
end))))
in (

let disc_inv_body = (

let uu____2283 = (

let uu____2286 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (uu____2286)))
in (mkEq uu____2283 norng))
in (

let disc_ax = (mkAnd ((disc_eq), (disc_inv_body)) norng)
in (mkDefineFun ((disc_name), ((xfv)::[]), (Bool_sort), (disc_ax), (Some ("Discriminator definition")))))))))))
in (

let projs = (match (injective) with
| true -> begin
(injective_constructor ((name), (projectors), (sort)))
end
| uu____2299 -> begin
[]
end)
in (

let uu____2300 = (

let uu____2302 = (

let uu____2303 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (uu____2303))
in (uu____2302)::(cdecl)::(cid)::projs)
in (

let uu____2304 = (

let uu____2306 = (

let uu____2308 = (

let uu____2309 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (uu____2309))
in (uu____2308)::[])
in (FStar_List.append ((disc)::[]) uu____2306))
in (FStar_List.append uu____2300 uu____2304))))))))
end))


let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (

let uu____2334 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun uu____2357 s -> (match (uu____2357) with
| (names, binders, n) -> begin
(

let prefix = (match (s) with
| Term_sort -> begin
"@x"
end
| uu____2385 -> begin
"@u"
end)
in (

let nm = (

let uu____2387 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix uu____2387))
in (

let names = (((nm), (s)))::names
in (

let b = (

let uu____2395 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm uu____2395))
in ((names), ((b)::binders), ((n + (Prims.parse_int "1"))))))))
end)) ((outer_names), ([]), (start))))
in (match (uu____2334) with
| (names, binders, n) -> begin
((names), ((FStar_List.rev binders)), (n))
end)))


let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let uu____2437 = (name_binders_inner [] (Prims.parse_int "0") sorts)
in (match (uu____2437) with
| (names, binders, n) -> begin
(((FStar_List.rev names)), (binders))
end)))


let termToSmt : term  ->  Prims.string = (fun t -> (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (uu____2494); freevars = uu____2495; rng = uu____2496})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| uu____2504 -> begin
tm
end))))))))
in (

let rec aux' = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____2527 = (FStar_List.nth names i)
in (FStar_All.pipe_right uu____2527 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(

let uu____2537 = (

let uu____2538 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right uu____2538 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) uu____2537))
end
| Labeled (t, uu____2542, uu____2543) -> begin
(aux n names t)
end
| LblPos (t, s) -> begin
(

let uu____2546 = (aux n names t)
in (FStar_Util.format2 "(! %s :lblpos %s)" uu____2546 s))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let uu____2560 = (name_binders_inner names n sorts)
in (match (uu____2560) with
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
| uu____2588 -> begin
(

let uu____2591 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (

let uu____2599 = (

let uu____2600 = (FStar_List.map (fun p -> (

let uu____2603 = (aux n names p)
in (FStar_Util.format1 "%s" uu____2603))) pats)
in (FStar_String.concat " " uu____2600))
in (FStar_Util.format1 "\n:pattern (%s)" uu____2599)))))
in (FStar_All.pipe_right uu____2591 (FStar_String.concat "\n")))
end)
in (match (((pats), (wopt))) with
| ((([])::[], None)) | (([], None)) -> begin
(

let uu____2617 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders uu____2617))
end
| uu____2618 -> begin
(

let uu____2624 = (aux n names body)
in (

let uu____2625 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders uu____2624 uu____2625 pats_str)))
end))))
end))
end
| Let (es, body) -> begin
(

let uu____2630 = (FStar_List.fold_left (fun uu____2645 e -> (match (uu____2645) with
| (names0, binders, n0) -> begin
(

let nm = (

let uu____2673 = (FStar_Util.string_of_int n0)
in (Prims.strcat "@lb" uu____2673))
in (

let names0 = (((nm), (Term_sort)))::names0
in (

let b = (

let uu____2681 = (aux n names e)
in (FStar_Util.format2 "(%s %s)" nm uu____2681))
in ((names0), ((b)::binders), ((n0 + (Prims.parse_int "1")))))))
end)) ((names), ([]), (n)) es)
in (match (uu____2630) with
| (names, binders, n) -> begin
(

let uu____2699 = (aux n names body)
in (FStar_Util.format2 "(let (%s) %s)" (FStar_String.concat " " binders) uu____2699))
end))
end))
and aux = (fun n names t -> (

let s = (aux' n names t)
in (match ((t.rng <> norng)) with
| true -> begin
(

let uu____2705 = (FStar_Range.string_of_range t.rng)
in (

let uu____2706 = (FStar_Range.string_of_use_range t.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____2705 uu____2706 s)))
end
| uu____2707 -> begin
s
end)))
in (aux (Prims.parse_int "0") [] t))))


let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun uu___88_2711 -> (match (uu___88_2711) with
| None -> begin
""
end
| Some (c) -> begin
(

let uu____2714 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(failwith "Impossible")
end
| (hd)::[] -> begin
((hd), (""))
end
| (hd)::uu____2723 -> begin
((hd), ("..."))
end)
in (match (uu____2714) with
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

let uu____2740 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun uu___89_2742 -> (match (uu___89_2742) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" uu____2740))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (

let uu____2755 = (caption_to_string c)
in (

let uu____2756 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____2755 f (FStar_String.concat " " l) uu____2756))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let uu____2764 = (name_binders arg_sorts)
in (match (uu____2764) with
| (names, binders) -> begin
(

let body = (

let uu____2782 = (FStar_List.map (fun x -> (mkFreeV x norng)) names)
in (inst uu____2782 body))
in (

let uu____2789 = (caption_to_string c)
in (

let uu____2790 = (strSort retsort)
in (

let uu____2791 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____2789 f (FStar_String.concat " " binders) uu____2790 uu____2791)))))
end))
end
| Assume (t, c, Some (n)) -> begin
(

let uu____2796 = (caption_to_string c)
in (

let uu____2797 = (termToSmt t)
in (FStar_Util.format3 "%s(assert (!\n%s\n:named %s))" uu____2796 uu____2797 (escape n))))
end
| Assume (t, c, None) -> begin
(

let uu____2801 = (caption_to_string c)
in (

let uu____2802 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" uu____2801 uu____2802)))
end
| Eval (t) -> begin
(

let uu____2804 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" uu____2804))
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

let uu____2968 = (

let uu____2970 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right uu____2970 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right uu____2968 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mk_Range_const : term = (mkApp (("Range_const"), ([])) norng)


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____2995 = (

let uu____2999 = (

let uu____3001 = (mkInteger' i norng)
in (uu____3001)::[])
in (("Tm_uvar"), (uu____2999)))
in (mkApp uu____2995 r)))


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
| uu____3042 -> begin
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
| uu____3049 -> begin
(Prims.raise FStar_Util.Impos)
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (uu____3057)::(t1)::(t2)::[]); freevars = uu____3060; rng = uu____3061})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (uu____3068)::(t1)::(t2)::[]); freevars = uu____3071; rng = uu____3072})::[]) -> begin
(

let uu____3079 = (mkEq ((t1), (t2)) norng)
in (mkNot uu____3079 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = uu____3082; rng = uu____3083})::[]) -> begin
(

let uu____3090 = (

let uu____3093 = (unboxInt t1)
in (

let uu____3094 = (unboxInt t2)
in ((uu____3093), (uu____3094))))
in (mkLTE uu____3090 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = uu____3097; rng = uu____3098})::[]) -> begin
(

let uu____3105 = (

let uu____3108 = (unboxInt t1)
in (

let uu____3109 = (unboxInt t2)
in ((uu____3108), (uu____3109))))
in (mkLT uu____3105 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = uu____3112; rng = uu____3113})::[]) -> begin
(

let uu____3120 = (

let uu____3123 = (unboxInt t1)
in (

let uu____3124 = (unboxInt t2)
in ((uu____3123), (uu____3124))))
in (mkGTE uu____3120 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = uu____3127; rng = uu____3128})::[]) -> begin
(

let uu____3135 = (

let uu____3138 = (unboxInt t1)
in (

let uu____3139 = (unboxInt t2)
in ((uu____3138), (uu____3139))))
in (mkGT uu____3135 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = uu____3142; rng = uu____3143})::[]) -> begin
(

let uu____3150 = (

let uu____3153 = (unboxBool t1)
in (

let uu____3154 = (unboxBool t2)
in ((uu____3153), (uu____3154))))
in (mkAnd uu____3150 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = uu____3157; rng = uu____3158})::[]) -> begin
(

let uu____3165 = (

let uu____3168 = (unboxBool t1)
in (

let uu____3169 = (unboxBool t2)
in ((uu____3168), (uu____3169))))
in (mkOr uu____3165 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t)::[]); freevars = uu____3171; rng = uu____3172})::[]) -> begin
(

let uu____3179 = (unboxBool t)
in (mkNot uu____3179 t.rng))
end
| App (Var ("Prims.b2t"), (t1)::[]) -> begin
(

let uu___90_3182 = (unboxBool t1)
in {tm = uu___90_3182.tm; freevars = uu___90_3182.freevars; rng = t.rng})
end
| uu____3185 -> begin
(mkApp (("Valid"), ((t)::[])) t.rng)
end))


let mk_HasType : term  ->  term  ->  term = (fun v t -> (mkApp (("HasType"), ((v)::(t)::[])) t.rng))


let mk_HasTypeZ : term  ->  term  ->  term = (fun v t -> (mkApp (("HasTypeZ"), ((v)::(t)::[])) t.rng))


let mk_IsTyped : term  ->  term = (fun v -> (mkApp (("IsTyped"), ((v)::[])) norng))


let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v t -> (

let uu____3214 = (FStar_Options.unthrottle_inductives ())
in (match (uu____3214) with
| true -> begin
(mk_HasType v t)
end
| uu____3215 -> begin
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

let uu____3271 = (

let uu____3275 = (

let uu____3277 = (mkInteger' i norng)
in (uu____3277)::[])
in (("FString_const"), (uu____3275)))
in (mkApp uu____3271 r)))


let mk_Precedes : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (

let uu____3288 = (mkApp (("Precedes"), ((x1)::(x2)::[])) r)
in (FStar_All.pipe_right uu____3288 mk_Valid)))


let mk_LexCons : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (mkApp (("LexCons"), ((x1)::(x2)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n -> (match ((n = (Prims.parse_int "0"))) with
| true -> begin
(mkApp (("ZFuel"), ([])) norng)
end
| uu____3304 -> begin
(

let uu____3305 = (

let uu____3309 = (

let uu____3311 = (n_fuel (n - (Prims.parse_int "1")))
in (uu____3311)::[])
in (("SFuel"), (uu____3309)))
in (mkApp uu____3305 norng))
end))


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term Prims.option  ->  term Prims.option  ->  FStar_Range.range  ->  term Prims.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (Some (p1), Some (p2)) -> begin
(

let uu____3334 = (mkAnd ((p1), (p2)) r)
in Some (uu____3334))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))


let mk_and_opt_l : term Prims.option Prims.list  ->  FStar_Range.range  ->  term Prims.option = (fun pl r -> (FStar_List.fold_right (fun p out -> (mk_and_opt p out r)) pl None))


let mk_and_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____3367 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l uu____3367)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____3378 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l uu____3378)))


let mk_haseq : term  ->  term = (fun t -> (

let uu____3384 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid uu____3384)))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "(Integer %s)" n)
end
| BoundV (n) -> begin
(

let uu____3398 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "(BoundV %s)" uu____3398))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (Prims.fst fv))
end
| App (op, l) -> begin
(

let uu____3406 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) uu____3406))
end
| Labeled (t, r1, r2) -> begin
(

let uu____3410 = (print_smt_term t)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 uu____3410))
end
| LblPos (t, s) -> begin
(

let uu____3413 = (print_smt_term t)
in (FStar_Util.format2 "(LblPos %s %s)" s uu____3413))
end
| Quant (qop, l, uu____3416, uu____3417, t) -> begin
(

let uu____3427 = (print_smt_term_list_list l)
in (

let uu____3428 = (print_smt_term t)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____3427 uu____3428)))
end
| Let (es, body) -> begin
(

let uu____3433 = (print_smt_term_list es)
in (

let uu____3434 = (print_smt_term body)
in (FStar_Util.format2 "(let %s %s)" uu____3433 uu____3434)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (

let uu____3437 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right uu____3437 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (

let uu____3447 = (

let uu____3448 = (

let uu____3449 = (print_smt_term_list l)
in (Prims.strcat uu____3449 " ] "))
in (Prims.strcat "; [ " uu____3448))
in (Prims.strcat s uu____3447))) "" l))




