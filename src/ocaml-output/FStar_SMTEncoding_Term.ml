
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


type constructor_field =
(Prims.string * sort * Prims.bool)


type constructor_t =
(Prims.string * constructor_field Prims.list * sort * Prims.int * Prims.bool)


type constructors =
constructor_t Prims.list

type decl =
| DefPrelude
| DeclFun of (Prims.string * sort Prims.list * sort * caption)
| DefineFun of (Prims.string * sort Prims.list * sort * term * caption)
| Assume of (term * caption * Prims.string)
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
| uu____602 -> begin
false
end))


let __proj__Assume__item___0 : decl  ->  (term * caption * Prims.string) = (fun projectee -> (match (projectee) with
| Assume (_0) -> begin
_0
end))


let uu___is_Caption : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Caption (_0) -> begin
true
end
| uu____623 -> begin
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
| uu____635 -> begin
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
| uu____647 -> begin
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
| uu____658 -> begin
false
end))


let uu___is_Pop : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____662 -> begin
false
end))


let uu___is_CheckSat : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckSat -> begin
true
end
| uu____666 -> begin
false
end))


let uu___is_GetUnsatCore : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetUnsatCore -> begin
true
end
| uu____670 -> begin
false
end))


let uu___is_SetOption : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOption (_0) -> begin
true
end
| uu____677 -> begin
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
| uu____694 -> begin
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
| (FreeV (x1), FreeV (y1)) -> begin
(fv_eq x1 y1)
end
| uu____731 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun uu___83_736 -> (match (uu___83_736) with
| {tm = FreeV (x); freevars = uu____738; rng = uu____739} -> begin
(fv_sort x)
end
| uu____746 -> begin
(failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun uu___84_749 -> (match (uu___84_749) with
| {tm = FreeV (fv); freevars = uu____751; rng = uu____752} -> begin
fv
end
| uu____759 -> begin
(failwith "impossible")
end))


let rec freevars : term  ->  (Prims.string * sort) Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (uu____780, tms) -> begin
(FStar_List.collect freevars tms)
end
| (Quant (_, _, _, _, t1)) | (Labeled (t1, _, _)) | (LblPos (t1, _)) -> begin
(freevars t1)
end
| Let (es, body) -> begin
(FStar_List.collect freevars ((body)::es))
end))


let free_variables : term  ->  fvs = (fun t -> (

let uu____807 = (FStar_ST.read t.freevars)
in (match (uu____807) with
| Some (b) -> begin
b
end
| None -> begin
(

let fvs = (

let uu____830 = (freevars t)
in (FStar_Util.remove_dups fv_eq uu____830))
in ((FStar_ST.write t.freevars (Some (fvs)));
fvs;
))
end)))


let qop_to_string : qop  ->  Prims.string = (fun uu___85_842 -> (match (uu___85_842) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun uu___86_845 -> (match (uu___86_845) with
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


let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun uu___87_850 -> (match (uu___87_850) with
| None -> begin
""
end
| Some (i) -> begin
(

let uu____853 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" uu____853))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____861 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" uu____861))
end
| FreeV (x) -> begin
(

let uu____865 = (

let uu____866 = (strSort (Prims.snd x))
in (Prims.strcat ":" uu____866))
in (Prims.strcat (Prims.fst x) uu____865))
end
| App (op, tms) -> begin
(

let uu____871 = (

let uu____872 = (

let uu____873 = (

let uu____874 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right uu____874 (FStar_String.concat " ")))
in (Prims.strcat uu____873 ")"))
in (Prims.strcat (op_to_string op) uu____872))
in (Prims.strcat "(" uu____871))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____880 = (hash_of_term t1)
in (

let uu____881 = (

let uu____882 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 uu____882))
in (Prims.strcat uu____880 uu____881)))
end
| LblPos (t1, r) -> begin
(

let uu____885 = (

let uu____886 = (hash_of_term t1)
in (Prims.strcat uu____886 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " uu____885))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let uu____900 = (

let uu____901 = (

let uu____902 = (

let uu____903 = (

let uu____904 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right uu____904 (FStar_String.concat " ")))
in (

let uu____907 = (

let uu____908 = (

let uu____909 = (hash_of_term body)
in (

let uu____910 = (

let uu____911 = (

let uu____912 = (weightToSmt wopt)
in (

let uu____913 = (

let uu____914 = (

let uu____915 = (

let uu____916 = (FStar_All.pipe_right pats (FStar_List.map (fun pats1 -> (

let uu____924 = (FStar_List.map hash_of_term pats1)
in (FStar_All.pipe_right uu____924 (FStar_String.concat " "))))))
in (FStar_All.pipe_right uu____916 (FStar_String.concat "; ")))
in (Prims.strcat uu____915 "))"))
in (Prims.strcat " " uu____914))
in (Prims.strcat uu____912 uu____913)))
in (Prims.strcat " " uu____911))
in (Prims.strcat uu____909 uu____910)))
in (Prims.strcat ")(! " uu____908))
in (Prims.strcat uu____903 uu____907)))
in (Prims.strcat " (" uu____902))
in (Prims.strcat (qop_to_string qop) uu____901))
in (Prims.strcat "(" uu____900))
end
| Let (es, body) -> begin
(

let uu____932 = (

let uu____933 = (

let uu____934 = (FStar_List.map hash_of_term es)
in (FStar_All.pipe_right uu____934 (FStar_String.concat " ")))
in (

let uu____937 = (

let uu____938 = (

let uu____939 = (hash_of_term body)
in (Prims.strcat uu____939 ")"))
in (Prims.strcat ") " uu____938))
in (Prims.strcat uu____933 uu____937)))
in (Prims.strcat "(let (" uu____932))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (

let uu____947 = (FStar_Util.mk_ref None)
in {tm = t; freevars = uu____947; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((TrueOp), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((FalseOp), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____976 = (

let uu____977 = (FStar_Util.ensure_decimal i)
in Integer (uu____977))
in (mk uu____976 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____984 = (FStar_Util.string_of_int i)
in (mkInteger uu____984 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun uu____1020 r -> (match (uu____1020) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (TrueOp, uu____1036) -> begin
(mkFalse r)
end
| App (FalseOp, uu____1039) -> begin
(mkTrue r)
end
| uu____1042 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1050 r -> (match (uu____1050) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____1056), uu____1057) -> begin
t2
end
| (uu____1060, App (TrueOp, uu____1061)) -> begin
t1
end
| ((App (FalseOp, _), _)) | ((_, App (FalseOp, _))) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (uu____1077, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), uu____1083) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____1087 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1097 r -> (match (uu____1097) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((App (TrueOp, _), _)) | ((_, App (TrueOp, _))) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____1109), uu____1110) -> begin
t2
end
| (uu____1113, App (FalseOp, uu____1114)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (uu____1124, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), uu____1130) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____1134 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1144 r -> (match (uu____1144) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((_, App (TrueOp, _))) | ((App (FalseOp, _), _)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____1156), uu____1157) -> begin
t2
end
| (uu____1160, App (Imp, (t1')::(t2')::[])) -> begin
(

let uu____1164 = (

let uu____1168 = (

let uu____1170 = (mkAnd ((t1), (t1')) r)
in (uu____1170)::(t2')::[])
in ((Imp), (uu____1168)))
in (mkApp' uu____1164 r))
end
| uu____1172 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op uu____1185 r -> (match (uu____1185) with
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


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun uu____1272 r -> (match (uu____1272) with
| (t1, t2, t3) -> begin
(match (t1.tm) with
| App (TrueOp, uu____1280) -> begin
t2
end
| App (FalseOp, uu____1283) -> begin
t3
end
| uu____1286 -> begin
(match (((t2.tm), (t3.tm))) with
| (App (TrueOp, uu____1287), App (TrueOp, uu____1288)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____1293), uu____1294) -> begin
(

let uu____1297 = (

let uu____1300 = (mkNot t1 t1.rng)
in ((uu____1300), (t3)))
in (mkImp uu____1297 r))
end
| (uu____1301, App (TrueOp, uu____1302)) -> begin
(mkImp ((t1), (t2)) r)
end
| (uu____1305, uu____1306) -> begin
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


let mkQuant : (qop * term Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1334 r -> (match (uu____1334) with
| (qop, pats, wopt, vars, body) -> begin
(match (((FStar_List.length vars) = (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____1360 -> begin
(match (body.tm) with
| App (TrueOp, uu____1361) -> begin
body
end
| uu____1364 -> begin
(mk (Quant (((qop), (pats), (wopt), (vars), (body)))) r)
end)
end)
end))


let mkLet : (term Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1376 r -> (match (uu____1376) with
| (es, body) -> begin
(match (((FStar_List.length es) = (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____1387 -> begin
(mk (Let (((es), (body)))) r)
end)
end))


let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (

let nvars = (FStar_List.length fvs)
in (

let index_of = (fun fv -> (

let uu____1404 = (FStar_Util.try_find_index (fv_eq fv) fvs)
in (match (uu____1404) with
| None -> begin
None
end
| Some (i) -> begin
Some ((nvars - (i + (Prims.parse_int "1"))))
end)))
in (

let rec aux = (fun ix t1 -> (

let uu____1418 = (FStar_ST.read t1.freevars)
in (match (uu____1418) with
| Some ([]) -> begin
t1
end
| uu____1434 -> begin
(match (t1.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
t1
end
| FreeV (x) -> begin
(

let uu____1444 = (index_of x)
in (match (uu____1444) with
| None -> begin
t1
end
| Some (i) -> begin
(mkBoundV (i + ix) t1.rng)
end))
end
| App (op, tms) -> begin
(

let uu____1451 = (

let uu____1455 = (FStar_List.map (aux ix) tms)
in ((op), (uu____1455)))
in (mkApp' uu____1451 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____1461 = (

let uu____1462 = (

let uu____1466 = (aux ix t2)
in ((uu____1466), (r1), (r2)))
in Labeled (uu____1462))
in (mk uu____1461 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____1469 = (

let uu____1470 = (

let uu____1473 = (aux ix t2)
in ((uu____1473), (r)))
in LblPos (uu____1470))
in (mk uu____1469 t2.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n1 = (FStar_List.length vars)
in (

let uu____1489 = (

let uu____1499 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n1)))))
in (

let uu____1510 = (aux (ix + n1) body)
in ((qop), (uu____1499), (wopt), (vars), (uu____1510))))
in (mkQuant uu____1489 t1.rng)))
end
| Let (es, body) -> begin
(

let uu____1521 = (FStar_List.fold_left (fun uu____1528 e -> (match (uu____1528) with
| (ix1, l) -> begin
(

let uu____1540 = (

let uu____1542 = (aux ix1 e)
in (uu____1542)::l)
in (((ix1 + (Prims.parse_int "1"))), (uu____1540)))
end)) ((ix), ([])) es)
in (match (uu____1521) with
| (ix1, es_rev) -> begin
(

let uu____1549 = (

let uu____1553 = (aux ix1 body)
in (((FStar_List.rev es_rev)), (uu____1553)))
in (mkLet uu____1549 t1.rng))
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
| (Integer (_)) | (FreeV (_)) -> begin
t1
end
| BoundV (i) -> begin
(match ((((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1))) with
| true -> begin
(FStar_List.nth tms1 (i - shift))
end
| uu____1579 -> begin
t1
end)
end
| App (op, tms2) -> begin
(

let uu____1584 = (

let uu____1588 = (FStar_List.map (aux shift) tms2)
in ((op), (uu____1588)))
in (mkApp' uu____1584 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____1594 = (

let uu____1595 = (

let uu____1599 = (aux shift t2)
in ((uu____1599), (r1), (r2)))
in Labeled (uu____1595))
in (mk uu____1594 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____1602 = (

let uu____1603 = (

let uu____1606 = (aux shift t2)
in ((uu____1606), (r)))
in LblPos (uu____1603))
in (mk uu____1602 t2.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift1 = (shift + m)
in (

let uu____1625 = (

let uu____1635 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift1))))
in (

let uu____1644 = (aux shift1 body)
in ((qop), (uu____1635), (wopt), (vars), (uu____1644))))
in (mkQuant uu____1625 t1.rng))))
end
| Let (es, body) -> begin
(

let uu____1653 = (FStar_List.fold_left (fun uu____1660 e -> (match (uu____1660) with
| (ix, es1) -> begin
(

let uu____1672 = (

let uu____1674 = (aux shift e)
in (uu____1674)::es1)
in (((shift + (Prims.parse_int "1"))), (uu____1672)))
end)) ((shift), ([])) es)
in (match (uu____1653) with
| (shift1, es_rev) -> begin
(

let uu____1681 = (

let uu____1685 = (aux shift1 body)
in (((FStar_List.rev es_rev)), (uu____1685)))
in (mkLet uu____1681 t1.rng))
end))
end))
in (aux (Prims.parse_int "0") t)))))


let subst : term  ->  fv  ->  term  ->  term = (fun t fv s -> (

let uu____1696 = (abstr ((fv)::[]) t)
in (inst ((s)::[]) uu____1696)))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1710 -> (match (uu____1710) with
| (qop, pats, wopt, vars, body) -> begin
(

let uu____1735 = (

let uu____1745 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (

let uu____1754 = (FStar_List.map fv_sort vars)
in (

let uu____1758 = (abstr vars body)
in ((qop), (uu____1745), (wopt), (uu____1754), (uu____1758)))))
in (mkQuant uu____1735))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1775 r -> (match (uu____1775) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)) r)
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____1812 r -> (match (uu____1812) with
| (pats, wopt, vars, body) -> begin
(

let uu____1831 = (mkQuant' ((Forall), (pats), (wopt), (vars), (body)))
in (uu____1831 r))
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____1846 r -> (match (uu____1846) with
| (pats, vars, body) -> begin
(

let uu____1860 = (mkQuant' ((Forall), (pats), (None), (vars), (body)))
in (uu____1860 r))
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____1875 r -> (match (uu____1875) with
| (pats, vars, body) -> begin
(

let uu____1889 = (mkQuant' ((Exists), (pats), (None), (vars), (body)))
in (uu____1889 r))
end))


let mkLet' : ((fv * term) Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1904 r -> (match (uu____1904) with
| (bindings, body) -> begin
(

let uu____1919 = (FStar_List.split bindings)
in (match (uu____1919) with
| (vars, es) -> begin
(

let uu____1930 = (

let uu____1934 = (abstr vars body)
in ((es), (uu____1934)))
in (mkLet uu____1930 r))
end))
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun uu____1946 -> (match (uu____1946) with
| (nm, vars, s, tm, c) -> begin
(

let uu____1966 = (

let uu____1973 = (FStar_List.map fv_sort vars)
in (

let uu____1977 = (abstr vars tm)
in ((nm), (uu____1973), (s), (uu____1977), (c))))
in DefineFun (uu____1966))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (

let uu____1982 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" uu____1982)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun uu____1989 id -> (match (uu____1989) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (

let uu____1996 = (

let uu____2000 = (

let uu____2001 = (

let uu____2004 = (mkInteger' id norng)
in (

let uu____2005 = (

let uu____2006 = (

let uu____2010 = (constr_id_of_sort sort)
in (

let uu____2011 = (

let uu____2013 = (mkApp ((tok_name), ([])) norng)
in (uu____2013)::[])
in ((uu____2010), (uu____2011))))
in (mkApp uu____2006 norng))
in ((uu____2004), (uu____2005))))
in (mkEq uu____2001 norng))
in ((uu____2000), (Some ("fresh token")), (a_name)))
in Assume (uu____1996)))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun uu____2024 -> (match (uu____2024) with
| (name, arg_sorts, sort, id) -> begin
(

let id1 = (FStar_Util.string_of_int id)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (

let uu____2043 = (

let uu____2046 = (

let uu____2047 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____2047))
in ((uu____2046), (s)))
in (mkFreeV uu____2043 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (

let uu____2053 = (

let uu____2057 = (constr_id_of_sort sort)
in ((uu____2057), ((capp)::[])))
in (mkApp uu____2053 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (

let uu____2060 = (

let uu____2064 = (

let uu____2065 = (

let uu____2071 = (

let uu____2072 = (

let uu____2075 = (mkInteger id1 norng)
in ((uu____2075), (cid_app)))
in (mkEq uu____2072 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____2071)))
in (mkForall uu____2065 norng))
in ((uu____2064), (Some ("Constructor distinct")), (a_name)))
in Assume (uu____2060))))))))
end))


let injective_constructor : (Prims.string * constructor_field Prims.list * sort)  ->  decls_t = (fun uu____2088 -> (match (uu____2088) with
| (name, fields, sort) -> begin
(

let n_bvars = (FStar_List.length fields)
in (

let bvar_name = (fun i -> (

let uu____2104 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____2104)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (

let uu____2121 = (

let uu____2124 = (bvar_name i)
in ((uu____2124), (s)))
in (mkFreeV uu____2121)))
in (

let bvars = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____2133 -> (match (uu____2133) with
| (uu____2137, s, uu____2139) -> begin
(

let uu____2140 = (bvar i s)
in (uu____2140 norng))
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let uu____2147 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____2158 -> (match (uu____2158) with
| (name1, s, projectible) -> begin
(

let cproj_app = (mkApp ((name1), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((name1), ((sort)::[]), (s), (Some ("Projector"))))
in (match (projectible) with
| true -> begin
(

let a_name = (Prims.strcat "projection_inverse_" name1)
in (

let uu____2173 = (

let uu____2175 = (

let uu____2176 = (

let uu____2180 = (

let uu____2181 = (

let uu____2187 = (

let uu____2188 = (

let uu____2191 = (

let uu____2192 = (bvar i s)
in (uu____2192 norng))
in ((cproj_app), (uu____2191)))
in (mkEq uu____2188 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____2187)))
in (mkForall uu____2181 norng))
in ((uu____2180), (Some ("Projection inverse")), (a_name)))
in Assume (uu____2176))
in (uu____2175)::[])
in (proj_name)::uu____2173))
end
| uu____2201 -> begin
(proj_name)::[]
end)))
end))))
in (FStar_All.pipe_right uu____2147 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun uu____2207 -> (match (uu____2207) with
| (name, fields, sort, id, injective) -> begin
(

let injective1 = (injective || true)
in (

let field_sorts = (FStar_All.pipe_right fields (FStar_List.map (fun uu____2223 -> (match (uu____2223) with
| (uu____2227, sort1, uu____2229) -> begin
sort1
end))))
in (

let cdecl = DeclFun (((name), (field_sorts), (sort), (Some ("Constructor"))))
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

let uu____2242 = (

let uu____2245 = (

let uu____2246 = (

let uu____2250 = (constr_id_of_sort sort)
in ((uu____2250), ((xx)::[])))
in (mkApp uu____2246 norng))
in (

let uu____2252 = (

let uu____2253 = (FStar_Util.string_of_int id)
in (mkInteger uu____2253 norng))
in ((uu____2245), (uu____2252))))
in (mkEq uu____2242 norng))
in (

let uu____2254 = (

let uu____2262 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____2285 -> (match (uu____2285) with
| (proj, s, projectible) -> begin
(match (projectible) with
| true -> begin
(

let uu____2302 = (mkApp ((proj), ((xx)::[])) norng)
in ((uu____2302), ([])))
end
| uu____2309 -> begin
(

let fi = (

let uu____2313 = (

let uu____2314 = (FStar_Util.string_of_int i)
in (Prims.strcat "f_" uu____2314))
in ((uu____2313), (s)))
in (

let uu____2315 = (mkFreeV fi norng)
in ((uu____2315), ((fi)::[]))))
end)
end))))
in (FStar_All.pipe_right uu____2262 FStar_List.split))
in (match (uu____2254) with
| (proj_terms, ex_vars) -> begin
(

let ex_vars1 = (FStar_List.flatten ex_vars)
in (

let disc_inv_body = (

let uu____2358 = (

let uu____2361 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (uu____2361)))
in (mkEq uu____2358 norng))
in (

let disc_inv_body1 = (match (ex_vars1) with
| [] -> begin
disc_inv_body
end
| uu____2366 -> begin
(mkExists (([]), (ex_vars1), (disc_inv_body)) norng)
end)
in (

let disc_ax = (mkAnd ((disc_eq), (disc_inv_body1)) norng)
in (

let def = (mkDefineFun ((disc_name), ((xfv)::[]), (Bool_sort), (disc_ax), (Some ("Discriminator definition"))))
in def)))))
end))))))
in (

let projs = (match (injective1) with
| true -> begin
(injective_constructor ((name), (fields), (sort)))
end
| uu____2388 -> begin
[]
end)
in (

let uu____2389 = (

let uu____2391 = (

let uu____2392 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (uu____2392))
in (uu____2391)::(cdecl)::(cid)::projs)
in (

let uu____2393 = (

let uu____2395 = (

let uu____2397 = (

let uu____2398 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (uu____2398))
in (uu____2397)::[])
in (FStar_List.append ((disc)::[]) uu____2395))
in (FStar_List.append uu____2389 uu____2393)))))))))
end))


let name_binders_inner : Prims.string Prims.option  ->  (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun prefix_opt outer_names start sorts -> (

let uu____2428 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun uu____2451 s -> (match (uu____2451) with
| (names, binders, n1) -> begin
(

let prefix1 = (match (s) with
| Term_sort -> begin
"@x"
end
| uu____2479 -> begin
"@u"
end)
in (

let prefix2 = (match (prefix_opt) with
| None -> begin
prefix1
end
| Some (p) -> begin
(Prims.strcat p prefix1)
end)
in (

let nm = (

let uu____2483 = (FStar_Util.string_of_int n1)
in (Prims.strcat prefix2 uu____2483))
in (

let names1 = (((nm), (s)))::names
in (

let b = (

let uu____2491 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm uu____2491))
in ((names1), ((b)::binders), ((n1 + (Prims.parse_int "1")))))))))
end)) ((outer_names), ([]), (start))))
in (match (uu____2428) with
| (names, binders, n1) -> begin
((names), ((FStar_List.rev binders)), (n1))
end)))


let name_macro_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let uu____2533 = (name_binders_inner (Some ("__")) [] (Prims.parse_int "0") sorts)
in (match (uu____2533) with
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
| uu____2586 -> begin
(

let uu____2587 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "%s.%s" enclosing_name uu____2587))
end);
))))
in (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (uu____2609); freevars = uu____2610; rng = uu____2611})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| uu____2619 -> begin
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

let uu____2655 = (FStar_List.nth names i)
in (FStar_All.pipe_right uu____2655 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(

let uu____2665 = (

let uu____2666 = (FStar_List.map (aux1 n1 names) tms)
in (FStar_All.pipe_right uu____2666 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) uu____2665))
end
| Labeled (t2, uu____2670, uu____2671) -> begin
(aux1 n1 names t2)
end
| LblPos (t2, s) -> begin
(

let uu____2674 = (aux1 n1 names t2)
in (FStar_Util.format2 "(! %s :lblpos %s)" uu____2674 s))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let qid = (next_qid ())
in (

let uu____2689 = (name_binders_inner None names n1 sorts)
in (match (uu____2689) with
| (names1, binders, n2) -> begin
(

let binders1 = (FStar_All.pipe_right binders (FStar_String.concat " "))
in (

let pats1 = (remove_guard_free pats)
in (

let pats_str = (match (pats1) with
| (([])::[]) | ([]) -> begin
";;no pats"
end
| uu____2717 -> begin
(

let uu____2720 = (FStar_All.pipe_right pats1 (FStar_List.map (fun pats2 -> (

let uu____2728 = (

let uu____2729 = (FStar_List.map (fun p -> (

let uu____2732 = (aux1 n2 names1 p)
in (FStar_Util.format1 "%s" uu____2732))) pats2)
in (FStar_String.concat " " uu____2729))
in (FStar_Util.format1 "\n:pattern (%s)" uu____2728)))))
in (FStar_All.pipe_right uu____2720 (FStar_String.concat "\n")))
end)
in (

let uu____2734 = (

let uu____2736 = (

let uu____2738 = (

let uu____2740 = (aux1 n2 names1 body)
in (

let uu____2741 = (

let uu____2743 = (weightToSmt wopt)
in (uu____2743)::(pats_str)::(qid)::[])
in (uu____2740)::uu____2741))
in (binders1)::uu____2738)
in ((qop_to_string qop))::uu____2736)
in (FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))" uu____2734)))))
end)))
end
| Let (es, body) -> begin
(

let uu____2748 = (FStar_List.fold_left (fun uu____2763 e -> (match (uu____2763) with
| (names0, binders, n0) -> begin
(

let nm = (

let uu____2791 = (FStar_Util.string_of_int n0)
in (Prims.strcat "@lb" uu____2791))
in (

let names01 = (((nm), (Term_sort)))::names0
in (

let b = (

let uu____2799 = (aux1 n1 names e)
in (FStar_Util.format2 "(%s %s)" nm uu____2799))
in ((names01), ((b)::binders), ((n0 + (Prims.parse_int "1")))))))
end)) ((names), ([]), (n1)) es)
in (match (uu____2748) with
| (names1, binders, n2) -> begin
(

let uu____2817 = (aux1 n2 names1 body)
in (FStar_Util.format2 "(let (%s) %s)" (FStar_String.concat " " binders) uu____2817))
end))
end)))
and aux = (fun depth n1 names t1 -> (

let s = (aux' depth n1 names t1)
in (match ((t1.rng <> norng)) with
| true -> begin
(

let uu____2824 = (FStar_Range.string_of_range t1.rng)
in (

let uu____2825 = (FStar_Range.string_of_use_range t1.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____2824 uu____2825 s)))
end
| uu____2826 -> begin
s
end)))
in (aux (Prims.parse_int "0") (Prims.parse_int "0") [] t)))))


let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun uu___88_2830 -> (match (uu___88_2830) with
| None -> begin
""
end
| Some (c) -> begin
(

let uu____2833 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(failwith "Impossible")
end
| (hd1)::[] -> begin
((hd1), (""))
end
| (hd1)::uu____2842 -> begin
((hd1), ("..."))
end)
in (match (uu____2833) with
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

let uu____2859 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun uu___89_2861 -> (match (uu___89_2861) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" uu____2859))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (

let uu____2874 = (caption_to_string c)
in (

let uu____2875 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____2874 f (FStar_String.concat " " l) uu____2875))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let uu____2883 = (name_macro_binders arg_sorts)
in (match (uu____2883) with
| (names, binders) -> begin
(

let body1 = (

let uu____2901 = (FStar_List.map (fun x -> (mkFreeV x norng)) names)
in (inst uu____2901 body))
in (

let uu____2908 = (caption_to_string c)
in (

let uu____2909 = (strSort retsort)
in (

let uu____2910 = (termToSmt (escape f) body1)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____2908 f (FStar_String.concat " " binders) uu____2909 uu____2910)))))
end))
end
| Assume (t, c, n1) -> begin
(

let n2 = (escape n1)
in (

let uu____2915 = (caption_to_string c)
in (

let uu____2916 = (termToSmt n2 t)
in (FStar_Util.format3 "%s(assert (! %s\n:named %s))" uu____2915 uu____2916 n2))))
end
| Eval (t) -> begin
(

let uu____2918 = (termToSmt "eval" t)
in (FStar_Util.format1 "(eval %s)" uu____2918))
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
| SetOption (s, v1) -> begin
(FStar_Util.format2 "(set-option :%s %s)" s v1)
end
| PrintStats -> begin
"(get-info :all-statistics)"
end)))
and mkPrelude : Prims.string  ->  Prims.string = (fun z3options -> (

let basic = (Prims.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n")
in (

let constrs = ((("FString_const"), (((("FString_const_proj_0"), (Int_sort), (true)))::[]), (String_sort), ((Prims.parse_int "0")), (true)))::((("Tm_type"), ([]), (Term_sort), ((Prims.parse_int "2")), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "3")), (false)))::((("Tm_uvar"), (((("Tm_uvar_fst"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "5")), (true)))::((("Tm_unit"), ([]), (Term_sort), ((Prims.parse_int "6")), (true)))::((("BoxInt"), (((("BoxInt_proj_0"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "7")), (true)))::((("BoxBool"), (((("BoxBool_proj_0"), (Bool_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "8")), (true)))::((("BoxString"), (((("BoxString_proj_0"), (String_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "9")), (true)))::((("BoxRef"), (((("BoxRef_proj_0"), (Ref_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "10")), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort), (true)))::((("LexCons_1"), (Term_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "11")), (true)))::[]
in (

let bcons = (

let uu____3122 = (

let uu____3124 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right uu____3124 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right uu____3122 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mk_Range_const : term = (mkApp (("Range_const"), ([])) norng)


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____3149 = (

let uu____3153 = (

let uu____3155 = (mkInteger' i norng)
in (uu____3155)::[])
in (("Tm_uvar"), (uu____3153)))
in (mkApp uu____3149 r)))


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
| uu____3196 -> begin
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
| uu____3203 -> begin
(Prims.raise FStar_Util.Impos)
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (uu____3211)::(t1)::(t2)::[]); freevars = uu____3214; rng = uu____3215})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (uu____3222)::(t1)::(t2)::[]); freevars = uu____3225; rng = uu____3226})::[]) -> begin
(

let uu____3233 = (mkEq ((t1), (t2)) norng)
in (mkNot uu____3233 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = uu____3236; rng = uu____3237})::[]) -> begin
(

let uu____3244 = (

let uu____3247 = (unboxInt t1)
in (

let uu____3248 = (unboxInt t2)
in ((uu____3247), (uu____3248))))
in (mkLTE uu____3244 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = uu____3251; rng = uu____3252})::[]) -> begin
(

let uu____3259 = (

let uu____3262 = (unboxInt t1)
in (

let uu____3263 = (unboxInt t2)
in ((uu____3262), (uu____3263))))
in (mkLT uu____3259 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = uu____3266; rng = uu____3267})::[]) -> begin
(

let uu____3274 = (

let uu____3277 = (unboxInt t1)
in (

let uu____3278 = (unboxInt t2)
in ((uu____3277), (uu____3278))))
in (mkGTE uu____3274 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = uu____3281; rng = uu____3282})::[]) -> begin
(

let uu____3289 = (

let uu____3292 = (unboxInt t1)
in (

let uu____3293 = (unboxInt t2)
in ((uu____3292), (uu____3293))))
in (mkGT uu____3289 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = uu____3296; rng = uu____3297})::[]) -> begin
(

let uu____3304 = (

let uu____3307 = (unboxBool t1)
in (

let uu____3308 = (unboxBool t2)
in ((uu____3307), (uu____3308))))
in (mkAnd uu____3304 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = uu____3311; rng = uu____3312})::[]) -> begin
(

let uu____3319 = (

let uu____3322 = (unboxBool t1)
in (

let uu____3323 = (unboxBool t2)
in ((uu____3322), (uu____3323))))
in (mkOr uu____3319 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t1)::[]); freevars = uu____3325; rng = uu____3326})::[]) -> begin
(

let uu____3333 = (unboxBool t1)
in (mkNot uu____3333 t1.rng))
end
| App (Var ("Prims.b2t"), (t1)::[]) -> begin
(

let uu___90_3336 = (unboxBool t1)
in {tm = uu___90_3336.tm; freevars = uu___90_3336.freevars; rng = t.rng})
end
| uu____3339 -> begin
(mkApp (("Valid"), ((t)::[])) t.rng)
end))


let mk_HasType : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasType"), ((v1)::(t)::[])) t.rng))


let mk_HasTypeZ : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasTypeZ"), ((v1)::(t)::[])) t.rng))


let mk_IsTyped : term  ->  term = (fun v1 -> (mkApp (("IsTyped"), ((v1)::[])) norng))


let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v1 t -> (

let uu____3368 = (FStar_Options.unthrottle_inductives ())
in (match (uu____3368) with
| true -> begin
(mk_HasType v1 t)
end
| uu____3369 -> begin
(mkApp (("HasTypeFuel"), ((f)::(v1)::(t)::[])) t.rng)
end)))


let mk_HasTypeWithFuel : term Prims.option  ->  term  ->  term  ->  term = (fun f v1 t -> (match (f) with
| None -> begin
(mk_HasType v1 t)
end
| Some (f1) -> begin
(mk_HasTypeFuel f1 v1 t)
end))


let mk_NoHoist : term  ->  term  ->  term = (fun dummy b -> (mkApp (("NoHoist"), ((dummy)::(b)::[])) b.rng))


let mk_Destruct : term  ->  FStar_Range.range  ->  term = (fun v1 -> (mkApp (("Destruct"), ((v1)::[]))))


let mk_Rank : term  ->  FStar_Range.range  ->  term = (fun x -> (mkApp (("Rank"), ((x)::[]))))


let mk_tester : Prims.string  ->  term  ->  term = (fun n1 t -> (mkApp (((Prims.strcat "is-" n1)), ((t)::[])) t.rng))


let mk_ApplyTF : term  ->  term  ->  term = (fun t t' -> (mkApp (("ApplyTF"), ((t)::(t')::[])) t.rng))


let mk_ApplyTT : term  ->  term  ->  FStar_Range.range  ->  term = (fun t t' r -> (mkApp (("ApplyTT"), ((t)::(t')::[])) r))


let mk_String_const : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____3432 = (

let uu____3436 = (

let uu____3438 = (mkInteger' i norng)
in (uu____3438)::[])
in (("FString_const"), (uu____3436)))
in (mkApp uu____3432 r)))


let mk_Precedes : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (

let uu____3449 = (mkApp (("Precedes"), ((x1)::(x2)::[])) r)
in (FStar_All.pipe_right uu____3449 mk_Valid)))


let mk_LexCons : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (mkApp (("LexCons"), ((x1)::(x2)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n1 -> (match ((n1 = (Prims.parse_int "0"))) with
| true -> begin
(mkApp (("ZFuel"), ([])) norng)
end
| uu____3465 -> begin
(

let uu____3466 = (

let uu____3470 = (

let uu____3472 = (n_fuel (n1 - (Prims.parse_int "1")))
in (uu____3472)::[])
in (("SFuel"), (uu____3470)))
in (mkApp uu____3466 norng))
end))


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term Prims.option  ->  term Prims.option  ->  FStar_Range.range  ->  term Prims.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (Some (p11), Some (p21)) -> begin
(

let uu____3495 = (mkAnd ((p11), (p21)) r)
in Some (uu____3495))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))


let mk_and_opt_l : term Prims.option Prims.list  ->  FStar_Range.range  ->  term Prims.option = (fun pl r -> (FStar_List.fold_right (fun p out -> (mk_and_opt p out r)) pl None))


let mk_and_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____3528 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l uu____3528)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____3539 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l uu____3539)))


let mk_haseq : term  ->  term = (fun t -> (

let uu____3545 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid uu____3545)))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n1) -> begin
(FStar_Util.format1 "(Integer %s)" n1)
end
| BoundV (n1) -> begin
(

let uu____3559 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(BoundV %s)" uu____3559))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (Prims.fst fv))
end
| App (op, l) -> begin
(

let uu____3567 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) uu____3567))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____3571 = (print_smt_term t1)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 uu____3571))
end
| LblPos (t1, s) -> begin
(

let uu____3574 = (print_smt_term t1)
in (FStar_Util.format2 "(LblPos %s %s)" s uu____3574))
end
| Quant (qop, l, uu____3577, uu____3578, t1) -> begin
(

let uu____3588 = (print_smt_term_list_list l)
in (

let uu____3589 = (print_smt_term t1)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____3588 uu____3589)))
end
| Let (es, body) -> begin
(

let uu____3594 = (print_smt_term_list es)
in (

let uu____3595 = (print_smt_term body)
in (FStar_Util.format2 "(let %s %s)" uu____3594 uu____3595)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (

let uu____3598 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right uu____3598 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l1 -> (

let uu____3608 = (

let uu____3609 = (

let uu____3610 = (print_smt_term_list l1)
in (Prims.strcat uu____3610 " ] "))
in (Prims.strcat "; [ " uu____3609))
in (Prims.strcat s uu____3608))) "" l))




