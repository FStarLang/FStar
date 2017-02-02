
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
(let _0_171 = (strSort s1)
in (let _0_170 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _0_171 _0_170)))
end
| Arrow (s1, s2) -> begin
(let _0_173 = (strSort s1)
in (let _0_172 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _0_173 _0_172)))
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
| uu____104 -> begin
false
end))


let uu___is_FalseOp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FalseOp -> begin
true
end
| uu____108 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____112 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____116 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____120 -> begin
false
end))


let uu___is_Imp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Imp -> begin
true
end
| uu____124 -> begin
false
end))


let uu___is_Iff : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iff -> begin
true
end
| uu____128 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____132 -> begin
false
end))


let uu___is_LT : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LT -> begin
true
end
| uu____136 -> begin
false
end))


let uu___is_LTE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LTE -> begin
true
end
| uu____140 -> begin
false
end))


let uu___is_GT : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GT -> begin
true
end
| uu____144 -> begin
false
end))


let uu___is_GTE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GTE -> begin
true
end
| uu____148 -> begin
false
end))


let uu___is_Add : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Add -> begin
true
end
| uu____152 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____156 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____160 -> begin
false
end))


let uu___is_Mul : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mul -> begin
true
end
| uu____164 -> begin
false
end))


let uu___is_Minus : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Minus -> begin
true
end
| uu____168 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____172 -> begin
false
end))


let uu___is_ITE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ITE -> begin
true
end
| uu____176 -> begin
false
end))


let uu___is_Var : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Var (_0) -> begin
true
end
| uu____181 -> begin
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
| uu____192 -> begin
false
end))


let uu___is_Exists : qop  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exists -> begin
true
end
| uu____196 -> begin
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
| uu____255 -> begin
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
| uu____267 -> begin
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
| uu____281 -> begin
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
| uu____302 -> begin
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
| uu____332 -> begin
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
| uu____374 -> begin
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
| uu____397 -> begin
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
| uu____492 -> begin
false
end))


let uu___is_DeclFun : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DeclFun (_0) -> begin
true
end
| uu____502 -> begin
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
| uu____535 -> begin
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
| uu____569 -> begin
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
| uu____593 -> begin
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
| uu____605 -> begin
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
| uu____617 -> begin
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
| uu____628 -> begin
false
end))


let uu___is_Pop : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____632 -> begin
false
end))


let uu___is_CheckSat : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckSat -> begin
true
end
| uu____636 -> begin
false
end))


let uu___is_GetUnsatCore : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetUnsatCore -> begin
true
end
| uu____640 -> begin
false
end))


let uu___is_SetOption : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOption (_0) -> begin
true
end
| uu____647 -> begin
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
| uu____664 -> begin
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
| uu____701 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun uu___83_706 -> (match (uu___83_706) with
| {tm = FreeV (x); freevars = uu____708; rng = uu____709} -> begin
(fv_sort x)
end
| uu____716 -> begin
(failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun uu___84_719 -> (match (uu___84_719) with
| {tm = FreeV (fv); freevars = uu____721; rng = uu____722} -> begin
fv
end
| uu____729 -> begin
(failwith "impossible")
end))


let rec freevars : term  ->  (Prims.string * sort) Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (uu____750, tms) -> begin
(FStar_List.collect freevars tms)
end
| (Quant (_, _, _, _, t)) | (Labeled (t, _, _)) | (LblPos (t, _)) -> begin
(freevars t)
end))


let free_variables : term  ->  fvs = (fun t -> (

let uu____771 = (FStar_ST.read t.freevars)
in (match (uu____771) with
| Some (b) -> begin
b
end
| None -> begin
(

let fvs = (let _0_174 = (freevars t)
in (FStar_Util.remove_dups fv_eq _0_174))
in ((FStar_ST.write t.freevars (Some (fvs)));
fvs;
))
end)))


let qop_to_string : qop  ->  Prims.string = (fun uu___85_804 -> (match (uu___85_804) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun uu___86_807 -> (match (uu___86_807) with
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


let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun uu___87_812 -> (match (uu___87_812) with
| None -> begin
""
end
| Some (i) -> begin
(let _0_175 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _0_175))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _0_176 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _0_176))
end
| FreeV (x) -> begin
(let _0_178 = (let _0_177 = (strSort (Prims.snd x))
in (Prims.strcat ":" _0_177))
in (Prims.strcat (Prims.fst x) _0_178))
end
| App (op, tms) -> begin
(let _0_182 = (let _0_181 = (let _0_180 = (let _0_179 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right _0_179 (FStar_String.concat " ")))
in (Prims.strcat _0_180 ")"))
in (Prims.strcat (op_to_string op) _0_181))
in (Prims.strcat "(" _0_182))
end
| Labeled (t, r1, r2) -> begin
(let _0_185 = (hash_of_term t)
in (let _0_184 = (let _0_183 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 _0_183))
in (Prims.strcat _0_185 _0_184)))
end
| LblPos (t, r) -> begin
(let _0_187 = (let _0_186 = (hash_of_term t)
in (Prims.strcat _0_186 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " _0_187))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _0_203 = (let _0_202 = (let _0_201 = (let _0_200 = (let _0_188 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _0_188 (FStar_String.concat " ")))
in (let _0_199 = (let _0_198 = (let _0_197 = (hash_of_term body)
in (let _0_196 = (let _0_195 = (let _0_194 = (weightToSmt wopt)
in (let _0_193 = (let _0_192 = (let _0_191 = (let _0_190 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _0_189 = (FStar_List.map hash_of_term pats)
in (FStar_All.pipe_right _0_189 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _0_190 (FStar_String.concat "; ")))
in (Prims.strcat _0_191 "))"))
in (Prims.strcat " " _0_192))
in (Prims.strcat _0_194 _0_193)))
in (Prims.strcat " " _0_195))
in (Prims.strcat _0_197 _0_196)))
in (Prims.strcat ")(! " _0_198))
in (Prims.strcat _0_200 _0_199)))
in (Prims.strcat " (" _0_201))
in (Prims.strcat (qop_to_string qop) _0_202))
in (Prims.strcat "(" _0_203))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (let _0_204 = (FStar_Util.mk_ref None)
in {tm = t; freevars = _0_204; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((TrueOp), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((FalseOp), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (let _0_205 = Integer ((FStar_Util.ensure_decimal i))
in (mk _0_205 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (let _0_206 = (FStar_Util.string_of_int i)
in (mkInteger _0_206 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun uu____928 r -> (match (uu____928) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (TrueOp, uu____944) -> begin
(mkFalse r)
end
| App (FalseOp, uu____947) -> begin
(mkTrue r)
end
| uu____950 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____958 r -> (match (uu____958) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____964), uu____965) -> begin
t2
end
| (uu____968, App (TrueOp, uu____969)) -> begin
t1
end
| ((App (FalseOp, _), _)) | ((_, App (FalseOp, _))) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (uu____985, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), uu____991) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____995 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1005 r -> (match (uu____1005) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((App (TrueOp, _), _)) | ((_, App (TrueOp, _))) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____1017), uu____1018) -> begin
t2
end
| (uu____1021, App (FalseOp, uu____1022)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (uu____1032, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), uu____1038) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____1042 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____1052 r -> (match (uu____1052) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((_, App (TrueOp, _))) | ((App (FalseOp, _), _)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____1064), uu____1065) -> begin
t2
end
| (uu____1068, App (Imp, (t1')::(t2')::[])) -> begin
(let _0_209 = (let _0_208 = (let _0_207 = (mkAnd ((t1), (t1')) r)
in (_0_207)::(t2')::[])
in ((Imp), (_0_208)))
in (mkApp' _0_209 r))
end
| uu____1073 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op uu____1086 r -> (match (uu____1086) with
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


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun uu____1173 r -> (match (uu____1173) with
| (t1, t2, t3) -> begin
(match (((t2.tm), (t3.tm))) with
| (App (TrueOp, uu____1181), App (TrueOp, uu____1182)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____1187), uu____1188) -> begin
(let _0_211 = (let _0_210 = (mkNot t1 t1.rng)
in ((_0_210), (t3)))
in (mkImp _0_211 r))
end
| (uu____1191, App (TrueOp, uu____1192)) -> begin
(mkImp ((t1), (t2)) r)
end
| (uu____1195, uu____1196) -> begin
(mkApp' ((ITE), ((t1)::(t2)::(t3)::[])) r)
end)
end))


let mkCases : term Prims.list  ->  FStar_Range.range  ->  term = (fun t r -> (match (t) with
| [] -> begin
(failwith "Impos")
end
| (hd)::tl -> begin
(FStar_List.fold_left (fun out t -> (mkAnd ((out), (t)) r)) hd tl)
end))


let mkQuant : (qop * term Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1224 r -> (match (uu____1224) with
| (qop, pats, wopt, vars, body) -> begin
(match (((FStar_List.length vars) = (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____1250 -> begin
(match (body.tm) with
| App (TrueOp, uu____1251) -> begin
body
end
| uu____1254 -> begin
(mk (Quant (((qop), (pats), (wopt), (vars), (body)))) r)
end)
end)
end))


let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (

let nvars = (FStar_List.length fvs)
in (

let index_of = (fun fv -> (

let uu____1274 = (FStar_Util.try_find_index (fv_eq fv) fvs)
in (match (uu____1274) with
| None -> begin
None
end
| Some (i) -> begin
Some ((nvars - (i + (Prims.parse_int "1"))))
end)))
in (

let rec aux = (fun ix t -> (

let uu____1288 = (FStar_ST.read t.freevars)
in (match (uu____1288) with
| Some ([]) -> begin
t
end
| uu____1304 -> begin
(match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
t
end
| FreeV (x) -> begin
(

let uu____1314 = (index_of x)
in (match (uu____1314) with
| None -> begin
t
end
| Some (i) -> begin
(mkBoundV (i + ix) t.rng)
end))
end
| App (op, tms) -> begin
(let _0_213 = (let _0_212 = (FStar_List.map (aux ix) tms)
in ((op), (_0_212)))
in (mkApp' _0_213 t.rng))
end
| Labeled (t, r1, r2) -> begin
(let _0_215 = Labeled ((let _0_214 = (aux ix t)
in ((_0_214), (r1), (r2))))
in (mk _0_215 t.rng))
end
| LblPos (t, r) -> begin
(let _0_217 = LblPos ((let _0_216 = (aux ix t)
in ((_0_216), (r))))
in (mk _0_217 t.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n = (FStar_List.length vars)
in (let _0_220 = (let _0_219 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _0_218 = (aux (ix + n) body)
in ((qop), (_0_219), (wopt), (vars), (_0_218))))
in (mkQuant _0_220 t.rng)))
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
| uu____1380 -> begin
t
end)
end
| App (op, tms) -> begin
(let _0_222 = (let _0_221 = (FStar_List.map (aux shift) tms)
in ((op), (_0_221)))
in (mkApp' _0_222 t.rng))
end
| Labeled (t, r1, r2) -> begin
(let _0_224 = Labeled ((let _0_223 = (aux shift t)
in ((_0_223), (r1), (r2))))
in (mk _0_224 t.rng))
end
| LblPos (t, r) -> begin
(let _0_226 = LblPos ((let _0_225 = (aux shift t)
in ((_0_225), (r))))
in (mk _0_226 t.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift = (shift + m)
in (let _0_229 = (let _0_228 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _0_227 = (aux shift body)
in ((qop), (_0_228), (wopt), (vars), (_0_227))))
in (mkQuant _0_229 t.rng))))
end))
in (aux (Prims.parse_int "0") t)))))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1432 -> (match (uu____1432) with
| (qop, pats, wopt, vars, body) -> begin
(mkQuant (let _0_232 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _0_231 = (FStar_List.map fv_sort vars)
in (let _0_230 = (abstr vars body)
in ((qop), (_0_232), (wopt), (_0_231), (_0_230))))))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____1481 r -> (match (uu____1481) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)) r)
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____1518 r -> (match (uu____1518) with
| (pats, wopt, vars, body) -> begin
((mkQuant' ((Forall), (pats), (wopt), (vars), (body))) r)
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____1549 r -> (match (uu____1549) with
| (pats, vars, body) -> begin
((mkQuant' ((Forall), (pats), (None), (vars), (body))) r)
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun uu____1575 r -> (match (uu____1575) with
| (pats, vars, body) -> begin
((mkQuant' ((Exists), (pats), (None), (vars), (body))) r)
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun uu____1602 -> (match (uu____1602) with
| (nm, vars, s, tm, c) -> begin
DefineFun ((let _0_234 = (FStar_List.map fv_sort vars)
in (let _0_233 = (abstr vars tm)
in ((nm), (_0_234), (s), (_0_233), (c)))))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _0_235 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _0_235)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun uu____1634 id -> (match (uu____1634) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in Assume ((let _0_243 = (let _0_242 = (let _0_241 = (mkInteger' id norng)
in (let _0_240 = (let _0_239 = (let _0_238 = (constr_id_of_sort sort)
in (let _0_237 = (let _0_236 = (mkApp ((tok_name), ([])) norng)
in (_0_236)::[])
in ((_0_238), (_0_237))))
in (mkApp _0_239 norng))
in ((_0_241), (_0_240))))
in (mkEq _0_242 norng))
in ((_0_243), (Some ("fresh token")), (Some (a_name))))))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun uu____1652 -> (match (uu____1652) with
| (name, arg_sorts, sort, id) -> begin
(

let id = (FStar_Util.string_of_int id)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (let _0_246 = (let _0_245 = (let _0_244 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _0_244))
in ((_0_245), (s)))
in (mkFreeV _0_246 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (let _0_248 = (let _0_247 = (constr_id_of_sort sort)
in ((_0_247), ((capp)::[])))
in (mkApp _0_248 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in Assume ((let _0_253 = (let _0_252 = (let _0_251 = (let _0_250 = (let _0_249 = (mkInteger id norng)
in ((_0_249), (cid_app)))
in (mkEq _0_250 norng))
in ((((capp)::[])::[]), (bvar_names), (_0_251)))
in (mkForall _0_252 norng))
in ((_0_253), (Some ("Constructor distinct")), (Some (a_name)))))))))))
end))


let injective_constructor : (Prims.string * (Prims.string * sort) Prims.list * sort)  ->  decls_t = (fun uu____1693 -> (match (uu____1693) with
| (name, projectors, sort) -> begin
(

let n_bvars = (FStar_List.length projectors)
in (

let bvar_name = (fun i -> (let _0_254 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _0_254)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (mkFreeV (let _0_255 = (bvar_name i)
in ((_0_255), (s)))))
in (

let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i uu____1742 -> (match (uu____1742) with
| (uu____1745, s) -> begin
((bvar i s) norng)
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (let _0_263 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i uu____1763 -> (match (uu____1763) with
| (name, s) -> begin
(

let cproj_app = (mkApp ((name), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((name), ((sort)::[]), (s), (Some ("Projector"))))
in (

let a_name = (Prims.strcat "projection_inverse_" name)
in (let _0_262 = (let _0_261 = Assume ((let _0_260 = (let _0_259 = (let _0_258 = (let _0_257 = (let _0_256 = ((bvar i s) norng)
in ((cproj_app), (_0_256)))
in (mkEq _0_257 norng))
in ((((capp)::[])::[]), (bvar_names), (_0_258)))
in (mkForall _0_259 norng))
in ((_0_260), (Some ("Projection inverse")), (Some (a_name)))))
in (_0_261)::[])
in (proj_name)::_0_262))))
end))))
in (FStar_All.pipe_right _0_263 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun uu____1784 -> (match (uu____1784) with
| (name, projectors, sort, id, injective) -> begin
(

let injective = (injective || true)
in (

let cdecl = DeclFun ((let _0_264 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_0_264), (sort), (Some ("Constructor")))))
in (

let cid = (fresh_constructor (let _0_265 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_0_265), (sort), (id))))
in (

let disc = (

let disc_name = (Prims.strcat "is-" name)
in (

let xfv = (("x"), (sort))
in (

let xx = (mkFreeV xfv norng)
in (

let disc_eq = (let _0_271 = (let _0_270 = (let _0_267 = (let _0_266 = (constr_id_of_sort sort)
in ((_0_266), ((xx)::[])))
in (mkApp _0_267 norng))
in (let _0_269 = (let _0_268 = (FStar_Util.string_of_int id)
in (mkInteger _0_268 norng))
in ((_0_270), (_0_269))))
in (mkEq _0_271 norng))
in (

let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun uu____1820 -> (match (uu____1820) with
| (proj, s) -> begin
(mkApp ((proj), ((xx)::[])) norng)
end))))
in (

let disc_inv_body = (let _0_273 = (let _0_272 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (_0_272)))
in (mkEq _0_273 norng))
in (

let disc_ax = (mkAnd ((disc_eq), (disc_inv_body)) norng)
in (mkDefineFun ((disc_name), ((xfv)::[]), (Bool_sort), (disc_ax), (Some ("Discriminator definition")))))))))))
in (

let projs = (match (injective) with
| true -> begin
(injective_constructor ((name), (projectors), (sort)))
end
| uu____1839 -> begin
[]
end)
in (let _0_278 = (let _0_274 = Caption ((FStar_Util.format1 "<start constructor %s>" name))
in (_0_274)::(cdecl)::(cid)::projs)
in (let _0_277 = (let _0_276 = (let _0_275 = Caption ((FStar_Util.format1 "</end constructor %s>" name))
in (_0_275)::[])
in (FStar_List.append ((disc)::[]) _0_276))
in (FStar_List.append _0_278 _0_277))))))))
end))


let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (

let uu____1864 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun uu____1887 s -> (match (uu____1887) with
| (names, binders, n) -> begin
(

let prefix = (match (s) with
| Term_sort -> begin
"@x"
end
| uu____1915 -> begin
"@u"
end)
in (

let nm = (let _0_279 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _0_279))
in (

let names = (((nm), (s)))::names
in (

let b = (let _0_280 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _0_280))
in ((names), ((b)::binders), ((n + (Prims.parse_int "1"))))))))
end)) ((outer_names), ([]), (start))))
in (match (uu____1864) with
| (names, binders, n) -> begin
((names), ((FStar_List.rev binders)), (n))
end)))


let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let uu____1965 = (name_binders_inner [] (Prims.parse_int "0") sorts)
in (match (uu____1965) with
| (names, binders, n) -> begin
(((FStar_List.rev names)), (binders))
end)))


let termToSmt : term  ->  Prims.string = (fun t -> (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (uu____2022); freevars = uu____2023; rng = uu____2024})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| uu____2032 -> begin
tm
end))))))))
in (

let rec aux' = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _0_281 = (FStar_List.nth names i)
in (FStar_All.pipe_right _0_281 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _0_283 = (let _0_282 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _0_282 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _0_283))
end
| Labeled (t, uu____2066, uu____2067) -> begin
(aux n names t)
end
| LblPos (t, s) -> begin
(let _0_284 = (aux n names t)
in (FStar_Util.format2 "(! %s :lblpos %s)" _0_284 s))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let uu____2083 = (name_binders_inner names n sorts)
in (match (uu____2083) with
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
| uu____2111 -> begin
(let _0_288 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _0_287 = (let _0_286 = (FStar_List.map (fun p -> (let _0_285 = (aux n names p)
in (FStar_Util.format1 "%s" _0_285))) pats)
in (FStar_String.concat " " _0_286))
in (FStar_Util.format1 "\n:pattern (%s)" _0_287)))))
in (FStar_All.pipe_right _0_288 (FStar_String.concat "\n")))
end)
in (match (((pats), (wopt))) with
| ((([])::[], None)) | (([], None)) -> begin
(let _0_289 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _0_289))
end
| uu____2134 -> begin
(let _0_291 = (aux n names body)
in (let _0_290 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _0_291 _0_290 pats_str)))
end))))
end))
end))
and aux = (fun n names t -> (

let s = (aux' n names t)
in (match ((t.rng <> norng)) with
| true -> begin
(let _0_293 = (FStar_Range.string_of_range t.rng)
in (let _0_292 = (FStar_Range.string_of_use_range t.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" _0_293 _0_292 s)))
end
| uu____2145 -> begin
s
end)))
in (aux (Prims.parse_int "0") [] t))))


let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun uu___88_2149 -> (match (uu___88_2149) with
| None -> begin
""
end
| Some (c) -> begin
(

let uu____2152 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(failwith "Impossible")
end
| (hd)::[] -> begin
((hd), (""))
end
| (hd)::uu____2161 -> begin
((hd), ("..."))
end)
in (match (uu____2152) with
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
(let _0_294 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun uu___89_2179 -> (match (uu___89_2179) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _0_294))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (let _0_296 = (caption_to_string c)
in (let _0_295 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _0_296 f (FStar_String.concat " " l) _0_295))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let uu____2199 = (name_binders arg_sorts)
in (match (uu____2199) with
| (names, binders) -> begin
(

let body = (let _0_297 = (FStar_List.map (fun x -> (mkFreeV x norng)) names)
in (inst _0_297 body))
in (let _0_300 = (caption_to_string c)
in (let _0_299 = (strSort retsort)
in (let _0_298 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _0_300 f (FStar_String.concat " " binders) _0_299 _0_298)))))
end))
end
| Assume (t, c, Some (n)) -> begin
(let _0_302 = (caption_to_string c)
in (let _0_301 = (termToSmt t)
in (FStar_Util.format3 "%s(assert (!\n%s\n:named %s))" _0_302 _0_301 (escape n))))
end
| Assume (t, c, None) -> begin
(let _0_304 = (caption_to_string c)
in (let _0_303 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _0_304 _0_303)))
end
| Eval (t) -> begin
(let _0_305 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _0_305))
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

let bcons = (let _0_307 = (let _0_306 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _0_306 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _0_307 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mk_Range_const : term = (mkApp (("Range_const"), ([])) norng)


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (let _0_310 = (let _0_309 = (let _0_308 = (mkInteger' i norng)
in (_0_308)::[])
in (("Tm_uvar"), (_0_309)))
in (mkApp _0_310 r)))


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
| uu____2456 -> begin
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
| uu____2463 -> begin
(Prims.raise FStar_Util.Impos)
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (uu____2471)::(t1)::(t2)::[]); freevars = uu____2474; rng = uu____2475})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (uu____2482)::(t1)::(t2)::[]); freevars = uu____2485; rng = uu____2486})::[]) -> begin
(let _0_311 = (mkEq ((t1), (t2)) norng)
in (mkNot _0_311 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = uu____2495; rng = uu____2496})::[]) -> begin
(let _0_314 = (let _0_313 = (unboxInt t1)
in (let _0_312 = (unboxInt t2)
in ((_0_313), (_0_312))))
in (mkLTE _0_314 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = uu____2505; rng = uu____2506})::[]) -> begin
(let _0_317 = (let _0_316 = (unboxInt t1)
in (let _0_315 = (unboxInt t2)
in ((_0_316), (_0_315))))
in (mkLT _0_317 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = uu____2515; rng = uu____2516})::[]) -> begin
(let _0_320 = (let _0_319 = (unboxInt t1)
in (let _0_318 = (unboxInt t2)
in ((_0_319), (_0_318))))
in (mkGTE _0_320 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = uu____2525; rng = uu____2526})::[]) -> begin
(let _0_323 = (let _0_322 = (unboxInt t1)
in (let _0_321 = (unboxInt t2)
in ((_0_322), (_0_321))))
in (mkGT _0_323 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = uu____2535; rng = uu____2536})::[]) -> begin
(let _0_326 = (let _0_325 = (unboxBool t1)
in (let _0_324 = (unboxBool t2)
in ((_0_325), (_0_324))))
in (mkAnd _0_326 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = uu____2545; rng = uu____2546})::[]) -> begin
(let _0_329 = (let _0_328 = (unboxBool t1)
in (let _0_327 = (unboxBool t2)
in ((_0_328), (_0_327))))
in (mkOr _0_329 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t)::[]); freevars = uu____2554; rng = uu____2555})::[]) -> begin
(let _0_330 = (unboxBool t)
in (mkNot _0_330 t.rng))
end
| App (Var ("Prims.b2t"), (t1)::[]) -> begin
(

let uu___90_2564 = (unboxBool t1)
in {tm = uu___90_2564.tm; freevars = uu___90_2564.freevars; rng = t.rng})
end
| uu____2567 -> begin
(mkApp (("Valid"), ((t)::[])) t.rng)
end))


let mk_HasType : term  ->  term  ->  term = (fun v t -> (mkApp (("HasType"), ((v)::(t)::[])) t.rng))


let mk_HasTypeZ : term  ->  term  ->  term = (fun v t -> (mkApp (("HasTypeZ"), ((v)::(t)::[])) t.rng))


let mk_IsTyped : term  ->  term = (fun v -> (mkApp (("IsTyped"), ((v)::[])) norng))


let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v t -> (

let uu____2596 = (FStar_Options.unthrottle_inductives ())
in (match (uu____2596) with
| true -> begin
(mk_HasType v t)
end
| uu____2597 -> begin
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


let mk_String_const : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (let _0_333 = (let _0_332 = (let _0_331 = (mkInteger' i norng)
in (_0_331)::[])
in (("FString_const"), (_0_332)))
in (mkApp _0_333 r)))


let mk_Precedes : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (let _0_334 = (mkApp (("Precedes"), ((x1)::(x2)::[])) r)
in (FStar_All.pipe_right _0_334 mk_Valid)))


let mk_LexCons : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (mkApp (("LexCons"), ((x1)::(x2)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n -> (match ((n = (Prims.parse_int "0"))) with
| true -> begin
(mkApp (("ZFuel"), ([])) norng)
end
| uu____2678 -> begin
(let _0_337 = (let _0_336 = (let _0_335 = (n_fuel (n - (Prims.parse_int "1")))
in (_0_335)::[])
in (("SFuel"), (_0_336)))
in (mkApp _0_337 norng))
end))


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term Prims.option  ->  term Prims.option  ->  FStar_Range.range  ->  term Prims.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (Some (p1), Some (p2)) -> begin
Some ((mkAnd ((p1), (p2)) r))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))


let mk_and_opt_l : term Prims.option Prims.list  ->  FStar_Range.range  ->  term Prims.option = (fun pl r -> (FStar_List.fold_right (fun p out -> (mk_and_opt p out r)) pl None))


let mk_and_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (let _0_338 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l _0_338)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (let _0_339 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l _0_339)))


let mk_haseq : term  ->  term = (fun t -> (mk_Valid (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "(Integer %s)" n)
end
| BoundV (n) -> begin
(let _0_340 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "(BoundV %s)" _0_340))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (Prims.fst fv))
end
| App (op, l) -> begin
(let _0_341 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _0_341))
end
| Labeled (t, r1, r2) -> begin
(let _0_342 = (print_smt_term t)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 _0_342))
end
| LblPos (t, s) -> begin
(let _0_343 = (print_smt_term t)
in (FStar_Util.format2 "(LblPos %s %s)" s _0_343))
end
| Quant (qop, l, uu____2775, uu____2776, t) -> begin
(let _0_345 = (print_smt_term_list_list l)
in (let _0_344 = (print_smt_term t)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) _0_345 _0_344)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (let _0_346 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right _0_346 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _0_349 = (let _0_348 = (let _0_347 = (print_smt_term_list l)
in (Prims.strcat _0_347 " ] "))
in (Prims.strcat "; [ " _0_348))
in (Prims.strcat s _0_349))) "" l))




