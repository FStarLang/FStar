
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


let is_Bool_sort = (fun _discr_ -> (match (_discr_) with
| Bool_sort (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int_sort = (fun _discr_ -> (match (_discr_) with
| Int_sort (_) -> begin
true
end
| _ -> begin
false
end))


let is_String_sort = (fun _discr_ -> (match (_discr_) with
| String_sort (_) -> begin
true
end
| _ -> begin
false
end))


let is_Ref_sort = (fun _discr_ -> (match (_discr_) with
| Ref_sort (_) -> begin
true
end
| _ -> begin
false
end))


let is_Term_sort = (fun _discr_ -> (match (_discr_) with
| Term_sort (_) -> begin
true
end
| _ -> begin
false
end))


let is_Fuel_sort = (fun _discr_ -> (match (_discr_) with
| Fuel_sort (_) -> begin
true
end
| _ -> begin
false
end))


let is_Array = (fun _discr_ -> (match (_discr_) with
| Array (_) -> begin
true
end
| _ -> begin
false
end))


let is_Arrow = (fun _discr_ -> (match (_discr_) with
| Arrow (_) -> begin
true
end
| _ -> begin
false
end))


let is_Sort = (fun _discr_ -> (match (_discr_) with
| Sort (_) -> begin
true
end
| _ -> begin
false
end))


let ___Array____0 = (fun projectee -> (match (projectee) with
| Array (_86_10) -> begin
_86_10
end))


let ___Arrow____0 = (fun projectee -> (match (projectee) with
| Arrow (_86_13) -> begin
_86_13
end))


let ___Sort____0 = (fun projectee -> (match (projectee) with
| Sort (_86_16) -> begin
_86_16
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
(let _183_52 = (strSort s1)
in (let _183_51 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _183_52 _183_51)))
end
| Arrow (s1, s2) -> begin
(let _183_54 = (strSort s1)
in (let _183_53 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _183_54 _183_53)))
end
| Sort (s) -> begin
s
end))


type op =
| True
| False
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


let is_True = (fun _discr_ -> (match (_discr_) with
| True (_) -> begin
true
end
| _ -> begin
false
end))


let is_False = (fun _discr_ -> (match (_discr_) with
| False (_) -> begin
true
end
| _ -> begin
false
end))


let is_Not = (fun _discr_ -> (match (_discr_) with
| Not (_) -> begin
true
end
| _ -> begin
false
end))


let is_And = (fun _discr_ -> (match (_discr_) with
| And (_) -> begin
true
end
| _ -> begin
false
end))


let is_Or = (fun _discr_ -> (match (_discr_) with
| Or (_) -> begin
true
end
| _ -> begin
false
end))


let is_Imp = (fun _discr_ -> (match (_discr_) with
| Imp (_) -> begin
true
end
| _ -> begin
false
end))


let is_Iff = (fun _discr_ -> (match (_discr_) with
| Iff (_) -> begin
true
end
| _ -> begin
false
end))


let is_Eq = (fun _discr_ -> (match (_discr_) with
| Eq (_) -> begin
true
end
| _ -> begin
false
end))


let is_LT = (fun _discr_ -> (match (_discr_) with
| LT (_) -> begin
true
end
| _ -> begin
false
end))


let is_LTE = (fun _discr_ -> (match (_discr_) with
| LTE (_) -> begin
true
end
| _ -> begin
false
end))


let is_GT = (fun _discr_ -> (match (_discr_) with
| GT (_) -> begin
true
end
| _ -> begin
false
end))


let is_GTE = (fun _discr_ -> (match (_discr_) with
| GTE (_) -> begin
true
end
| _ -> begin
false
end))


let is_Add = (fun _discr_ -> (match (_discr_) with
| Add (_) -> begin
true
end
| _ -> begin
false
end))


let is_Sub = (fun _discr_ -> (match (_discr_) with
| Sub (_) -> begin
true
end
| _ -> begin
false
end))


let is_Div = (fun _discr_ -> (match (_discr_) with
| Div (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mul = (fun _discr_ -> (match (_discr_) with
| Mul (_) -> begin
true
end
| _ -> begin
false
end))


let is_Minus = (fun _discr_ -> (match (_discr_) with
| Minus (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mod = (fun _discr_ -> (match (_discr_) with
| Mod (_) -> begin
true
end
| _ -> begin
false
end))


let is_ITE = (fun _discr_ -> (match (_discr_) with
| ITE (_) -> begin
true
end
| _ -> begin
false
end))


let is_Var = (fun _discr_ -> (match (_discr_) with
| Var (_) -> begin
true
end
| _ -> begin
false
end))


let ___Var____0 = (fun projectee -> (match (projectee) with
| Var (_86_36) -> begin
_86_36
end))


type qop =
| Forall
| Exists


let is_Forall = (fun _discr_ -> (match (_discr_) with
| Forall (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exists = (fun _discr_ -> (match (_discr_) with
| Exists (_) -> begin
true
end
| _ -> begin
false
end))


type term' =
| Integer of Prims.string
| BoundV of Prims.int
| FreeV of fv
| App of (op * term Prims.list)
| Quant of (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)
| Labeled of (term * Prims.string * FStar_Range.range) 
 and term =
{tm : term'; freevars : fvs FStar_Syntax_Syntax.memo} 
 and pat =
term 
 and fv =
(Prims.string * sort) 
 and fvs =
fv Prims.list


let is_Integer = (fun _discr_ -> (match (_discr_) with
| Integer (_) -> begin
true
end
| _ -> begin
false
end))


let is_BoundV = (fun _discr_ -> (match (_discr_) with
| BoundV (_) -> begin
true
end
| _ -> begin
false
end))


let is_FreeV = (fun _discr_ -> (match (_discr_) with
| FreeV (_) -> begin
true
end
| _ -> begin
false
end))


let is_App = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))


let is_Quant = (fun _discr_ -> (match (_discr_) with
| Quant (_) -> begin
true
end
| _ -> begin
false
end))


let is_Labeled = (fun _discr_ -> (match (_discr_) with
| Labeled (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mkterm : term  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkterm"))))


let ___Integer____0 = (fun projectee -> (match (projectee) with
| Integer (_86_41) -> begin
_86_41
end))


let ___BoundV____0 = (fun projectee -> (match (projectee) with
| BoundV (_86_44) -> begin
_86_44
end))


let ___FreeV____0 = (fun projectee -> (match (projectee) with
| FreeV (_86_47) -> begin
_86_47
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_86_50) -> begin
_86_50
end))


let ___Quant____0 = (fun projectee -> (match (projectee) with
| Quant (_86_53) -> begin
_86_53
end))


let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_86_56) -> begin
_86_56
end))


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


let is_DefPrelude = (fun _discr_ -> (match (_discr_) with
| DefPrelude (_) -> begin
true
end
| _ -> begin
false
end))


let is_DeclFun = (fun _discr_ -> (match (_discr_) with
| DeclFun (_) -> begin
true
end
| _ -> begin
false
end))


let is_DefineFun = (fun _discr_ -> (match (_discr_) with
| DefineFun (_) -> begin
true
end
| _ -> begin
false
end))


let is_Assume = (fun _discr_ -> (match (_discr_) with
| Assume (_) -> begin
true
end
| _ -> begin
false
end))


let is_Caption = (fun _discr_ -> (match (_discr_) with
| Caption (_) -> begin
true
end
| _ -> begin
false
end))


let is_Eval = (fun _discr_ -> (match (_discr_) with
| Eval (_) -> begin
true
end
| _ -> begin
false
end))


let is_Echo = (fun _discr_ -> (match (_discr_) with
| Echo (_) -> begin
true
end
| _ -> begin
false
end))


let is_Push = (fun _discr_ -> (match (_discr_) with
| Push (_) -> begin
true
end
| _ -> begin
false
end))


let is_Pop = (fun _discr_ -> (match (_discr_) with
| Pop (_) -> begin
true
end
| _ -> begin
false
end))


let is_CheckSat = (fun _discr_ -> (match (_discr_) with
| CheckSat (_) -> begin
true
end
| _ -> begin
false
end))


let is_GetUnsatCore = (fun _discr_ -> (match (_discr_) with
| GetUnsatCore (_) -> begin
true
end
| _ -> begin
false
end))


let is_SetOption = (fun _discr_ -> (match (_discr_) with
| SetOption (_) -> begin
true
end
| _ -> begin
false
end))


let ___DeclFun____0 = (fun projectee -> (match (projectee) with
| DeclFun (_86_60) -> begin
_86_60
end))


let ___DefineFun____0 = (fun projectee -> (match (projectee) with
| DefineFun (_86_63) -> begin
_86_63
end))


let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_86_66) -> begin
_86_66
end))


let ___Caption____0 = (fun projectee -> (match (projectee) with
| Caption (_86_69) -> begin
_86_69
end))


let ___Eval____0 = (fun projectee -> (match (projectee) with
| Eval (_86_72) -> begin
_86_72
end))


let ___Echo____0 = (fun projectee -> (match (projectee) with
| Echo (_86_75) -> begin
_86_75
end))


let ___SetOption____0 = (fun projectee -> (match (projectee) with
| SetOption (_86_78) -> begin
_86_78
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
| _86_90 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun _86_1 -> (match (_86_1) with
| {tm = FreeV (x); freevars = _86_93} -> begin
(fv_sort x)
end
| _86_98 -> begin
(FStar_All.failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun _86_2 -> (match (_86_2) with
| {tm = FreeV (fv); freevars = _86_101} -> begin
fv
end
| _86_106 -> begin
(FStar_All.failwith "impossible")
end))


let rec freevars : term  ->  fv Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (_86_117, tms) -> begin
(FStar_List.collect freevars tms)
end
| (Quant (_, _, _, _, t)) | (Labeled (t, _, _)) -> begin
(freevars t)
end))


let free_variables : term  ->  fvs = (fun t -> (match ((FStar_ST.read t.freevars)) with
| Some (b) -> begin
b
end
| None -> begin
(

let fvs = (let _183_301 = (freevars t)
in (FStar_Util.remove_dups fv_eq _183_301))
in (

let _86_143 = (FStar_ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))


let qop_to_string : qop  ->  Prims.string = (fun _86_3 -> (match (_86_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun _86_4 -> (match (_86_4) with
| True -> begin
"true"
end
| False -> begin
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


let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun _86_5 -> (match (_86_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _183_308 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _183_308))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _183_312 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _183_312))
end
| FreeV (x) -> begin
(let _183_314 = (let _183_313 = (strSort (Prims.snd x))
in (Prims.strcat ":" _183_313))
in (Prims.strcat (Prims.fst x) _183_314))
end
| App (op, tms) -> begin
(let _183_318 = (let _183_317 = (let _183_316 = (let _183_315 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right _183_315 (FStar_String.concat " ")))
in (Prims.strcat _183_316 ")"))
in (Prims.strcat (op_to_string op) _183_317))
in (Prims.strcat "(" _183_318))
end
| Labeled (t, r1, r2) -> begin
(let _183_321 = (hash_of_term t)
in (let _183_320 = (let _183_319 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 _183_319))
in (Prims.strcat _183_321 _183_320)))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _183_338 = (let _183_337 = (let _183_336 = (let _183_335 = (let _183_322 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _183_322 (FStar_String.concat " ")))
in (let _183_334 = (let _183_333 = (let _183_332 = (hash_of_term body)
in (let _183_331 = (let _183_330 = (let _183_329 = (weightToSmt wopt)
in (let _183_328 = (let _183_327 = (let _183_326 = (let _183_325 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _183_324 = (FStar_List.map hash_of_term pats)
in (FStar_All.pipe_right _183_324 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _183_325 (FStar_String.concat "; ")))
in (Prims.strcat _183_326 "))"))
in (Prims.strcat " " _183_327))
in (Prims.strcat _183_329 _183_328)))
in (Prims.strcat " " _183_330))
in (Prims.strcat _183_332 _183_331)))
in (Prims.strcat ")(! " _183_333))
in (Prims.strcat _183_335 _183_334)))
in (Prims.strcat " (" _183_336))
in (Prims.strcat (qop_to_string qop) _183_337))
in (Prims.strcat "(" _183_338))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


type hash_cons_tab =
{mk_term : term'  ->  term; use_query_table : Prims.unit  ->  Prims.unit; drop_query_table : Prims.unit  ->  Prims.unit}


let is_Mkhash_cons_tab : hash_cons_tab  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkhash_cons_tab"))))


let mk : term'  ->  term = (fun t -> (let _183_370 = (FStar_Util.mk_ref None)
in {tm = t; freevars = _183_370}))


let mkTrue : term = (mk (App (((True), ([])))))


let mkFalse : term = (mk (App (((False), ([])))))


let mkInteger : Prims.string  ->  term = (fun i -> (let _183_374 = (let _183_373 = (FStar_Util.ensure_decimal i)
in Integer (_183_373))
in (mk _183_374)))


let mkInteger' : Prims.int  ->  term = (fun i -> (let _183_377 = (FStar_Util.string_of_int i)
in (mkInteger _183_377)))


let mkBoundV : Prims.int  ->  term = (fun i -> (mk (BoundV (i))))


let mkFreeV : (Prims.string * sort)  ->  term = (fun x -> (mk (FreeV (x))))


let mkApp' : (op * term Prims.list)  ->  term = (fun f -> (mk (App (f))))


let mkApp : (Prims.string * term Prims.list)  ->  term = (fun _86_211 -> (match (_86_211) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))))
end))


let mkNot : term  ->  term = (fun t -> (match (t.tm) with
| App (True, _86_215) -> begin
mkFalse
end
| App (False, _86_220) -> begin
mkTrue
end
| _86_224 -> begin
(mkApp' ((Not), ((t)::[])))
end))


let mkAnd : (term * term)  ->  term = (fun _86_227 -> (match (_86_227) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (True, _86_230), _86_234) -> begin
t2
end
| (_86_237, App (True, _86_240)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
mkFalse
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))))
end
| (_86_270, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)))
end
| (App (And, ts1), _86_281) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))))
end
| _86_284 -> begin
(mkApp' ((And), ((t1)::(t2)::[])))
end)
end))


let mkOr : (term * term)  ->  term = (fun _86_287 -> (match (_86_287) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
mkTrue
end
| (App (False, _86_306), _86_310) -> begin
t2
end
| (_86_313, App (False, _86_316)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))))
end
| (_86_330, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)))
end
| (App (Or, ts1), _86_341) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))))
end
| _86_344 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])))
end)
end))


let mkImp : (term * term)  ->  term = (fun _86_347 -> (match (_86_347) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((_, App (True, _))) | ((App (False, _), _)) -> begin
mkTrue
end
| (App (True, _86_366), _86_370) -> begin
t2
end
| (_86_373, App (Imp, (t1')::(t2')::[])) -> begin
(let _183_396 = (let _183_395 = (let _183_394 = (mkAnd ((t1), (t1')))
in (_183_394)::(t2')::[])
in ((Imp), (_183_395)))
in (mkApp' _183_396))
end
| _86_382 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])))
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  term = (fun op _86_386 -> (match (_86_386) with
| (t1, t2) -> begin
(mkApp' ((op), ((t1)::(t2)::[])))
end))


let mkMinus : term  ->  term = (fun t -> (mkApp' ((Minus), ((t)::[]))))


let mkIff : (term * term)  ->  term = (mk_bin_op Iff)


let mkEq : (term * term)  ->  term = (mk_bin_op Eq)


let mkLT : (term * term)  ->  term = (mk_bin_op LT)


let mkLTE : (term * term)  ->  term = (mk_bin_op LTE)


let mkGT : (term * term)  ->  term = (mk_bin_op GT)


let mkGTE : (term * term)  ->  term = (mk_bin_op GTE)


let mkAdd : (term * term)  ->  term = (mk_bin_op Add)


let mkSub : (term * term)  ->  term = (mk_bin_op Sub)


let mkDiv : (term * term)  ->  term = (mk_bin_op Div)


let mkMul : (term * term)  ->  term = (mk_bin_op Mul)


let mkMod : (term * term)  ->  term = (mk_bin_op Mod)


let mkITE : (term * term * term)  ->  term = (fun _86_391 -> (match (_86_391) with
| (t1, t2, t3) -> begin
(match (((t2.tm), (t3.tm))) with
| (App (True, _86_394), App (True, _86_399)) -> begin
mkTrue
end
| (App (True, _86_405), _86_409) -> begin
(let _183_417 = (let _183_416 = (mkNot t1)
in ((_183_416), (t3)))
in (mkImp _183_417))
end
| (_86_412, App (True, _86_415)) -> begin
(mkImp ((t1), (t2)))
end
| (_86_420, _86_422) -> begin
(mkApp' ((ITE), ((t1)::(t2)::(t3)::[])))
end)
end))


let mkCases : term Prims.list  ->  term = (fun t -> (match (t) with
| [] -> begin
(FStar_All.failwith "Impos")
end
| (hd)::tl -> begin
(FStar_List.fold_left (fun out t -> (mkAnd ((out), (t)))) hd tl)
end))


let mkQuant : (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _86_436 -> (match (_86_436) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = (Prims.parse_int "0")) then begin
body
end else begin
(match (body.tm) with
| App (True, _86_439) -> begin
body
end
| _86_443 -> begin
(mk (Quant (((qop), (pats), (wopt), (vars), (body)))))
end)
end
end))


let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (

let nvars = (FStar_List.length fvs)
in (

let index_of = (fun fv -> (match ((FStar_Util.try_find_index (fv_eq fv) fvs)) with
| None -> begin
None
end
| Some (i) -> begin
Some ((nvars - (i + (Prims.parse_int "1"))))
end))
in (

let rec aux = (fun ix t -> (match ((FStar_ST.read t.freevars)) with
| Some ([]) -> begin
t
end
| _86_458 -> begin
(match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
t
end
| FreeV (x) -> begin
(match ((index_of x)) with
| None -> begin
t
end
| Some (i) -> begin
(mkBoundV (i + ix))
end)
end
| App (op, tms) -> begin
(let _183_435 = (let _183_434 = (FStar_List.map (aux ix) tms)
in ((op), (_183_434)))
in (mkApp' _183_435))
end
| Labeled (t, r1, r2) -> begin
(let _183_438 = (let _183_437 = (let _183_436 = (aux ix t)
in ((_183_436), (r1), (r2)))
in Labeled (_183_437))
in (mk _183_438))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n = (FStar_List.length vars)
in (let _183_441 = (let _183_440 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _183_439 = (aux (ix + n) body)
in ((qop), (_183_440), (wopt), (vars), (_183_439))))
in (mkQuant _183_441)))
end)
end))
in (aux (Prims.parse_int "0") t)))))


let inst : term Prims.list  ->  term  ->  term = (fun tms t -> (

let n = (FStar_List.length tms)
in (

let rec aux = (fun shift t -> (match (t.tm) with
| (Integer (_)) | (FreeV (_)) -> begin
t
end
| BoundV (i) -> begin
if (((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n)) then begin
(FStar_List.nth tms (i - shift))
end else begin
t
end
end
| App (op, tms) -> begin
(let _183_451 = (let _183_450 = (FStar_List.map (aux shift) tms)
in ((op), (_183_450)))
in (mkApp' _183_451))
end
| Labeled (t, r1, r2) -> begin
(let _183_454 = (let _183_453 = (let _183_452 = (aux shift t)
in ((_183_452), (r1), (r2)))
in Labeled (_183_453))
in (mk _183_454))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift = (shift + m)
in (let _183_457 = (let _183_456 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _183_455 = (aux shift body)
in ((qop), (_183_456), (wopt), (vars), (_183_455))))
in (mkQuant _183_457))))
end))
in (aux (Prims.parse_int "0") t))))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list * term)  ->  term = (fun _86_524 -> (match (_86_524) with
| (qop, pats, wopt, vars, body) -> begin
(let _183_463 = (let _183_462 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _183_461 = (FStar_List.map fv_sort vars)
in (let _183_460 = (abstr vars body)
in ((qop), (_183_462), (wopt), (_183_461), (_183_460)))))
in (mkQuant _183_463))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _86_529 -> (match (_86_529) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)))
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  term = (fun _86_534 -> (match (_86_534) with
| (pats, wopt, vars, body) -> begin
(mkQuant' ((Forall), (pats), (wopt), (vars), (body)))
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _86_538 -> (match (_86_538) with
| (pats, vars, body) -> begin
(mkQuant' ((Forall), (pats), (None), (vars), (body)))
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _86_542 -> (match (_86_542) with
| (pats, vars, body) -> begin
(mkQuant' ((Exists), (pats), (None), (vars), (body)))
end))


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun _86_548 -> (match (_86_548) with
| (nm, vars, s, tm, c) -> begin
(let _183_476 = (let _183_475 = (FStar_List.map fv_sort vars)
in (let _183_474 = (abstr vars tm)
in ((nm), (_183_475), (s), (_183_474), (c))))
in DefineFun (_183_476))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _183_479 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _183_479)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun _86_552 id -> (match (_86_552) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (let _183_492 = (let _183_491 = (let _183_490 = (let _183_489 = (mkInteger' id)
in (let _183_488 = (let _183_487 = (let _183_486 = (constr_id_of_sort sort)
in (let _183_485 = (let _183_484 = (mkApp ((tok_name), ([])))
in (_183_484)::[])
in ((_183_486), (_183_485))))
in (mkApp _183_487))
in ((_183_489), (_183_488))))
in (mkEq _183_490))
in ((_183_491), (Some ("fresh token")), (Some (a_name))))
in Assume (_183_492)))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun _86_559 -> (match (_86_559) with
| (name, arg_sorts, sort, id) -> begin
(

let id = (FStar_Util.string_of_int id)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (let _183_499 = (let _183_498 = (let _183_497 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _183_497))
in ((_183_498), (s)))
in (mkFreeV _183_499)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)))
in (

let cid_app = (let _183_501 = (let _183_500 = (constr_id_of_sort sort)
in ((_183_500), ((capp)::[])))
in (mkApp _183_501))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (let _183_507 = (let _183_506 = (let _183_505 = (let _183_504 = (let _183_503 = (let _183_502 = (mkInteger id)
in ((_183_502), (cid_app)))
in (mkEq _183_503))
in ((((capp)::[])::[]), (bvar_names), (_183_504)))
in (mkForall _183_505))
in ((_183_506), (Some ("Constructor distinct")), (Some (a_name))))
in Assume (_183_507))))))))
end))


let injective_constructor : (Prims.string * (Prims.string * sort) Prims.list * sort)  ->  decls_t = (fun _86_571 -> (match (_86_571) with
| (name, projectors, sort) -> begin
(

let n_bvars = (FStar_List.length projectors)
in (

let bvar_name = (fun i -> (let _183_512 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _183_512)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (let _183_520 = (let _183_519 = (bvar_name i)
in ((_183_519), (s)))
in (mkFreeV _183_520)))
in (

let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _86_584 -> (match (_86_584) with
| (_86_582, s) -> begin
(bvar i s)
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)))
in (let _183_533 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _86_591 -> (match (_86_591) with
| (name, s) -> begin
(

let cproj_app = (mkApp ((name), ((capp)::[])))
in (

let proj_name = DeclFun (((name), ((sort)::[]), (s), (Some ("Projector"))))
in (

let a_name = (Prims.strcat "projection_inverse_" name)
in (let _183_532 = (let _183_531 = (let _183_530 = (let _183_529 = (let _183_528 = (let _183_527 = (let _183_526 = (let _183_525 = (bvar i s)
in ((cproj_app), (_183_525)))
in (mkEq _183_526))
in ((((capp)::[])::[]), (bvar_names), (_183_527)))
in (mkForall _183_528))
in ((_183_529), (Some ("Projection inverse")), (Some (a_name))))
in Assume (_183_530))
in (_183_531)::[])
in (proj_name)::_183_532))))
end))))
in (FStar_All.pipe_right _183_533 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun _86_600 -> (match (_86_600) with
| (name, projectors, sort, id, injective) -> begin
(

let injective = (injective || true)
in (

let cdecl = (let _183_537 = (let _183_536 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_183_536), (sort), (Some ("Constructor"))))
in DeclFun (_183_537))
in (

let cid = (let _183_539 = (let _183_538 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_183_538), (sort), (id)))
in (fresh_constructor _183_539))
in (

let disc = (

let disc_name = (Prims.strcat "is-" name)
in (

let xfv = (("x"), (sort))
in (

let xx = (mkFreeV xfv)
in (

let disc_eq = (let _183_545 = (let _183_544 = (let _183_541 = (let _183_540 = (constr_id_of_sort sort)
in ((_183_540), ((xx)::[])))
in (mkApp _183_541))
in (let _183_543 = (let _183_542 = (FStar_Util.string_of_int id)
in (mkInteger _183_542))
in ((_183_544), (_183_543))))
in (mkEq _183_545))
in (

let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _86_610 -> (match (_86_610) with
| (proj, s) -> begin
(mkApp ((proj), ((xx)::[])))
end))))
in (

let disc_inv_body = (let _183_548 = (let _183_547 = (mkApp ((name), (proj_terms)))
in ((xx), (_183_547)))
in (mkEq _183_548))
in (

let disc_ax = (mkAnd ((disc_eq), (disc_inv_body)))
in (mkDefineFun ((disc_name), ((xfv)::[]), (Bool_sort), (disc_ax), (Some ("Discriminator definition")))))))))))
in (

let projs = if injective then begin
(injective_constructor ((name), (projectors), (sort)))
end else begin
[]
end
in (let _183_555 = (let _183_550 = (let _183_549 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_183_549))
in (_183_550)::(cdecl)::(cid)::projs)
in (let _183_554 = (let _183_553 = (let _183_552 = (let _183_551 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_183_551))
in (_183_552)::[])
in (FStar_List.append ((disc)::[]) _183_553))
in (FStar_List.append _183_555 _183_554))))))))
end))


let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (

let _86_634 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _86_622 s -> (match (_86_622) with
| (names, binders, n) -> begin
(

let prefix = (match (s) with
| Term_sort -> begin
"@x"
end
| _86_626 -> begin
"@u"
end)
in (

let nm = (let _183_564 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _183_564))
in (

let names = (((nm), (s)))::names
in (

let b = (let _183_565 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _183_565))
in ((names), ((b)::binders), ((n + (Prims.parse_int "1"))))))))
end)) ((outer_names), ([]), (start))))
in (match (_86_634) with
| (names, binders, n) -> begin
((names), ((FStar_List.rev binders)), (n))
end)))


let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let _86_639 = (name_binders_inner [] (Prims.parse_int "0") sorts)
in (match (_86_639) with
| (names, binders, n) -> begin
(((FStar_List.rev names)), (binders))
end)))


let termToSmt : term  ->  Prims.string = (fun t -> (

let rec aux = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _183_576 = (FStar_List.nth names i)
in (FStar_All.pipe_right _183_576 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _183_578 = (let _183_577 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _183_577 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _183_578))
end
| Labeled (t, _86_661, _86_663) -> begin
(aux n names t)
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let _86_676 = (name_binders_inner names n sorts)
in (match (_86_676) with
| (names, binders, n) -> begin
(

let binders = (FStar_All.pipe_right binders (FStar_String.concat " "))
in (

let pats_str = (match (pats) with
| (([])::[]) | ([]) -> begin
""
end
| _86_682 -> begin
(let _183_584 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _183_583 = (let _183_582 = (FStar_List.map (fun p -> (let _183_581 = (aux n names p)
in (FStar_Util.format1 "%s" _183_581))) pats)
in (FStar_String.concat " " _183_582))
in (FStar_Util.format1 "\n:pattern (%s)" _183_583)))))
in (FStar_All.pipe_right _183_584 (FStar_String.concat "\n")))
end)
in (match (((pats), (wopt))) with
| ((([])::[], None)) | (([], None)) -> begin
(let _183_585 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _183_585))
end
| _86_694 -> begin
(let _183_587 = (aux n names body)
in (let _183_586 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _183_587 _183_586 pats_str)))
end)))
end))
end))
in (aux (Prims.parse_int "0") [] t)))


let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun _86_6 -> (match (_86_6) with
| None -> begin
""
end
| Some (c) -> begin
(

let _86_708 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::[] -> begin
((hd), (""))
end
| (hd)::_86_703 -> begin
((hd), ("..."))
end)
in (match (_86_708) with
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
(let _183_598 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _86_7 -> (match (_86_7) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _183_598))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (let _183_600 = (caption_to_string c)
in (let _183_599 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _183_600 f (FStar_String.concat " " l) _183_599))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let _86_737 = (name_binders arg_sorts)
in (match (_86_737) with
| (names, binders) -> begin
(

let body = (let _183_601 = (FStar_List.map mkFreeV names)
in (inst _183_601 body))
in (let _183_604 = (caption_to_string c)
in (let _183_603 = (strSort retsort)
in (let _183_602 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _183_604 f (FStar_String.concat " " binders) _183_603 _183_602)))))
end))
end
| Assume (t, c, Some (n)) -> begin
(let _183_606 = (caption_to_string c)
in (let _183_605 = (termToSmt t)
in (FStar_Util.format3 "%s(assert (!\n%s\n:named %s))" _183_606 _183_605 (escape n))))
end
| Assume (t, c, None) -> begin
(let _183_608 = (caption_to_string c)
in (let _183_607 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _183_608 _183_607)))
end
| Eval (t) -> begin
(let _183_609 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _183_609))
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
end)))
and mkPrelude : Prims.string  ->  Prims.string = (fun z3options -> (

let basic = (Prims.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n")
in (

let constrs = ((("FString_const"), (((("FString_const_proj_0"), (Int_sort)))::[]), (String_sort), ((Prims.parse_int "0")), (true)))::((("Tm_type"), ([]), (Term_sort), ((Prims.parse_int "2")), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort)))::[]), (Term_sort), ((Prims.parse_int "3")), (false)))::((("Tm_uvar"), (((("Tm_uvar_fst"), (Int_sort)))::[]), (Term_sort), ((Prims.parse_int "5")), (true)))::((("Tm_unit"), ([]), (Term_sort), ((Prims.parse_int "6")), (true)))::((("BoxInt"), (((("BoxInt_proj_0"), (Int_sort)))::[]), (Term_sort), ((Prims.parse_int "7")), (true)))::((("BoxBool"), (((("BoxBool_proj_0"), (Bool_sort)))::[]), (Term_sort), ((Prims.parse_int "8")), (true)))::((("BoxString"), (((("BoxString_proj_0"), (String_sort)))::[]), (Term_sort), ((Prims.parse_int "9")), (true)))::((("BoxRef"), (((("BoxRef_proj_0"), (Ref_sort)))::[]), (Term_sort), ((Prims.parse_int "10")), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort)))::((("LexCons_1"), (Term_sort)))::[]), (Term_sort), ((Prims.parse_int "11")), (true)))::[]
in (

let bcons = (let _183_612 = (let _183_611 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _183_611 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _183_612 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mk_Range_const : term = (mkApp (("Range_const"), ([])))


let mk_Term_type : term = (mkApp (("Tm_type"), ([])))


let mk_Term_app : term  ->  term  ->  term = (fun t1 t2 -> (mkApp (("Tm_app"), ((t1)::(t2)::[]))))


let mk_Term_uvar : Prims.int  ->  term = (fun i -> (let _183_621 = (let _183_620 = (let _183_619 = (mkInteger' i)
in (_183_619)::[])
in (("Tm_uvar"), (_183_620)))
in (mkApp _183_621)))


let mk_Term_unit : term = (mkApp (("Tm_unit"), ([])))


let boxInt : term  ->  term = (fun t -> (mkApp (("BoxInt"), ((t)::[]))))


let unboxInt : term  ->  term = (fun t -> (mkApp (("BoxInt_proj_0"), ((t)::[]))))


let boxBool : term  ->  term = (fun t -> (mkApp (("BoxBool"), ((t)::[]))))


let unboxBool : term  ->  term = (fun t -> (mkApp (("BoxBool_proj_0"), ((t)::[]))))


let boxString : term  ->  term = (fun t -> (mkApp (("BoxString"), ((t)::[]))))


let unboxString : term  ->  term = (fun t -> (mkApp (("BoxString_proj_0"), ((t)::[]))))


let boxRef : term  ->  term = (fun t -> (mkApp (("BoxRef"), ((t)::[]))))


let unboxRef : term  ->  term = (fun t -> (mkApp (("BoxRef_proj_0"), ((t)::[]))))


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
| _86_785 -> begin
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
| _86_793 -> begin
(Prims.raise FStar_Util.Impos)
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[]))))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (_86_805)::(t1)::(t2)::[]); freevars = _86_799})::[]) -> begin
(mkEq ((t1), (t2)))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (_86_822)::(t1)::(t2)::[]); freevars = _86_816})::[]) -> begin
(let _183_650 = (mkEq ((t1), (t2)))
in (mkNot _183_650))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = _86_833})::[]) -> begin
(let _183_653 = (let _183_652 = (unboxInt t1)
in (let _183_651 = (unboxInt t2)
in ((_183_652), (_183_651))))
in (mkLTE _183_653))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = _86_848})::[]) -> begin
(let _183_656 = (let _183_655 = (unboxInt t1)
in (let _183_654 = (unboxInt t2)
in ((_183_655), (_183_654))))
in (mkLT _183_656))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = _86_863})::[]) -> begin
(let _183_659 = (let _183_658 = (unboxInt t1)
in (let _183_657 = (unboxInt t2)
in ((_183_658), (_183_657))))
in (mkGTE _183_659))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = _86_878})::[]) -> begin
(let _183_662 = (let _183_661 = (unboxInt t1)
in (let _183_660 = (unboxInt t2)
in ((_183_661), (_183_660))))
in (mkGT _183_662))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = _86_893})::[]) -> begin
(let _183_665 = (let _183_664 = (unboxBool t1)
in (let _183_663 = (unboxBool t2)
in ((_183_664), (_183_663))))
in (mkAnd _183_665))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = _86_908})::[]) -> begin
(let _183_668 = (let _183_667 = (unboxBool t1)
in (let _183_666 = (unboxBool t2)
in ((_183_667), (_183_666))))
in (mkOr _183_668))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t)::[]); freevars = _86_923})::[]) -> begin
(let _183_669 = (unboxBool t)
in (mkNot _183_669))
end
| App (Var ("Prims.b2t"), (t)::[]) -> begin
(unboxBool t)
end
| _86_941 -> begin
(mkApp (("Valid"), ((t)::[])))
end))


let mk_HasType : term  ->  term  ->  term = (fun v t -> (mkApp (("HasType"), ((v)::(t)::[]))))


let mk_HasTypeZ : term  ->  term  ->  term = (fun v t -> (mkApp (("HasTypeZ"), ((v)::(t)::[]))))


let mk_IsTyped : term  ->  term = (fun v -> (mkApp (("IsTyped"), ((v)::[]))))


let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v t -> if (FStar_Options.unthrottle_inductives ()) then begin
(mk_HasType v t)
end else begin
(mkApp (("HasTypeFuel"), ((f)::(v)::(t)::[])))
end)


let mk_HasTypeWithFuel : term Prims.option  ->  term  ->  term  ->  term = (fun f v t -> (match (f) with
| None -> begin
(mk_HasType v t)
end
| Some (f) -> begin
(mk_HasTypeFuel f v t)
end))


let mk_Destruct : term  ->  term = (fun v -> (mkApp (("Destruct"), ((v)::[]))))


let mk_Rank : term  ->  term = (fun x -> (mkApp (("Rank"), ((x)::[]))))


let mk_tester : Prims.string  ->  term  ->  term = (fun n t -> (mkApp (((Prims.strcat "is-" n)), ((t)::[]))))


let mk_ApplyTF : term  ->  term  ->  term = (fun t t' -> (mkApp (("ApplyTF"), ((t)::(t')::[]))))


let mk_ApplyTT : term  ->  term  ->  term = (fun t t' -> (mkApp (("ApplyTT"), ((t)::(t')::[]))))


let mk_String_const : Prims.int  ->  term = (fun i -> (let _183_712 = (let _183_711 = (let _183_710 = (mkInteger' i)
in (_183_710)::[])
in (("FString_const"), (_183_711)))
in (mkApp _183_712)))


let mk_Precedes : term  ->  term  ->  term = (fun x1 x2 -> (let _183_717 = (mkApp (("Precedes"), ((x1)::(x2)::[])))
in (FStar_All.pipe_right _183_717 mk_Valid)))


let mk_LexCons : term  ->  term  ->  term = (fun x1 x2 -> (mkApp (("LexCons"), ((x1)::(x2)::[]))))


let rec n_fuel : Prims.int  ->  term = (fun n -> if (n = (Prims.parse_int "0")) then begin
(mkApp (("ZFuel"), ([])))
end else begin
(let _183_726 = (let _183_725 = (let _183_724 = (n_fuel (n - (Prims.parse_int "1")))
in (_183_724)::[])
in (("SFuel"), (_183_725)))
in (mkApp _183_726))
end)


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term Prims.option  ->  term Prims.option  ->  term Prims.option = (fun p1 p2 -> (match (((p1), (p2))) with
| (Some (p1), Some (p2)) -> begin
(let _183_731 = (mkAnd ((p1), (p2)))
in Some (_183_731))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))


let mk_and_opt_l : term Prims.option Prims.list  ->  term Prims.option = (fun pl -> (FStar_List.fold_left (fun out p -> (mk_and_opt p out)) None pl))


let mk_and_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkTrue
end
| (hd)::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkAnd ((p1), (p2)))) hd tl)
end))


let mk_or_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkFalse
end
| (hd)::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkOr ((p1), (p2)))) hd tl)
end))


let mk_haseq : term  ->  term = (fun t -> (let _183_746 = (mkApp (("Prims.hasEq"), ((t)::[])))
in (mk_Valid _183_746)))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "(Integer %s)" n)
end
| BoundV (n) -> begin
(let _183_751 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "(BoundV %s)" _183_751))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (Prims.fst fv))
end
| App (op, l) -> begin
(let _183_752 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _183_752))
end
| Labeled (t, r1, r2) -> begin
(let _183_753 = (print_smt_term t)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 _183_753))
end
| Quant (qop, l, _86_1024, _86_1026, t) -> begin
(let _183_755 = (print_smt_term_list_list l)
in (let _183_754 = (print_smt_term t)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) _183_755 _183_754)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (let _183_757 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right _183_757 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _183_763 = (let _183_762 = (let _183_761 = (print_smt_term_list l)
in (Prims.strcat _183_761 " ] "))
in (Prims.strcat "; [ " _183_762))
in (Prims.strcat s _183_763))) "" l))




