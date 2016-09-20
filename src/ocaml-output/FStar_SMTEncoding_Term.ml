
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
| Array (_83_10) -> begin
_83_10
end))


let ___Arrow____0 = (fun projectee -> (match (projectee) with
| Arrow (_83_13) -> begin
_83_13
end))


let ___Sort____0 = (fun projectee -> (match (projectee) with
| Sort (_83_16) -> begin
_83_16
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
(let _177_52 = (strSort s1)
in (let _177_51 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _177_52 _177_51)))
end
| Arrow (s1, s2) -> begin
(let _177_54 = (strSort s1)
in (let _177_53 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _177_54 _177_53)))
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
| Var (_83_36) -> begin
_83_36
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
{tm : term'; hash : Prims.string; freevars : fvs FStar_Syntax_Syntax.memo} 
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
| Integer (_83_42) -> begin
_83_42
end))


let ___BoundV____0 = (fun projectee -> (match (projectee) with
| BoundV (_83_45) -> begin
_83_45
end))


let ___FreeV____0 = (fun projectee -> (match (projectee) with
| FreeV (_83_48) -> begin
_83_48
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_83_51) -> begin
_83_51
end))


let ___Quant____0 = (fun projectee -> (match (projectee) with
| Quant (_83_54) -> begin
_83_54
end))


let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_83_57) -> begin
_83_57
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
| DeclFun (_83_61) -> begin
_83_61
end))


let ___DefineFun____0 = (fun projectee -> (match (projectee) with
| DefineFun (_83_64) -> begin
_83_64
end))


let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_83_67) -> begin
_83_67
end))


let ___Caption____0 = (fun projectee -> (match (projectee) with
| Caption (_83_70) -> begin
_83_70
end))


let ___Eval____0 = (fun projectee -> (match (projectee) with
| Eval (_83_73) -> begin
_83_73
end))


let ___Echo____0 = (fun projectee -> (match (projectee) with
| Echo (_83_76) -> begin
_83_76
end))


let ___SetOption____0 = (fun projectee -> (match (projectee) with
| SetOption (_83_79) -> begin
_83_79
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
| _83_91 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun _83_1 -> (match (_83_1) with
| {tm = FreeV (x); hash = _83_96; freevars = _83_94} -> begin
(fv_sort x)
end
| _83_101 -> begin
(FStar_All.failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun _83_2 -> (match (_83_2) with
| {tm = FreeV (fv); hash = _83_106; freevars = _83_104} -> begin
fv
end
| _83_111 -> begin
(FStar_All.failwith "impossible")
end))


let rec freevars : term  ->  fv Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (_83_122, tms) -> begin
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

let fvs = (let _177_304 = (freevars t)
in (FStar_Util.remove_dups fv_eq _177_304))
in (

let _83_148 = (FStar_ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))


let qop_to_string : qop  ->  Prims.string = (fun _83_3 -> (match (_83_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun _83_4 -> (match (_83_4) with
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


let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun _83_5 -> (match (_83_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _177_311 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _177_311))
end))


let hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _177_314 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _177_314))
end
| FreeV (x) -> begin
(let _177_316 = (let _177_315 = (strSort (Prims.snd x))
in (Prims.strcat ":" _177_315))
in (Prims.strcat (Prims.fst x) _177_316))
end
| App (op, tms) -> begin
(let _177_321 = (let _177_320 = (let _177_319 = (let _177_318 = (FStar_List.map (fun t -> t.hash) tms)
in (FStar_All.pipe_right _177_318 (FStar_String.concat " ")))
in (Prims.strcat _177_319 ")"))
in (Prims.strcat (op_to_string op) _177_320))
in (Prims.strcat "(" _177_321))
end
| Labeled (t, r1, r2) -> begin
(let _177_323 = (let _177_322 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 _177_322))
in (Prims.strcat t.hash _177_323))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _177_331 = (let _177_324 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _177_324 (FStar_String.concat " ")))
in (let _177_330 = (weightToSmt wopt)
in (let _177_329 = (let _177_328 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _177_327 = (FStar_List.map (fun p -> p.hash) pats)
in (FStar_All.pipe_right _177_327 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _177_328 (FStar_String.concat "; ")))
in (FStar_Util.format5 "(%s (%s)(! %s %s %s))" (qop_to_string qop) _177_331 body.hash _177_330 _177_329))))
end))


let __all_terms : term FStar_Util.smap FStar_ST.ref = (let _177_332 = (FStar_Util.smap_create (Prims.parse_int "10000"))
in (FStar_ST.alloc _177_332))


let all_terms : Prims.unit  ->  term FStar_Util.smap = (fun _83_205 -> (match (()) with
| () -> begin
(FStar_ST.read __all_terms)
end))


let mk : term'  ->  term = (fun t -> (

let key = (hash_of_term' t)
in (match ((let _177_337 = (all_terms ())
in (FStar_Util.smap_try_find _177_337 key))) with
| Some (tm) -> begin
tm
end
| None -> begin
(

let tm = (let _177_338 = (FStar_Util.mk_ref None)
in {tm = t; hash = key; freevars = _177_338})
in (

let _83_212 = (let _177_339 = (all_terms ())
in (FStar_Util.smap_add _177_339 key tm))
in tm))
end)))


let mkTrue : term = (mk (App (((True), ([])))))


let mkFalse : term = (mk (App (((False), ([])))))


let mkInteger : Prims.string  ->  term = (fun i -> (let _177_343 = (let _177_342 = (FStar_Util.ensure_decimal i)
in Integer (_177_342))
in (mk _177_343)))


let mkInteger' : Prims.int  ->  term = (fun i -> (let _177_346 = (FStar_Util.string_of_int i)
in (mkInteger _177_346)))


let mkBoundV : Prims.int  ->  term = (fun i -> (mk (BoundV (i))))


let mkFreeV : (Prims.string * sort)  ->  term = (fun x -> (mk (FreeV (x))))


let mkApp' : (op * term Prims.list)  ->  term = (fun f -> (mk (App (f))))


let mkApp : (Prims.string * term Prims.list)  ->  term = (fun _83_221 -> (match (_83_221) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))))
end))


let mkNot : term  ->  term = (fun t -> (match (t.tm) with
| App (True, _83_225) -> begin
mkFalse
end
| App (False, _83_230) -> begin
mkTrue
end
| _83_234 -> begin
(mkApp' ((Not), ((t)::[])))
end))


let mkAnd : (term * term)  ->  term = (fun _83_237 -> (match (_83_237) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (True, _83_240), _83_244) -> begin
t2
end
| (_83_247, App (True, _83_250)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
mkFalse
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))))
end
| (_83_280, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)))
end
| (App (And, ts1), _83_291) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))))
end
| _83_294 -> begin
(mkApp' ((And), ((t1)::(t2)::[])))
end)
end))


let mkOr : (term * term)  ->  term = (fun _83_297 -> (match (_83_297) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
mkTrue
end
| (App (False, _83_316), _83_320) -> begin
t2
end
| (_83_323, App (False, _83_326)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))))
end
| (_83_340, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)))
end
| (App (Or, ts1), _83_351) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))))
end
| _83_354 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])))
end)
end))


let mkImp : (term * term)  ->  term = (fun _83_357 -> (match (_83_357) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((_, App (True, _))) | ((App (False, _), _)) -> begin
mkTrue
end
| (App (True, _83_376), _83_380) -> begin
t2
end
| (_83_383, App (Imp, (t1')::(t2')::[])) -> begin
(let _177_365 = (let _177_364 = (let _177_363 = (mkAnd ((t1), (t1')))
in (_177_363)::(t2')::[])
in ((Imp), (_177_364)))
in (mkApp' _177_365))
end
| _83_392 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])))
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  term = (fun op _83_396 -> (match (_83_396) with
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


let mkITE : (term * term * term)  ->  term = (fun _83_401 -> (match (_83_401) with
| (t1, t2, t3) -> begin
(match (((t2.tm), (t3.tm))) with
| (App (True, _83_404), App (True, _83_409)) -> begin
mkTrue
end
| (App (True, _83_415), _83_419) -> begin
(let _177_386 = (let _177_385 = (mkNot t1)
in ((_177_385), (t3)))
in (mkImp _177_386))
end
| (_83_422, App (True, _83_425)) -> begin
(mkImp ((t1), (t2)))
end
| (_83_430, _83_432) -> begin
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


let mkQuant : (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _83_446 -> (match (_83_446) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = (Prims.parse_int "0")) then begin
body
end else begin
(match (body.tm) with
| App (True, _83_449) -> begin
body
end
| _83_453 -> begin
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
| _83_468 -> begin
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
(let _177_404 = (let _177_403 = (FStar_List.map (aux ix) tms)
in ((op), (_177_403)))
in (mkApp' _177_404))
end
| Labeled (t, r1, r2) -> begin
(let _177_407 = (let _177_406 = (let _177_405 = (aux ix t)
in ((_177_405), (r1), (r2)))
in Labeled (_177_406))
in (mk _177_407))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n = (FStar_List.length vars)
in (let _177_410 = (let _177_409 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _177_408 = (aux (ix + n) body)
in ((qop), (_177_409), (wopt), (vars), (_177_408))))
in (mkQuant _177_410)))
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
(let _177_420 = (let _177_419 = (FStar_List.map (aux shift) tms)
in ((op), (_177_419)))
in (mkApp' _177_420))
end
| Labeled (t, r1, r2) -> begin
(let _177_423 = (let _177_422 = (let _177_421 = (aux shift t)
in ((_177_421), (r1), (r2)))
in Labeled (_177_422))
in (mk _177_423))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift = (shift + m)
in (let _177_426 = (let _177_425 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _177_424 = (aux shift body)
in ((qop), (_177_425), (wopt), (vars), (_177_424))))
in (mkQuant _177_426))))
end))
in (aux (Prims.parse_int "0") t))))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list * term)  ->  term = (fun _83_534 -> (match (_83_534) with
| (qop, pats, wopt, vars, body) -> begin
(let _177_432 = (let _177_431 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _177_430 = (FStar_List.map fv_sort vars)
in (let _177_429 = (abstr vars body)
in ((qop), (_177_431), (wopt), (_177_430), (_177_429)))))
in (mkQuant _177_432))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _83_539 -> (match (_83_539) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)))
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  term = (fun _83_544 -> (match (_83_544) with
| (pats, wopt, vars, body) -> begin
(mkQuant' ((Forall), (pats), (wopt), (vars), (body)))
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _83_548 -> (match (_83_548) with
| (pats, vars, body) -> begin
(mkQuant' ((Forall), (pats), (None), (vars), (body)))
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _83_552 -> (match (_83_552) with
| (pats, vars, body) -> begin
(mkQuant' ((Exists), (pats), (None), (vars), (body)))
end))


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun _83_558 -> (match (_83_558) with
| (nm, vars, s, tm, c) -> begin
(let _177_445 = (let _177_444 = (FStar_List.map fv_sort vars)
in (let _177_443 = (abstr vars tm)
in ((nm), (_177_444), (s), (_177_443), (c))))
in DefineFun (_177_445))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _177_448 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _177_448)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun _83_562 id -> (match (_83_562) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (let _177_461 = (let _177_460 = (let _177_459 = (let _177_458 = (mkInteger' id)
in (let _177_457 = (let _177_456 = (let _177_455 = (constr_id_of_sort sort)
in (let _177_454 = (let _177_453 = (mkApp ((tok_name), ([])))
in (_177_453)::[])
in ((_177_455), (_177_454))))
in (mkApp _177_456))
in ((_177_458), (_177_457))))
in (mkEq _177_459))
in ((_177_460), (Some ("fresh token")), (Some (a_name))))
in Assume (_177_461)))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun _83_569 -> (match (_83_569) with
| (name, arg_sorts, sort, id) -> begin
(

let id = (FStar_Util.string_of_int id)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (let _177_468 = (let _177_467 = (let _177_466 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _177_466))
in ((_177_467), (s)))
in (mkFreeV _177_468)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)))
in (

let cid_app = (let _177_470 = (let _177_469 = (constr_id_of_sort sort)
in ((_177_469), ((capp)::[])))
in (mkApp _177_470))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (let _177_476 = (let _177_475 = (let _177_474 = (let _177_473 = (let _177_472 = (let _177_471 = (mkInteger id)
in ((_177_471), (cid_app)))
in (mkEq _177_472))
in ((((capp)::[])::[]), (bvar_names), (_177_473)))
in (mkForall _177_474))
in ((_177_475), (Some ("Constructor distinct")), (Some (a_name))))
in Assume (_177_476))))))))
end))


let injective_constructor : (Prims.string * (Prims.string * sort) Prims.list * sort)  ->  decls_t = (fun _83_581 -> (match (_83_581) with
| (name, projectors, sort) -> begin
(

let n_bvars = (FStar_List.length projectors)
in (

let bvar_name = (fun i -> (let _177_481 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _177_481)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (let _177_489 = (let _177_488 = (bvar_name i)
in ((_177_488), (s)))
in (mkFreeV _177_489)))
in (

let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _83_594 -> (match (_83_594) with
| (_83_592, s) -> begin
(bvar i s)
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)))
in (let _177_502 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _83_601 -> (match (_83_601) with
| (name, s) -> begin
(

let cproj_app = (mkApp ((name), ((capp)::[])))
in (

let proj_name = DeclFun (((name), ((sort)::[]), (s), (Some ("Projector"))))
in (

let a_name = (Prims.strcat "projection_inverse_" name)
in (let _177_501 = (let _177_500 = (let _177_499 = (let _177_498 = (let _177_497 = (let _177_496 = (let _177_495 = (let _177_494 = (bvar i s)
in ((cproj_app), (_177_494)))
in (mkEq _177_495))
in ((((capp)::[])::[]), (bvar_names), (_177_496)))
in (mkForall _177_497))
in ((_177_498), (Some ("Projection inverse")), (Some (a_name))))
in Assume (_177_499))
in (_177_500)::[])
in (proj_name)::_177_501))))
end))))
in (FStar_All.pipe_right _177_502 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun _83_610 -> (match (_83_610) with
| (name, projectors, sort, id, injective) -> begin
(

let injective = (injective || true)
in (

let cdecl = (let _177_506 = (let _177_505 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_177_505), (sort), (Some ("Constructor"))))
in DeclFun (_177_506))
in (

let cid = (let _177_508 = (let _177_507 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_177_507), (sort), (id)))
in (fresh_constructor _177_508))
in (

let disc = (

let disc_name = (Prims.strcat "is-" name)
in (

let xfv = (("x"), (sort))
in (

let xx = (mkFreeV xfv)
in (

let disc_eq = (let _177_514 = (let _177_513 = (let _177_510 = (let _177_509 = (constr_id_of_sort sort)
in ((_177_509), ((xx)::[])))
in (mkApp _177_510))
in (let _177_512 = (let _177_511 = (FStar_Util.string_of_int id)
in (mkInteger _177_511))
in ((_177_513), (_177_512))))
in (mkEq _177_514))
in (

let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _83_620 -> (match (_83_620) with
| (proj, s) -> begin
(mkApp ((proj), ((xx)::[])))
end))))
in (

let disc_inv_body = (let _177_517 = (let _177_516 = (mkApp ((name), (proj_terms)))
in ((xx), (_177_516)))
in (mkEq _177_517))
in (

let disc_ax = (mkAnd ((disc_eq), (disc_inv_body)))
in (mkDefineFun ((disc_name), ((xfv)::[]), (Bool_sort), (disc_ax), (Some ("Discriminator definition")))))))))))
in (

let projs = if injective then begin
(injective_constructor ((name), (projectors), (sort)))
end else begin
[]
end
in (let _177_524 = (let _177_519 = (let _177_518 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_177_518))
in (_177_519)::(cdecl)::(cid)::projs)
in (let _177_523 = (let _177_522 = (let _177_521 = (let _177_520 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_177_520))
in (_177_521)::[])
in (FStar_List.append ((disc)::[]) _177_522))
in (FStar_List.append _177_524 _177_523))))))))
end))


let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (

let _83_644 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _83_632 s -> (match (_83_632) with
| (names, binders, n) -> begin
(

let prefix = (match (s) with
| Term_sort -> begin
"@x"
end
| _83_636 -> begin
"@u"
end)
in (

let nm = (let _177_533 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _177_533))
in (

let names = (((nm), (s)))::names
in (

let b = (let _177_534 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _177_534))
in ((names), ((b)::binders), ((n + (Prims.parse_int "1"))))))))
end)) ((outer_names), ([]), (start))))
in (match (_83_644) with
| (names, binders, n) -> begin
((names), ((FStar_List.rev binders)), (n))
end)))


let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let _83_649 = (name_binders_inner [] (Prims.parse_int "0") sorts)
in (match (_83_649) with
| (names, binders, n) -> begin
(((FStar_List.rev names)), (binders))
end)))


let termToSmt : term  ->  Prims.string = (fun t -> (

let rec aux = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _177_545 = (FStar_List.nth names i)
in (FStar_All.pipe_right _177_545 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _177_547 = (let _177_546 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _177_546 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _177_547))
end
| Labeled (t, _83_671, _83_673) -> begin
(aux n names t)
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let _83_686 = (name_binders_inner names n sorts)
in (match (_83_686) with
| (names, binders, n) -> begin
(

let binders = (FStar_All.pipe_right binders (FStar_String.concat " "))
in (

let pats_str = (match (pats) with
| (([])::[]) | ([]) -> begin
""
end
| _83_692 -> begin
(let _177_553 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _177_552 = (let _177_551 = (FStar_List.map (fun p -> (let _177_550 = (aux n names p)
in (FStar_Util.format1 "%s" _177_550))) pats)
in (FStar_String.concat " " _177_551))
in (FStar_Util.format1 "\n:pattern (%s)" _177_552)))))
in (FStar_All.pipe_right _177_553 (FStar_String.concat "\n")))
end)
in (match (((pats), (wopt))) with
| ((([])::[], None)) | (([], None)) -> begin
(let _177_554 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _177_554))
end
| _83_704 -> begin
(let _177_556 = (aux n names body)
in (let _177_555 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _177_556 _177_555 pats_str)))
end)))
end))
end))
in (aux (Prims.parse_int "0") [] t)))


let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun _83_6 -> (match (_83_6) with
| None -> begin
""
end
| Some (c) -> begin
(

let _83_718 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::[] -> begin
((hd), (""))
end
| (hd)::_83_713 -> begin
((hd), ("..."))
end)
in (match (_83_718) with
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
(let _177_567 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _83_7 -> (match (_83_7) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _177_567))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (let _177_569 = (caption_to_string c)
in (let _177_568 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _177_569 f (FStar_String.concat " " l) _177_568))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let _83_747 = (name_binders arg_sorts)
in (match (_83_747) with
| (names, binders) -> begin
(

let body = (let _177_570 = (FStar_List.map mkFreeV names)
in (inst _177_570 body))
in (let _177_573 = (caption_to_string c)
in (let _177_572 = (strSort retsort)
in (let _177_571 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _177_573 f (FStar_String.concat " " binders) _177_572 _177_571)))))
end))
end
| Assume (t, c, Some (n)) -> begin
(let _177_575 = (caption_to_string c)
in (let _177_574 = (termToSmt t)
in (FStar_Util.format3 "%s(assert (!\n%s\n:named %s))" _177_575 _177_574 (escape n))))
end
| Assume (t, c, None) -> begin
(let _177_577 = (caption_to_string c)
in (let _177_576 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _177_577 _177_576)))
end
| Eval (t) -> begin
(let _177_578 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _177_578))
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

let bcons = (let _177_581 = (let _177_580 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _177_580 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _177_581 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mk_Range_const : term = (mkApp (("Range_const"), ([])))


let mk_Term_type : term = (mkApp (("Tm_type"), ([])))


let mk_Term_app : term  ->  term  ->  term = (fun t1 t2 -> (mkApp (("Tm_app"), ((t1)::(t2)::[]))))


let mk_Term_uvar : Prims.int  ->  term = (fun i -> (let _177_590 = (let _177_589 = (let _177_588 = (mkInteger' i)
in (_177_588)::[])
in (("Tm_uvar"), (_177_589)))
in (mkApp _177_590)))


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
| _83_795 -> begin
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
| _83_803 -> begin
(Prims.raise FStar_Util.Impos)
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[]))))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (_83_817)::(t1)::(t2)::[]); hash = _83_811; freevars = _83_809})::[]) -> begin
(mkEq ((t1), (t2)))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (_83_836)::(t1)::(t2)::[]); hash = _83_830; freevars = _83_828})::[]) -> begin
(let _177_619 = (mkEq ((t1), (t2)))
in (mkNot _177_619))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); hash = _83_849; freevars = _83_847})::[]) -> begin
(let _177_622 = (let _177_621 = (unboxInt t1)
in (let _177_620 = (unboxInt t2)
in ((_177_621), (_177_620))))
in (mkLTE _177_622))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); hash = _83_866; freevars = _83_864})::[]) -> begin
(let _177_625 = (let _177_624 = (unboxInt t1)
in (let _177_623 = (unboxInt t2)
in ((_177_624), (_177_623))))
in (mkLT _177_625))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); hash = _83_883; freevars = _83_881})::[]) -> begin
(let _177_628 = (let _177_627 = (unboxInt t1)
in (let _177_626 = (unboxInt t2)
in ((_177_627), (_177_626))))
in (mkGTE _177_628))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); hash = _83_900; freevars = _83_898})::[]) -> begin
(let _177_631 = (let _177_630 = (unboxInt t1)
in (let _177_629 = (unboxInt t2)
in ((_177_630), (_177_629))))
in (mkGT _177_631))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); hash = _83_917; freevars = _83_915})::[]) -> begin
(let _177_634 = (let _177_633 = (unboxBool t1)
in (let _177_632 = (unboxBool t2)
in ((_177_633), (_177_632))))
in (mkAnd _177_634))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); hash = _83_934; freevars = _83_932})::[]) -> begin
(let _177_637 = (let _177_636 = (unboxBool t1)
in (let _177_635 = (unboxBool t2)
in ((_177_636), (_177_635))))
in (mkOr _177_637))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t)::[]); hash = _83_951; freevars = _83_949})::[]) -> begin
(let _177_638 = (unboxBool t)
in (mkNot _177_638))
end
| App (Var ("Prims.b2t"), (t)::[]) -> begin
(unboxBool t)
end
| _83_969 -> begin
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


let mk_String_const : Prims.int  ->  term = (fun i -> (let _177_681 = (let _177_680 = (let _177_679 = (mkInteger' i)
in (_177_679)::[])
in (("FString_const"), (_177_680)))
in (mkApp _177_681)))


let mk_Precedes : term  ->  term  ->  term = (fun x1 x2 -> (let _177_686 = (mkApp (("Precedes"), ((x1)::(x2)::[])))
in (FStar_All.pipe_right _177_686 mk_Valid)))


let mk_LexCons : term  ->  term  ->  term = (fun x1 x2 -> (mkApp (("LexCons"), ((x1)::(x2)::[]))))


let rec n_fuel : Prims.int  ->  term = (fun n -> if (n = (Prims.parse_int "0")) then begin
(mkApp (("ZFuel"), ([])))
end else begin
(let _177_695 = (let _177_694 = (let _177_693 = (n_fuel (n - (Prims.parse_int "1")))
in (_177_693)::[])
in (("SFuel"), (_177_694)))
in (mkApp _177_695))
end)


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term Prims.option  ->  term Prims.option  ->  term Prims.option = (fun p1 p2 -> (match (((p1), (p2))) with
| (Some (p1), Some (p2)) -> begin
(let _177_700 = (mkAnd ((p1), (p2)))
in Some (_177_700))
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


let mk_haseq : term  ->  term = (fun t -> (let _177_715 = (mkApp (("Prims.hasEq"), ((t)::[])))
in (mk_Valid _177_715)))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "(Integer %s)" n)
end
| BoundV (n) -> begin
(let _177_720 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "(BoundV %s)" _177_720))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (Prims.fst fv))
end
| App (op, l) -> begin
(let _177_721 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _177_721))
end
| Labeled (t, r1, r2) -> begin
(let _177_722 = (print_smt_term t)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 _177_722))
end
| Quant (qop, l, _83_1052, _83_1054, t) -> begin
(let _177_724 = (print_smt_term_list_list l)
in (let _177_723 = (print_smt_term t)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) _177_724 _177_723)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (let _177_726 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right _177_726 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _177_732 = (let _177_731 = (let _177_730 = (print_smt_term_list l)
in (Prims.strcat _177_730 " ] "))
in (Prims.strcat "; [ " _177_731))
in (Prims.strcat s _177_732))) "" l))




