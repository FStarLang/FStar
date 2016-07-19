
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
| Array (_81_10) -> begin
_81_10
end))


let ___Arrow____0 = (fun projectee -> (match (projectee) with
| Arrow (_81_13) -> begin
_81_13
end))


let ___Sort____0 = (fun projectee -> (match (projectee) with
| Sort (_81_16) -> begin
_81_16
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
"String"
end
| Ref_sort -> begin
"Ref"
end
| Fuel_sort -> begin
"Fuel"
end
| Array (s1, s2) -> begin
(let _173_52 = (strSort s1)
in (let _173_51 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _173_52 _173_51)))
end
| Arrow (s1, s2) -> begin
(let _173_54 = (strSort s1)
in (let _173_53 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _173_54 _173_53)))
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
| Var (_81_36) -> begin
_81_36
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
| Integer (_81_42) -> begin
_81_42
end))


let ___BoundV____0 = (fun projectee -> (match (projectee) with
| BoundV (_81_45) -> begin
_81_45
end))


let ___FreeV____0 = (fun projectee -> (match (projectee) with
| FreeV (_81_48) -> begin
_81_48
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_81_51) -> begin
_81_51
end))


let ___Quant____0 = (fun projectee -> (match (projectee) with
| Quant (_81_54) -> begin
_81_54
end))


let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_81_57) -> begin
_81_57
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
| DeclFun (_81_61) -> begin
_81_61
end))


let ___DefineFun____0 = (fun projectee -> (match (projectee) with
| DefineFun (_81_64) -> begin
_81_64
end))


let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_81_67) -> begin
_81_67
end))


let ___Caption____0 = (fun projectee -> (match (projectee) with
| Caption (_81_70) -> begin
_81_70
end))


let ___Eval____0 = (fun projectee -> (match (projectee) with
| Eval (_81_73) -> begin
_81_73
end))


let ___Echo____0 = (fun projectee -> (match (projectee) with
| Echo (_81_76) -> begin
_81_76
end))


let ___SetOption____0 = (fun projectee -> (match (projectee) with
| SetOption (_81_79) -> begin
_81_79
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
| _81_91 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun _81_1 -> (match (_81_1) with
| {tm = FreeV (x); hash = _81_96; freevars = _81_94} -> begin
(fv_sort x)
end
| _81_101 -> begin
(FStar_All.failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun _81_2 -> (match (_81_2) with
| {tm = FreeV (fv); hash = _81_106; freevars = _81_104} -> begin
fv
end
| _81_111 -> begin
(FStar_All.failwith "impossible")
end))


let rec freevars : term  ->  fv Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (_81_122, tms) -> begin
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

let fvs = (let _173_304 = (freevars t)
in (FStar_Util.remove_dups fv_eq _173_304))
in (

let _81_148 = (FStar_ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))


let qop_to_string : qop  ->  Prims.string = (fun _81_3 -> (match (_81_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun _81_4 -> (match (_81_4) with
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


let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun _81_5 -> (match (_81_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _173_311 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _173_311))
end))


let hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _173_314 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _173_314))
end
| FreeV (x) -> begin
(let _173_315 = (strSort (Prims.snd x))
in (Prims.strcat (Prims.strcat (Prims.fst x) ":") _173_315))
end
| App (op, tms) -> begin
(let _173_319 = (let _173_318 = (let _173_317 = (FStar_List.map (fun t -> t.hash) tms)
in (FStar_All.pipe_right _173_317 (FStar_String.concat " ")))
in (Prims.strcat (Prims.strcat "(" (op_to_string op)) _173_318))
in (Prims.strcat _173_319 ")"))
end
| Labeled (t, r1, r2) -> begin
(let _173_320 = (FStar_Range.string_of_range r2)
in (Prims.strcat (Prims.strcat t.hash r1) _173_320))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _173_328 = (let _173_321 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _173_321 (FStar_String.concat " ")))
in (let _173_327 = (weightToSmt wopt)
in (let _173_326 = (let _173_325 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _173_324 = (FStar_List.map (fun p -> p.hash) pats)
in (FStar_All.pipe_right _173_324 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _173_325 (FStar_String.concat "; ")))
in (FStar_Util.format5 "(%s (%s)(! %s %s %s))" (qop_to_string qop) _173_328 body.hash _173_327 _173_326))))
end))


let __all_terms : term FStar_Util.smap FStar_ST.ref = (let _173_329 = (FStar_Util.smap_create 10000)
in (FStar_ST.alloc _173_329))


let all_terms : Prims.unit  ->  term FStar_Util.smap = (fun _81_205 -> (match (()) with
| () -> begin
(FStar_ST.read __all_terms)
end))


let mk : term'  ->  term = (fun t -> (

let key = (hash_of_term' t)
in (match ((let _173_334 = (all_terms ())
in (FStar_Util.smap_try_find _173_334 key))) with
| Some (tm) -> begin
tm
end
| None -> begin
(

let tm = (let _173_335 = (FStar_Util.mk_ref None)
in {tm = t; hash = key; freevars = _173_335})
in (

let _81_212 = (let _173_336 = (all_terms ())
in (FStar_Util.smap_add _173_336 key tm))
in tm))
end)))


let mkTrue : term = (mk (App (((True), ([])))))


let mkFalse : term = (mk (App (((False), ([])))))


let mkInteger : Prims.string  ->  term = (fun i -> (let _173_340 = (let _173_339 = (FStar_Util.ensure_decimal i)
in Integer (_173_339))
in (mk _173_340)))


let mkInteger' : Prims.int  ->  term = (fun i -> (let _173_343 = (FStar_Util.string_of_int i)
in (mkInteger _173_343)))


let mkBoundV : Prims.int  ->  term = (fun i -> (mk (BoundV (i))))


let mkFreeV : (Prims.string * sort)  ->  term = (fun x -> (mk (FreeV (x))))


let mkApp' : (op * term Prims.list)  ->  term = (fun f -> (mk (App (f))))


let mkApp : (Prims.string * term Prims.list)  ->  term = (fun _81_221 -> (match (_81_221) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))))
end))


let mkNot : term  ->  term = (fun t -> (match (t.tm) with
| App (True, _81_225) -> begin
mkFalse
end
| App (False, _81_230) -> begin
mkTrue
end
| _81_234 -> begin
(mkApp' ((Not), ((t)::[])))
end))


let mkAnd : (term * term)  ->  term = (fun _81_237 -> (match (_81_237) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (True, _81_240), _81_244) -> begin
t2
end
| (_81_247, App (True, _81_250)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
mkFalse
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))))
end
| (_81_280, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)))
end
| (App (And, ts1), _81_291) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))))
end
| _81_294 -> begin
(mkApp' ((And), ((t1)::(t2)::[])))
end)
end))


let mkOr : (term * term)  ->  term = (fun _81_297 -> (match (_81_297) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
mkTrue
end
| (App (False, _81_316), _81_320) -> begin
t2
end
| (_81_323, App (False, _81_326)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))))
end
| (_81_340, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)))
end
| (App (Or, ts1), _81_351) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))))
end
| _81_354 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])))
end)
end))


let mkImp : (term * term)  ->  term = (fun _81_357 -> (match (_81_357) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((_, App (True, _))) | ((App (False, _), _)) -> begin
mkTrue
end
| (App (True, _81_376), _81_380) -> begin
t2
end
| (_81_383, App (Imp, (t1')::(t2')::[])) -> begin
(let _173_362 = (let _173_361 = (let _173_360 = (mkAnd ((t1), (t1')))
in (_173_360)::(t2')::[])
in ((Imp), (_173_361)))
in (mkApp' _173_362))
end
| _81_392 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])))
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  term = (fun op _81_396 -> (match (_81_396) with
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


let mkITE : (term * term * term)  ->  term = (fun _81_401 -> (match (_81_401) with
| (t1, t2, t3) -> begin
(match (((t2.tm), (t3.tm))) with
| (App (True, _81_404), App (True, _81_409)) -> begin
mkTrue
end
| (App (True, _81_415), _81_419) -> begin
(let _173_383 = (let _173_382 = (mkNot t1)
in ((_173_382), (t3)))
in (mkImp _173_383))
end
| (_81_422, App (True, _81_425)) -> begin
(mkImp ((t1), (t2)))
end
| (_81_430, _81_432) -> begin
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


let mkQuant : (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _81_446 -> (match (_81_446) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = 0) then begin
body
end else begin
(match (body.tm) with
| App (True, _81_449) -> begin
body
end
| _81_453 -> begin
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
Some ((nvars - (i + 1)))
end))
in (

let rec aux = (fun ix t -> (match ((FStar_ST.read t.freevars)) with
| Some ([]) -> begin
t
end
| _81_468 -> begin
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
(let _173_401 = (let _173_400 = (FStar_List.map (aux ix) tms)
in ((op), (_173_400)))
in (mkApp' _173_401))
end
| Labeled (t, r1, r2) -> begin
(let _173_404 = (let _173_403 = (let _173_402 = (aux ix t)
in ((_173_402), (r1), (r2)))
in Labeled (_173_403))
in (mk _173_404))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n = (FStar_List.length vars)
in (let _173_407 = (let _173_406 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _173_405 = (aux (ix + n) body)
in ((qop), (_173_406), (wopt), (vars), (_173_405))))
in (mkQuant _173_407)))
end)
end))
in (aux 0 t)))))


let inst : term Prims.list  ->  term  ->  term = (fun tms t -> (

let n = (FStar_List.length tms)
in (

let rec aux = (fun shift t -> (match (t.tm) with
| (Integer (_)) | (FreeV (_)) -> begin
t
end
| BoundV (i) -> begin
if ((0 <= (i - shift)) && ((i - shift) < n)) then begin
(FStar_List.nth tms (i - shift))
end else begin
t
end
end
| App (op, tms) -> begin
(let _173_417 = (let _173_416 = (FStar_List.map (aux shift) tms)
in ((op), (_173_416)))
in (mkApp' _173_417))
end
| Labeled (t, r1, r2) -> begin
(let _173_420 = (let _173_419 = (let _173_418 = (aux shift t)
in ((_173_418), (r1), (r2)))
in Labeled (_173_419))
in (mk _173_420))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift = (shift + m)
in (let _173_423 = (let _173_422 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _173_421 = (aux shift body)
in ((qop), (_173_422), (wopt), (vars), (_173_421))))
in (mkQuant _173_423))))
end))
in (aux 0 t))))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list * term)  ->  term = (fun _81_534 -> (match (_81_534) with
| (qop, pats, wopt, vars, body) -> begin
(let _173_429 = (let _173_428 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _173_427 = (FStar_List.map fv_sort vars)
in (let _173_426 = (abstr vars body)
in ((qop), (_173_428), (wopt), (_173_427), (_173_426)))))
in (mkQuant _173_429))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _81_539 -> (match (_81_539) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)))
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  term = (fun _81_544 -> (match (_81_544) with
| (pats, wopt, vars, body) -> begin
(mkQuant' ((Forall), (pats), (wopt), (vars), (body)))
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _81_548 -> (match (_81_548) with
| (pats, vars, body) -> begin
(mkQuant' ((Forall), (pats), (None), (vars), (body)))
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _81_552 -> (match (_81_552) with
| (pats, vars, body) -> begin
(mkQuant' ((Exists), (pats), (None), (vars), (body)))
end))


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun _81_558 -> (match (_81_558) with
| (nm, vars, s, tm, c) -> begin
(let _173_442 = (let _173_441 = (FStar_List.map fv_sort vars)
in (let _173_440 = (abstr vars tm)
in ((nm), (_173_441), (s), (_173_440), (c))))
in DefineFun (_173_442))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _173_445 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _173_445)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun _81_562 id -> (match (_81_562) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (let _173_458 = (let _173_457 = (let _173_456 = (let _173_455 = (mkInteger' id)
in (let _173_454 = (let _173_453 = (let _173_452 = (constr_id_of_sort sort)
in (let _173_451 = (let _173_450 = (mkApp ((tok_name), ([])))
in (_173_450)::[])
in ((_173_452), (_173_451))))
in (mkApp _173_453))
in ((_173_455), (_173_454))))
in (mkEq _173_456))
in ((_173_457), (Some ("fresh token")), (Some (a_name))))
in Assume (_173_458)))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun _81_569 -> (match (_81_569) with
| (name, arg_sorts, sort, id) -> begin
(

let id = (FStar_Util.string_of_int id)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (let _173_465 = (let _173_464 = (let _173_463 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _173_463))
in ((_173_464), (s)))
in (mkFreeV _173_465)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)))
in (

let cid_app = (let _173_467 = (let _173_466 = (constr_id_of_sort sort)
in ((_173_466), ((capp)::[])))
in (mkApp _173_467))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (let _173_473 = (let _173_472 = (let _173_471 = (let _173_470 = (let _173_469 = (let _173_468 = (mkInteger id)
in ((_173_468), (cid_app)))
in (mkEq _173_469))
in ((((capp)::[])::[]), (bvar_names), (_173_470)))
in (mkForall _173_471))
in ((_173_472), (Some ("Constructor distinct")), (Some (a_name))))
in Assume (_173_473))))))))
end))


let injective_constructor : (Prims.string * (Prims.string * sort) Prims.list * sort)  ->  decls_t = (fun _81_581 -> (match (_81_581) with
| (name, projectors, sort) -> begin
(

let n_bvars = (FStar_List.length projectors)
in (

let bvar_name = (fun i -> (let _173_478 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _173_478)))
in (

let bvar_index = (fun i -> (n_bvars - (i + 1)))
in (

let bvar = (fun i s -> (let _173_486 = (let _173_485 = (bvar_name i)
in ((_173_485), (s)))
in (mkFreeV _173_486)))
in (

let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _81_594 -> (match (_81_594) with
| (_81_592, s) -> begin
(bvar i s)
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)))
in (let _173_499 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _81_601 -> (match (_81_601) with
| (name, s) -> begin
(

let cproj_app = (mkApp ((name), ((capp)::[])))
in (

let proj_name = DeclFun (((name), ((sort)::[]), (s), (Some ("Projector"))))
in (

let a_name = (Prims.strcat "projection_inverse_" name)
in (let _173_498 = (let _173_497 = (let _173_496 = (let _173_495 = (let _173_494 = (let _173_493 = (let _173_492 = (let _173_491 = (bvar i s)
in ((cproj_app), (_173_491)))
in (mkEq _173_492))
in ((((capp)::[])::[]), (bvar_names), (_173_493)))
in (mkForall _173_494))
in ((_173_495), (Some ("Projection inverse")), (Some (a_name))))
in Assume (_173_496))
in (_173_497)::[])
in (proj_name)::_173_498))))
end))))
in (FStar_All.pipe_right _173_499 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun _81_610 -> (match (_81_610) with
| (name, projectors, sort, id, injective) -> begin
(

let injective = (injective || true)
in (

let cdecl = (let _173_503 = (let _173_502 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_173_502), (sort), (Some ("Constructor"))))
in DeclFun (_173_503))
in (

let cid = (let _173_505 = (let _173_504 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_173_504), (sort), (id)))
in (fresh_constructor _173_505))
in (

let disc = (

let disc_name = (Prims.strcat "is-" name)
in (

let xfv = (("x"), (sort))
in (

let xx = (mkFreeV xfv)
in (

let disc_eq = (let _173_511 = (let _173_510 = (let _173_507 = (let _173_506 = (constr_id_of_sort sort)
in ((_173_506), ((xx)::[])))
in (mkApp _173_507))
in (let _173_509 = (let _173_508 = (FStar_Util.string_of_int id)
in (mkInteger _173_508))
in ((_173_510), (_173_509))))
in (mkEq _173_511))
in (

let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _81_620 -> (match (_81_620) with
| (proj, s) -> begin
(mkApp ((proj), ((xx)::[])))
end))))
in (

let disc_inv_body = (let _173_514 = (let _173_513 = (mkApp ((name), (proj_terms)))
in ((xx), (_173_513)))
in (mkEq _173_514))
in (

let disc_ax = (mkAnd ((disc_eq), (disc_inv_body)))
in (mkDefineFun ((disc_name), ((xfv)::[]), (Bool_sort), (disc_ax), (Some ("Discriminator definition")))))))))))
in (

let projs = if injective then begin
(injective_constructor ((name), (projectors), (sort)))
end else begin
[]
end
in (let _173_521 = (let _173_517 = (let _173_516 = (let _173_515 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_173_515))
in (_173_516)::(cdecl)::(cid)::projs)
in (FStar_List.append _173_517 ((disc)::[])))
in (let _173_520 = (let _173_519 = (let _173_518 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_173_518))
in (_173_519)::[])
in (FStar_List.append _173_521 _173_520))))))))
end))


let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (

let _81_644 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _81_632 s -> (match (_81_632) with
| (names, binders, n) -> begin
(

let prefix = (match (s) with
| Term_sort -> begin
"@x"
end
| _81_636 -> begin
"@u"
end)
in (

let nm = (let _173_530 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _173_530))
in (

let names = (((nm), (s)))::names
in (

let b = (let _173_531 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _173_531))
in ((names), ((b)::binders), ((n + 1)))))))
end)) ((outer_names), ([]), (start))))
in (match (_81_644) with
| (names, binders, n) -> begin
((names), ((FStar_List.rev binders)), (n))
end)))


let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let _81_649 = (name_binders_inner [] 0 sorts)
in (match (_81_649) with
| (names, binders, n) -> begin
(((FStar_List.rev names)), (binders))
end)))


let termToSmt : term  ->  Prims.string = (fun t -> (

let rec aux = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _173_542 = (FStar_List.nth names i)
in (FStar_All.pipe_right _173_542 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _173_544 = (let _173_543 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _173_543 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _173_544))
end
| Labeled (t, _81_671, _81_673) -> begin
(aux n names t)
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let _81_686 = (name_binders_inner names n sorts)
in (match (_81_686) with
| (names, binders, n) -> begin
(

let binders = (FStar_All.pipe_right binders (FStar_String.concat " "))
in (

let pats_str = (match (pats) with
| (([])::[]) | ([]) -> begin
""
end
| _81_692 -> begin
(let _173_550 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _173_549 = (let _173_548 = (FStar_List.map (fun p -> (let _173_547 = (aux n names p)
in (FStar_Util.format1 "%s" _173_547))) pats)
in (FStar_String.concat " " _173_548))
in (FStar_Util.format1 "\n:pattern (%s)" _173_549)))))
in (FStar_All.pipe_right _173_550 (FStar_String.concat "\n")))
end)
in (match (((pats), (wopt))) with
| ((([])::[], None)) | (([], None)) -> begin
(let _173_551 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _173_551))
end
| _81_704 -> begin
(let _173_553 = (aux n names body)
in (let _173_552 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _173_553 _173_552 pats_str)))
end)))
end))
end))
in (aux 0 [] t)))


let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun _81_6 -> (match (_81_6) with
| None -> begin
""
end
| Some (c) -> begin
(

let _81_718 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::[] -> begin
((hd), (""))
end
| (hd)::_81_713 -> begin
((hd), ("..."))
end)
in (match (_81_718) with
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
(let _173_564 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _81_7 -> (match (_81_7) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _173_564))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (let _173_566 = (caption_to_string c)
in (let _173_565 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _173_566 f (FStar_String.concat " " l) _173_565))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let _81_747 = (name_binders arg_sorts)
in (match (_81_747) with
| (names, binders) -> begin
(

let body = (let _173_567 = (FStar_List.map mkFreeV names)
in (inst _173_567 body))
in (let _173_570 = (caption_to_string c)
in (let _173_569 = (strSort retsort)
in (let _173_568 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _173_570 f (FStar_String.concat " " binders) _173_569 _173_568)))))
end))
end
| Assume (t, c, Some (n)) -> begin
(let _173_572 = (caption_to_string c)
in (let _173_571 = (termToSmt t)
in (FStar_Util.format3 "%s(assert (!\n%s\n:named %s))" _173_572 _173_571 (escape n))))
end
| Assume (t, c, None) -> begin
(let _173_574 = (caption_to_string c)
in (let _173_573 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _173_574 _173_573)))
end
| Eval (t) -> begin
(let _173_575 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _173_575))
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

let basic = (Prims.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort String)\n(declare-fun String_constr_id (String) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n")
in (

let constrs = ((("String_const"), (((("String_const_proj_0"), (Int_sort)))::[]), (String_sort), (0), (true)))::((("Tm_type"), ([]), (Term_sort), (2), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort)))::[]), (Term_sort), (3), (false)))::((("Tm_uvar"), (((("Tm_uvar_fst"), (Int_sort)))::[]), (Term_sort), (5), (true)))::((("Tm_unit"), ([]), (Term_sort), (6), (true)))::((("BoxInt"), (((("BoxInt_proj_0"), (Int_sort)))::[]), (Term_sort), (7), (true)))::((("BoxBool"), (((("BoxBool_proj_0"), (Bool_sort)))::[]), (Term_sort), (8), (true)))::((("BoxString"), (((("BoxString_proj_0"), (String_sort)))::[]), (Term_sort), (9), (true)))::((("BoxRef"), (((("BoxRef_proj_0"), (Ref_sort)))::[]), (Term_sort), (10), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort)))::((("LexCons_1"), (Term_sort)))::[]), (Term_sort), (11), (true)))::[]
in (

let bcons = (let _173_578 = (let _173_577 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _173_577 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _173_578 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat (Prims.strcat basic bcons) lex_ordering))))))


let mk_Range_const : term = (mkApp (("Range_const"), ([])))


let mk_Term_type : term = (mkApp (("Tm_type"), ([])))


let mk_Term_app : term  ->  term  ->  term = (fun t1 t2 -> (mkApp (("Tm_app"), ((t1)::(t2)::[]))))


let mk_Term_uvar : Prims.int  ->  term = (fun i -> (let _173_587 = (let _173_586 = (let _173_585 = (mkInteger' i)
in (_173_585)::[])
in (("Tm_uvar"), (_173_586)))
in (mkApp _173_587)))


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
| _81_795 -> begin
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
| _81_803 -> begin
(Prims.raise FStar_Util.Impos)
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[]))))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (_81_817)::(t1)::(t2)::[]); hash = _81_811; freevars = _81_809})::[]) -> begin
(mkEq ((t1), (t2)))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (_81_836)::(t1)::(t2)::[]); hash = _81_830; freevars = _81_828})::[]) -> begin
(let _173_616 = (mkEq ((t1), (t2)))
in (mkNot _173_616))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); hash = _81_849; freevars = _81_847})::[]) -> begin
(let _173_619 = (let _173_618 = (unboxInt t1)
in (let _173_617 = (unboxInt t2)
in ((_173_618), (_173_617))))
in (mkLTE _173_619))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); hash = _81_866; freevars = _81_864})::[]) -> begin
(let _173_622 = (let _173_621 = (unboxInt t1)
in (let _173_620 = (unboxInt t2)
in ((_173_621), (_173_620))))
in (mkLT _173_622))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); hash = _81_883; freevars = _81_881})::[]) -> begin
(let _173_625 = (let _173_624 = (unboxInt t1)
in (let _173_623 = (unboxInt t2)
in ((_173_624), (_173_623))))
in (mkGTE _173_625))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); hash = _81_900; freevars = _81_898})::[]) -> begin
(let _173_628 = (let _173_627 = (unboxInt t1)
in (let _173_626 = (unboxInt t2)
in ((_173_627), (_173_626))))
in (mkGT _173_628))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); hash = _81_917; freevars = _81_915})::[]) -> begin
(let _173_631 = (let _173_630 = (unboxBool t1)
in (let _173_629 = (unboxBool t2)
in ((_173_630), (_173_629))))
in (mkAnd _173_631))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); hash = _81_934; freevars = _81_932})::[]) -> begin
(let _173_634 = (let _173_633 = (unboxBool t1)
in (let _173_632 = (unboxBool t2)
in ((_173_633), (_173_632))))
in (mkOr _173_634))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t)::[]); hash = _81_951; freevars = _81_949})::[]) -> begin
(let _173_635 = (unboxBool t)
in (mkNot _173_635))
end
| App (Var ("Prims.b2t"), (t)::[]) -> begin
(unboxBool t)
end
| _81_969 -> begin
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


let mk_String_const : Prims.int  ->  term = (fun i -> (let _173_678 = (let _173_677 = (let _173_676 = (mkInteger' i)
in (_173_676)::[])
in (("String_const"), (_173_677)))
in (mkApp _173_678)))


let mk_Precedes : term  ->  term  ->  term = (fun x1 x2 -> (let _173_683 = (mkApp (("Precedes"), ((x1)::(x2)::[])))
in (FStar_All.pipe_right _173_683 mk_Valid)))


let mk_LexCons : term  ->  term  ->  term = (fun x1 x2 -> (mkApp (("LexCons"), ((x1)::(x2)::[]))))


let rec n_fuel : Prims.int  ->  term = (fun n -> if (n = 0) then begin
(mkApp (("ZFuel"), ([])))
end else begin
(let _173_692 = (let _173_691 = (let _173_690 = (n_fuel (n - 1))
in (_173_690)::[])
in (("SFuel"), (_173_691)))
in (mkApp _173_692))
end)


let fuel_2 : term = (n_fuel 2)


let fuel_100 : term = (n_fuel 100)


let mk_and_opt : term Prims.option  ->  term Prims.option  ->  term Prims.option = (fun p1 p2 -> (match (((p1), (p2))) with
| (Some (p1), Some (p2)) -> begin
(let _173_697 = (mkAnd ((p1), (p2)))
in Some (_173_697))
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


let mk_haseq : term  ->  term = (fun t -> (let _173_712 = (mkApp (("Prims.hasEq"), ((t)::[])))
in (mk_Valid _173_712)))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "(Integer %s)" n)
end
| BoundV (n) -> begin
(let _173_717 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "(BoundV %s)" _173_717))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (Prims.fst fv))
end
| App (op, l) -> begin
(let _173_718 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _173_718))
end
| Labeled (t, r1, r2) -> begin
(let _173_719 = (print_smt_term t)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 _173_719))
end
| Quant (qop, l, _81_1052, _81_1054, t) -> begin
(let _173_721 = (print_smt_term_list_list l)
in (let _173_720 = (print_smt_term t)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) _173_721 _173_720)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (let _173_723 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right _173_723 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _173_728 = (let _173_727 = (print_smt_term_list l)
in (Prims.strcat (Prims.strcat s "; [ ") _173_727))
in (Prims.strcat _173_728 " ] "))) "" l))




