
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
(let _178_52 = (strSort s1)
in (let _178_51 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _178_52 _178_51)))
end
| Arrow (s1, s2) -> begin
(let _178_54 = (strSort s1)
in (let _178_53 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _178_54 _178_53)))
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
{tm : term'; freevars : fvs FStar_Syntax_Syntax.memo; rng : FStar_Range.range} 
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
| {tm = FreeV (x); freevars = _83_96; rng = _83_94} -> begin
(fv_sort x)
end
| _83_101 -> begin
(FStar_All.failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun _83_2 -> (match (_83_2) with
| {tm = FreeV (fv); freevars = _83_106; rng = _83_104} -> begin
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

let fvs = (let _178_304 = (freevars t)
in (FStar_Util.remove_dups fv_eq _178_304))
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
(let _178_311 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _178_311))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _178_315 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _178_315))
end
| FreeV (x) -> begin
(let _178_317 = (let _178_316 = (strSort (Prims.snd x))
in (Prims.strcat ":" _178_316))
in (Prims.strcat (Prims.fst x) _178_317))
end
| App (op, tms) -> begin
(let _178_321 = (let _178_320 = (let _178_319 = (let _178_318 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right _178_318 (FStar_String.concat " ")))
in (Prims.strcat _178_319 ")"))
in (Prims.strcat (op_to_string op) _178_320))
in (Prims.strcat "(" _178_321))
end
| Labeled (t, r1, r2) -> begin
(let _178_324 = (hash_of_term t)
in (let _178_323 = (let _178_322 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 _178_322))
in (Prims.strcat _178_324 _178_323)))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _178_341 = (let _178_340 = (let _178_339 = (let _178_338 = (let _178_325 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _178_325 (FStar_String.concat " ")))
in (let _178_337 = (let _178_336 = (let _178_335 = (hash_of_term body)
in (let _178_334 = (let _178_333 = (let _178_332 = (weightToSmt wopt)
in (let _178_331 = (let _178_330 = (let _178_329 = (let _178_328 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _178_327 = (FStar_List.map hash_of_term pats)
in (FStar_All.pipe_right _178_327 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _178_328 (FStar_String.concat "; ")))
in (Prims.strcat _178_329 "))"))
in (Prims.strcat " " _178_330))
in (Prims.strcat _178_332 _178_331)))
in (Prims.strcat " " _178_333))
in (Prims.strcat _178_335 _178_334)))
in (Prims.strcat ")(! " _178_336))
in (Prims.strcat _178_338 _178_337)))
in (Prims.strcat " (" _178_339))
in (Prims.strcat (qop_to_string qop) _178_340))
in (Prims.strcat "(" _178_341))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (let _178_347 = (FStar_Util.mk_ref None)
in {tm = t; freevars = _178_347; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((True), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((False), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (let _178_357 = (let _178_356 = (FStar_Util.ensure_decimal i)
in Integer (_178_356))
in (mk _178_357 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (let _178_362 = (FStar_Util.string_of_int i)
in (mkInteger _178_362 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun _83_220 r -> (match (_83_220) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (True, _83_226) -> begin
(mkFalse r)
end
| App (False, _83_231) -> begin
(mkTrue r)
end
| _83_235 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun _83_238 r -> (match (_83_238) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (True, _83_242), _83_246) -> begin
t2
end
| (_83_249, App (True, _83_252)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (_83_282, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), _83_293) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| _83_296 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun _83_299 r -> (match (_83_299) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
(mkTrue r)
end
| (App (False, _83_319), _83_323) -> begin
t2
end
| (_83_326, App (False, _83_329)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (_83_343, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), _83_354) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| _83_357 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun _83_360 r -> (match (_83_360) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((_, App (True, _))) | ((App (False, _), _)) -> begin
(mkTrue r)
end
| (App (True, _83_380), _83_384) -> begin
t2
end
| (_83_387, App (Imp, (t1')::(t2')::[])) -> begin
(let _178_397 = (let _178_396 = (let _178_395 = (mkAnd ((t1), (t1')) r)
in (_178_395)::(t2')::[])
in ((Imp), (_178_396)))
in (mkApp' _178_397 r))
end
| _83_396 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op _83_400 r -> (match (_83_400) with
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


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun _83_407 r -> (match (_83_407) with
| (t1, t2, t3) -> begin
(match (((t2.tm), (t3.tm))) with
| (App (True, _83_411), App (True, _83_416)) -> begin
(mkTrue r)
end
| (App (True, _83_422), _83_426) -> begin
(let _178_435 = (let _178_434 = (mkNot t1 t1.rng)
in ((_178_434), (t3)))
in (mkImp _178_435 r))
end
| (_83_429, App (True, _83_432)) -> begin
(mkImp ((t1), (t2)) r)
end
| (_83_437, _83_439) -> begin
(mkApp' ((ITE), ((t1)::(t2)::(t3)::[])) r)
end)
end))


let mkCases : term Prims.list  ->  FStar_Range.range  ->  term = (fun t r -> (match (t) with
| [] -> begin
(FStar_All.failwith "Impos")
end
| (hd)::tl -> begin
(FStar_List.fold_left (fun out t -> (mkAnd ((out), (t)) r)) hd tl)
end))


let mkQuant : (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun _83_454 r -> (match (_83_454) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = (Prims.parse_int "0")) then begin
body
end else begin
(match (body.tm) with
| App (True, _83_458) -> begin
body
end
| _83_462 -> begin
(mk (Quant (((qop), (pats), (wopt), (vars), (body)))) r)
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
| _83_477 -> begin
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
(mkBoundV (i + ix) t.rng)
end)
end
| App (op, tms) -> begin
(let _178_457 = (let _178_456 = (FStar_List.map (aux ix) tms)
in ((op), (_178_456)))
in (mkApp' _178_457 t.rng))
end
| Labeled (t, r1, r2) -> begin
(let _178_460 = (let _178_459 = (let _178_458 = (aux ix t)
in ((_178_458), (r1), (r2)))
in Labeled (_178_459))
in (mk _178_460 t.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n = (FStar_List.length vars)
in (let _178_463 = (let _178_462 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _178_461 = (aux (ix + n) body)
in ((qop), (_178_462), (wopt), (vars), (_178_461))))
in (mkQuant _178_463 t.rng)))
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
(let _178_473 = (let _178_472 = (FStar_List.map (aux shift) tms)
in ((op), (_178_472)))
in (mkApp' _178_473 t.rng))
end
| Labeled (t, r1, r2) -> begin
(let _178_476 = (let _178_475 = (let _178_474 = (aux shift t)
in ((_178_474), (r1), (r2)))
in Labeled (_178_475))
in (mk _178_476 t.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift = (shift + m)
in (let _178_479 = (let _178_478 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _178_477 = (aux shift body)
in ((qop), (_178_478), (wopt), (vars), (_178_477))))
in (mkQuant _178_479 t.rng))))
end))
in (aux (Prims.parse_int "0") t))))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list * term)  ->  FStar_Range.range  ->  term = (fun _83_543 -> (match (_83_543) with
| (qop, pats, wopt, vars, body) -> begin
(let _178_490 = (let _178_489 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _178_488 = (FStar_List.map fv_sort vars)
in (let _178_487 = (abstr vars body)
in ((qop), (_178_489), (wopt), (_178_488), (_178_487)))))
in (mkQuant _178_490))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun _83_548 r -> (match (_83_548) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)) r)
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  FStar_Range.range  ->  term = (fun _83_554 r -> (match (_83_554) with
| (pats, wopt, vars, body) -> begin
(mkQuant' ((Forall), (pats), (wopt), (vars), (body)) r)
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun _83_559 r -> (match (_83_559) with
| (pats, vars, body) -> begin
(mkQuant' ((Forall), (pats), (None), (vars), (body)) r)
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun _83_564 r -> (match (_83_564) with
| (pats, vars, body) -> begin
(mkQuant' ((Exists), (pats), (None), (vars), (body)) r)
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun _83_571 -> (match (_83_571) with
| (nm, vars, s, tm, c) -> begin
(let _178_511 = (let _178_510 = (FStar_List.map fv_sort vars)
in (let _178_509 = (abstr vars tm)
in ((nm), (_178_510), (s), (_178_509), (c))))
in DefineFun (_178_511))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _178_514 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _178_514)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun _83_575 id -> (match (_83_575) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (let _178_527 = (let _178_526 = (let _178_525 = (let _178_524 = (mkInteger' id norng)
in (let _178_523 = (let _178_522 = (let _178_521 = (constr_id_of_sort sort)
in (let _178_520 = (let _178_519 = (mkApp ((tok_name), ([])) norng)
in (_178_519)::[])
in ((_178_521), (_178_520))))
in (mkApp _178_522 norng))
in ((_178_524), (_178_523))))
in (mkEq _178_525 norng))
in ((_178_526), (Some ("fresh token")), (Some (a_name))))
in Assume (_178_527)))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun _83_582 -> (match (_83_582) with
| (name, arg_sorts, sort, id) -> begin
(

let id = (FStar_Util.string_of_int id)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (let _178_534 = (let _178_533 = (let _178_532 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _178_532))
in ((_178_533), (s)))
in (mkFreeV _178_534 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (let _178_536 = (let _178_535 = (constr_id_of_sort sort)
in ((_178_535), ((capp)::[])))
in (mkApp _178_536 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (let _178_542 = (let _178_541 = (let _178_540 = (let _178_539 = (let _178_538 = (let _178_537 = (mkInteger id norng)
in ((_178_537), (cid_app)))
in (mkEq _178_538 norng))
in ((((capp)::[])::[]), (bvar_names), (_178_539)))
in (mkForall _178_540 norng))
in ((_178_541), (Some ("Constructor distinct")), (Some (a_name))))
in Assume (_178_542))))))))
end))


let injective_constructor : (Prims.string * (Prims.string * sort) Prims.list * sort)  ->  decls_t = (fun _83_594 -> (match (_83_594) with
| (name, projectors, sort) -> begin
(

let n_bvars = (FStar_List.length projectors)
in (

let bvar_name = (fun i -> (let _178_547 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _178_547)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (let _178_559 = (let _178_558 = (bvar_name i)
in ((_178_558), (s)))
in (mkFreeV _178_559)))
in (

let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _83_607 -> (match (_83_607) with
| (_83_605, s) -> begin
(bvar i s norng)
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (let _178_572 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _83_614 -> (match (_83_614) with
| (name, s) -> begin
(

let cproj_app = (mkApp ((name), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((name), ((sort)::[]), (s), (Some ("Projector"))))
in (

let a_name = (Prims.strcat "projection_inverse_" name)
in (let _178_571 = (let _178_570 = (let _178_569 = (let _178_568 = (let _178_567 = (let _178_566 = (let _178_565 = (let _178_564 = (bvar i s norng)
in ((cproj_app), (_178_564)))
in (mkEq _178_565 norng))
in ((((capp)::[])::[]), (bvar_names), (_178_566)))
in (mkForall _178_567 norng))
in ((_178_568), (Some ("Projection inverse")), (Some (a_name))))
in Assume (_178_569))
in (_178_570)::[])
in (proj_name)::_178_571))))
end))))
in (FStar_All.pipe_right _178_572 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun _83_623 -> (match (_83_623) with
| (name, projectors, sort, id, injective) -> begin
(

let injective = (injective || true)
in (

let cdecl = (let _178_576 = (let _178_575 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_178_575), (sort), (Some ("Constructor"))))
in DeclFun (_178_576))
in (

let cid = (let _178_578 = (let _178_577 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_178_577), (sort), (id)))
in (fresh_constructor _178_578))
in (

let disc = (

let disc_name = (Prims.strcat "is-" name)
in (

let xfv = (("x"), (sort))
in (

let xx = (mkFreeV xfv norng)
in (

let disc_eq = (let _178_584 = (let _178_583 = (let _178_580 = (let _178_579 = (constr_id_of_sort sort)
in ((_178_579), ((xx)::[])))
in (mkApp _178_580 norng))
in (let _178_582 = (let _178_581 = (FStar_Util.string_of_int id)
in (mkInteger _178_581 norng))
in ((_178_583), (_178_582))))
in (mkEq _178_584 norng))
in (

let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _83_633 -> (match (_83_633) with
| (proj, s) -> begin
(mkApp ((proj), ((xx)::[])) norng)
end))))
in (

let disc_inv_body = (let _178_587 = (let _178_586 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (_178_586)))
in (mkEq _178_587 norng))
in (

let disc_ax = (mkAnd ((disc_eq), (disc_inv_body)) norng)
in (mkDefineFun ((disc_name), ((xfv)::[]), (Bool_sort), (disc_ax), (Some ("Discriminator definition")))))))))))
in (

let projs = if injective then begin
(injective_constructor ((name), (projectors), (sort)))
end else begin
[]
end
in (let _178_594 = (let _178_589 = (let _178_588 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_178_588))
in (_178_589)::(cdecl)::(cid)::projs)
in (let _178_593 = (let _178_592 = (let _178_591 = (let _178_590 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_178_590))
in (_178_591)::[])
in (FStar_List.append ((disc)::[]) _178_592))
in (FStar_List.append _178_594 _178_593))))))))
end))


let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (

let _83_657 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _83_645 s -> (match (_83_645) with
| (names, binders, n) -> begin
(

let prefix = (match (s) with
| Term_sort -> begin
"@x"
end
| _83_649 -> begin
"@u"
end)
in (

let nm = (let _178_603 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _178_603))
in (

let names = (((nm), (s)))::names
in (

let b = (let _178_604 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _178_604))
in ((names), ((b)::binders), ((n + (Prims.parse_int "1"))))))))
end)) ((outer_names), ([]), (start))))
in (match (_83_657) with
| (names, binders, n) -> begin
((names), ((FStar_List.rev binders)), (n))
end)))


let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let _83_662 = (name_binders_inner [] (Prims.parse_int "0") sorts)
in (match (_83_662) with
| (names, binders, n) -> begin
(((FStar_List.rev names)), (binders))
end)))


let termToSmt : term  ->  Prims.string = (fun t -> (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (_83_675); freevars = _83_673; rng = _83_671})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| _83_688 -> begin
tm
end))))))))
in (

let rec aux' = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _178_622 = (FStar_List.nth names i)
in (FStar_All.pipe_right _178_622 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _178_624 = (let _178_623 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _178_623 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _178_624))
end
| Labeled (t, _83_710, _83_712) -> begin
(aux n names t)
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let _83_725 = (name_binders_inner names n sorts)
in (match (_83_725) with
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
| _83_732 -> begin
(let _178_630 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _178_629 = (let _178_628 = (FStar_List.map (fun p -> (let _178_627 = (aux n names p)
in (FStar_Util.format1 "%s" _178_627))) pats)
in (FStar_String.concat " " _178_628))
in (FStar_Util.format1 "\n:pattern (%s)" _178_629)))))
in (FStar_All.pipe_right _178_630 (FStar_String.concat "\n")))
end)
in (match (((pats), (wopt))) with
| ((([])::[], None)) | (([], None)) -> begin
(let _178_631 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _178_631))
end
| _83_744 -> begin
(let _178_633 = (aux n names body)
in (let _178_632 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _178_633 _178_632 pats_str)))
end))))
end))
end))
and aux = (fun n names t -> (

let s = (aux' n names t)
in if (t.rng <> norng) then begin
(let _178_638 = (FStar_Range.string_of_range t.rng)
in (let _178_637 = (FStar_Range.string_of_use_range t.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" _178_638 _178_637 s)))
end else begin
s
end))
in (aux (Prims.parse_int "0") [] t))))


let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun _83_6 -> (match (_83_6) with
| None -> begin
""
end
| Some (c) -> begin
(

let _83_762 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::[] -> begin
((hd), (""))
end
| (hd)::_83_757 -> begin
((hd), ("..."))
end)
in (match (_83_762) with
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
(let _178_649 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _83_7 -> (match (_83_7) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _178_649))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (let _178_651 = (caption_to_string c)
in (let _178_650 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _178_651 f (FStar_String.concat " " l) _178_650))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let _83_791 = (name_binders arg_sorts)
in (match (_83_791) with
| (names, binders) -> begin
(

let body = (let _178_653 = (FStar_List.map (fun x -> (mkFreeV x norng)) names)
in (inst _178_653 body))
in (let _178_656 = (caption_to_string c)
in (let _178_655 = (strSort retsort)
in (let _178_654 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _178_656 f (FStar_String.concat " " binders) _178_655 _178_654)))))
end))
end
| Assume (t, c, Some (n)) -> begin
(let _178_658 = (caption_to_string c)
in (let _178_657 = (termToSmt t)
in (FStar_Util.format3 "%s(assert (!\n%s\n:named %s))" _178_658 _178_657 (escape n))))
end
| Assume (t, c, None) -> begin
(let _178_660 = (caption_to_string c)
in (let _178_659 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _178_660 _178_659)))
end
| Eval (t) -> begin
(let _178_661 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _178_661))
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

let bcons = (let _178_664 = (let _178_663 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _178_663 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _178_664 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mk_Range_const : term = (mkApp (("Range_const"), ([])) norng)


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (let _178_677 = (let _178_676 = (let _178_675 = (mkInteger' i norng)
in (_178_675)::[])
in (("Tm_uvar"), (_178_676)))
in (mkApp _178_677 r)))


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
| _83_842 -> begin
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
| _83_850 -> begin
(Prims.raise FStar_Util.Impos)
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (_83_864)::(t1)::(t2)::[]); freevars = _83_858; rng = _83_856})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (_83_883)::(t1)::(t2)::[]); freevars = _83_877; rng = _83_875})::[]) -> begin
(let _178_706 = (mkEq ((t1), (t2)) norng)
in (mkNot _178_706 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = _83_896; rng = _83_894})::[]) -> begin
(let _178_709 = (let _178_708 = (unboxInt t1)
in (let _178_707 = (unboxInt t2)
in ((_178_708), (_178_707))))
in (mkLTE _178_709 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = _83_913; rng = _83_911})::[]) -> begin
(let _178_712 = (let _178_711 = (unboxInt t1)
in (let _178_710 = (unboxInt t2)
in ((_178_711), (_178_710))))
in (mkLT _178_712 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = _83_930; rng = _83_928})::[]) -> begin
(let _178_715 = (let _178_714 = (unboxInt t1)
in (let _178_713 = (unboxInt t2)
in ((_178_714), (_178_713))))
in (mkGTE _178_715 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = _83_947; rng = _83_945})::[]) -> begin
(let _178_718 = (let _178_717 = (unboxInt t1)
in (let _178_716 = (unboxInt t2)
in ((_178_717), (_178_716))))
in (mkGT _178_718 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = _83_964; rng = _83_962})::[]) -> begin
(let _178_721 = (let _178_720 = (unboxBool t1)
in (let _178_719 = (unboxBool t2)
in ((_178_720), (_178_719))))
in (mkAnd _178_721 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = _83_981; rng = _83_979})::[]) -> begin
(let _178_724 = (let _178_723 = (unboxBool t1)
in (let _178_722 = (unboxBool t2)
in ((_178_723), (_178_722))))
in (mkOr _178_724 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t)::[]); freevars = _83_998; rng = _83_996})::[]) -> begin
(let _178_725 = (unboxBool t)
in (mkNot _178_725 t.rng))
end
| App (Var ("Prims.b2t"), (t1)::[]) -> begin
(

let _83_1015 = (unboxBool t1)
in {tm = _83_1015.tm; freevars = _83_1015.freevars; rng = t.rng})
end
| _83_1018 -> begin
(mkApp (("Valid"), ((t)::[])) t.rng)
end))


let mk_HasType : term  ->  term  ->  term = (fun v t -> (mkApp (("HasType"), ((v)::(t)::[])) t.rng))


let mk_HasTypeZ : term  ->  term  ->  term = (fun v t -> (mkApp (("HasTypeZ"), ((v)::(t)::[])) t.rng))


let mk_IsTyped : term  ->  term = (fun v -> (mkApp (("IsTyped"), ((v)::[])) norng))


let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v t -> if (FStar_Options.unthrottle_inductives ()) then begin
(mk_HasType v t)
end else begin
(mkApp (("HasTypeFuel"), ((f)::(v)::(t)::[])) t.rng)
end)


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


let mk_String_const : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (let _178_780 = (let _178_779 = (let _178_778 = (mkInteger' i norng)
in (_178_778)::[])
in (("FString_const"), (_178_779)))
in (mkApp _178_780 r)))


let mk_Precedes : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (let _178_787 = (mkApp (("Precedes"), ((x1)::(x2)::[])) r)
in (FStar_All.pipe_right _178_787 mk_Valid)))


let mk_LexCons : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (mkApp (("LexCons"), ((x1)::(x2)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n -> if (n = (Prims.parse_int "0")) then begin
(mkApp (("ZFuel"), ([])) norng)
end else begin
(let _178_798 = (let _178_797 = (let _178_796 = (n_fuel (n - (Prims.parse_int "1")))
in (_178_796)::[])
in (("SFuel"), (_178_797)))
in (mkApp _178_798 norng))
end)


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term Prims.option  ->  term Prims.option  ->  FStar_Range.range  ->  term Prims.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (Some (p1), Some (p2)) -> begin
(let _178_805 = (mkAnd ((p1), (p2)) r)
in Some (_178_805))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))


let mk_and_opt_l : term Prims.option Prims.list  ->  FStar_Range.range  ->  term Prims.option = (fun pl r -> (FStar_List.fold_left (fun out p -> (mk_and_opt p out r)) None pl))


let mk_and_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (match (l) with
| [] -> begin
(mkTrue r)
end
| (hd)::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) hd tl)
end))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (match (l) with
| [] -> begin
(mkFalse r)
end
| (hd)::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkOr ((p1), (p2)) r)) hd tl)
end))


let mk_haseq : term  ->  term = (fun t -> (let _178_826 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid _178_826)))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "(Integer %s)" n)
end
| BoundV (n) -> begin
(let _178_831 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "(BoundV %s)" _178_831))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (Prims.fst fv))
end
| App (op, l) -> begin
(let _178_832 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _178_832))
end
| Labeled (t, r1, r2) -> begin
(let _178_833 = (print_smt_term t)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 _178_833))
end
| Quant (qop, l, _83_1109, _83_1111, t) -> begin
(let _178_835 = (print_smt_term_list_list l)
in (let _178_834 = (print_smt_term t)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) _178_835 _178_834)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (let _178_837 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right _178_837 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _178_843 = (let _178_842 = (let _178_841 = (print_smt_term_list l)
in (Prims.strcat _178_841 " ] "))
in (Prims.strcat "; [ " _178_842))
in (Prims.strcat s _178_843))) "" l))




