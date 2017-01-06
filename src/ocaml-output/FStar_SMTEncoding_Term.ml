
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
(let _185_52 = (strSort s1)
in (let _185_51 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _185_52 _185_51)))
end
| Arrow (s1, s2) -> begin
(let _185_54 = (strSort s1)
in (let _185_53 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _185_54 _185_53)))
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
| LblPos of (term * Prims.string) 
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


let is_LblPos = (fun _discr_ -> (match (_discr_) with
| LblPos (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mkterm : term  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkterm"))))


let ___Integer____0 = (fun projectee -> (match (projectee) with
| Integer (_86_42) -> begin
_86_42
end))


let ___BoundV____0 = (fun projectee -> (match (projectee) with
| BoundV (_86_45) -> begin
_86_45
end))


let ___FreeV____0 = (fun projectee -> (match (projectee) with
| FreeV (_86_48) -> begin
_86_48
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_86_51) -> begin
_86_51
end))


let ___Quant____0 = (fun projectee -> (match (projectee) with
| Quant (_86_54) -> begin
_86_54
end))


let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_86_57) -> begin
_86_57
end))


let ___LblPos____0 = (fun projectee -> (match (projectee) with
| LblPos (_86_60) -> begin
_86_60
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
| PrintStats


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


let is_PrintStats = (fun _discr_ -> (match (_discr_) with
| PrintStats (_) -> begin
true
end
| _ -> begin
false
end))


let ___DeclFun____0 = (fun projectee -> (match (projectee) with
| DeclFun (_86_64) -> begin
_86_64
end))


let ___DefineFun____0 = (fun projectee -> (match (projectee) with
| DefineFun (_86_67) -> begin
_86_67
end))


let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_86_70) -> begin
_86_70
end))


let ___Caption____0 = (fun projectee -> (match (projectee) with
| Caption (_86_73) -> begin
_86_73
end))


let ___Eval____0 = (fun projectee -> (match (projectee) with
| Eval (_86_76) -> begin
_86_76
end))


let ___Echo____0 = (fun projectee -> (match (projectee) with
| Echo (_86_79) -> begin
_86_79
end))


let ___SetOption____0 = (fun projectee -> (match (projectee) with
| SetOption (_86_82) -> begin
_86_82
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
| _86_94 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun _86_1 -> (match (_86_1) with
| {tm = FreeV (x); freevars = _86_99; rng = _86_97} -> begin
(fv_sort x)
end
| _86_104 -> begin
(failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun _86_2 -> (match (_86_2) with
| {tm = FreeV (fv); freevars = _86_109; rng = _86_107} -> begin
fv
end
| _86_114 -> begin
(failwith "impossible")
end))


let rec freevars : term  ->  fv Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (_86_125, tms) -> begin
(FStar_List.collect freevars tms)
end
| (Quant (_, _, _, _, t)) | (Labeled (t, _, _)) | (LblPos (t, _)) -> begin
(freevars t)
end))


let free_variables : term  ->  fvs = (fun t -> (match ((FStar_ST.read t.freevars)) with
| Some (b) -> begin
b
end
| None -> begin
(

let fvs = (let _185_319 = (freevars t)
in (FStar_Util.remove_dups fv_eq _185_319))
in (

let _86_155 = (FStar_ST.op_Colon_Equals t.freevars (Some (fvs)))
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
(let _185_326 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _185_326))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _185_330 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _185_330))
end
| FreeV (x) -> begin
(let _185_332 = (let _185_331 = (strSort (Prims.snd x))
in (Prims.strcat ":" _185_331))
in (Prims.strcat (Prims.fst x) _185_332))
end
| App (op, tms) -> begin
(let _185_336 = (let _185_335 = (let _185_334 = (let _185_333 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right _185_333 (FStar_String.concat " ")))
in (Prims.strcat _185_334 ")"))
in (Prims.strcat (op_to_string op) _185_335))
in (Prims.strcat "(" _185_336))
end
| Labeled (t, r1, r2) -> begin
(let _185_339 = (hash_of_term t)
in (let _185_338 = (let _185_337 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 _185_337))
in (Prims.strcat _185_339 _185_338)))
end
| LblPos (t, r) -> begin
(let _185_341 = (let _185_340 = (hash_of_term t)
in (Prims.strcat _185_340 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " _185_341))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _185_358 = (let _185_357 = (let _185_356 = (let _185_355 = (let _185_342 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _185_342 (FStar_String.concat " ")))
in (let _185_354 = (let _185_353 = (let _185_352 = (hash_of_term body)
in (let _185_351 = (let _185_350 = (let _185_349 = (weightToSmt wopt)
in (let _185_348 = (let _185_347 = (let _185_346 = (let _185_345 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _185_344 = (FStar_List.map hash_of_term pats)
in (FStar_All.pipe_right _185_344 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _185_345 (FStar_String.concat "; ")))
in (Prims.strcat _185_346 "))"))
in (Prims.strcat " " _185_347))
in (Prims.strcat _185_349 _185_348)))
in (Prims.strcat " " _185_350))
in (Prims.strcat _185_352 _185_351)))
in (Prims.strcat ")(! " _185_353))
in (Prims.strcat _185_355 _185_354)))
in (Prims.strcat " (" _185_356))
in (Prims.strcat (qop_to_string qop) _185_357))
in (Prims.strcat "(" _185_358))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (let _185_364 = (FStar_Util.mk_ref None)
in {tm = t; freevars = _185_364; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((True), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((False), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (let _185_374 = (let _185_373 = (FStar_Util.ensure_decimal i)
in Integer (_185_373))
in (mk _185_374 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (let _185_379 = (FStar_Util.string_of_int i)
in (mkInteger _185_379 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun _86_231 r -> (match (_86_231) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (True, _86_237) -> begin
(mkFalse r)
end
| App (False, _86_242) -> begin
(mkTrue r)
end
| _86_246 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun _86_249 r -> (match (_86_249) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (True, _86_253), _86_257) -> begin
t2
end
| (_86_260, App (True, _86_263)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (_86_293, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), _86_304) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| _86_307 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun _86_310 r -> (match (_86_310) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
(mkTrue r)
end
| (App (False, _86_330), _86_334) -> begin
t2
end
| (_86_337, App (False, _86_340)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (_86_354, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), _86_365) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| _86_368 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun _86_371 r -> (match (_86_371) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((_, App (True, _))) | ((App (False, _), _)) -> begin
(mkTrue r)
end
| (App (True, _86_391), _86_395) -> begin
t2
end
| (_86_398, App (Imp, (t1')::(t2')::[])) -> begin
(let _185_414 = (let _185_413 = (let _185_412 = (mkAnd ((t1), (t1')) r)
in (_185_412)::(t2')::[])
in ((Imp), (_185_413)))
in (mkApp' _185_414 r))
end
| _86_407 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op _86_411 r -> (match (_86_411) with
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


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun _86_418 r -> (match (_86_418) with
| (t1, t2, t3) -> begin
(match (((t2.tm), (t3.tm))) with
| (App (True, _86_422), App (True, _86_427)) -> begin
(mkTrue r)
end
| (App (True, _86_433), _86_437) -> begin
(let _185_452 = (let _185_451 = (mkNot t1 t1.rng)
in ((_185_451), (t3)))
in (mkImp _185_452 r))
end
| (_86_440, App (True, _86_443)) -> begin
(mkImp ((t1), (t2)) r)
end
| (_86_448, _86_450) -> begin
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


let mkQuant : (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun _86_465 r -> (match (_86_465) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = (Prims.parse_int "0")) then begin
body
end else begin
(match (body.tm) with
| App (True, _86_469) -> begin
body
end
| _86_473 -> begin
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
| _86_488 -> begin
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
(let _185_474 = (let _185_473 = (FStar_List.map (aux ix) tms)
in ((op), (_185_473)))
in (mkApp' _185_474 t.rng))
end
| Labeled (t, r1, r2) -> begin
(let _185_477 = (let _185_476 = (let _185_475 = (aux ix t)
in ((_185_475), (r1), (r2)))
in Labeled (_185_476))
in (mk _185_477 t.rng))
end
| LblPos (t, r) -> begin
(let _185_480 = (let _185_479 = (let _185_478 = (aux ix t)
in ((_185_478), (r)))
in LblPos (_185_479))
in (mk _185_480 t.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n = (FStar_List.length vars)
in (let _185_483 = (let _185_482 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _185_481 = (aux (ix + n) body)
in ((qop), (_185_482), (wopt), (vars), (_185_481))))
in (mkQuant _185_483 t.rng)))
end)
end))
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
if (((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n)) then begin
(FStar_List.nth tms (i - shift))
end else begin
t
end
end
| App (op, tms) -> begin
(let _185_493 = (let _185_492 = (FStar_List.map (aux shift) tms)
in ((op), (_185_492)))
in (mkApp' _185_493 t.rng))
end
| Labeled (t, r1, r2) -> begin
(let _185_496 = (let _185_495 = (let _185_494 = (aux shift t)
in ((_185_494), (r1), (r2)))
in Labeled (_185_495))
in (mk _185_496 t.rng))
end
| LblPos (t, r) -> begin
(let _185_499 = (let _185_498 = (let _185_497 = (aux shift t)
in ((_185_497), (r)))
in LblPos (_185_498))
in (mk _185_499 t.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift = (shift + m)
in (let _185_502 = (let _185_501 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _185_500 = (aux shift body)
in ((qop), (_185_501), (wopt), (vars), (_185_500))))
in (mkQuant _185_502 t.rng))))
end))
in (aux (Prims.parse_int "0") t)))))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list * term)  ->  FStar_Range.range  ->  term = (fun _86_563 -> (match (_86_563) with
| (qop, pats, wopt, vars, body) -> begin
(let _185_513 = (let _185_512 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _185_511 = (FStar_List.map fv_sort vars)
in (let _185_510 = (abstr vars body)
in ((qop), (_185_512), (wopt), (_185_511), (_185_510)))))
in (mkQuant _185_513))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun _86_568 r -> (match (_86_568) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)) r)
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  FStar_Range.range  ->  term = (fun _86_574 r -> (match (_86_574) with
| (pats, wopt, vars, body) -> begin
(mkQuant' ((Forall), (pats), (wopt), (vars), (body)) r)
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun _86_579 r -> (match (_86_579) with
| (pats, vars, body) -> begin
(mkQuant' ((Forall), (pats), (None), (vars), (body)) r)
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun _86_584 r -> (match (_86_584) with
| (pats, vars, body) -> begin
(mkQuant' ((Exists), (pats), (None), (vars), (body)) r)
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun _86_591 -> (match (_86_591) with
| (nm, vars, s, tm, c) -> begin
(let _185_534 = (let _185_533 = (FStar_List.map fv_sort vars)
in (let _185_532 = (abstr vars tm)
in ((nm), (_185_533), (s), (_185_532), (c))))
in DefineFun (_185_534))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _185_537 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _185_537)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun _86_595 id -> (match (_86_595) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (let _185_550 = (let _185_549 = (let _185_548 = (let _185_547 = (mkInteger' id norng)
in (let _185_546 = (let _185_545 = (let _185_544 = (constr_id_of_sort sort)
in (let _185_543 = (let _185_542 = (mkApp ((tok_name), ([])) norng)
in (_185_542)::[])
in ((_185_544), (_185_543))))
in (mkApp _185_545 norng))
in ((_185_547), (_185_546))))
in (mkEq _185_548 norng))
in ((_185_549), (Some ("fresh token")), (Some (a_name))))
in Assume (_185_550)))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun _86_602 -> (match (_86_602) with
| (name, arg_sorts, sort, id) -> begin
(

let id = (FStar_Util.string_of_int id)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (let _185_557 = (let _185_556 = (let _185_555 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _185_555))
in ((_185_556), (s)))
in (mkFreeV _185_557 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (let _185_559 = (let _185_558 = (constr_id_of_sort sort)
in ((_185_558), ((capp)::[])))
in (mkApp _185_559 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (let _185_565 = (let _185_564 = (let _185_563 = (let _185_562 = (let _185_561 = (let _185_560 = (mkInteger id norng)
in ((_185_560), (cid_app)))
in (mkEq _185_561 norng))
in ((((capp)::[])::[]), (bvar_names), (_185_562)))
in (mkForall _185_563 norng))
in ((_185_564), (Some ("Constructor distinct")), (Some (a_name))))
in Assume (_185_565))))))))
end))


let injective_constructor : (Prims.string * (Prims.string * sort) Prims.list * sort)  ->  decls_t = (fun _86_614 -> (match (_86_614) with
| (name, projectors, sort) -> begin
(

let n_bvars = (FStar_List.length projectors)
in (

let bvar_name = (fun i -> (let _185_570 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _185_570)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (let _185_582 = (let _185_581 = (bvar_name i)
in ((_185_581), (s)))
in (mkFreeV _185_582)))
in (

let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _86_627 -> (match (_86_627) with
| (_86_625, s) -> begin
(bvar i s norng)
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (let _185_595 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _86_634 -> (match (_86_634) with
| (name, s) -> begin
(

let cproj_app = (mkApp ((name), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((name), ((sort)::[]), (s), (Some ("Projector"))))
in (

let a_name = (Prims.strcat "projection_inverse_" name)
in (let _185_594 = (let _185_593 = (let _185_592 = (let _185_591 = (let _185_590 = (let _185_589 = (let _185_588 = (let _185_587 = (bvar i s norng)
in ((cproj_app), (_185_587)))
in (mkEq _185_588 norng))
in ((((capp)::[])::[]), (bvar_names), (_185_589)))
in (mkForall _185_590 norng))
in ((_185_591), (Some ("Projection inverse")), (Some (a_name))))
in Assume (_185_592))
in (_185_593)::[])
in (proj_name)::_185_594))))
end))))
in (FStar_All.pipe_right _185_595 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun _86_643 -> (match (_86_643) with
| (name, projectors, sort, id, injective) -> begin
(

let injective = (injective || true)
in (

let cdecl = (let _185_599 = (let _185_598 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_185_598), (sort), (Some ("Constructor"))))
in DeclFun (_185_599))
in (

let cid = (let _185_601 = (let _185_600 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_185_600), (sort), (id)))
in (fresh_constructor _185_601))
in (

let disc = (

let disc_name = (Prims.strcat "is-" name)
in (

let xfv = (("x"), (sort))
in (

let xx = (mkFreeV xfv norng)
in (

let disc_eq = (let _185_607 = (let _185_606 = (let _185_603 = (let _185_602 = (constr_id_of_sort sort)
in ((_185_602), ((xx)::[])))
in (mkApp _185_603 norng))
in (let _185_605 = (let _185_604 = (FStar_Util.string_of_int id)
in (mkInteger _185_604 norng))
in ((_185_606), (_185_605))))
in (mkEq _185_607 norng))
in (

let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _86_653 -> (match (_86_653) with
| (proj, s) -> begin
(mkApp ((proj), ((xx)::[])) norng)
end))))
in (

let disc_inv_body = (let _185_610 = (let _185_609 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (_185_609)))
in (mkEq _185_610 norng))
in (

let disc_ax = (mkAnd ((disc_eq), (disc_inv_body)) norng)
in (mkDefineFun ((disc_name), ((xfv)::[]), (Bool_sort), (disc_ax), (Some ("Discriminator definition")))))))))))
in (

let projs = if injective then begin
(injective_constructor ((name), (projectors), (sort)))
end else begin
[]
end
in (let _185_617 = (let _185_612 = (let _185_611 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_185_611))
in (_185_612)::(cdecl)::(cid)::projs)
in (let _185_616 = (let _185_615 = (let _185_614 = (let _185_613 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_185_613))
in (_185_614)::[])
in (FStar_List.append ((disc)::[]) _185_615))
in (FStar_List.append _185_617 _185_616))))))))
end))


let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (

let _86_677 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _86_665 s -> (match (_86_665) with
| (names, binders, n) -> begin
(

let prefix = (match (s) with
| Term_sort -> begin
"@x"
end
| _86_669 -> begin
"@u"
end)
in (

let nm = (let _185_626 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _185_626))
in (

let names = (((nm), (s)))::names
in (

let b = (let _185_627 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _185_627))
in ((names), ((b)::binders), ((n + (Prims.parse_int "1"))))))))
end)) ((outer_names), ([]), (start))))
in (match (_86_677) with
| (names, binders, n) -> begin
((names), ((FStar_List.rev binders)), (n))
end)))


let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let _86_682 = (name_binders_inner [] (Prims.parse_int "0") sorts)
in (match (_86_682) with
| (names, binders, n) -> begin
(((FStar_List.rev names)), (binders))
end)))


let termToSmt : term  ->  Prims.string = (fun t -> (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (_86_695); freevars = _86_693; rng = _86_691})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| _86_708 -> begin
tm
end))))))))
in (

let rec aux' = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _185_645 = (FStar_List.nth names i)
in (FStar_All.pipe_right _185_645 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _185_647 = (let _185_646 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _185_646 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _185_647))
end
| Labeled (t, _86_730, _86_732) -> begin
(aux n names t)
end
| LblPos (t, s) -> begin
(let _185_648 = (aux n names t)
in (FStar_Util.format2 "(! %s :lblpos %s)" _185_648 s))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let _86_749 = (name_binders_inner names n sorts)
in (match (_86_749) with
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
| _86_756 -> begin
(let _185_654 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _185_653 = (let _185_652 = (FStar_List.map (fun p -> (let _185_651 = (aux n names p)
in (FStar_Util.format1 "%s" _185_651))) pats)
in (FStar_String.concat " " _185_652))
in (FStar_Util.format1 "\n:pattern (%s)" _185_653)))))
in (FStar_All.pipe_right _185_654 (FStar_String.concat "\n")))
end)
in (match (((pats), (wopt))) with
| ((([])::[], None)) | (([], None)) -> begin
(let _185_655 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _185_655))
end
| _86_768 -> begin
(let _185_657 = (aux n names body)
in (let _185_656 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _185_657 _185_656 pats_str)))
end))))
end))
end))
and aux = (fun n names t -> (

let s = (aux' n names t)
in if (t.rng <> norng) then begin
(let _185_662 = (FStar_Range.string_of_range t.rng)
in (let _185_661 = (FStar_Range.string_of_use_range t.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" _185_662 _185_661 s)))
end else begin
s
end))
in (aux (Prims.parse_int "0") [] t))))


let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun _86_6 -> (match (_86_6) with
| None -> begin
""
end
| Some (c) -> begin
(

let _86_786 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(failwith "Impossible")
end
| (hd)::[] -> begin
((hd), (""))
end
| (hd)::_86_781 -> begin
((hd), ("..."))
end)
in (match (_86_786) with
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
(let _185_673 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _86_7 -> (match (_86_7) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _185_673))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (let _185_675 = (caption_to_string c)
in (let _185_674 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _185_675 f (FStar_String.concat " " l) _185_674))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let _86_815 = (name_binders arg_sorts)
in (match (_86_815) with
| (names, binders) -> begin
(

let body = (let _185_677 = (FStar_List.map (fun x -> (mkFreeV x norng)) names)
in (inst _185_677 body))
in (let _185_680 = (caption_to_string c)
in (let _185_679 = (strSort retsort)
in (let _185_678 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _185_680 f (FStar_String.concat " " binders) _185_679 _185_678)))))
end))
end
| Assume (t, c, Some (n)) -> begin
(let _185_682 = (caption_to_string c)
in (let _185_681 = (termToSmt t)
in (FStar_Util.format3 "%s(assert (!\n%s\n:named %s))" _185_682 _185_681 (escape n))))
end
| Assume (t, c, None) -> begin
(let _185_684 = (caption_to_string c)
in (let _185_683 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _185_684 _185_683)))
end
| Eval (t) -> begin
(let _185_685 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _185_685))
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

let bcons = (let _185_688 = (let _185_687 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _185_687 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _185_688 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mk_Range_const : term = (mkApp (("Range_const"), ([])) norng)


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (let _185_701 = (let _185_700 = (let _185_699 = (mkInteger' i norng)
in (_185_699)::[])
in (("Tm_uvar"), (_185_700)))
in (mkApp _185_701 r)))


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
| _86_867 -> begin
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
| _86_875 -> begin
(Prims.raise FStar_Util.Impos)
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (_86_889)::(t1)::(t2)::[]); freevars = _86_883; rng = _86_881})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (_86_908)::(t1)::(t2)::[]); freevars = _86_902; rng = _86_900})::[]) -> begin
(let _185_730 = (mkEq ((t1), (t2)) norng)
in (mkNot _185_730 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = _86_921; rng = _86_919})::[]) -> begin
(let _185_733 = (let _185_732 = (unboxInt t1)
in (let _185_731 = (unboxInt t2)
in ((_185_732), (_185_731))))
in (mkLTE _185_733 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = _86_938; rng = _86_936})::[]) -> begin
(let _185_736 = (let _185_735 = (unboxInt t1)
in (let _185_734 = (unboxInt t2)
in ((_185_735), (_185_734))))
in (mkLT _185_736 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = _86_955; rng = _86_953})::[]) -> begin
(let _185_739 = (let _185_738 = (unboxInt t1)
in (let _185_737 = (unboxInt t2)
in ((_185_738), (_185_737))))
in (mkGTE _185_739 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = _86_972; rng = _86_970})::[]) -> begin
(let _185_742 = (let _185_741 = (unboxInt t1)
in (let _185_740 = (unboxInt t2)
in ((_185_741), (_185_740))))
in (mkGT _185_742 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = _86_989; rng = _86_987})::[]) -> begin
(let _185_745 = (let _185_744 = (unboxBool t1)
in (let _185_743 = (unboxBool t2)
in ((_185_744), (_185_743))))
in (mkAnd _185_745 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = _86_1006; rng = _86_1004})::[]) -> begin
(let _185_748 = (let _185_747 = (unboxBool t1)
in (let _185_746 = (unboxBool t2)
in ((_185_747), (_185_746))))
in (mkOr _185_748 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t)::[]); freevars = _86_1023; rng = _86_1021})::[]) -> begin
(let _185_749 = (unboxBool t)
in (mkNot _185_749 t.rng))
end
| App (Var ("Prims.b2t"), (t1)::[]) -> begin
(

let _86_1040 = (unboxBool t1)
in {tm = _86_1040.tm; freevars = _86_1040.freevars; rng = t.rng})
end
| _86_1043 -> begin
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


let mk_String_const : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (let _185_804 = (let _185_803 = (let _185_802 = (mkInteger' i norng)
in (_185_802)::[])
in (("FString_const"), (_185_803)))
in (mkApp _185_804 r)))


let mk_Precedes : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (let _185_811 = (mkApp (("Precedes"), ((x1)::(x2)::[])) r)
in (FStar_All.pipe_right _185_811 mk_Valid)))


let mk_LexCons : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (mkApp (("LexCons"), ((x1)::(x2)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n -> if (n = (Prims.parse_int "0")) then begin
(mkApp (("ZFuel"), ([])) norng)
end else begin
(let _185_822 = (let _185_821 = (let _185_820 = (n_fuel (n - (Prims.parse_int "1")))
in (_185_820)::[])
in (("SFuel"), (_185_821)))
in (mkApp _185_822 norng))
end)


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term Prims.option  ->  term Prims.option  ->  FStar_Range.range  ->  term Prims.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (Some (p1), Some (p2)) -> begin
(let _185_829 = (mkAnd ((p1), (p2)) r)
in Some (_185_829))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))


let mk_and_opt_l : term Prims.option Prims.list  ->  FStar_Range.range  ->  term Prims.option = (fun pl r -> (FStar_List.fold_right (fun p out -> (mk_and_opt p out r)) pl None))


let mk_and_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (let _185_842 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l _185_842)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (let _185_849 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l _185_849)))


let mk_haseq : term  ->  term = (fun t -> (let _185_852 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid _185_852)))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "(Integer %s)" n)
end
| BoundV (n) -> begin
(let _185_857 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "(BoundV %s)" _185_857))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (Prims.fst fv))
end
| App (op, l) -> begin
(let _185_858 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _185_858))
end
| Labeled (t, r1, r2) -> begin
(let _185_859 = (print_smt_term t)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 _185_859))
end
| LblPos (t, s) -> begin
(let _185_860 = (print_smt_term t)
in (FStar_Util.format2 "(LblPos %s %s)" s _185_860))
end
| Quant (qop, l, _86_1130, _86_1132, t) -> begin
(let _185_862 = (print_smt_term_list_list l)
in (let _185_861 = (print_smt_term t)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) _185_862 _185_861)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (let _185_864 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right _185_864 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _185_870 = (let _185_869 = (let _185_868 = (print_smt_term_list l)
in (Prims.strcat _185_868 " ] "))
in (Prims.strcat "; [ " _185_869))
in (Prims.strcat s _185_870))) "" l))




