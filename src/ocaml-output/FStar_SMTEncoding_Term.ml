
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
| Array (_85_10) -> begin
_85_10
end))


let ___Arrow____0 = (fun projectee -> (match (projectee) with
| Arrow (_85_13) -> begin
_85_13
end))


let ___Sort____0 = (fun projectee -> (match (projectee) with
| Sort (_85_16) -> begin
_85_16
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
(let _182_52 = (strSort s1)
in (let _182_51 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _182_52 _182_51)))
end
| Arrow (s1, s2) -> begin
(let _182_54 = (strSort s1)
in (let _182_53 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _182_54 _182_53)))
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
| Var (_85_36) -> begin
_85_36
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


let is_Mkterm : term  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkterm"))))


let ___Integer____0 = (fun projectee -> (match (projectee) with
| Integer (_85_42) -> begin
_85_42
end))


let ___BoundV____0 = (fun projectee -> (match (projectee) with
| BoundV (_85_45) -> begin
_85_45
end))


let ___FreeV____0 = (fun projectee -> (match (projectee) with
| FreeV (_85_48) -> begin
_85_48
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_85_51) -> begin
_85_51
end))


let ___Quant____0 = (fun projectee -> (match (projectee) with
| Quant (_85_54) -> begin
_85_54
end))


let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_85_57) -> begin
_85_57
end))


let ___LblPos____0 = (fun projectee -> (match (projectee) with
| LblPos (_85_60) -> begin
_85_60
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
| DeclFun (_85_64) -> begin
_85_64
end))


let ___DefineFun____0 = (fun projectee -> (match (projectee) with
| DefineFun (_85_67) -> begin
_85_67
end))


let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_85_70) -> begin
_85_70
end))


let ___Caption____0 = (fun projectee -> (match (projectee) with
| Caption (_85_73) -> begin
_85_73
end))


let ___Eval____0 = (fun projectee -> (match (projectee) with
| Eval (_85_76) -> begin
_85_76
end))


let ___Echo____0 = (fun projectee -> (match (projectee) with
| Echo (_85_79) -> begin
_85_79
end))


let ___SetOption____0 = (fun projectee -> (match (projectee) with
| SetOption (_85_82) -> begin
_85_82
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
| _85_94 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun _85_1 -> (match (_85_1) with
| {tm = FreeV (x); freevars = _85_99; rng = _85_97} -> begin
(fv_sort x)
end
| _85_104 -> begin
(FStar_All.failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun _85_2 -> (match (_85_2) with
| {tm = FreeV (fv); freevars = _85_109; rng = _85_107} -> begin
fv
end
| _85_114 -> begin
(FStar_All.failwith "impossible")
end))


let rec freevars : term  ->  fv Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (_85_125, tms) -> begin
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

let fvs = (let _182_319 = (freevars t)
in (FStar_Util.remove_dups fv_eq _182_319))
in (

let _85_155 = (FStar_ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))


let qop_to_string : qop  ->  Prims.string = (fun _85_3 -> (match (_85_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun _85_4 -> (match (_85_4) with
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


let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun _85_5 -> (match (_85_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _182_326 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _182_326))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _182_330 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _182_330))
end
| FreeV (x) -> begin
(let _182_332 = (let _182_331 = (strSort (Prims.snd x))
in (Prims.strcat ":" _182_331))
in (Prims.strcat (Prims.fst x) _182_332))
end
| App (op, tms) -> begin
(let _182_336 = (let _182_335 = (let _182_334 = (let _182_333 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right _182_333 (FStar_String.concat " ")))
in (Prims.strcat _182_334 ")"))
in (Prims.strcat (op_to_string op) _182_335))
in (Prims.strcat "(" _182_336))
end
| Labeled (t, r1, r2) -> begin
(let _182_339 = (hash_of_term t)
in (let _182_338 = (let _182_337 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 _182_337))
in (Prims.strcat _182_339 _182_338)))
end
| LblPos (t, r) -> begin
(let _182_341 = (let _182_340 = (hash_of_term t)
in (Prims.strcat _182_340 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " _182_341))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _182_358 = (let _182_357 = (let _182_356 = (let _182_355 = (let _182_342 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _182_342 (FStar_String.concat " ")))
in (let _182_354 = (let _182_353 = (let _182_352 = (hash_of_term body)
in (let _182_351 = (let _182_350 = (let _182_349 = (weightToSmt wopt)
in (let _182_348 = (let _182_347 = (let _182_346 = (let _182_345 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _182_344 = (FStar_List.map hash_of_term pats)
in (FStar_All.pipe_right _182_344 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _182_345 (FStar_String.concat "; ")))
in (Prims.strcat _182_346 "))"))
in (Prims.strcat " " _182_347))
in (Prims.strcat _182_349 _182_348)))
in (Prims.strcat " " _182_350))
in (Prims.strcat _182_352 _182_351)))
in (Prims.strcat ")(! " _182_353))
in (Prims.strcat _182_355 _182_354)))
in (Prims.strcat " (" _182_356))
in (Prims.strcat (qop_to_string qop) _182_357))
in (Prims.strcat "(" _182_358))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (let _182_364 = (FStar_Util.mk_ref None)
in {tm = t; freevars = _182_364; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((True), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((False), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (let _182_374 = (let _182_373 = (FStar_Util.ensure_decimal i)
in Integer (_182_373))
in (mk _182_374 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (let _182_379 = (FStar_Util.string_of_int i)
in (mkInteger _182_379 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun _85_231 r -> (match (_85_231) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (True, _85_237) -> begin
(mkFalse r)
end
| App (False, _85_242) -> begin
(mkTrue r)
end
| _85_246 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun _85_249 r -> (match (_85_249) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (True, _85_253), _85_257) -> begin
t2
end
| (_85_260, App (True, _85_263)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (_85_293, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), _85_304) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| _85_307 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun _85_310 r -> (match (_85_310) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
(mkTrue r)
end
| (App (False, _85_330), _85_334) -> begin
t2
end
| (_85_337, App (False, _85_340)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (_85_354, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), _85_365) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| _85_368 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun _85_371 r -> (match (_85_371) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((_, App (True, _))) | ((App (False, _), _)) -> begin
(mkTrue r)
end
| (App (True, _85_391), _85_395) -> begin
t2
end
| (_85_398, App (Imp, (t1')::(t2')::[])) -> begin
(let _182_414 = (let _182_413 = (let _182_412 = (mkAnd ((t1), (t1')) r)
in (_182_412)::(t2')::[])
in ((Imp), (_182_413)))
in (mkApp' _182_414 r))
end
| _85_407 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op _85_411 r -> (match (_85_411) with
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


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun _85_418 r -> (match (_85_418) with
| (t1, t2, t3) -> begin
(match (((t2.tm), (t3.tm))) with
| (App (True, _85_422), App (True, _85_427)) -> begin
(mkTrue r)
end
| (App (True, _85_433), _85_437) -> begin
(let _182_452 = (let _182_451 = (mkNot t1 t1.rng)
in ((_182_451), (t3)))
in (mkImp _182_452 r))
end
| (_85_440, App (True, _85_443)) -> begin
(mkImp ((t1), (t2)) r)
end
| (_85_448, _85_450) -> begin
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


let mkQuant : (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun _85_465 r -> (match (_85_465) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = (Prims.parse_int "0")) then begin
body
end else begin
(match (body.tm) with
| App (True, _85_469) -> begin
body
end
| _85_473 -> begin
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
| _85_488 -> begin
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
(let _182_474 = (let _182_473 = (FStar_List.map (aux ix) tms)
in ((op), (_182_473)))
in (mkApp' _182_474 t.rng))
end
| Labeled (t, r1, r2) -> begin
(let _182_477 = (let _182_476 = (let _182_475 = (aux ix t)
in ((_182_475), (r1), (r2)))
in Labeled (_182_476))
in (mk _182_477 t.rng))
end
| LblPos (t, r) -> begin
(let _182_480 = (let _182_479 = (let _182_478 = (aux ix t)
in ((_182_478), (r)))
in LblPos (_182_479))
in (mk _182_480 t.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n = (FStar_List.length vars)
in (let _182_483 = (let _182_482 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _182_481 = (aux (ix + n) body)
in ((qop), (_182_482), (wopt), (vars), (_182_481))))
in (mkQuant _182_483 t.rng)))
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
(let _182_493 = (let _182_492 = (FStar_List.map (aux shift) tms)
in ((op), (_182_492)))
in (mkApp' _182_493 t.rng))
end
| Labeled (t, r1, r2) -> begin
(let _182_496 = (let _182_495 = (let _182_494 = (aux shift t)
in ((_182_494), (r1), (r2)))
in Labeled (_182_495))
in (mk _182_496 t.rng))
end
| LblPos (t, r) -> begin
(let _182_499 = (let _182_498 = (let _182_497 = (aux shift t)
in ((_182_497), (r)))
in LblPos (_182_498))
in (mk _182_499 t.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift = (shift + m)
in (let _182_502 = (let _182_501 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _182_500 = (aux shift body)
in ((qop), (_182_501), (wopt), (vars), (_182_500))))
in (mkQuant _182_502 t.rng))))
end))
in (aux (Prims.parse_int "0") t)))))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list * term)  ->  FStar_Range.range  ->  term = (fun _85_563 -> (match (_85_563) with
| (qop, pats, wopt, vars, body) -> begin
(let _182_513 = (let _182_512 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _182_511 = (FStar_List.map fv_sort vars)
in (let _182_510 = (abstr vars body)
in ((qop), (_182_512), (wopt), (_182_511), (_182_510)))))
in (mkQuant _182_513))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun _85_568 r -> (match (_85_568) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)) r)
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  FStar_Range.range  ->  term = (fun _85_574 r -> (match (_85_574) with
| (pats, wopt, vars, body) -> begin
(mkQuant' ((Forall), (pats), (wopt), (vars), (body)) r)
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun _85_579 r -> (match (_85_579) with
| (pats, vars, body) -> begin
(mkQuant' ((Forall), (pats), (None), (vars), (body)) r)
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun _85_584 r -> (match (_85_584) with
| (pats, vars, body) -> begin
(mkQuant' ((Exists), (pats), (None), (vars), (body)) r)
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun _85_591 -> (match (_85_591) with
| (nm, vars, s, tm, c) -> begin
(let _182_534 = (let _182_533 = (FStar_List.map fv_sort vars)
in (let _182_532 = (abstr vars tm)
in ((nm), (_182_533), (s), (_182_532), (c))))
in DefineFun (_182_534))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _182_537 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _182_537)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun _85_595 id -> (match (_85_595) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (let _182_550 = (let _182_549 = (let _182_548 = (let _182_547 = (mkInteger' id norng)
in (let _182_546 = (let _182_545 = (let _182_544 = (constr_id_of_sort sort)
in (let _182_543 = (let _182_542 = (mkApp ((tok_name), ([])) norng)
in (_182_542)::[])
in ((_182_544), (_182_543))))
in (mkApp _182_545 norng))
in ((_182_547), (_182_546))))
in (mkEq _182_548 norng))
in ((_182_549), (Some ("fresh token")), (Some (a_name))))
in Assume (_182_550)))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun _85_602 -> (match (_85_602) with
| (name, arg_sorts, sort, id) -> begin
(

let id = (FStar_Util.string_of_int id)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (let _182_557 = (let _182_556 = (let _182_555 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _182_555))
in ((_182_556), (s)))
in (mkFreeV _182_557 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (let _182_559 = (let _182_558 = (constr_id_of_sort sort)
in ((_182_558), ((capp)::[])))
in (mkApp _182_559 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (let _182_565 = (let _182_564 = (let _182_563 = (let _182_562 = (let _182_561 = (let _182_560 = (mkInteger id norng)
in ((_182_560), (cid_app)))
in (mkEq _182_561 norng))
in ((((capp)::[])::[]), (bvar_names), (_182_562)))
in (mkForall _182_563 norng))
in ((_182_564), (Some ("Constructor distinct")), (Some (a_name))))
in Assume (_182_565))))))))
end))


let injective_constructor : (Prims.string * (Prims.string * sort) Prims.list * sort)  ->  decls_t = (fun _85_614 -> (match (_85_614) with
| (name, projectors, sort) -> begin
(

let n_bvars = (FStar_List.length projectors)
in (

let bvar_name = (fun i -> (let _182_570 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _182_570)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (let _182_582 = (let _182_581 = (bvar_name i)
in ((_182_581), (s)))
in (mkFreeV _182_582)))
in (

let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _85_627 -> (match (_85_627) with
| (_85_625, s) -> begin
(bvar i s norng)
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (let _182_595 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _85_634 -> (match (_85_634) with
| (name, s) -> begin
(

let cproj_app = (mkApp ((name), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((name), ((sort)::[]), (s), (Some ("Projector"))))
in (

let a_name = (Prims.strcat "projection_inverse_" name)
in (let _182_594 = (let _182_593 = (let _182_592 = (let _182_591 = (let _182_590 = (let _182_589 = (let _182_588 = (let _182_587 = (bvar i s norng)
in ((cproj_app), (_182_587)))
in (mkEq _182_588 norng))
in ((((capp)::[])::[]), (bvar_names), (_182_589)))
in (mkForall _182_590 norng))
in ((_182_591), (Some ("Projection inverse")), (Some (a_name))))
in Assume (_182_592))
in (_182_593)::[])
in (proj_name)::_182_594))))
end))))
in (FStar_All.pipe_right _182_595 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun _85_643 -> (match (_85_643) with
| (name, projectors, sort, id, injective) -> begin
(

let injective = (injective || true)
in (

let cdecl = (let _182_599 = (let _182_598 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_182_598), (sort), (Some ("Constructor"))))
in DeclFun (_182_599))
in (

let cid = (let _182_601 = (let _182_600 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_182_600), (sort), (id)))
in (fresh_constructor _182_601))
in (

let disc = (

let disc_name = (Prims.strcat "is-" name)
in (

let xfv = (("x"), (sort))
in (

let xx = (mkFreeV xfv norng)
in (

let disc_eq = (let _182_607 = (let _182_606 = (let _182_603 = (let _182_602 = (constr_id_of_sort sort)
in ((_182_602), ((xx)::[])))
in (mkApp _182_603 norng))
in (let _182_605 = (let _182_604 = (FStar_Util.string_of_int id)
in (mkInteger _182_604 norng))
in ((_182_606), (_182_605))))
in (mkEq _182_607 norng))
in (

let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _85_653 -> (match (_85_653) with
| (proj, s) -> begin
(mkApp ((proj), ((xx)::[])) norng)
end))))
in (

let disc_inv_body = (let _182_610 = (let _182_609 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (_182_609)))
in (mkEq _182_610 norng))
in (

let disc_ax = (mkAnd ((disc_eq), (disc_inv_body)) norng)
in (mkDefineFun ((disc_name), ((xfv)::[]), (Bool_sort), (disc_ax), (Some ("Discriminator definition")))))))))))
in (

let projs = if injective then begin
(injective_constructor ((name), (projectors), (sort)))
end else begin
[]
end
in (let _182_617 = (let _182_612 = (let _182_611 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_182_611))
in (_182_612)::(cdecl)::(cid)::projs)
in (let _182_616 = (let _182_615 = (let _182_614 = (let _182_613 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_182_613))
in (_182_614)::[])
in (FStar_List.append ((disc)::[]) _182_615))
in (FStar_List.append _182_617 _182_616))))))))
end))


let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (

let _85_677 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _85_665 s -> (match (_85_665) with
| (names, binders, n) -> begin
(

let prefix = (match (s) with
| Term_sort -> begin
"@x"
end
| _85_669 -> begin
"@u"
end)
in (

let nm = (let _182_626 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _182_626))
in (

let names = (((nm), (s)))::names
in (

let b = (let _182_627 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _182_627))
in ((names), ((b)::binders), ((n + (Prims.parse_int "1"))))))))
end)) ((outer_names), ([]), (start))))
in (match (_85_677) with
| (names, binders, n) -> begin
((names), ((FStar_List.rev binders)), (n))
end)))


let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let _85_682 = (name_binders_inner [] (Prims.parse_int "0") sorts)
in (match (_85_682) with
| (names, binders, n) -> begin
(((FStar_List.rev names)), (binders))
end)))


let termToSmt : term  ->  Prims.string = (fun t -> (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (_85_695); freevars = _85_693; rng = _85_691})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| _85_708 -> begin
tm
end))))))))
in (

let rec aux' = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _182_645 = (FStar_List.nth names i)
in (FStar_All.pipe_right _182_645 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _182_647 = (let _182_646 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _182_646 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _182_647))
end
| Labeled (t, _85_730, _85_732) -> begin
(aux n names t)
end
| LblPos (t, s) -> begin
(let _182_648 = (aux n names t)
in (FStar_Util.format2 "(! %s :lblpos %s)" _182_648 s))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let _85_749 = (name_binders_inner names n sorts)
in (match (_85_749) with
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
| _85_756 -> begin
(let _182_654 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _182_653 = (let _182_652 = (FStar_List.map (fun p -> (let _182_651 = (aux n names p)
in (FStar_Util.format1 "%s" _182_651))) pats)
in (FStar_String.concat " " _182_652))
in (FStar_Util.format1 "\n:pattern (%s)" _182_653)))))
in (FStar_All.pipe_right _182_654 (FStar_String.concat "\n")))
end)
in (match (((pats), (wopt))) with
| ((([])::[], None)) | (([], None)) -> begin
(let _182_655 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _182_655))
end
| _85_768 -> begin
(let _182_657 = (aux n names body)
in (let _182_656 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _182_657 _182_656 pats_str)))
end))))
end))
end))
and aux = (fun n names t -> (

let s = (aux' n names t)
in if (t.rng <> norng) then begin
(let _182_662 = (FStar_Range.string_of_range t.rng)
in (let _182_661 = (FStar_Range.string_of_use_range t.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" _182_662 _182_661 s)))
end else begin
s
end))
in (aux (Prims.parse_int "0") [] t))))


let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun _85_6 -> (match (_85_6) with
| None -> begin
""
end
| Some (c) -> begin
(

let _85_786 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::[] -> begin
((hd), (""))
end
| (hd)::_85_781 -> begin
((hd), ("..."))
end)
in (match (_85_786) with
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
(let _182_673 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _85_7 -> (match (_85_7) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _182_673))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (let _182_675 = (caption_to_string c)
in (let _182_674 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _182_675 f (FStar_String.concat " " l) _182_674))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let _85_815 = (name_binders arg_sorts)
in (match (_85_815) with
| (names, binders) -> begin
(

let body = (let _182_677 = (FStar_List.map (fun x -> (mkFreeV x norng)) names)
in (inst _182_677 body))
in (let _182_680 = (caption_to_string c)
in (let _182_679 = (strSort retsort)
in (let _182_678 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _182_680 f (FStar_String.concat " " binders) _182_679 _182_678)))))
end))
end
| Assume (t, c, Some (n)) -> begin
(let _182_682 = (caption_to_string c)
in (let _182_681 = (termToSmt t)
in (FStar_Util.format3 "%s(assert (!\n%s\n:named %s))" _182_682 _182_681 (escape n))))
end
| Assume (t, c, None) -> begin
(let _182_684 = (caption_to_string c)
in (let _182_683 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _182_684 _182_683)))
end
| Eval (t) -> begin
(let _182_685 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _182_685))
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

let bcons = (let _182_688 = (let _182_687 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _182_687 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _182_688 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mk_Range_const : term = (mkApp (("Range_const"), ([])) norng)


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (let _182_701 = (let _182_700 = (let _182_699 = (mkInteger' i norng)
in (_182_699)::[])
in (("Tm_uvar"), (_182_700)))
in (mkApp _182_701 r)))


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
| _85_867 -> begin
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
| _85_875 -> begin
(Prims.raise FStar_Util.Impos)
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (_85_889)::(t1)::(t2)::[]); freevars = _85_883; rng = _85_881})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (_85_908)::(t1)::(t2)::[]); freevars = _85_902; rng = _85_900})::[]) -> begin
(let _182_730 = (mkEq ((t1), (t2)) norng)
in (mkNot _182_730 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = _85_921; rng = _85_919})::[]) -> begin
(let _182_733 = (let _182_732 = (unboxInt t1)
in (let _182_731 = (unboxInt t2)
in ((_182_732), (_182_731))))
in (mkLTE _182_733 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = _85_938; rng = _85_936})::[]) -> begin
(let _182_736 = (let _182_735 = (unboxInt t1)
in (let _182_734 = (unboxInt t2)
in ((_182_735), (_182_734))))
in (mkLT _182_736 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = _85_955; rng = _85_953})::[]) -> begin
(let _182_739 = (let _182_738 = (unboxInt t1)
in (let _182_737 = (unboxInt t2)
in ((_182_738), (_182_737))))
in (mkGTE _182_739 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = _85_972; rng = _85_970})::[]) -> begin
(let _182_742 = (let _182_741 = (unboxInt t1)
in (let _182_740 = (unboxInt t2)
in ((_182_741), (_182_740))))
in (mkGT _182_742 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = _85_989; rng = _85_987})::[]) -> begin
(let _182_745 = (let _182_744 = (unboxBool t1)
in (let _182_743 = (unboxBool t2)
in ((_182_744), (_182_743))))
in (mkAnd _182_745 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = _85_1006; rng = _85_1004})::[]) -> begin
(let _182_748 = (let _182_747 = (unboxBool t1)
in (let _182_746 = (unboxBool t2)
in ((_182_747), (_182_746))))
in (mkOr _182_748 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t)::[]); freevars = _85_1023; rng = _85_1021})::[]) -> begin
(let _182_749 = (unboxBool t)
in (mkNot _182_749 t.rng))
end
| App (Var ("Prims.b2t"), (t1)::[]) -> begin
(

let _85_1040 = (unboxBool t1)
in {tm = _85_1040.tm; freevars = _85_1040.freevars; rng = t.rng})
end
| _85_1043 -> begin
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


let mk_String_const : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (let _182_804 = (let _182_803 = (let _182_802 = (mkInteger' i norng)
in (_182_802)::[])
in (("FString_const"), (_182_803)))
in (mkApp _182_804 r)))


let mk_Precedes : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (let _182_811 = (mkApp (("Precedes"), ((x1)::(x2)::[])) r)
in (FStar_All.pipe_right _182_811 mk_Valid)))


let mk_LexCons : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (mkApp (("LexCons"), ((x1)::(x2)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n -> if (n = (Prims.parse_int "0")) then begin
(mkApp (("ZFuel"), ([])) norng)
end else begin
(let _182_822 = (let _182_821 = (let _182_820 = (n_fuel (n - (Prims.parse_int "1")))
in (_182_820)::[])
in (("SFuel"), (_182_821)))
in (mkApp _182_822 norng))
end)


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term Prims.option  ->  term Prims.option  ->  FStar_Range.range  ->  term Prims.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (Some (p1), Some (p2)) -> begin
(let _182_829 = (mkAnd ((p1), (p2)) r)
in Some (_182_829))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))


let mk_and_opt_l : term Prims.option Prims.list  ->  FStar_Range.range  ->  term Prims.option = (fun pl r -> (FStar_List.fold_right (fun p out -> (mk_and_opt p out r)) pl None))


let mk_and_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (let _182_842 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l _182_842)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (let _182_849 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l _182_849)))


let mk_haseq : term  ->  term = (fun t -> (let _182_852 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid _182_852)))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "(Integer %s)" n)
end
| BoundV (n) -> begin
(let _182_857 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "(BoundV %s)" _182_857))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (Prims.fst fv))
end
| App (op, l) -> begin
(let _182_858 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _182_858))
end
| Labeled (t, r1, r2) -> begin
(let _182_859 = (print_smt_term t)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 _182_859))
end
| LblPos (t, s) -> begin
(let _182_860 = (print_smt_term t)
in (FStar_Util.format2 "(LblPos %s %s)" s _182_860))
end
| Quant (qop, l, _85_1130, _85_1132, t) -> begin
(let _182_862 = (print_smt_term_list_list l)
in (let _182_861 = (print_smt_term t)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) _182_862 _182_861)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (let _182_864 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right _182_864 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _182_870 = (let _182_869 = (let _182_868 = (print_smt_term_list l)
in (Prims.strcat _182_868 " ] "))
in (Prims.strcat "; [ " _182_869))
in (Prims.strcat s _182_870))) "" l))




