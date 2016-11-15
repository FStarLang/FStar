
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


let ___LblPos____0 = (fun projectee -> (match (projectee) with
| LblPos (_83_60) -> begin
_83_60
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
| DeclFun (_83_64) -> begin
_83_64
end))


let ___DefineFun____0 = (fun projectee -> (match (projectee) with
| DefineFun (_83_67) -> begin
_83_67
end))


let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_83_70) -> begin
_83_70
end))


let ___Caption____0 = (fun projectee -> (match (projectee) with
| Caption (_83_73) -> begin
_83_73
end))


let ___Eval____0 = (fun projectee -> (match (projectee) with
| Eval (_83_76) -> begin
_83_76
end))


let ___Echo____0 = (fun projectee -> (match (projectee) with
| Echo (_83_79) -> begin
_83_79
end))


let ___SetOption____0 = (fun projectee -> (match (projectee) with
| SetOption (_83_82) -> begin
_83_82
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
| _83_94 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun _83_1 -> (match (_83_1) with
| {tm = FreeV (x); freevars = _83_99; rng = _83_97} -> begin
(fv_sort x)
end
| _83_104 -> begin
(FStar_All.failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun _83_2 -> (match (_83_2) with
| {tm = FreeV (fv); freevars = _83_109; rng = _83_107} -> begin
fv
end
| _83_114 -> begin
(FStar_All.failwith "impossible")
end))


let rec freevars : term  ->  fv Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (_83_125, tms) -> begin
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

let fvs = (let _178_318 = (freevars t)
in (FStar_Util.remove_dups fv_eq _178_318))
in (

let _83_155 = (FStar_ST.op_Colon_Equals t.freevars (Some (fvs)))
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
(let _178_325 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _178_325))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _178_329 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _178_329))
end
| FreeV (x) -> begin
(let _178_331 = (let _178_330 = (strSort (Prims.snd x))
in (Prims.strcat ":" _178_330))
in (Prims.strcat (Prims.fst x) _178_331))
end
| App (op, tms) -> begin
(let _178_335 = (let _178_334 = (let _178_333 = (let _178_332 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right _178_332 (FStar_String.concat " ")))
in (Prims.strcat _178_333 ")"))
in (Prims.strcat (op_to_string op) _178_334))
in (Prims.strcat "(" _178_335))
end
| Labeled (t, r1, r2) -> begin
(let _178_338 = (hash_of_term t)
in (let _178_337 = (let _178_336 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 _178_336))
in (Prims.strcat _178_338 _178_337)))
end
| LblPos (t, r) -> begin
(let _178_340 = (let _178_339 = (hash_of_term t)
in (Prims.strcat _178_339 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " _178_340))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _178_357 = (let _178_356 = (let _178_355 = (let _178_354 = (let _178_341 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _178_341 (FStar_String.concat " ")))
in (let _178_353 = (let _178_352 = (let _178_351 = (hash_of_term body)
in (let _178_350 = (let _178_349 = (let _178_348 = (weightToSmt wopt)
in (let _178_347 = (let _178_346 = (let _178_345 = (let _178_344 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _178_343 = (FStar_List.map hash_of_term pats)
in (FStar_All.pipe_right _178_343 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _178_344 (FStar_String.concat "; ")))
in (Prims.strcat _178_345 "))"))
in (Prims.strcat " " _178_346))
in (Prims.strcat _178_348 _178_347)))
in (Prims.strcat " " _178_349))
in (Prims.strcat _178_351 _178_350)))
in (Prims.strcat ")(! " _178_352))
in (Prims.strcat _178_354 _178_353)))
in (Prims.strcat " (" _178_355))
in (Prims.strcat (qop_to_string qop) _178_356))
in (Prims.strcat "(" _178_357))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (let _178_363 = (FStar_Util.mk_ref None)
in {tm = t; freevars = _178_363; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((True), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((False), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (let _178_373 = (let _178_372 = (FStar_Util.ensure_decimal i)
in Integer (_178_372))
in (mk _178_373 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (let _178_378 = (FStar_Util.string_of_int i)
in (mkInteger _178_378 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun _83_231 r -> (match (_83_231) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (True, _83_237) -> begin
(mkFalse r)
end
| App (False, _83_242) -> begin
(mkTrue r)
end
| _83_246 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun _83_249 r -> (match (_83_249) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (True, _83_253), _83_257) -> begin
t2
end
| (_83_260, App (True, _83_263)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (_83_293, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), _83_304) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| _83_307 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun _83_310 r -> (match (_83_310) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
(mkTrue r)
end
| (App (False, _83_330), _83_334) -> begin
t2
end
| (_83_337, App (False, _83_340)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (_83_354, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), _83_365) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| _83_368 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun _83_371 r -> (match (_83_371) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((_, App (True, _))) | ((App (False, _), _)) -> begin
(mkTrue r)
end
| (App (True, _83_391), _83_395) -> begin
t2
end
| (_83_398, App (Imp, (t1')::(t2')::[])) -> begin
(let _178_413 = (let _178_412 = (let _178_411 = (mkAnd ((t1), (t1')) r)
in (_178_411)::(t2')::[])
in ((Imp), (_178_412)))
in (mkApp' _178_413 r))
end
| _83_407 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op _83_411 r -> (match (_83_411) with
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


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun _83_418 r -> (match (_83_418) with
| (t1, t2, t3) -> begin
(match (((t2.tm), (t3.tm))) with
| (App (True, _83_422), App (True, _83_427)) -> begin
(mkTrue r)
end
| (App (True, _83_433), _83_437) -> begin
(let _178_451 = (let _178_450 = (mkNot t1 t1.rng)
in ((_178_450), (t3)))
in (mkImp _178_451 r))
end
| (_83_440, App (True, _83_443)) -> begin
(mkImp ((t1), (t2)) r)
end
| (_83_448, _83_450) -> begin
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


let mkQuant : (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun _83_465 r -> (match (_83_465) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = (Prims.parse_int "0")) then begin
body
end else begin
(match (body.tm) with
| App (True, _83_469) -> begin
body
end
| _83_473 -> begin
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
| _83_488 -> begin
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
(let _178_473 = (let _178_472 = (FStar_List.map (aux ix) tms)
in ((op), (_178_472)))
in (mkApp' _178_473 t.rng))
end
| Labeled (t, r1, r2) -> begin
(let _178_476 = (let _178_475 = (let _178_474 = (aux ix t)
in ((_178_474), (r1), (r2)))
in Labeled (_178_475))
in (mk _178_476 t.rng))
end
| LblPos (t, r) -> begin
(let _178_479 = (let _178_478 = (let _178_477 = (aux ix t)
in ((_178_477), (r)))
in LblPos (_178_478))
in (mk _178_479 t.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n = (FStar_List.length vars)
in (let _178_482 = (let _178_481 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _178_480 = (aux (ix + n) body)
in ((qop), (_178_481), (wopt), (vars), (_178_480))))
in (mkQuant _178_482 t.rng)))
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
(let _178_492 = (let _178_491 = (FStar_List.map (aux shift) tms)
in ((op), (_178_491)))
in (mkApp' _178_492 t.rng))
end
| Labeled (t, r1, r2) -> begin
(let _178_495 = (let _178_494 = (let _178_493 = (aux shift t)
in ((_178_493), (r1), (r2)))
in Labeled (_178_494))
in (mk _178_495 t.rng))
end
| LblPos (t, r) -> begin
(let _178_498 = (let _178_497 = (let _178_496 = (aux shift t)
in ((_178_496), (r)))
in LblPos (_178_497))
in (mk _178_498 t.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift = (shift + m)
in (let _178_501 = (let _178_500 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _178_499 = (aux shift body)
in ((qop), (_178_500), (wopt), (vars), (_178_499))))
in (mkQuant _178_501 t.rng))))
end))
in (aux (Prims.parse_int "0") t)))))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list * term)  ->  FStar_Range.range  ->  term = (fun _83_563 -> (match (_83_563) with
| (qop, pats, wopt, vars, body) -> begin
(let _178_512 = (let _178_511 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _178_510 = (FStar_List.map fv_sort vars)
in (let _178_509 = (abstr vars body)
in ((qop), (_178_511), (wopt), (_178_510), (_178_509)))))
in (mkQuant _178_512))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun _83_568 r -> (match (_83_568) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)) r)
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  FStar_Range.range  ->  term = (fun _83_574 r -> (match (_83_574) with
| (pats, wopt, vars, body) -> begin
(mkQuant' ((Forall), (pats), (wopt), (vars), (body)) r)
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun _83_579 r -> (match (_83_579) with
| (pats, vars, body) -> begin
(mkQuant' ((Forall), (pats), (None), (vars), (body)) r)
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun _83_584 r -> (match (_83_584) with
| (pats, vars, body) -> begin
(mkQuant' ((Exists), (pats), (None), (vars), (body)) r)
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun _83_591 -> (match (_83_591) with
| (nm, vars, s, tm, c) -> begin
(let _178_533 = (let _178_532 = (FStar_List.map fv_sort vars)
in (let _178_531 = (abstr vars tm)
in ((nm), (_178_532), (s), (_178_531), (c))))
in DefineFun (_178_533))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _178_536 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _178_536)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun _83_595 id -> (match (_83_595) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (let _178_549 = (let _178_548 = (let _178_547 = (let _178_546 = (mkInteger' id norng)
in (let _178_545 = (let _178_544 = (let _178_543 = (constr_id_of_sort sort)
in (let _178_542 = (let _178_541 = (mkApp ((tok_name), ([])) norng)
in (_178_541)::[])
in ((_178_543), (_178_542))))
in (mkApp _178_544 norng))
in ((_178_546), (_178_545))))
in (mkEq _178_547 norng))
in ((_178_548), (Some ("fresh token")), (Some (a_name))))
in Assume (_178_549)))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun _83_602 -> (match (_83_602) with
| (name, arg_sorts, sort, id) -> begin
(

let id = (FStar_Util.string_of_int id)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (let _178_556 = (let _178_555 = (let _178_554 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _178_554))
in ((_178_555), (s)))
in (mkFreeV _178_556 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (let _178_558 = (let _178_557 = (constr_id_of_sort sort)
in ((_178_557), ((capp)::[])))
in (mkApp _178_558 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (let _178_564 = (let _178_563 = (let _178_562 = (let _178_561 = (let _178_560 = (let _178_559 = (mkInteger id norng)
in ((_178_559), (cid_app)))
in (mkEq _178_560 norng))
in ((((capp)::[])::[]), (bvar_names), (_178_561)))
in (mkForall _178_562 norng))
in ((_178_563), (Some ("Constructor distinct")), (Some (a_name))))
in Assume (_178_564))))))))
end))


let injective_constructor : (Prims.string * (Prims.string * sort) Prims.list * sort)  ->  decls_t = (fun _83_614 -> (match (_83_614) with
| (name, projectors, sort) -> begin
(

let n_bvars = (FStar_List.length projectors)
in (

let bvar_name = (fun i -> (let _178_569 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _178_569)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (let _178_581 = (let _178_580 = (bvar_name i)
in ((_178_580), (s)))
in (mkFreeV _178_581)))
in (

let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _83_627 -> (match (_83_627) with
| (_83_625, s) -> begin
(bvar i s norng)
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (let _178_594 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _83_634 -> (match (_83_634) with
| (name, s) -> begin
(

let cproj_app = (mkApp ((name), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((name), ((sort)::[]), (s), (Some ("Projector"))))
in (

let a_name = (Prims.strcat "projection_inverse_" name)
in (let _178_593 = (let _178_592 = (let _178_591 = (let _178_590 = (let _178_589 = (let _178_588 = (let _178_587 = (let _178_586 = (bvar i s norng)
in ((cproj_app), (_178_586)))
in (mkEq _178_587 norng))
in ((((capp)::[])::[]), (bvar_names), (_178_588)))
in (mkForall _178_589 norng))
in ((_178_590), (Some ("Projection inverse")), (Some (a_name))))
in Assume (_178_591))
in (_178_592)::[])
in (proj_name)::_178_593))))
end))))
in (FStar_All.pipe_right _178_594 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun _83_643 -> (match (_83_643) with
| (name, projectors, sort, id, injective) -> begin
(

let injective = (injective || true)
in (

let cdecl = (let _178_598 = (let _178_597 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_178_597), (sort), (Some ("Constructor"))))
in DeclFun (_178_598))
in (

let cid = (let _178_600 = (let _178_599 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_178_599), (sort), (id)))
in (fresh_constructor _178_600))
in (

let disc = (

let disc_name = (Prims.strcat "is-" name)
in (

let xfv = (("x"), (sort))
in (

let xx = (mkFreeV xfv norng)
in (

let disc_eq = (let _178_606 = (let _178_605 = (let _178_602 = (let _178_601 = (constr_id_of_sort sort)
in ((_178_601), ((xx)::[])))
in (mkApp _178_602 norng))
in (let _178_604 = (let _178_603 = (FStar_Util.string_of_int id)
in (mkInteger _178_603 norng))
in ((_178_605), (_178_604))))
in (mkEq _178_606 norng))
in (

let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _83_653 -> (match (_83_653) with
| (proj, s) -> begin
(mkApp ((proj), ((xx)::[])) norng)
end))))
in (

let disc_inv_body = (let _178_609 = (let _178_608 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (_178_608)))
in (mkEq _178_609 norng))
in (

let disc_ax = (mkAnd ((disc_eq), (disc_inv_body)) norng)
in (mkDefineFun ((disc_name), ((xfv)::[]), (Bool_sort), (disc_ax), (Some ("Discriminator definition")))))))))))
in (

let projs = if injective then begin
(injective_constructor ((name), (projectors), (sort)))
end else begin
[]
end
in (let _178_616 = (let _178_611 = (let _178_610 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_178_610))
in (_178_611)::(cdecl)::(cid)::projs)
in (let _178_615 = (let _178_614 = (let _178_613 = (let _178_612 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_178_612))
in (_178_613)::[])
in (FStar_List.append ((disc)::[]) _178_614))
in (FStar_List.append _178_616 _178_615))))))))
end))


let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (

let _83_677 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _83_665 s -> (match (_83_665) with
| (names, binders, n) -> begin
(

let prefix = (match (s) with
| Term_sort -> begin
"@x"
end
| _83_669 -> begin
"@u"
end)
in (

let nm = (let _178_625 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _178_625))
in (

let names = (((nm), (s)))::names
in (

let b = (let _178_626 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _178_626))
in ((names), ((b)::binders), ((n + (Prims.parse_int "1"))))))))
end)) ((outer_names), ([]), (start))))
in (match (_83_677) with
| (names, binders, n) -> begin
((names), ((FStar_List.rev binders)), (n))
end)))


let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let _83_682 = (name_binders_inner [] (Prims.parse_int "0") sorts)
in (match (_83_682) with
| (names, binders, n) -> begin
(((FStar_List.rev names)), (binders))
end)))


let termToSmt : term  ->  Prims.string = (fun t -> (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (_83_695); freevars = _83_693; rng = _83_691})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| _83_708 -> begin
tm
end))))))))
in (

let rec aux' = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _178_644 = (FStar_List.nth names i)
in (FStar_All.pipe_right _178_644 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _178_646 = (let _178_645 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _178_645 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _178_646))
end
| Labeled (t, _83_730, _83_732) -> begin
(aux n names t)
end
| LblPos (t, s) -> begin
(let _178_647 = (aux n names t)
in (FStar_Util.format2 "(! %s :lblpos %s)" _178_647 s))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let _83_749 = (name_binders_inner names n sorts)
in (match (_83_749) with
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
| _83_756 -> begin
(let _178_653 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _178_652 = (let _178_651 = (FStar_List.map (fun p -> (let _178_650 = (aux n names p)
in (FStar_Util.format1 "%s" _178_650))) pats)
in (FStar_String.concat " " _178_651))
in (FStar_Util.format1 "\n:pattern (%s)" _178_652)))))
in (FStar_All.pipe_right _178_653 (FStar_String.concat "\n")))
end)
in (match (((pats), (wopt))) with
| ((([])::[], None)) | (([], None)) -> begin
(let _178_654 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _178_654))
end
| _83_768 -> begin
(let _178_656 = (aux n names body)
in (let _178_655 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _178_656 _178_655 pats_str)))
end))))
end))
end))
and aux = (fun n names t -> (

let s = (aux' n names t)
in if (t.rng <> norng) then begin
(let _178_661 = (FStar_Range.string_of_range t.rng)
in (let _178_660 = (FStar_Range.string_of_use_range t.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" _178_661 _178_660 s)))
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

let _83_786 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::[] -> begin
((hd), (""))
end
| (hd)::_83_781 -> begin
((hd), ("..."))
end)
in (match (_83_786) with
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
(let _178_672 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _83_7 -> (match (_83_7) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _178_672))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (let _178_674 = (caption_to_string c)
in (let _178_673 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _178_674 f (FStar_String.concat " " l) _178_673))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let _83_815 = (name_binders arg_sorts)
in (match (_83_815) with
| (names, binders) -> begin
(

let body = (let _178_676 = (FStar_List.map (fun x -> (mkFreeV x norng)) names)
in (inst _178_676 body))
in (let _178_679 = (caption_to_string c)
in (let _178_678 = (strSort retsort)
in (let _178_677 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _178_679 f (FStar_String.concat " " binders) _178_678 _178_677)))))
end))
end
| Assume (t, c, Some (n)) -> begin
(let _178_681 = (caption_to_string c)
in (let _178_680 = (termToSmt t)
in (FStar_Util.format3 "%s(assert (!\n%s\n:named %s))" _178_681 _178_680 (escape n))))
end
| Assume (t, c, None) -> begin
(let _178_683 = (caption_to_string c)
in (let _178_682 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _178_683 _178_682)))
end
| Eval (t) -> begin
(let _178_684 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _178_684))
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

let bcons = (let _178_687 = (let _178_686 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _178_686 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _178_687 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mk_Range_const : term = (mkApp (("Range_const"), ([])) norng)


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (let _178_700 = (let _178_699 = (let _178_698 = (mkInteger' i norng)
in (_178_698)::[])
in (("Tm_uvar"), (_178_699)))
in (mkApp _178_700 r)))


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
| _83_866 -> begin
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
| _83_874 -> begin
(Prims.raise FStar_Util.Impos)
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (_83_888)::(t1)::(t2)::[]); freevars = _83_882; rng = _83_880})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (_83_907)::(t1)::(t2)::[]); freevars = _83_901; rng = _83_899})::[]) -> begin
(let _178_729 = (mkEq ((t1), (t2)) norng)
in (mkNot _178_729 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = _83_920; rng = _83_918})::[]) -> begin
(let _178_732 = (let _178_731 = (unboxInt t1)
in (let _178_730 = (unboxInt t2)
in ((_178_731), (_178_730))))
in (mkLTE _178_732 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = _83_937; rng = _83_935})::[]) -> begin
(let _178_735 = (let _178_734 = (unboxInt t1)
in (let _178_733 = (unboxInt t2)
in ((_178_734), (_178_733))))
in (mkLT _178_735 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = _83_954; rng = _83_952})::[]) -> begin
(let _178_738 = (let _178_737 = (unboxInt t1)
in (let _178_736 = (unboxInt t2)
in ((_178_737), (_178_736))))
in (mkGTE _178_738 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = _83_971; rng = _83_969})::[]) -> begin
(let _178_741 = (let _178_740 = (unboxInt t1)
in (let _178_739 = (unboxInt t2)
in ((_178_740), (_178_739))))
in (mkGT _178_741 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = _83_988; rng = _83_986})::[]) -> begin
(let _178_744 = (let _178_743 = (unboxBool t1)
in (let _178_742 = (unboxBool t2)
in ((_178_743), (_178_742))))
in (mkAnd _178_744 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = _83_1005; rng = _83_1003})::[]) -> begin
(let _178_747 = (let _178_746 = (unboxBool t1)
in (let _178_745 = (unboxBool t2)
in ((_178_746), (_178_745))))
in (mkOr _178_747 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t)::[]); freevars = _83_1022; rng = _83_1020})::[]) -> begin
(let _178_748 = (unboxBool t)
in (mkNot _178_748 t.rng))
end
| App (Var ("Prims.b2t"), (t1)::[]) -> begin
(

let _83_1039 = (unboxBool t1)
in {tm = _83_1039.tm; freevars = _83_1039.freevars; rng = t.rng})
end
| _83_1042 -> begin
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


let mk_String_const : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (let _178_803 = (let _178_802 = (let _178_801 = (mkInteger' i norng)
in (_178_801)::[])
in (("FString_const"), (_178_802)))
in (mkApp _178_803 r)))


let mk_Precedes : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (let _178_810 = (mkApp (("Precedes"), ((x1)::(x2)::[])) r)
in (FStar_All.pipe_right _178_810 mk_Valid)))


let mk_LexCons : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (mkApp (("LexCons"), ((x1)::(x2)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n -> if (n = (Prims.parse_int "0")) then begin
(mkApp (("ZFuel"), ([])) norng)
end else begin
(let _178_821 = (let _178_820 = (let _178_819 = (n_fuel (n - (Prims.parse_int "1")))
in (_178_819)::[])
in (("SFuel"), (_178_820)))
in (mkApp _178_821 norng))
end)


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term Prims.option  ->  term Prims.option  ->  FStar_Range.range  ->  term Prims.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (Some (p1), Some (p2)) -> begin
(let _178_828 = (mkAnd ((p1), (p2)) r)
in Some (_178_828))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))


let mk_and_opt_l : term Prims.option Prims.list  ->  FStar_Range.range  ->  term Prims.option = (fun pl r -> (FStar_List.fold_right (fun p out -> (mk_and_opt p out r)) pl None))


let mk_and_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (let _178_841 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l _178_841)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (let _178_848 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l _178_848)))


let mk_haseq : term  ->  term = (fun t -> (let _178_851 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid _178_851)))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "(Integer %s)" n)
end
| BoundV (n) -> begin
(let _178_856 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "(BoundV %s)" _178_856))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (Prims.fst fv))
end
| App (op, l) -> begin
(let _178_857 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _178_857))
end
| Labeled (t, r1, r2) -> begin
(let _178_858 = (print_smt_term t)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 _178_858))
end
| LblPos (t, s) -> begin
(let _178_859 = (print_smt_term t)
in (FStar_Util.format2 "(LblPos %s %s)" s _178_859))
end
| Quant (qop, l, _83_1129, _83_1131, t) -> begin
(let _178_861 = (print_smt_term_list_list l)
in (let _178_860 = (print_smt_term t)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) _178_861 _178_860)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (let _178_863 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right _178_863 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _178_869 = (let _178_868 = (let _178_867 = (print_smt_term_list l)
in (Prims.strcat _178_867 " ] "))
in (Prims.strcat "; [ " _178_868))
in (Prims.strcat s _178_869))) "" l))




