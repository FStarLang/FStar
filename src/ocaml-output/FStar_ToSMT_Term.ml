
open Prims
type sort =
| Bool_sort
| Int_sort
| Kind_sort
| Type_sort
| Term_sort
| String_sort
| Ref_sort
| Fuel_sort
| Array of (sort * sort)
| Arrow of (sort * sort)
| Sort of Prims.string

let is_Bool_sort = (fun _discr_ -> (match (_discr_) with
| Bool_sort -> begin
true
end
| _ -> begin
false
end))

let is_Int_sort = (fun _discr_ -> (match (_discr_) with
| Int_sort -> begin
true
end
| _ -> begin
false
end))

let is_Kind_sort = (fun _discr_ -> (match (_discr_) with
| Kind_sort -> begin
true
end
| _ -> begin
false
end))

let is_Type_sort = (fun _discr_ -> (match (_discr_) with
| Type_sort -> begin
true
end
| _ -> begin
false
end))

let is_Term_sort = (fun _discr_ -> (match (_discr_) with
| Term_sort -> begin
true
end
| _ -> begin
false
end))

let is_String_sort = (fun _discr_ -> (match (_discr_) with
| String_sort -> begin
true
end
| _ -> begin
false
end))

let is_Ref_sort = (fun _discr_ -> (match (_discr_) with
| Ref_sort -> begin
true
end
| _ -> begin
false
end))

let is_Fuel_sort = (fun _discr_ -> (match (_discr_) with
| Fuel_sort -> begin
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
| Array (_51_10) -> begin
_51_10
end))

let ___Arrow____0 = (fun projectee -> (match (projectee) with
| Arrow (_51_13) -> begin
_51_13
end))

let ___Sort____0 = (fun projectee -> (match (projectee) with
| Sort (_51_16) -> begin
_51_16
end))

let rec strSort = (fun x -> (match (x) with
| Bool_sort -> begin
"Bool"
end
| Int_sort -> begin
"Int"
end
| Kind_sort -> begin
"Kind"
end
| Type_sort -> begin
"Type"
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
(let _117_54 = (strSort s1)
in (let _117_53 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _117_54 _117_53)))
end
| Arrow (s1, s2) -> begin
(let _117_56 = (strSort s1)
in (let _117_55 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _117_56 _117_55)))
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
| True -> begin
true
end
| _ -> begin
false
end))

let is_False = (fun _discr_ -> (match (_discr_) with
| False -> begin
true
end
| _ -> begin
false
end))

let is_Not = (fun _discr_ -> (match (_discr_) with
| Not -> begin
true
end
| _ -> begin
false
end))

let is_And = (fun _discr_ -> (match (_discr_) with
| And -> begin
true
end
| _ -> begin
false
end))

let is_Or = (fun _discr_ -> (match (_discr_) with
| Or -> begin
true
end
| _ -> begin
false
end))

let is_Imp = (fun _discr_ -> (match (_discr_) with
| Imp -> begin
true
end
| _ -> begin
false
end))

let is_Iff = (fun _discr_ -> (match (_discr_) with
| Iff -> begin
true
end
| _ -> begin
false
end))

let is_Eq = (fun _discr_ -> (match (_discr_) with
| Eq -> begin
true
end
| _ -> begin
false
end))

let is_LT = (fun _discr_ -> (match (_discr_) with
| LT -> begin
true
end
| _ -> begin
false
end))

let is_LTE = (fun _discr_ -> (match (_discr_) with
| LTE -> begin
true
end
| _ -> begin
false
end))

let is_GT = (fun _discr_ -> (match (_discr_) with
| GT -> begin
true
end
| _ -> begin
false
end))

let is_GTE = (fun _discr_ -> (match (_discr_) with
| GTE -> begin
true
end
| _ -> begin
false
end))

let is_Add = (fun _discr_ -> (match (_discr_) with
| Add -> begin
true
end
| _ -> begin
false
end))

let is_Sub = (fun _discr_ -> (match (_discr_) with
| Sub -> begin
true
end
| _ -> begin
false
end))

let is_Div = (fun _discr_ -> (match (_discr_) with
| Div -> begin
true
end
| _ -> begin
false
end))

let is_Mul = (fun _discr_ -> (match (_discr_) with
| Mul -> begin
true
end
| _ -> begin
false
end))

let is_Minus = (fun _discr_ -> (match (_discr_) with
| Minus -> begin
true
end
| _ -> begin
false
end))

let is_Mod = (fun _discr_ -> (match (_discr_) with
| Mod -> begin
true
end
| _ -> begin
false
end))

let is_ITE = (fun _discr_ -> (match (_discr_) with
| ITE -> begin
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
| Var (_51_38) -> begin
_51_38
end))

type qop =
| Forall
| Exists

let is_Forall = (fun _discr_ -> (match (_discr_) with
| Forall -> begin
true
end
| _ -> begin
false
end))

let is_Exists = (fun _discr_ -> (match (_discr_) with
| Exists -> begin
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
 and term =
{tm : term'; hash : Prims.string; freevars : fvs FStar_Absyn_Syntax.memo} 
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

let is_Mkterm = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkterm"))))

let ___Integer____0 = (fun projectee -> (match (projectee) with
| Integer (_51_44) -> begin
_51_44
end))

let ___BoundV____0 = (fun projectee -> (match (projectee) with
| BoundV (_51_47) -> begin
_51_47
end))

let ___FreeV____0 = (fun projectee -> (match (projectee) with
| FreeV (_51_50) -> begin
_51_50
end))

let ___App____0 = (fun projectee -> (match (projectee) with
| App (_51_53) -> begin
_51_53
end))

let ___Quant____0 = (fun projectee -> (match (projectee) with
| Quant (_51_56) -> begin
_51_56
end))

let fv_eq = (fun x y -> ((Prims.fst x) = (Prims.fst y)))

let fv_sort = (fun x -> (Prims.snd x))

let freevar_eq = (fun x y -> (match ((x.tm, y.tm)) with
| (FreeV (x), FreeV (y)) -> begin
(fv_eq x y)
end
| _51_69 -> begin
false
end))

let freevar_sort = (fun _51_1 -> (match (_51_1) with
| {tm = FreeV (x); hash = _51_74; freevars = _51_72} -> begin
(fv_sort x)
end
| _51_79 -> begin
(FStar_All.failwith "impossible")
end))

let fv_of_term = (fun _51_2 -> (match (_51_2) with
| {tm = FreeV (fv); hash = _51_84; freevars = _51_82} -> begin
fv
end
| _51_89 -> begin
(FStar_All.failwith "impossible")
end))

let rec freevars = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (_51_100, tms) -> begin
(FStar_List.collect freevars tms)
end
| Quant (_51_105, _51_107, _51_109, _51_111, t) -> begin
(freevars t)
end))

let free_variables = (fun t -> (match ((FStar_ST.read t.freevars)) with
| Some (b) -> begin
b
end
| None -> begin
(let fvs = (let _117_189 = (freevars t)
in (FStar_Util.remove_dups fv_eq _117_189))
in (let _51_120 = (FStar_ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))

let qop_to_string = (fun _51_3 -> (match (_51_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))

let op_to_string = (fun _51_4 -> (match (_51_4) with
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

let weightToSmt = (fun _51_5 -> (match (_51_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _117_196 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _117_196))
end))

let rec hash_of_term' = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _117_199 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _117_199))
end
| FreeV (x) -> begin
(let _117_200 = (strSort (Prims.snd x))
in (Prims.strcat (Prims.strcat (Prims.fst x) ":") _117_200))
end
| App (op, tms) -> begin
(let _117_204 = (let _117_203 = (let _117_202 = (FStar_List.map (fun t -> t.hash) tms)
in (FStar_All.pipe_right _117_202 (FStar_String.concat " ")))
in (Prims.strcat (Prims.strcat "(" (op_to_string op)) _117_203))
in (Prims.strcat _117_204 ")"))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _117_212 = (let _117_205 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _117_205 (FStar_String.concat " ")))
in (let _117_211 = (weightToSmt wopt)
in (let _117_210 = (let _117_209 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _117_208 = (FStar_List.map (fun p -> p.hash) pats)
in (FStar_All.pipe_right _117_208 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _117_209 (FStar_String.concat "; ")))
in (FStar_Util.format5 "(%s (%s)(! %s %s %s))" (qop_to_string qop) _117_212 body.hash _117_211 _117_210))))
end))

let __all_terms = (let _117_213 = (FStar_Util.smap_create 10000)
in (FStar_ST.alloc _117_213))

let all_terms = (fun _51_172 -> (match (()) with
| () -> begin
(FStar_ST.read __all_terms)
end))

let mk = (fun t -> (let key = (hash_of_term' t)
in (match ((let _117_218 = (all_terms ())
in (FStar_Util.smap_try_find _117_218 key))) with
| Some (tm) -> begin
tm
end
| None -> begin
(let tm = (let _117_219 = (FStar_Util.mk_ref None)
in {tm = t; hash = key; freevars = _117_219})
in (let _51_179 = (let _117_220 = (all_terms ())
in (FStar_Util.smap_add _117_220 key tm))
in tm))
end)))

let mkTrue = (mk (App ((True, []))))

let mkFalse = (mk (App ((False, []))))

let mkInteger = (fun i -> (mk (Integer (i))))

let mkInteger32 = (fun i -> (mkInteger (FStar_Util.string_of_int32 i)))

let mkInteger' = (fun i -> (let _117_227 = (FStar_Util.string_of_int i)
in (mkInteger _117_227)))

let mkBoundV = (fun i -> (mk (BoundV (i))))

let mkFreeV = (fun x -> (mk (FreeV (x))))

let mkApp' = (fun f -> (mk (App (f))))

let mkApp = (fun _51_189 -> (match (_51_189) with
| (s, args) -> begin
(mk (App ((Var (s), args))))
end))

let mkNot = (fun t -> (match (t.tm) with
| App (True, _51_193) -> begin
mkFalse
end
| App (False, _51_198) -> begin
mkTrue
end
| _51_202 -> begin
(mkApp' (Not, (t)::[]))
end))

let mkAnd = (fun _51_205 -> (match (_51_205) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (App (True, _51_208), _51_212) -> begin
t2
end
| (_51_215, App (True, _51_218)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
mkFalse
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' (And, (FStar_List.append ts1 ts2)))
end
| (_51_248, App (And, ts2)) -> begin
(mkApp' (And, (t1)::ts2))
end
| (App (And, ts1), _51_259) -> begin
(mkApp' (And, (FStar_List.append ts1 ((t2)::[]))))
end
| _51_262 -> begin
(mkApp' (And, (t1)::(t2)::[]))
end)
end))

let mkOr = (fun _51_265 -> (match (_51_265) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
mkTrue
end
| (App (False, _51_284), _51_288) -> begin
t2
end
| (_51_291, App (False, _51_294)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' (Or, (FStar_List.append ts1 ts2)))
end
| (_51_308, App (Or, ts2)) -> begin
(mkApp' (Or, (t1)::ts2))
end
| (App (Or, ts1), _51_319) -> begin
(mkApp' (Or, (FStar_List.append ts1 ((t2)::[]))))
end
| _51_322 -> begin
(mkApp' (Or, (t1)::(t2)::[]))
end)
end))

let mkImp = (fun _51_325 -> (match (_51_325) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (_51_327, App (True, _51_330)) -> begin
mkTrue
end
| (App (True, _51_336), _51_340) -> begin
t2
end
| (_51_343, App (Imp, t1'::t2'::[])) -> begin
(let _117_246 = (let _117_245 = (let _117_244 = (mkAnd (t1, t1'))
in (_117_244)::(t2')::[])
in (Imp, _117_245))
in (mkApp' _117_246))
end
| _51_352 -> begin
(mkApp' (Imp, (t1)::(t2)::[]))
end)
end))

let mk_bin_op = (fun op _51_356 -> (match (_51_356) with
| (t1, t2) -> begin
(mkApp' (op, (t1)::(t2)::[]))
end))

let mkMinus = (fun t -> (mkApp' (Minus, (t)::[])))

let mkIff = (mk_bin_op Iff)

let mkEq = (mk_bin_op Eq)

let mkLT = (mk_bin_op LT)

let mkLTE = (mk_bin_op LTE)

let mkGT = (mk_bin_op GT)

let mkGTE = (mk_bin_op GTE)

let mkAdd = (mk_bin_op Add)

let mkSub = (mk_bin_op Sub)

let mkDiv = (mk_bin_op Div)

let mkMul = (mk_bin_op Mul)

let mkMod = (mk_bin_op Mod)

let mkITE = (fun _51_361 -> (match (_51_361) with
| (t1, t2, t3) -> begin
(match ((t2.tm, t3.tm)) with
| (App (True, _51_364), App (True, _51_369)) -> begin
mkTrue
end
| (App (True, _51_375), _51_379) -> begin
(let _117_267 = (let _117_266 = (mkNot t1)
in (_117_266, t3))
in (mkImp _117_267))
end
| (_51_382, App (True, _51_385)) -> begin
(mkImp (t1, t2))
end
| (_51_390, _51_392) -> begin
(mkApp' (ITE, (t1)::(t2)::(t3)::[]))
end)
end))

let mkCases = (fun t -> (match (t) with
| [] -> begin
(FStar_All.failwith "Impos")
end
| hd::tl -> begin
(FStar_List.fold_left (fun out t -> (mkAnd (out, t))) hd tl)
end))

let mkQuant = (fun _51_406 -> (match (_51_406) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = 0) then begin
body
end else begin
(match (body.tm) with
| App (True, _51_409) -> begin
body
end
| _51_413 -> begin
(mk (Quant ((qop, pats, wopt, vars, body))))
end)
end
end))

let abstr = (fun fvs t -> (let nvars = (FStar_List.length fvs)
in (let index_of = (fun fv -> (match ((FStar_Util.try_find_index (fv_eq fv) fvs)) with
| None -> begin
None
end
| Some (i) -> begin
Some ((nvars - (i + 1)))
end))
in (let rec aux = (fun ix t -> (match ((FStar_ST.read t.freevars)) with
| Some ([]) -> begin
t
end
| _51_428 -> begin
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
(let _117_285 = (let _117_284 = (FStar_List.map (aux ix) tms)
in (op, _117_284))
in (mkApp' _117_285))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(let n = (FStar_List.length vars)
in (let _117_288 = (let _117_287 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _117_286 = (aux (ix + n) body)
in (qop, _117_287, wopt, vars, _117_286)))
in (mkQuant _117_288)))
end)
end))
in (aux 0 t)))))

let inst = (fun tms t -> (let n = (FStar_List.length tms)
in (let rec aux = (fun shift t -> (match (t.tm) with
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
(let _117_298 = (let _117_297 = (FStar_List.map (aux shift) tms)
in (op, _117_297))
in (mkApp' _117_298))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(let m = (FStar_List.length vars)
in (let shift = (shift + m)
in (let _117_301 = (let _117_300 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _117_299 = (aux shift body)
in (qop, _117_300, wopt, vars, _117_299)))
in (mkQuant _117_301))))
end))
in (aux 0 t))))

let mkQuant' = (fun _51_484 -> (match (_51_484) with
| (qop, pats, wopt, vars, body) -> begin
(let _117_307 = (let _117_306 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _117_305 = (FStar_List.map fv_sort vars)
in (let _117_304 = (abstr vars body)
in (qop, _117_306, wopt, _117_305, _117_304))))
in (mkQuant _117_307))
end))

let mkForall'' = (fun _51_489 -> (match (_51_489) with
| (pats, wopt, sorts, body) -> begin
(mkQuant (Forall, pats, wopt, sorts, body))
end))

let mkForall' = (fun _51_494 -> (match (_51_494) with
| (pats, wopt, vars, body) -> begin
(mkQuant' (Forall, pats, wopt, vars, body))
end))

let mkForall = (fun _51_498 -> (match (_51_498) with
| (pats, vars, body) -> begin
(mkQuant' (Forall, pats, None, vars, body))
end))

let mkExists = (fun _51_502 -> (match (_51_502) with
| (pats, vars, body) -> begin
(mkQuant' (Exists, pats, None, vars, body))
end))

type caption =
Prims.string Prims.option

type binders =
(Prims.string * sort) Prims.list

type projector =
(Prims.string * sort)

type constructor_t =
(Prims.string * projector Prims.list * sort * Prims.int)

type constructors =
constructor_t Prims.list

type decl =
| DefPrelude
| DeclFun of (Prims.string * sort Prims.list * sort * caption)
| DefineFun of (Prims.string * sort Prims.list * sort * term * caption)
| Assume of (term * caption)
| Caption of Prims.string
| Eval of term
| Echo of Prims.string
| Push
| Pop
| CheckSat

let is_DefPrelude = (fun _discr_ -> (match (_discr_) with
| DefPrelude -> begin
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
| Push -> begin
true
end
| _ -> begin
false
end))

let is_Pop = (fun _discr_ -> (match (_discr_) with
| Pop -> begin
true
end
| _ -> begin
false
end))

let is_CheckSat = (fun _discr_ -> (match (_discr_) with
| CheckSat -> begin
true
end
| _ -> begin
false
end))

let ___DeclFun____0 = (fun projectee -> (match (projectee) with
| DeclFun (_51_505) -> begin
_51_505
end))

let ___DefineFun____0 = (fun projectee -> (match (projectee) with
| DefineFun (_51_508) -> begin
_51_508
end))

let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_51_511) -> begin
_51_511
end))

let ___Caption____0 = (fun projectee -> (match (projectee) with
| Caption (_51_514) -> begin
_51_514
end))

let ___Eval____0 = (fun projectee -> (match (projectee) with
| Eval (_51_517) -> begin
_51_517
end))

let ___Echo____0 = (fun projectee -> (match (projectee) with
| Echo (_51_520) -> begin
_51_520
end))

type decls_t =
decl Prims.list

let mkDefineFun = (fun _51_526 -> (match (_51_526) with
| (nm, vars, s, tm, c) -> begin
(let _117_408 = (let _117_407 = (FStar_List.map fv_sort vars)
in (let _117_406 = (abstr vars tm)
in (nm, _117_407, s, _117_406, c)))
in DefineFun (_117_408))
end))

let constr_id_of_sort = (fun sort -> (let _117_411 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _117_411)))

let fresh_token = (fun _51_530 id -> (match (_51_530) with
| (tok_name, sort) -> begin
(let _117_424 = (let _117_423 = (let _117_422 = (let _117_421 = (mkInteger' id)
in (let _117_420 = (let _117_419 = (let _117_418 = (constr_id_of_sort sort)
in (let _117_417 = (let _117_416 = (mkApp (tok_name, []))
in (_117_416)::[])
in (_117_418, _117_417)))
in (mkApp _117_419))
in (_117_421, _117_420)))
in (mkEq _117_422))
in (_117_423, Some ("fresh token")))
in Assume (_117_424))
end))

let constructor_to_decl = (fun _51_536 -> (match (_51_536) with
| (name, projectors, sort, id) -> begin
(let id = (FStar_Util.string_of_int id)
in (let cdecl = (let _117_428 = (let _117_427 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in (name, _117_427, sort, Some ("Constructor")))
in DeclFun (_117_428))
in (let n_bvars = (FStar_List.length projectors)
in (let bvar_name = (fun i -> (let _117_431 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _117_431)))
in (let bvar_index = (fun i -> (n_bvars - (i + 1)))
in (let bvar = (fun i s -> (let _117_439 = (let _117_438 = (bvar_name i)
in (_117_438, s))
in (mkFreeV _117_439)))
in (let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _51_551 -> (match (_51_551) with
| (_51_549, s) -> begin
(bvar i s)
end))))
in (let bvar_names = (FStar_List.map fv_of_term bvars)
in (let capp = (mkApp (name, bvars))
in (let cid_app = (let _117_443 = (let _117_442 = (constr_id_of_sort sort)
in (_117_442, (capp)::[]))
in (mkApp _117_443))
in (let cid = (let _117_449 = (let _117_448 = (let _117_447 = (let _117_446 = (let _117_445 = (let _117_444 = (mkInteger id)
in (_117_444, cid_app))
in (mkEq _117_445))
in (((capp)::[])::[], bvar_names, _117_446))
in (mkForall _117_447))
in (_117_448, Some ("Constructor distinct")))
in Assume (_117_449))
in (let disc_name = (Prims.strcat "is-" name)
in (let xfv = ("x", sort)
in (let xx = (mkFreeV xfv)
in (let disc_eq = (let _117_454 = (let _117_453 = (let _117_451 = (let _117_450 = (constr_id_of_sort sort)
in (_117_450, (xx)::[]))
in (mkApp _117_451))
in (let _117_452 = (mkInteger id)
in (_117_453, _117_452)))
in (mkEq _117_454))
in (let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _51_563 -> (match (_51_563) with
| (proj, s) -> begin
(mkApp (proj, (xx)::[]))
end))))
in (let disc_inv_body = (let _117_457 = (let _117_456 = (mkApp (name, proj_terms))
in (xx, _117_456))
in (mkEq _117_457))
in (let disc_ax = (mkAnd (disc_eq, disc_inv_body))
in (let disc = (mkDefineFun (disc_name, (xfv)::[], Bool_sort, disc_ax, Some ("Discriminator definition")))
in (let projs = (let _117_468 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _51_571 -> (match (_51_571) with
| (name, s) -> begin
(let cproj_app = (mkApp (name, (capp)::[]))
in (let _117_467 = (let _117_466 = (let _117_465 = (let _117_464 = (let _117_463 = (let _117_462 = (let _117_461 = (let _117_460 = (bvar i s)
in (cproj_app, _117_460))
in (mkEq _117_461))
in (((capp)::[])::[], bvar_names, _117_462))
in (mkForall _117_463))
in (_117_464, Some ("Projection inverse")))
in Assume (_117_465))
in (_117_466)::[])
in (DeclFun ((name, (sort)::[], s, Some ("Projector"))))::_117_467))
end))))
in (FStar_All.pipe_right _117_468 FStar_List.flatten))
in (let _117_475 = (let _117_471 = (let _117_470 = (let _117_469 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_117_469))
in (_117_470)::(cdecl)::(cid)::projs)
in (FStar_List.append _117_471 ((disc)::[])))
in (let _117_474 = (let _117_473 = (let _117_472 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_117_472))
in (_117_473)::[])
in (FStar_List.append _117_475 _117_474)))))))))))))))))))))))
end))

let name_binders_inner = (fun outer_names start sorts -> (let _51_593 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _51_580 s -> (match (_51_580) with
| (names, binders, n) -> begin
(let prefix = (match (s) with
| Type_sort -> begin
"@a"
end
| Term_sort -> begin
"@x"
end
| _51_585 -> begin
"@u"
end)
in (let nm = (let _117_484 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _117_484))
in (let names = ((nm, s))::names
in (let b = (let _117_485 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _117_485))
in (names, (b)::binders, (n + 1))))))
end)) (outer_names, [], start)))
in (match (_51_593) with
| (names, binders, n) -> begin
(names, (FStar_List.rev binders), n)
end)))

let name_binders = (fun sorts -> (let _51_598 = (name_binders_inner [] 0 sorts)
in (match (_51_598) with
| (names, binders, n) -> begin
((FStar_List.rev names), binders)
end)))

let termToSmt = (fun t -> (let rec aux = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _117_496 = (FStar_List.nth names i)
in (FStar_All.pipe_right _117_496 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _117_498 = (let _117_497 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _117_497 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _117_498))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _51_628 = (name_binders_inner names n sorts)
in (match (_51_628) with
| (names, binders, n) -> begin
(let binders = (FStar_All.pipe_right binders (FStar_String.concat " "))
in (let pats_str = (match (pats) with
| ([]::[]) | ([]) -> begin
""
end
| _51_634 -> begin
(let _117_504 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _117_503 = (let _117_502 = (FStar_List.map (fun p -> (let _117_501 = (aux n names p)
in (FStar_Util.format1 "%s" _117_501))) pats)
in (FStar_String.concat " " _117_502))
in (FStar_Util.format1 "\n:pattern (%s)" _117_503)))))
in (FStar_All.pipe_right _117_504 (FStar_String.concat "\n")))
end)
in (match ((pats, wopt)) with
| (([]::[], None)) | (([], None)) -> begin
(let _117_505 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _117_505))
end
| _51_646 -> begin
(let _117_507 = (aux n names body)
in (let _117_506 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _117_507 _117_506 pats_str)))
end)))
end))
end))
in (aux 0 [] t)))

let caption_to_string = (fun _51_6 -> (match (_51_6) with
| None -> begin
""
end
| Some (c) -> begin
(let _51_653 = (FStar_Util.splitlines c)
in (match (_51_653) with
| hd::tl -> begin
(let suffix = (match (tl) with
| [] -> begin
""
end
| _51_656 -> begin
"..."
end)
in (FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd suffix))
end))
end))

let rec declToSmt = (fun z3options decl -> (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(let _117_516 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _51_7 -> (match (_51_7) with
| [] -> begin
""
end
| h::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _117_516))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(let l = (FStar_List.map strSort argsorts)
in (let _117_518 = (caption_to_string c)
in (let _117_517 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _117_518 f (FStar_String.concat " " l) _117_517))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(let _51_684 = (name_binders arg_sorts)
in (match (_51_684) with
| (names, binders) -> begin
(let body = (let _117_519 = (FStar_List.map mkFreeV names)
in (inst _117_519 body))
in (let _117_522 = (caption_to_string c)
in (let _117_521 = (strSort retsort)
in (let _117_520 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _117_522 f (FStar_String.concat " " binders) _117_521 _117_520)))))
end))
end
| Assume (t, c) -> begin
(let _117_524 = (caption_to_string c)
in (let _117_523 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _117_524 _117_523)))
end
| Eval (t) -> begin
(let _117_525 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _117_525))
end
| Echo (s) -> begin
(FStar_Util.format1 "(echo \"%s\")" s)
end
| CheckSat -> begin
"(check-sat)"
end
| Push -> begin
"(push)"
end
| Pop -> begin
"(pop)"
end))
and mkPrelude = (fun z3options -> (let basic = (Prims.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort String)\n(declare-fun String_constr_id (String) Int)\n\n(declare-sort Kind)\n(declare-fun Kind_constr_id (Kind) Int)\n\n(declare-sort Type)\n(declare-fun Type_constr_id (Type) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreKind (Type) Kind)\n(declare-fun PreType (Term) Type)\n(declare-fun Valid (Type) Bool)\n(declare-fun HasKind (Type Kind) Bool)\n(declare-fun HasTypeFuel (Fuel Term Type) Bool)\n(define-fun HasTypeZ ((x Term) (t Type)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Type)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Type))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Type)) (HasTypeZ x t)))\n(declare-fun ApplyEF (Term Fuel) Term)\n(declare-fun ApplyEE (Term Term) Term)\n(declare-fun ApplyET (Term Type) Term)\n(declare-fun ApplyTE (Type Term) Type)\n(declare-fun ApplyTT (Type Type) Type)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsType (Type Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Type)\n(assert (forall ((t Type))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.Precedes ((a Type) (b Type) (t1 Term) (t2 Term)) Type\n(Precedes t1 t2))\n")
in (let constrs = (("String_const", (("String_const_proj_0", Int_sort))::[], String_sort, 0))::(("Kind_type", [], Kind_sort, 0))::(("Kind_arrow", (("Kind_arrow_id", Int_sort))::[], Kind_sort, 1))::(("Kind_uvar", (("Kind_uvar_fst", Int_sort))::[], Kind_sort, 2))::(("Typ_fun", (("Typ_fun_id", Int_sort))::[], Type_sort, 1))::(("Typ_app", (("Typ_app_fst", Type_sort))::(("Typ_app_snd", Type_sort))::[], Type_sort, 2))::(("Typ_dep", (("Typ_dep_fst", Type_sort))::(("Typ_dep_snd", Term_sort))::[], Type_sort, 3))::(("Typ_uvar", (("Typ_uvar_fst", Int_sort))::[], Type_sort, 4))::(("Term_unit", [], Term_sort, 0))::(("BoxInt", (("BoxInt_proj_0", Int_sort))::[], Term_sort, 1))::(("BoxBool", (("BoxBool_proj_0", Bool_sort))::[], Term_sort, 2))::(("BoxString", (("BoxString_proj_0", String_sort))::[], Term_sort, 3))::(("BoxRef", (("BoxRef_proj_0", Ref_sort))::[], Term_sort, 4))::(("Exp_uvar", (("Exp_uvar_fst", Int_sort))::[], Term_sort, 5))::(("LexCons", (("LexCons_0", Term_sort))::(("LexCons_1", Term_sort))::[], Term_sort, 6))::[]
in (let bcons = (let _117_528 = (let _117_527 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _117_527 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _117_528 (FStar_String.concat "\n")))
in (let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat (Prims.strcat basic bcons) lex_ordering))))))

let mk_Kind_type = (mkApp ("Kind_type", []))

let mk_Kind_uvar = (fun i -> (let _117_533 = (let _117_532 = (let _117_531 = (mkInteger' i)
in (_117_531)::[])
in ("Kind_uvar", _117_532))
in (mkApp _117_533)))

let mk_Typ_app = (fun t1 t2 -> (mkApp ("Typ_app", (t1)::(t2)::[])))

let mk_Typ_dep = (fun t1 t2 -> (mkApp ("Typ_dep", (t1)::(t2)::[])))

let mk_Typ_uvar = (fun i -> (let _117_546 = (let _117_545 = (let _117_544 = (mkInteger' i)
in (_117_544)::[])
in ("Typ_uvar", _117_545))
in (mkApp _117_546)))

let mk_Exp_uvar = (fun i -> (let _117_551 = (let _117_550 = (let _117_549 = (mkInteger' i)
in (_117_549)::[])
in ("Exp_uvar", _117_550))
in (mkApp _117_551)))

let mk_Term_unit = (mkApp ("Term_unit", []))

let boxInt = (fun t -> (mkApp ("BoxInt", (t)::[])))

let unboxInt = (fun t -> (mkApp ("BoxInt_proj_0", (t)::[])))

let boxBool = (fun t -> (mkApp ("BoxBool", (t)::[])))

let unboxBool = (fun t -> (mkApp ("BoxBool_proj_0", (t)::[])))

let boxString = (fun t -> (mkApp ("BoxString", (t)::[])))

let unboxString = (fun t -> (mkApp ("BoxString_proj_0", (t)::[])))

let boxRef = (fun t -> (mkApp ("BoxRef", (t)::[])))

let unboxRef = (fun t -> (mkApp ("BoxRef_proj_0", (t)::[])))

let boxTerm = (fun sort t -> (match (sort) with
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
| _51_724 -> begin
(Prims.raise FStar_Util.Impos)
end))

let unboxTerm = (fun sort t -> (match (sort) with
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
| _51_732 -> begin
(Prims.raise FStar_Util.Impos)
end))

let mk_PreKind = (fun t -> (mkApp ("PreKind", (t)::[])))

let mk_PreType = (fun t -> (mkApp ("PreType", (t)::[])))

let mk_Valid = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_Equality"), _51_747::t1::t2::[]); hash = _51_741; freevars = _51_739}::[]) -> begin
(mkEq (t1, t2))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_disEquality"), _51_766::t1::t2::[]); hash = _51_760; freevars = _51_758}::[]) -> begin
(let _117_582 = (mkEq (t1, t2))
in (mkNot _117_582))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_LessThanOrEqual"), t1::t2::[]); hash = _51_779; freevars = _51_777}::[]) -> begin
(let _117_585 = (let _117_584 = (unboxInt t1)
in (let _117_583 = (unboxInt t2)
in (_117_584, _117_583)))
in (mkLTE _117_585))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_LessThan"), t1::t2::[]); hash = _51_796; freevars = _51_794}::[]) -> begin
(let _117_588 = (let _117_587 = (unboxInt t1)
in (let _117_586 = (unboxInt t2)
in (_117_587, _117_586)))
in (mkLT _117_588))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_GreaterThanOrEqual"), t1::t2::[]); hash = _51_813; freevars = _51_811}::[]) -> begin
(let _117_591 = (let _117_590 = (unboxInt t1)
in (let _117_589 = (unboxInt t2)
in (_117_590, _117_589)))
in (mkGTE _117_591))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_GreaterThan"), t1::t2::[]); hash = _51_830; freevars = _51_828}::[]) -> begin
(let _117_594 = (let _117_593 = (unboxInt t1)
in (let _117_592 = (unboxInt t2)
in (_117_593, _117_592)))
in (mkGT _117_594))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_AmpAmp"), t1::t2::[]); hash = _51_847; freevars = _51_845}::[]) -> begin
(let _117_597 = (let _117_596 = (unboxBool t1)
in (let _117_595 = (unboxBool t2)
in (_117_596, _117_595)))
in (mkAnd _117_597))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_BarBar"), t1::t2::[]); hash = _51_864; freevars = _51_862}::[]) -> begin
(let _117_600 = (let _117_599 = (unboxBool t1)
in (let _117_598 = (unboxBool t2)
in (_117_599, _117_598)))
in (mkOr _117_600))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_Negation"), t::[]); hash = _51_881; freevars = _51_879}::[]) -> begin
(let _117_601 = (unboxBool t)
in (mkNot _117_601))
end
| App (Var ("Prims.b2t"), t::[]) -> begin
(unboxBool t)
end
| _51_899 -> begin
(mkApp ("Valid", (t)::[]))
end))

let mk_HasType = (fun v t -> (mkApp ("HasType", (v)::(t)::[])))

let mk_HasTypeZ = (fun v t -> (mkApp ("HasTypeZ", (v)::(t)::[])))

let mk_IsTyped = (fun v -> (mkApp ("IsTyped", (v)::[])))

let mk_HasTypeFuel = (fun f v t -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(mk_HasType v t)
end else begin
(mkApp ("HasTypeFuel", (f)::(v)::(t)::[]))
end)

let mk_HasTypeWithFuel = (fun f v t -> (match (f) with
| None -> begin
(mk_HasType v t)
end
| Some (f) -> begin
(mk_HasTypeFuel f v t)
end))

let mk_Destruct = (fun v -> (mkApp ("Destruct", (v)::[])))

let mk_HasKind = (fun t k -> (mkApp ("HasKind", (t)::(k)::[])))

let mk_Rank = (fun x -> (mkApp ("Rank", (x)::[])))

let mk_tester = (fun n t -> (mkApp ((Prims.strcat "is-" n), (t)::[])))

let mk_ApplyTE = (fun t e -> (mkApp ("ApplyTE", (t)::(e)::[])))

let mk_ApplyTT = (fun t t' -> (mkApp ("ApplyTT", (t)::(t')::[])))

let mk_ApplyET = (fun e t -> (mkApp ("ApplyET", (e)::(t)::[])))

let mk_ApplyEE = (fun e e' -> (mkApp ("ApplyEE", (e)::(e')::[])))

let mk_ApplyEF = (fun e f -> (mkApp ("ApplyEF", (e)::(f)::[])))

let mk_String_const = (fun i -> (let _117_660 = (let _117_659 = (let _117_658 = (mkInteger' i)
in (_117_658)::[])
in ("String_const", _117_659))
in (mkApp _117_660)))

let mk_Precedes = (fun x1 x2 -> (let _117_665 = (mkApp ("Precedes", (x1)::(x2)::[]))
in (FStar_All.pipe_right _117_665 mk_Valid)))

let mk_LexCons = (fun x1 x2 -> (mkApp ("LexCons", (x1)::(x2)::[])))

let rec n_fuel = (fun n -> if (n = 0) then begin
(mkApp ("ZFuel", []))
end else begin
(let _117_674 = (let _117_673 = (let _117_672 = (n_fuel (n - 1))
in (_117_672)::[])
in ("SFuel", _117_673))
in (mkApp _117_674))
end)

let fuel_2 = (n_fuel 2)

let fuel_100 = (n_fuel 100)

let mk_and_opt = (fun p1 p2 -> (match ((p1, p2)) with
| (Some (p1), Some (p2)) -> begin
(let _117_679 = (mkAnd (p1, p2))
in Some (_117_679))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))

let mk_and_opt_l = (fun pl -> (FStar_List.fold_left (fun out p -> (mk_and_opt p out)) None pl))

let mk_and_l = (fun l -> (match (l) with
| [] -> begin
mkTrue
end
| hd::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkAnd (p1, p2))) hd tl)
end))

let mk_or_l = (fun l -> (match (l) with
| [] -> begin
mkFalse
end
| hd::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkOr (p1, p2))) hd tl)
end))

let rec print_smt_term = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "Integer %s" n)
end
| BoundV (n) -> begin
(let _117_696 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "BoundV %s" _117_696))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "FreeV %s" (Prims.fst fv))
end
| App (op, l) -> begin
(let _117_697 = (print_smt_term_list l)
in (FStar_Util.format2 "App %s [ %s ]" (op_to_string op) _117_697))
end
| Quant (qop, l, _51_984, _51_986, t) -> begin
(let _117_699 = (print_smt_term_list_list l)
in (let _117_698 = (print_smt_term t)
in (FStar_Util.format3 "Quant %s %s %s" (qop_to_string qop) _117_699 _117_698)))
end))
and print_smt_term_list = (fun l -> (FStar_List.fold_left (fun s t -> (let _117_703 = (print_smt_term t)
in (Prims.strcat (Prims.strcat s "; ") _117_703))) "" l))
and print_smt_term_list_list = (fun l -> (FStar_List.fold_left (fun s l -> (let _117_708 = (let _117_707 = (print_smt_term_list l)
in (Prims.strcat (Prims.strcat s "; [ ") _117_707))
in (Prims.strcat _117_708 " ] "))) "" l))




