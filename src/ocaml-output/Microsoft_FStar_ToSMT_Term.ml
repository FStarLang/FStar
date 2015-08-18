
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
| Sort of string

let is_Bool_sort = (fun ( _discr_ ) -> (match (_discr_) with
| Bool_sort -> begin
true
end
| _ -> begin
false
end))

let is_Int_sort = (fun ( _discr_ ) -> (match (_discr_) with
| Int_sort -> begin
true
end
| _ -> begin
false
end))

let is_Kind_sort = (fun ( _discr_ ) -> (match (_discr_) with
| Kind_sort -> begin
true
end
| _ -> begin
false
end))

let is_Type_sort = (fun ( _discr_ ) -> (match (_discr_) with
| Type_sort -> begin
true
end
| _ -> begin
false
end))

let is_Term_sort = (fun ( _discr_ ) -> (match (_discr_) with
| Term_sort -> begin
true
end
| _ -> begin
false
end))

let is_String_sort = (fun ( _discr_ ) -> (match (_discr_) with
| String_sort -> begin
true
end
| _ -> begin
false
end))

let is_Ref_sort = (fun ( _discr_ ) -> (match (_discr_) with
| Ref_sort -> begin
true
end
| _ -> begin
false
end))

let is_Fuel_sort = (fun ( _discr_ ) -> (match (_discr_) with
| Fuel_sort -> begin
true
end
| _ -> begin
false
end))

let is_Array = (fun ( _discr_ ) -> (match (_discr_) with
| Array (_) -> begin
true
end
| _ -> begin
false
end))

let is_Arrow = (fun ( _discr_ ) -> (match (_discr_) with
| Arrow (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sort = (fun ( _discr_ ) -> (match (_discr_) with
| Sort (_) -> begin
true
end
| _ -> begin
false
end))

let ___Array____0 = (fun ( projectee ) -> (match (projectee) with
| Array (_49_10) -> begin
_49_10
end))

let ___Arrow____0 = (fun ( projectee ) -> (match (projectee) with
| Arrow (_49_13) -> begin
_49_13
end))

let ___Sort____0 = (fun ( projectee ) -> (match (projectee) with
| Sort (_49_16) -> begin
_49_16
end))

let rec strSort = (fun ( x ) -> (match (x) with
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
| Array ((s1, s2)) -> begin
(let _120_54 = (strSort s1)
in (let _120_53 = (strSort s2)
in (Support.Microsoft.FStar.Util.format2 "(Array %s %s)" _120_54 _120_53)))
end
| Arrow ((s1, s2)) -> begin
(let _120_56 = (strSort s1)
in (let _120_55 = (strSort s2)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _120_56 _120_55)))
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
| Var of string

let is_True = (fun ( _discr_ ) -> (match (_discr_) with
| True -> begin
true
end
| _ -> begin
false
end))

let is_False = (fun ( _discr_ ) -> (match (_discr_) with
| False -> begin
true
end
| _ -> begin
false
end))

let is_Not = (fun ( _discr_ ) -> (match (_discr_) with
| Not -> begin
true
end
| _ -> begin
false
end))

let is_And = (fun ( _discr_ ) -> (match (_discr_) with
| And -> begin
true
end
| _ -> begin
false
end))

let is_Or = (fun ( _discr_ ) -> (match (_discr_) with
| Or -> begin
true
end
| _ -> begin
false
end))

let is_Imp = (fun ( _discr_ ) -> (match (_discr_) with
| Imp -> begin
true
end
| _ -> begin
false
end))

let is_Iff = (fun ( _discr_ ) -> (match (_discr_) with
| Iff -> begin
true
end
| _ -> begin
false
end))

let is_Eq = (fun ( _discr_ ) -> (match (_discr_) with
| Eq -> begin
true
end
| _ -> begin
false
end))

let is_LT = (fun ( _discr_ ) -> (match (_discr_) with
| LT -> begin
true
end
| _ -> begin
false
end))

let is_LTE = (fun ( _discr_ ) -> (match (_discr_) with
| LTE -> begin
true
end
| _ -> begin
false
end))

let is_GT = (fun ( _discr_ ) -> (match (_discr_) with
| GT -> begin
true
end
| _ -> begin
false
end))

let is_GTE = (fun ( _discr_ ) -> (match (_discr_) with
| GTE -> begin
true
end
| _ -> begin
false
end))

let is_Add = (fun ( _discr_ ) -> (match (_discr_) with
| Add -> begin
true
end
| _ -> begin
false
end))

let is_Sub = (fun ( _discr_ ) -> (match (_discr_) with
| Sub -> begin
true
end
| _ -> begin
false
end))

let is_Div = (fun ( _discr_ ) -> (match (_discr_) with
| Div -> begin
true
end
| _ -> begin
false
end))

let is_Mul = (fun ( _discr_ ) -> (match (_discr_) with
| Mul -> begin
true
end
| _ -> begin
false
end))

let is_Minus = (fun ( _discr_ ) -> (match (_discr_) with
| Minus -> begin
true
end
| _ -> begin
false
end))

let is_Mod = (fun ( _discr_ ) -> (match (_discr_) with
| Mod -> begin
true
end
| _ -> begin
false
end))

let is_ITE = (fun ( _discr_ ) -> (match (_discr_) with
| ITE -> begin
true
end
| _ -> begin
false
end))

let is_Var = (fun ( _discr_ ) -> (match (_discr_) with
| Var (_) -> begin
true
end
| _ -> begin
false
end))

let ___Var____0 = (fun ( projectee ) -> (match (projectee) with
| Var (_49_38) -> begin
_49_38
end))

type qop =
| Forall
| Exists

let is_Forall = (fun ( _discr_ ) -> (match (_discr_) with
| Forall -> begin
true
end
| _ -> begin
false
end))

let is_Exists = (fun ( _discr_ ) -> (match (_discr_) with
| Exists -> begin
true
end
| _ -> begin
false
end))

type term' =
| Integer of string
| BoundV of int
| FreeV of fv
| App of (op * term list)
| Quant of (qop * pat list list * int option * sort list * term) 
 and term =
{tm : term'; hash : string; freevars : fvs Microsoft_FStar_Absyn_Syntax.memo} 
 and pat =
term 
 and fv =
(string * sort) 
 and fvs =
fv list

let is_Integer = (fun ( _discr_ ) -> (match (_discr_) with
| Integer (_) -> begin
true
end
| _ -> begin
false
end))

let is_BoundV = (fun ( _discr_ ) -> (match (_discr_) with
| BoundV (_) -> begin
true
end
| _ -> begin
false
end))

let is_FreeV = (fun ( _discr_ ) -> (match (_discr_) with
| FreeV (_) -> begin
true
end
| _ -> begin
false
end))

let is_App = (fun ( _discr_ ) -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))

let is_Quant = (fun ( _discr_ ) -> (match (_discr_) with
| Quant (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkterm = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkterm"))

let ___Integer____0 = (fun ( projectee ) -> (match (projectee) with
| Integer (_49_44) -> begin
_49_44
end))

let ___BoundV____0 = (fun ( projectee ) -> (match (projectee) with
| BoundV (_49_47) -> begin
_49_47
end))

let ___FreeV____0 = (fun ( projectee ) -> (match (projectee) with
| FreeV (_49_50) -> begin
_49_50
end))

let ___App____0 = (fun ( projectee ) -> (match (projectee) with
| App (_49_53) -> begin
_49_53
end))

let ___Quant____0 = (fun ( projectee ) -> (match (projectee) with
| Quant (_49_56) -> begin
_49_56
end))

let fv_eq = (fun ( x ) ( y ) -> ((Support.Prims.fst x) = (Support.Prims.fst y)))

let fv_sort = (fun ( x ) -> (Support.Prims.snd x))

let freevar_eq = (fun ( x ) ( y ) -> (match ((x.tm, y.tm)) with
| (FreeV (x), FreeV (y)) -> begin
(fv_eq x y)
end
| _49_69 -> begin
false
end))

let freevar_sort = (fun ( _49_1 ) -> (match (_49_1) with
| {tm = FreeV (x); hash = _49_74; freevars = _49_72} -> begin
(fv_sort x)
end
| _49_79 -> begin
(Support.All.failwith "impossible")
end))

let fv_of_term = (fun ( _49_2 ) -> (match (_49_2) with
| {tm = FreeV (fv); hash = _49_84; freevars = _49_82} -> begin
fv
end
| _49_89 -> begin
(Support.All.failwith "impossible")
end))

let rec freevars = (fun ( t ) -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App ((_49_100, tms)) -> begin
(Support.List.collect freevars tms)
end
| Quant ((_49_105, _49_107, _49_109, _49_111, t)) -> begin
(freevars t)
end))

let free_variables = (fun ( t ) -> (match ((Support.ST.read t.freevars)) with
| Some (b) -> begin
b
end
| None -> begin
(let fvs = (let _120_189 = (freevars t)
in (Support.Microsoft.FStar.Util.remove_dups fv_eq _120_189))
in (let _49_120 = (Support.ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))

let qop_to_string = (fun ( _49_3 ) -> (match (_49_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))

let op_to_string = (fun ( _49_4 ) -> (match (_49_4) with
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

let weightToSmt = (fun ( _49_5 ) -> (match (_49_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _120_196 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format1 ":weight %s\n" _120_196))
end))

let rec hash_of_term' = (fun ( t ) -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _120_199 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.String.strcat "@" _120_199))
end
| FreeV (x) -> begin
(let _120_200 = (strSort (Support.Prims.snd x))
in (Support.String.strcat (Support.String.strcat (Support.Prims.fst x) ":") _120_200))
end
| App ((op, tms)) -> begin
(let _120_204 = (let _120_203 = (let _120_202 = (Support.List.map (fun ( t ) -> t.hash) tms)
in (Support.All.pipe_right _120_202 (Support.String.concat " ")))
in (Support.String.strcat (Support.String.strcat "(" (op_to_string op)) _120_203))
in (Support.String.strcat _120_204 ")"))
end
| Quant ((qop, pats, wopt, sorts, body)) -> begin
(let _120_212 = (let _120_205 = (Support.List.map strSort sorts)
in (Support.All.pipe_right _120_205 (Support.String.concat " ")))
in (let _120_211 = (weightToSmt wopt)
in (let _120_210 = (let _120_209 = (Support.All.pipe_right pats (Support.List.map (fun ( pats ) -> (let _120_208 = (Support.List.map (fun ( p ) -> p.hash) pats)
in (Support.All.pipe_right _120_208 (Support.String.concat " "))))))
in (Support.All.pipe_right _120_209 (Support.String.concat "; ")))
in (Support.Microsoft.FStar.Util.format5 "(%s (%s)(! %s %s %s))" (qop_to_string qop) _120_212 body.hash _120_211 _120_210))))
end))

let __all_terms = (let _120_213 = (Support.Microsoft.FStar.Util.smap_create 10000)
in (ref _120_213))

let all_terms = (fun ( _49_172 ) -> (match (()) with
| () -> begin
(Support.ST.read __all_terms)
end))

let mk = (fun ( t ) -> (let key = (hash_of_term' t)
in (match ((let _120_218 = (all_terms ())
in (Support.Microsoft.FStar.Util.smap_try_find _120_218 key))) with
| Some (tm) -> begin
tm
end
| None -> begin
(let tm = (let _120_219 = (Support.Microsoft.FStar.Util.mk_ref None)
in {tm = t; hash = key; freevars = _120_219})
in (let _49_179 = (let _120_220 = (all_terms ())
in (Support.Microsoft.FStar.Util.smap_add _120_220 key tm))
in tm))
end)))

let mkTrue = (mk (App ((True, []))))

let mkFalse = (mk (App ((False, []))))

let mkInteger = (fun ( i ) -> (mk (Integer (i))))

let mkInteger' = (fun ( i ) -> (let _120_225 = (Support.Microsoft.FStar.Util.string_of_int i)
in (mkInteger _120_225)))

let mkBoundV = (fun ( i ) -> (mk (BoundV (i))))

let mkFreeV = (fun ( x ) -> (mk (FreeV (x))))

let mkApp' = (fun ( f ) -> (mk (App (f))))

let mkApp = (fun ( _49_188 ) -> (match (_49_188) with
| (s, args) -> begin
(mk (App ((Var (s), args))))
end))

let mkNot = (fun ( t ) -> (match (t.tm) with
| App ((True, _49_192)) -> begin
mkFalse
end
| App ((False, _49_197)) -> begin
mkTrue
end
| _49_201 -> begin
(mkApp' (Not, (t)::[]))
end))

let mkAnd = (fun ( _49_204 ) -> (match (_49_204) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (App ((True, _49_207)), _49_211) -> begin
t2
end
| (_49_214, App ((True, _49_217))) -> begin
t1
end
| ((App ((False, _)), _)) | ((_, App ((False, _)))) -> begin
mkFalse
end
| (App ((And, ts1)), App ((And, ts2))) -> begin
(mkApp' (And, (Support.List.append ts1 ts2)))
end
| (_49_247, App ((And, ts2))) -> begin
(mkApp' (And, (t1)::ts2))
end
| (App ((And, ts1)), _49_258) -> begin
(mkApp' (And, (Support.List.append ts1 ((t2)::[]))))
end
| _49_261 -> begin
(mkApp' (And, (t1)::(t2)::[]))
end)
end))

let mkOr = (fun ( _49_264 ) -> (match (_49_264) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| ((App ((True, _)), _)) | ((_, App ((True, _)))) -> begin
mkTrue
end
| (App ((False, _49_283)), _49_287) -> begin
t2
end
| (_49_290, App ((False, _49_293))) -> begin
t1
end
| (App ((Or, ts1)), App ((Or, ts2))) -> begin
(mkApp' (Or, (Support.List.append ts1 ts2)))
end
| (_49_307, App ((Or, ts2))) -> begin
(mkApp' (Or, (t1)::ts2))
end
| (App ((Or, ts1)), _49_318) -> begin
(mkApp' (Or, (Support.List.append ts1 ((t2)::[]))))
end
| _49_321 -> begin
(mkApp' (Or, (t1)::(t2)::[]))
end)
end))

let mkImp = (fun ( _49_324 ) -> (match (_49_324) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (_49_326, App ((True, _49_329))) -> begin
mkTrue
end
| (App ((True, _49_335)), _49_339) -> begin
t2
end
| (_49_342, App ((Imp, t1'::t2'::[]))) -> begin
(let _120_244 = (let _120_243 = (let _120_242 = (mkAnd (t1, t1'))
in (_120_242)::(t2')::[])
in (Imp, _120_243))
in (mkApp' _120_244))
end
| _49_351 -> begin
(mkApp' (Imp, (t1)::(t2)::[]))
end)
end))

let mk_bin_op = (fun ( op ) ( _49_355 ) -> (match (_49_355) with
| (t1, t2) -> begin
(mkApp' (op, (t1)::(t2)::[]))
end))

let mkMinus = (fun ( t ) -> (mkApp' (Minus, (t)::[])))

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

let mkITE = (fun ( _49_360 ) -> (match (_49_360) with
| (t1, t2, t3) -> begin
(match ((t2.tm, t3.tm)) with
| (App ((True, _49_363)), App ((True, _49_368))) -> begin
mkTrue
end
| (App ((True, _49_374)), _49_378) -> begin
(let _120_265 = (let _120_264 = (mkNot t1)
in (_120_264, t3))
in (mkImp _120_265))
end
| (_49_381, App ((True, _49_384))) -> begin
(mkImp (t1, t2))
end
| (_49_389, _49_391) -> begin
(mkApp' (ITE, (t1)::(t2)::(t3)::[]))
end)
end))

let mkCases = (fun ( t ) -> (match (t) with
| [] -> begin
(Support.All.failwith "Impos")
end
| hd::tl -> begin
(Support.List.fold_left (fun ( out ) ( t ) -> (mkAnd (out, t))) hd tl)
end))

let mkQuant = (fun ( _49_405 ) -> (match (_49_405) with
| (qop, pats, wopt, vars, body) -> begin
(match (((Support.List.length vars) = 0)) with
| true -> begin
body
end
| false -> begin
(match (body.tm) with
| App ((True, _49_408)) -> begin
body
end
| _49_412 -> begin
(mk (Quant ((qop, pats, wopt, vars, body))))
end)
end)
end))

let abstr = (fun ( fvs ) ( t ) -> (let nvars = (Support.List.length fvs)
in (let index_of = (fun ( fv ) -> (match ((Support.Microsoft.FStar.Util.try_find_index (fv_eq fv) fvs)) with
| None -> begin
None
end
| Some (i) -> begin
Some ((nvars - (i + 1)))
end))
in (let rec aux = (fun ( ix ) ( t ) -> (match ((Support.ST.read t.freevars)) with
| Some ([]) -> begin
t
end
| _49_427 -> begin
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
| App ((op, tms)) -> begin
(let _120_283 = (let _120_282 = (Support.List.map (aux ix) tms)
in (op, _120_282))
in (mkApp' _120_283))
end
| Quant ((qop, pats, wopt, vars, body)) -> begin
(let n = (Support.List.length vars)
in (let _120_286 = (let _120_285 = (Support.All.pipe_right pats (Support.List.map (Support.List.map (aux (ix + n)))))
in (let _120_284 = (aux (ix + n) body)
in (qop, _120_285, wopt, vars, _120_284)))
in (mkQuant _120_286)))
end)
end))
in (aux 0 t)))))

let inst = (fun ( tms ) ( t ) -> (let n = (Support.List.length tms)
in (let rec aux = (fun ( shift ) ( t ) -> (match (t.tm) with
| (Integer (_)) | (FreeV (_)) -> begin
t
end
| BoundV (i) -> begin
(match (((0 <= (i - shift)) && ((i - shift) < n))) with
| true -> begin
(Support.List.nth tms (i - shift))
end
| false -> begin
t
end)
end
| App ((op, tms)) -> begin
(let _120_296 = (let _120_295 = (Support.List.map (aux shift) tms)
in (op, _120_295))
in (mkApp' _120_296))
end
| Quant ((qop, pats, wopt, vars, body)) -> begin
(let m = (Support.List.length vars)
in (let shift = (shift + m)
in (let _120_299 = (let _120_298 = (Support.All.pipe_right pats (Support.List.map (Support.List.map (aux shift))))
in (let _120_297 = (aux shift body)
in (qop, _120_298, wopt, vars, _120_297)))
in (mkQuant _120_299))))
end))
in (aux 0 t))))

let mkQuant' = (fun ( _49_483 ) -> (match (_49_483) with
| (qop, pats, wopt, vars, body) -> begin
(let _120_305 = (let _120_304 = (Support.All.pipe_right pats (Support.List.map (Support.List.map (abstr vars))))
in (let _120_303 = (Support.List.map fv_sort vars)
in (let _120_302 = (abstr vars body)
in (qop, _120_304, wopt, _120_303, _120_302))))
in (mkQuant _120_305))
end))

let mkForall'' = (fun ( _49_488 ) -> (match (_49_488) with
| (pats, wopt, sorts, body) -> begin
(mkQuant (Forall, pats, wopt, sorts, body))
end))

let mkForall' = (fun ( _49_493 ) -> (match (_49_493) with
| (pats, wopt, vars, body) -> begin
(mkQuant' (Forall, pats, wopt, vars, body))
end))

let mkForall = (fun ( _49_497 ) -> (match (_49_497) with
| (pats, vars, body) -> begin
(mkQuant' (Forall, (pats)::[], None, vars, body))
end))

let mkExists = (fun ( _49_501 ) -> (match (_49_501) with
| (pats, vars, body) -> begin
(mkQuant' (Exists, (pats)::[], None, vars, body))
end))

type caption =
string option

type binders =
(string * sort) list

type projector =
(string * sort)

type constructor_t =
(string * projector list * sort * int)

type constructors =
constructor_t list

type decl =
| DefPrelude
| DeclFun of (string * sort list * sort * caption)
| DefineFun of (string * sort list * sort * term * caption)
| Assume of (term * caption)
| Caption of string
| Eval of term
| Echo of string
| Push
| Pop
| CheckSat

let is_DefPrelude = (fun ( _discr_ ) -> (match (_discr_) with
| DefPrelude -> begin
true
end
| _ -> begin
false
end))

let is_DeclFun = (fun ( _discr_ ) -> (match (_discr_) with
| DeclFun (_) -> begin
true
end
| _ -> begin
false
end))

let is_DefineFun = (fun ( _discr_ ) -> (match (_discr_) with
| DefineFun (_) -> begin
true
end
| _ -> begin
false
end))

let is_Assume = (fun ( _discr_ ) -> (match (_discr_) with
| Assume (_) -> begin
true
end
| _ -> begin
false
end))

let is_Caption = (fun ( _discr_ ) -> (match (_discr_) with
| Caption (_) -> begin
true
end
| _ -> begin
false
end))

let is_Eval = (fun ( _discr_ ) -> (match (_discr_) with
| Eval (_) -> begin
true
end
| _ -> begin
false
end))

let is_Echo = (fun ( _discr_ ) -> (match (_discr_) with
| Echo (_) -> begin
true
end
| _ -> begin
false
end))

let is_Push = (fun ( _discr_ ) -> (match (_discr_) with
| Push -> begin
true
end
| _ -> begin
false
end))

let is_Pop = (fun ( _discr_ ) -> (match (_discr_) with
| Pop -> begin
true
end
| _ -> begin
false
end))

let is_CheckSat = (fun ( _discr_ ) -> (match (_discr_) with
| CheckSat -> begin
true
end
| _ -> begin
false
end))

let ___DeclFun____0 = (fun ( projectee ) -> (match (projectee) with
| DeclFun (_49_504) -> begin
_49_504
end))

let ___DefineFun____0 = (fun ( projectee ) -> (match (projectee) with
| DefineFun (_49_507) -> begin
_49_507
end))

let ___Assume____0 = (fun ( projectee ) -> (match (projectee) with
| Assume (_49_510) -> begin
_49_510
end))

let ___Caption____0 = (fun ( projectee ) -> (match (projectee) with
| Caption (_49_513) -> begin
_49_513
end))

let ___Eval____0 = (fun ( projectee ) -> (match (projectee) with
| Eval (_49_516) -> begin
_49_516
end))

let ___Echo____0 = (fun ( projectee ) -> (match (projectee) with
| Echo (_49_519) -> begin
_49_519
end))

type decls_t =
decl list

let mkDefineFun = (fun ( _49_525 ) -> (match (_49_525) with
| (nm, vars, s, tm, c) -> begin
(let _120_406 = (let _120_405 = (Support.List.map fv_sort vars)
in (let _120_404 = (abstr vars tm)
in (nm, _120_405, s, _120_404, c)))
in DefineFun (_120_406))
end))

let constr_id_of_sort = (fun ( sort ) -> (let _120_409 = (strSort sort)
in (Support.Microsoft.FStar.Util.format1 "%s_constr_id" _120_409)))

let fresh_token = (fun ( _49_529 ) ( id ) -> (match (_49_529) with
| (tok_name, sort) -> begin
(let _120_422 = (let _120_421 = (let _120_420 = (let _120_419 = (mkInteger' id)
in (let _120_418 = (let _120_417 = (let _120_416 = (constr_id_of_sort sort)
in (let _120_415 = (let _120_414 = (mkApp (tok_name, []))
in (_120_414)::[])
in (_120_416, _120_415)))
in (mkApp _120_417))
in (_120_419, _120_418)))
in (mkEq _120_420))
in (_120_421, Some ("fresh token")))
in Assume (_120_422))
end))

let constructor_to_decl = (fun ( _49_535 ) -> (match (_49_535) with
| (name, projectors, sort, id) -> begin
(let id = (Support.Microsoft.FStar.Util.string_of_int id)
in (let cdecl = (let _120_426 = (let _120_425 = (Support.All.pipe_right projectors (Support.List.map Support.Prims.snd))
in (name, _120_425, sort, Some ("Constructor")))
in DeclFun (_120_426))
in (let n_bvars = (Support.List.length projectors)
in (let bvar_name = (fun ( i ) -> (let _120_429 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.String.strcat "x_" _120_429)))
in (let bvar_index = (fun ( i ) -> (n_bvars - (i + 1)))
in (let bvar = (fun ( i ) ( s ) -> (let _120_437 = (let _120_436 = (bvar_name i)
in (_120_436, s))
in (mkFreeV _120_437)))
in (let bvars = (Support.All.pipe_right projectors (Support.List.mapi (fun ( i ) ( _49_550 ) -> (match (_49_550) with
| (_49_548, s) -> begin
(bvar i s)
end))))
in (let bvar_names = (Support.List.map fv_of_term bvars)
in (let capp = (mkApp (name, bvars))
in (let cid_app = (let _120_441 = (let _120_440 = (constr_id_of_sort sort)
in (_120_440, (capp)::[]))
in (mkApp _120_441))
in (let cid = (let _120_447 = (let _120_446 = (let _120_445 = (let _120_444 = (let _120_443 = (let _120_442 = (mkInteger id)
in (_120_442, cid_app))
in (mkEq _120_443))
in ([], bvar_names, _120_444))
in (mkForall _120_445))
in (_120_446, Some ("Constructor distinct")))
in Assume (_120_447))
in (let disc_name = (Support.String.strcat "is-" name)
in (let xfv = ("x", sort)
in (let xx = (mkFreeV xfv)
in (let disc_eq = (let _120_452 = (let _120_451 = (let _120_449 = (let _120_448 = (constr_id_of_sort sort)
in (_120_448, (xx)::[]))
in (mkApp _120_449))
in (let _120_450 = (mkInteger id)
in (_120_451, _120_450)))
in (mkEq _120_452))
in (let proj_terms = (Support.All.pipe_right projectors (Support.List.map (fun ( _49_562 ) -> (match (_49_562) with
| (proj, s) -> begin
(mkApp (proj, (xx)::[]))
end))))
in (let disc_inv_body = (let _120_455 = (let _120_454 = (mkApp (name, proj_terms))
in (xx, _120_454))
in (mkEq _120_455))
in (let disc_ax = (mkAnd (disc_eq, disc_inv_body))
in (let disc = (mkDefineFun (disc_name, (xfv)::[], Bool_sort, disc_ax, Some ("Discriminator definition")))
in (let projs = (let _120_466 = (Support.All.pipe_right projectors (Support.List.mapi (fun ( i ) ( _49_570 ) -> (match (_49_570) with
| (name, s) -> begin
(let cproj_app = (mkApp (name, (capp)::[]))
in (let _120_465 = (let _120_464 = (let _120_463 = (let _120_462 = (let _120_461 = (let _120_460 = (let _120_459 = (let _120_458 = (bvar i s)
in (cproj_app, _120_458))
in (mkEq _120_459))
in ((capp)::[], bvar_names, _120_460))
in (mkForall _120_461))
in (_120_462, Some ("Projection inverse")))
in Assume (_120_463))
in (_120_464)::[])
in (DeclFun ((name, (sort)::[], s, Some ("Projector"))))::_120_465))
end))))
in (Support.All.pipe_right _120_466 Support.List.flatten))
in (let _120_473 = (let _120_469 = (let _120_468 = (let _120_467 = (Support.Microsoft.FStar.Util.format1 "<start constructor %s>" name)
in Caption (_120_467))
in (_120_468)::(cdecl)::(cid)::projs)
in (Support.List.append _120_469 ((disc)::[])))
in (let _120_472 = (let _120_471 = (let _120_470 = (Support.Microsoft.FStar.Util.format1 "</end constructor %s>" name)
in Caption (_120_470))
in (_120_471)::[])
in (Support.List.append _120_473 _120_472)))))))))))))))))))))))
end))

let name_binders_inner = (fun ( outer_names ) ( start ) ( sorts ) -> (let _49_592 = (Support.All.pipe_right sorts (Support.List.fold_left (fun ( _49_579 ) ( s ) -> (match (_49_579) with
| (names, binders, n) -> begin
(let prefix = (match (s) with
| Type_sort -> begin
"@a"
end
| Term_sort -> begin
"@x"
end
| _49_584 -> begin
"@u"
end)
in (let nm = (let _120_482 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.String.strcat prefix _120_482))
in (let names = ((nm, s))::names
in (let b = (let _120_483 = (strSort s)
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" nm _120_483))
in (names, (b)::binders, (n + 1))))))
end)) (outer_names, [], start)))
in (match (_49_592) with
| (names, binders, n) -> begin
(names, (Support.List.rev binders), n)
end)))

let name_binders = (fun ( sorts ) -> (let _49_597 = (name_binders_inner [] 0 sorts)
in (match (_49_597) with
| (names, binders, n) -> begin
((Support.List.rev names), binders)
end)))

let termToSmt = (fun ( t ) -> (let rec aux = (fun ( n ) ( names ) ( t ) -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _120_494 = (Support.List.nth names i)
in (Support.All.pipe_right _120_494 Support.Prims.fst))
end
| FreeV (x) -> begin
(Support.Prims.fst x)
end
| App ((op, [])) -> begin
(op_to_string op)
end
| App ((op, tms)) -> begin
(let _120_496 = (let _120_495 = (Support.List.map (aux n names) tms)
in (Support.All.pipe_right _120_495 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" (op_to_string op) _120_496))
end
| Quant ((qop, pats, wopt, sorts, body)) -> begin
(let _49_627 = (name_binders_inner names n sorts)
in (match (_49_627) with
| (names, binders, n) -> begin
(let binders = (Support.All.pipe_right binders (Support.String.concat " "))
in (let pats_str = (match (pats) with
| ([]::[]) | ([]) -> begin
""
end
| _49_633 -> begin
(let _120_502 = (Support.All.pipe_right pats (Support.List.map (fun ( pats ) -> (let _120_501 = (let _120_500 = (Support.List.map (fun ( p ) -> (let _120_499 = (aux n names p)
in (Support.Microsoft.FStar.Util.format1 "%s" _120_499))) pats)
in (Support.String.concat " " _120_500))
in (Support.Microsoft.FStar.Util.format1 "\n:pattern (%s)" _120_501)))))
in (Support.All.pipe_right _120_502 (Support.String.concat "\n")))
end)
in (match ((pats, wopt)) with
| (([]::[], None)) | (([], None)) -> begin
(let _120_503 = (aux n names body)
in (Support.Microsoft.FStar.Util.format3 "(%s (%s)\n %s)" (qop_to_string qop) binders _120_503))
end
| _49_645 -> begin
(let _120_505 = (aux n names body)
in (let _120_504 = (weightToSmt wopt)
in (Support.Microsoft.FStar.Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _120_505 _120_504 pats_str)))
end)))
end))
end))
in (aux 0 [] t)))

let caption_to_string = (fun ( _49_6 ) -> (match (_49_6) with
| None -> begin
""
end
| Some (c) -> begin
(let _49_652 = (Support.Microsoft.FStar.Util.splitlines c)
in (match (_49_652) with
| hd::tl -> begin
(let suffix = (match (tl) with
| [] -> begin
""
end
| _49_655 -> begin
"..."
end)
in (Support.Microsoft.FStar.Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd suffix))
end))
end))

let rec declToSmt = (fun ( z3options ) ( decl ) -> (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(let _120_514 = (Support.All.pipe_right (Support.Microsoft.FStar.Util.splitlines c) (fun ( _49_7 ) -> (match (_49_7) with
| [] -> begin
""
end
| h::t -> begin
h
end)))
in (Support.Microsoft.FStar.Util.format1 "\n; %s" _120_514))
end
| DeclFun ((f, argsorts, retsort, c)) -> begin
(let l = (Support.List.map strSort argsorts)
in (let _120_516 = (caption_to_string c)
in (let _120_515 = (strSort retsort)
in (Support.Microsoft.FStar.Util.format4 "%s(declare-fun %s (%s) %s)" _120_516 f (Support.String.concat " " l) _120_515))))
end
| DefineFun ((f, arg_sorts, retsort, body, c)) -> begin
(let _49_683 = (name_binders arg_sorts)
in (match (_49_683) with
| (names, binders) -> begin
(let body = (let _120_517 = (Support.List.map mkFreeV names)
in (inst _120_517 body))
in (let _120_520 = (caption_to_string c)
in (let _120_519 = (strSort retsort)
in (let _120_518 = (termToSmt body)
in (Support.Microsoft.FStar.Util.format5 "%s(define-fun %s (%s) %s\n %s)" _120_520 f (Support.String.concat " " binders) _120_519 _120_518)))))
end))
end
| Assume ((t, c)) -> begin
(let _120_522 = (caption_to_string c)
in (let _120_521 = (termToSmt t)
in (Support.Microsoft.FStar.Util.format2 "%s(assert %s)" _120_522 _120_521)))
end
| Eval (t) -> begin
(let _120_523 = (termToSmt t)
in (Support.Microsoft.FStar.Util.format1 "(eval %s)" _120_523))
end
| Echo (s) -> begin
(Support.Microsoft.FStar.Util.format1 "(echo \"%s\")" s)
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
and mkPrelude = (fun ( z3options ) -> (let basic = (Support.String.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort String)\n(declare-fun String_constr_id (String) Int)\n\n(declare-sort Kind)\n(declare-fun Kind_constr_id (Kind) Int)\n\n(declare-sort Type)\n(declare-fun Type_constr_id (Type) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreKind (Type) Kind)\n(declare-fun PreType (Term) Type)\n(declare-fun Valid (Type) Bool)\n(declare-fun HasKind (Type Kind) Bool)\n(declare-fun HasTypeFuel (Fuel Term Type) Bool)\n(define-fun HasTypeZ ((x Term) (t Type)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Type)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Type))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Type)) (HasTypeZ x t)))\n(declare-fun ApplyEF (Term Fuel) Term)\n(declare-fun ApplyEE (Term Term) Term)\n(declare-fun ApplyET (Term Type) Term)\n(declare-fun ApplyTE (Type Term) Type)\n(declare-fun ApplyTT (Type Type) Type)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsType (Type Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Type)\n(assert (forall ((t Type))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.Precedes ((a Type) (b Type) (t1 Term) (t2 Term)) Type\n(Precedes t1 t2))\n")
in (let constrs = (("String_const", (("String_const_proj_0", Int_sort))::[], String_sort, 0))::(("Kind_type", [], Kind_sort, 0))::(("Kind_arrow", (("Kind_arrow_id", Int_sort))::[], Kind_sort, 1))::(("Kind_uvar", (("Kind_uvar_fst", Int_sort))::[], Kind_sort, 2))::(("Typ_fun", (("Typ_fun_id", Int_sort))::[], Type_sort, 1))::(("Typ_app", (("Typ_app_fst", Type_sort))::(("Typ_app_snd", Type_sort))::[], Type_sort, 2))::(("Typ_dep", (("Typ_dep_fst", Type_sort))::(("Typ_dep_snd", Term_sort))::[], Type_sort, 3))::(("Typ_uvar", (("Typ_uvar_fst", Int_sort))::[], Type_sort, 4))::(("Term_unit", [], Term_sort, 0))::(("BoxInt", (("BoxInt_proj_0", Int_sort))::[], Term_sort, 1))::(("BoxBool", (("BoxBool_proj_0", Bool_sort))::[], Term_sort, 2))::(("BoxString", (("BoxString_proj_0", String_sort))::[], Term_sort, 3))::(("BoxRef", (("BoxRef_proj_0", Ref_sort))::[], Term_sort, 4))::(("Exp_uvar", (("Exp_uvar_fst", Int_sort))::[], Term_sort, 5))::(("LexCons", (("LexCons_0", Term_sort))::(("LexCons_1", Term_sort))::[], Term_sort, 6))::[]
in (let bcons = (let _120_526 = (let _120_525 = (Support.All.pipe_right constrs (Support.List.collect constructor_to_decl))
in (Support.All.pipe_right _120_525 (Support.List.map (declToSmt z3options))))
in (Support.All.pipe_right _120_526 (Support.String.concat "\n")))
in (let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Support.String.strcat (Support.String.strcat basic bcons) lex_ordering))))))

let mk_Kind_type = (mkApp ("Kind_type", []))

let mk_Kind_uvar = (fun ( i ) -> (let _120_531 = (let _120_530 = (let _120_529 = (mkInteger' i)
in (_120_529)::[])
in ("Kind_uvar", _120_530))
in (mkApp _120_531)))

let mk_Typ_app = (fun ( t1 ) ( t2 ) -> (mkApp ("Typ_app", (t1)::(t2)::[])))

let mk_Typ_dep = (fun ( t1 ) ( t2 ) -> (mkApp ("Typ_dep", (t1)::(t2)::[])))

let mk_Typ_uvar = (fun ( i ) -> (let _120_544 = (let _120_543 = (let _120_542 = (mkInteger' i)
in (_120_542)::[])
in ("Typ_uvar", _120_543))
in (mkApp _120_544)))

let mk_Exp_uvar = (fun ( i ) -> (let _120_549 = (let _120_548 = (let _120_547 = (mkInteger' i)
in (_120_547)::[])
in ("Exp_uvar", _120_548))
in (mkApp _120_549)))

let mk_Term_unit = (mkApp ("Term_unit", []))

let boxInt = (fun ( t ) -> (mkApp ("BoxInt", (t)::[])))

let unboxInt = (fun ( t ) -> (mkApp ("BoxInt_proj_0", (t)::[])))

let boxBool = (fun ( t ) -> (mkApp ("BoxBool", (t)::[])))

let unboxBool = (fun ( t ) -> (mkApp ("BoxBool_proj_0", (t)::[])))

let boxString = (fun ( t ) -> (mkApp ("BoxString", (t)::[])))

let unboxString = (fun ( t ) -> (mkApp ("BoxString_proj_0", (t)::[])))

let boxRef = (fun ( t ) -> (mkApp ("BoxRef", (t)::[])))

let unboxRef = (fun ( t ) -> (mkApp ("BoxRef_proj_0", (t)::[])))

let boxTerm = (fun ( sort ) ( t ) -> (match (sort) with
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
| _49_723 -> begin
(raise (Support.Microsoft.FStar.Util.Impos))
end))

let unboxTerm = (fun ( sort ) ( t ) -> (match (sort) with
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
| _49_731 -> begin
(raise (Support.Microsoft.FStar.Util.Impos))
end))

let mk_PreKind = (fun ( t ) -> (mkApp ("PreKind", (t)::[])))

let mk_PreType = (fun ( t ) -> (mkApp ("PreType", (t)::[])))

let mk_Valid = (fun ( t ) -> (mkApp ("Valid", (t)::[])))

let mk_HasType = (fun ( v ) ( t ) -> (mkApp ("HasType", (v)::(t)::[])))

let mk_HasTypeZ = (fun ( v ) ( t ) -> (mkApp ("HasTypeZ", (v)::(t)::[])))

let mk_IsTyped = (fun ( v ) -> (mkApp ("IsTyped", (v)::[])))

let mk_HasTypeFuel = (fun ( f ) ( v ) ( t ) -> (match ((Support.ST.read Microsoft_FStar_Options.unthrottle_inductives)) with
| true -> begin
(mk_HasType v t)
end
| false -> begin
(mkApp ("HasTypeFuel", (f)::(v)::(t)::[]))
end))

let mk_HasTypeWithFuel = (fun ( f ) ( v ) ( t ) -> (match (f) with
| None -> begin
(mk_HasType v t)
end
| Some (f) -> begin
(mk_HasTypeFuel f v t)
end))

let mk_Destruct = (fun ( v ) -> (mkApp ("Destruct", (v)::[])))

let mk_HasKind = (fun ( t ) ( k ) -> (mkApp ("HasKind", (t)::(k)::[])))

let mk_Rank = (fun ( x ) -> (mkApp ("Rank", (x)::[])))

let mk_tester = (fun ( n ) ( t ) -> (mkApp ((Support.String.strcat "is-" n), (t)::[])))

let mk_ApplyTE = (fun ( t ) ( e ) -> (mkApp ("ApplyTE", (t)::(e)::[])))

let mk_ApplyTT = (fun ( t ) ( t' ) -> (mkApp ("ApplyTT", (t)::(t')::[])))

let mk_ApplyET = (fun ( e ) ( t ) -> (mkApp ("ApplyET", (e)::(t)::[])))

let mk_ApplyEE = (fun ( e ) ( e' ) -> (mkApp ("ApplyEE", (e)::(e')::[])))

let mk_ApplyEF = (fun ( e ) ( f ) -> (mkApp ("ApplyEF", (e)::(f)::[])))

let mk_String_const = (fun ( i ) -> (let _120_638 = (let _120_637 = (let _120_636 = (mkInteger' i)
in (_120_636)::[])
in ("String_const", _120_637))
in (mkApp _120_638)))

let mk_Precedes = (fun ( x1 ) ( x2 ) -> (let _120_643 = (mkApp ("Precedes", (x1)::(x2)::[]))
in (Support.All.pipe_right _120_643 mk_Valid)))

let mk_LexCons = (fun ( x1 ) ( x2 ) -> (mkApp ("LexCons", (x1)::(x2)::[])))

let rec n_fuel = (fun ( n ) -> (match ((n = 0)) with
| true -> begin
(mkApp ("ZFuel", []))
end
| false -> begin
(let _120_652 = (let _120_651 = (let _120_650 = (n_fuel (n - 1))
in (_120_650)::[])
in ("SFuel", _120_651))
in (mkApp _120_652))
end))

let fuel_2 = (n_fuel 2)

let fuel_100 = (n_fuel 100)

let mk_and_opt = (fun ( p1 ) ( p2 ) -> (match ((p1, p2)) with
| (Some (p1), Some (p2)) -> begin
(let _120_657 = (mkAnd (p1, p2))
in Some (_120_657))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))

let mk_and_opt_l = (fun ( pl ) -> (Support.List.fold_left (fun ( out ) ( p ) -> (mk_and_opt p out)) None pl))

let mk_and_l = (fun ( l ) -> (match (l) with
| [] -> begin
mkTrue
end
| hd::tl -> begin
(Support.List.fold_left (fun ( p1 ) ( p2 ) -> (mkAnd (p1, p2))) hd tl)
end))

let mk_or_l = (fun ( l ) -> (match (l) with
| [] -> begin
mkFalse
end
| hd::tl -> begin
(Support.List.fold_left (fun ( p1 ) ( p2 ) -> (mkOr (p1, p2))) hd tl)
end))

let rec print_smt_term = (fun ( t ) -> (match (t.tm) with
| Integer (n) -> begin
(Support.Microsoft.FStar.Util.format1 "Integer %s" n)
end
| BoundV (n) -> begin
(let _120_674 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "BoundV %s" _120_674))
end
| FreeV (fv) -> begin
(Support.Microsoft.FStar.Util.format1 "FreeV %s" (Support.Prims.fst fv))
end
| App ((op, l)) -> begin
(let _120_675 = (print_smt_term_list l)
in (Support.Microsoft.FStar.Util.format2 "App %s [ %s ]" (op_to_string op) _120_675))
end
| Quant ((qop, l, _49_819, _49_821, t)) -> begin
(let _120_677 = (print_smt_term_list_list l)
in (let _120_676 = (print_smt_term t)
in (Support.Microsoft.FStar.Util.format3 "Quant %s %s %s" (qop_to_string qop) _120_677 _120_676)))
end))
and print_smt_term_list = (fun ( l ) -> (Support.List.fold_left (fun ( s ) ( t ) -> (let _120_681 = (print_smt_term t)
in (Support.String.strcat (Support.String.strcat s "; ") _120_681))) "" l))
and print_smt_term_list_list = (fun ( l ) -> (Support.List.fold_left (fun ( s ) ( l ) -> (let _120_686 = (let _120_685 = (print_smt_term_list l)
in (Support.String.strcat (Support.String.strcat s "; [ ") _120_685))
in (Support.String.strcat _120_686 " ] "))) "" l))




