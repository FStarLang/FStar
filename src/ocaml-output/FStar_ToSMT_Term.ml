
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

let is_Bool_sort : sort  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Bool_sort -> begin
true
end
| _ -> begin
false
end))

let is_Int_sort : sort  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Int_sort -> begin
true
end
| _ -> begin
false
end))

let is_Kind_sort : sort  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Kind_sort -> begin
true
end
| _ -> begin
false
end))

let is_Type_sort : sort  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Type_sort -> begin
true
end
| _ -> begin
false
end))

let is_Term_sort : sort  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Term_sort -> begin
true
end
| _ -> begin
false
end))

let is_String_sort : sort  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| String_sort -> begin
true
end
| _ -> begin
false
end))

let is_Ref_sort : sort  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Ref_sort -> begin
true
end
| _ -> begin
false
end))

let is_Fuel_sort : sort  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Fuel_sort -> begin
true
end
| _ -> begin
false
end))

let is_Array : sort  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Array (_) -> begin
true
end
| _ -> begin
false
end))

let is_Arrow : sort  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Arrow (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sort : sort  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sort (_) -> begin
true
end
| _ -> begin
false
end))

let ___Array____0 : sort  ->  (sort * sort) = (fun projectee -> (match (projectee) with
| Array (_56_10) -> begin
_56_10
end))

let ___Arrow____0 : sort  ->  (sort * sort) = (fun projectee -> (match (projectee) with
| Arrow (_56_13) -> begin
_56_13
end))

let ___Sort____0 : sort  ->  Prims.string = (fun projectee -> (match (projectee) with
| Sort (_56_16) -> begin
_56_16
end))

let rec strSort : sort  ->  Prims.string = (fun x -> (match (x) with
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
(let _159_54 = (strSort s1)
in (let _159_53 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _159_54 _159_53)))
end
| Arrow (s1, s2) -> begin
(let _159_56 = (strSort s1)
in (let _159_55 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _159_56 _159_55)))
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

let is_True : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| True -> begin
true
end
| _ -> begin
false
end))

let is_False : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| False -> begin
true
end
| _ -> begin
false
end))

let is_Not : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Not -> begin
true
end
| _ -> begin
false
end))

let is_And : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| And -> begin
true
end
| _ -> begin
false
end))

let is_Or : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Or -> begin
true
end
| _ -> begin
false
end))

let is_Imp : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Imp -> begin
true
end
| _ -> begin
false
end))

let is_Iff : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Iff -> begin
true
end
| _ -> begin
false
end))

let is_Eq : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Eq -> begin
true
end
| _ -> begin
false
end))

let is_LT : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| LT -> begin
true
end
| _ -> begin
false
end))

let is_LTE : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| LTE -> begin
true
end
| _ -> begin
false
end))

let is_GT : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| GT -> begin
true
end
| _ -> begin
false
end))

let is_GTE : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| GTE -> begin
true
end
| _ -> begin
false
end))

let is_Add : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Add -> begin
true
end
| _ -> begin
false
end))

let is_Sub : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sub -> begin
true
end
| _ -> begin
false
end))

let is_Div : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Div -> begin
true
end
| _ -> begin
false
end))

let is_Mul : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Mul -> begin
true
end
| _ -> begin
false
end))

let is_Minus : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Minus -> begin
true
end
| _ -> begin
false
end))

let is_Mod : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Mod -> begin
true
end
| _ -> begin
false
end))

let is_ITE : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| ITE -> begin
true
end
| _ -> begin
false
end))

let is_Var : op  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Var (_) -> begin
true
end
| _ -> begin
false
end))

let ___Var____0 : op  ->  Prims.string = (fun projectee -> (match (projectee) with
| Var (_56_38) -> begin
_56_38
end))

type qop =
| Forall
| Exists

let is_Forall : qop  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Forall -> begin
true
end
| _ -> begin
false
end))

let is_Exists : qop  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
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

let is_Integer : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Integer (_) -> begin
true
end
| _ -> begin
false
end))

let is_BoundV : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| BoundV (_) -> begin
true
end
| _ -> begin
false
end))

let is_FreeV : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| FreeV (_) -> begin
true
end
| _ -> begin
false
end))

let is_App : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))

let is_Quant : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Quant (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkterm : term  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkterm"))))

let ___Integer____0 : term'  ->  Prims.string = (fun projectee -> (match (projectee) with
| Integer (_56_44) -> begin
_56_44
end))

let ___BoundV____0 : term'  ->  Prims.int = (fun projectee -> (match (projectee) with
| BoundV (_56_47) -> begin
_56_47
end))

let ___FreeV____0 : term'  ->  fv = (fun projectee -> (match (projectee) with
| FreeV (_56_50) -> begin
_56_50
end))

let ___App____0 : term'  ->  (op * term Prims.list) = (fun projectee -> (match (projectee) with
| App (_56_53) -> begin
_56_53
end))

let ___Quant____0 : term'  ->  (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term) = (fun projectee -> (match (projectee) with
| Quant (_56_56) -> begin
_56_56
end))

let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> ((Prims.fst x) = (Prims.fst y)))

let fv_sort = (fun x -> (Prims.snd x))

let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match ((x.tm, y.tm)) with
| (FreeV (x), FreeV (y)) -> begin
(fv_eq x y)
end
| _56_69 -> begin
false
end))

let freevar_sort : term  ->  sort = (fun _56_1 -> (match (_56_1) with
| {tm = FreeV (x); hash = _56_74; freevars = _56_72} -> begin
(fv_sort x)
end
| _56_79 -> begin
(FStar_All.failwith "impossible")
end))

let fv_of_term : term  ->  fv = (fun _56_2 -> (match (_56_2) with
| {tm = FreeV (fv); hash = _56_84; freevars = _56_82} -> begin
fv
end
| _56_89 -> begin
(FStar_All.failwith "impossible")
end))

let rec freevars : term  ->  fv Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (_56_100, tms) -> begin
(FStar_List.collect freevars tms)
end
| Quant (_56_105, _56_107, _56_109, _56_111, t) -> begin
(freevars t)
end))

let free_variables : term  ->  fvs = (fun t -> (match ((FStar_ST.read t.freevars)) with
| Some (b) -> begin
b
end
| None -> begin
(let fvs = (let _159_189 = (freevars t)
in (FStar_Util.remove_dups fv_eq _159_189))
in (let _56_120 = (FStar_ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))

let qop_to_string : qop  ->  Prims.string = (fun _56_3 -> (match (_56_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))

let op_to_string : op  ->  Prims.string = (fun _56_4 -> (match (_56_4) with
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

let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun _56_5 -> (match (_56_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _159_196 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _159_196))
end))

let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _159_199 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _159_199))
end
| FreeV (x) -> begin
(let _159_200 = (strSort (Prims.snd x))
in (Prims.strcat (Prims.strcat (Prims.fst x) ":") _159_200))
end
| App (op, tms) -> begin
(let _159_204 = (let _159_203 = (let _159_202 = (FStar_List.map (fun t -> t.hash) tms)
in (FStar_All.pipe_right _159_202 (FStar_String.concat " ")))
in (Prims.strcat (Prims.strcat "(" (op_to_string op)) _159_203))
in (Prims.strcat _159_204 ")"))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _159_212 = (let _159_205 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _159_205 (FStar_String.concat " ")))
in (let _159_211 = (weightToSmt wopt)
in (let _159_210 = (let _159_209 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _159_208 = (FStar_List.map (fun p -> p.hash) pats)
in (FStar_All.pipe_right _159_208 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _159_209 (FStar_String.concat "; ")))
in (FStar_Util.format5 "(%s (%s)(! %s %s %s))" (qop_to_string qop) _159_212 body.hash _159_211 _159_210))))
end))

let __all_terms : term FStar_Util.smap FStar_ST.ref = (let _159_213 = (FStar_Util.smap_create 10000)
in (FStar_ST.alloc _159_213))

let all_terms : Prims.unit  ->  term FStar_Util.smap = (fun _56_172 -> (match (()) with
| () -> begin
(FStar_ST.read __all_terms)
end))

let mk : term'  ->  term = (fun t -> (let key = (hash_of_term' t)
in (match ((let _159_218 = (all_terms ())
in (FStar_Util.smap_try_find _159_218 key))) with
| Some (tm) -> begin
tm
end
| None -> begin
(let tm = (let _159_219 = (FStar_Util.mk_ref None)
in {tm = t; hash = key; freevars = _159_219})
in (let _56_179 = (let _159_220 = (all_terms ())
in (FStar_Util.smap_add _159_220 key tm))
in tm))
end)))

let mkTrue : term = (mk (App ((True, []))))

let mkFalse : term = (mk (App ((False, []))))

let mkInteger : Prims.string  ->  term = (fun i -> (mk (Integer (i))))

let mkInteger32 : Prims.int32  ->  term = (fun i -> (mkInteger (FStar_Util.string_of_int32 i)))

let mkInteger' : Prims.int  ->  term = (fun i -> (let _159_227 = (FStar_Util.string_of_int i)
in (mkInteger _159_227)))

let mkBoundV : Prims.int  ->  term = (fun i -> (mk (BoundV (i))))

let mkFreeV : (Prims.string * sort)  ->  term = (fun x -> (mk (FreeV (x))))

let mkApp' : (op * term Prims.list)  ->  term = (fun f -> (mk (App (f))))

let mkApp : (Prims.string * term Prims.list)  ->  term = (fun _56_189 -> (match (_56_189) with
| (s, args) -> begin
(mk (App ((Var (s), args))))
end))

let mkNot : term  ->  term = (fun t -> (match (t.tm) with
| App (True, _56_193) -> begin
mkFalse
end
| App (False, _56_198) -> begin
mkTrue
end
| _56_202 -> begin
(mkApp' (Not, (t)::[]))
end))

let mkAnd : (term * term)  ->  term = (fun _56_205 -> (match (_56_205) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (App (True, _56_208), _56_212) -> begin
t2
end
| (_56_215, App (True, _56_218)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
mkFalse
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' (And, (FStar_List.append ts1 ts2)))
end
| (_56_248, App (And, ts2)) -> begin
(mkApp' (And, (t1)::ts2))
end
| (App (And, ts1), _56_259) -> begin
(mkApp' (And, (FStar_List.append ts1 ((t2)::[]))))
end
| _56_262 -> begin
(mkApp' (And, (t1)::(t2)::[]))
end)
end))

let mkOr : (term * term)  ->  term = (fun _56_265 -> (match (_56_265) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
mkTrue
end
| (App (False, _56_284), _56_288) -> begin
t2
end
| (_56_291, App (False, _56_294)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' (Or, (FStar_List.append ts1 ts2)))
end
| (_56_308, App (Or, ts2)) -> begin
(mkApp' (Or, (t1)::ts2))
end
| (App (Or, ts1), _56_319) -> begin
(mkApp' (Or, (FStar_List.append ts1 ((t2)::[]))))
end
| _56_322 -> begin
(mkApp' (Or, (t1)::(t2)::[]))
end)
end))

let mkImp : (term * term)  ->  term = (fun _56_325 -> (match (_56_325) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (_56_327, App (True, _56_330)) -> begin
mkTrue
end
| (App (True, _56_336), _56_340) -> begin
t2
end
| (_56_343, App (Imp, t1'::t2'::[])) -> begin
(let _159_246 = (let _159_245 = (let _159_244 = (mkAnd (t1, t1'))
in (_159_244)::(t2')::[])
in (Imp, _159_245))
in (mkApp' _159_246))
end
| _56_352 -> begin
(mkApp' (Imp, (t1)::(t2)::[]))
end)
end))

let mk_bin_op : op  ->  (term * term)  ->  term = (fun op _56_356 -> (match (_56_356) with
| (t1, t2) -> begin
(mkApp' (op, (t1)::(t2)::[]))
end))

let mkMinus : term  ->  term = (fun t -> (mkApp' (Minus, (t)::[])))

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

let mkITE : (term * term * term)  ->  term = (fun _56_361 -> (match (_56_361) with
| (t1, t2, t3) -> begin
(match ((t2.tm, t3.tm)) with
| (App (True, _56_364), App (True, _56_369)) -> begin
mkTrue
end
| (App (True, _56_375), _56_379) -> begin
(let _159_267 = (let _159_266 = (mkNot t1)
in (_159_266, t3))
in (mkImp _159_267))
end
| (_56_382, App (True, _56_385)) -> begin
(mkImp (t1, t2))
end
| (_56_390, _56_392) -> begin
(mkApp' (ITE, (t1)::(t2)::(t3)::[]))
end)
end))

let mkCases : term Prims.list  ->  term = (fun t -> (match (t) with
| [] -> begin
(FStar_All.failwith "Impos")
end
| hd::tl -> begin
(FStar_List.fold_left (fun out t -> (mkAnd (out, t))) hd tl)
end))

let mkQuant : (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _56_406 -> (match (_56_406) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = 0) then begin
body
end else begin
(match (body.tm) with
| App (True, _56_409) -> begin
body
end
| _56_413 -> begin
(mk (Quant ((qop, pats, wopt, vars, body))))
end)
end
end))

let abstr : fvs  ->  term  ->  term = (fun fvs t -> (let nvars = (FStar_List.length fvs)
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
| _56_428 -> begin
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
(let _159_285 = (let _159_284 = (FStar_List.map (aux ix) tms)
in (op, _159_284))
in (mkApp' _159_285))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(let n = (FStar_List.length vars)
in (let _159_288 = (let _159_287 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _159_286 = (aux (ix + n) body)
in (qop, _159_287, wopt, vars, _159_286)))
in (mkQuant _159_288)))
end)
end))
in (aux 0 t)))))

let inst : term Prims.list  ->  term  ->  term = (fun tms t -> (let n = (FStar_List.length tms)
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
(let _159_298 = (let _159_297 = (FStar_List.map (aux shift) tms)
in (op, _159_297))
in (mkApp' _159_298))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(let m = (FStar_List.length vars)
in (let shift = (shift + m)
in (let _159_301 = (let _159_300 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _159_299 = (aux shift body)
in (qop, _159_300, wopt, vars, _159_299)))
in (mkQuant _159_301))))
end))
in (aux 0 t))))

let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  term = (fun _56_484 -> (match (_56_484) with
| (qop, pats, wopt, vars, body) -> begin
(let _159_307 = (let _159_306 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _159_305 = (FStar_List.map fv_sort vars)
in (let _159_304 = (abstr vars body)
in (qop, _159_306, wopt, _159_305, _159_304))))
in (mkQuant _159_307))
end))

let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _56_489 -> (match (_56_489) with
| (pats, wopt, sorts, body) -> begin
(mkQuant (Forall, pats, wopt, sorts, body))
end))

let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  term = (fun _56_494 -> (match (_56_494) with
| (pats, wopt, vars, body) -> begin
(mkQuant' (Forall, pats, wopt, vars, body))
end))

let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _56_498 -> (match (_56_498) with
| (pats, vars, body) -> begin
(mkQuant' (Forall, pats, None, vars, body))
end))

let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _56_502 -> (match (_56_502) with
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

let is_DefPrelude : decl  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| DefPrelude -> begin
true
end
| _ -> begin
false
end))

let is_DeclFun : decl  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| DeclFun (_) -> begin
true
end
| _ -> begin
false
end))

let is_DefineFun : decl  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| DefineFun (_) -> begin
true
end
| _ -> begin
false
end))

let is_Assume : decl  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Assume (_) -> begin
true
end
| _ -> begin
false
end))

let is_Caption : decl  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Caption (_) -> begin
true
end
| _ -> begin
false
end))

let is_Eval : decl  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Eval (_) -> begin
true
end
| _ -> begin
false
end))

let is_Echo : decl  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Echo (_) -> begin
true
end
| _ -> begin
false
end))

let is_Push : decl  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Push -> begin
true
end
| _ -> begin
false
end))

let is_Pop : decl  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Pop -> begin
true
end
| _ -> begin
false
end))

let is_CheckSat : decl  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| CheckSat -> begin
true
end
| _ -> begin
false
end))

let ___DeclFun____0 : decl  ->  (Prims.string * sort Prims.list * sort * caption) = (fun projectee -> (match (projectee) with
| DeclFun (_56_505) -> begin
_56_505
end))

let ___DefineFun____0 : decl  ->  (Prims.string * sort Prims.list * sort * term * caption) = (fun projectee -> (match (projectee) with
| DefineFun (_56_508) -> begin
_56_508
end))

let ___Assume____0 : decl  ->  (term * caption) = (fun projectee -> (match (projectee) with
| Assume (_56_511) -> begin
_56_511
end))

let ___Caption____0 : decl  ->  Prims.string = (fun projectee -> (match (projectee) with
| Caption (_56_514) -> begin
_56_514
end))

let ___Eval____0 : decl  ->  term = (fun projectee -> (match (projectee) with
| Eval (_56_517) -> begin
_56_517
end))

let ___Echo____0 : decl  ->  Prims.string = (fun projectee -> (match (projectee) with
| Echo (_56_520) -> begin
_56_520
end))

type decls_t =
decl Prims.list

let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun _56_526 -> (match (_56_526) with
| (nm, vars, s, tm, c) -> begin
(let _159_408 = (let _159_407 = (FStar_List.map fv_sort vars)
in (let _159_406 = (abstr vars tm)
in (nm, _159_407, s, _159_406, c)))
in DefineFun (_159_408))
end))

let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _159_411 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _159_411)))

let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun _56_530 id -> (match (_56_530) with
| (tok_name, sort) -> begin
(let _159_424 = (let _159_423 = (let _159_422 = (let _159_421 = (mkInteger' id)
in (let _159_420 = (let _159_419 = (let _159_418 = (constr_id_of_sort sort)
in (let _159_417 = (let _159_416 = (mkApp (tok_name, []))
in (_159_416)::[])
in (_159_418, _159_417)))
in (mkApp _159_419))
in (_159_421, _159_420)))
in (mkEq _159_422))
in (_159_423, Some ("fresh token")))
in Assume (_159_424))
end))

let constructor_to_decl : constructor_t  ->  decls_t = (fun _56_536 -> (match (_56_536) with
| (name, projectors, sort, id) -> begin
(let id = (FStar_Util.string_of_int id)
in (let cdecl = (let _159_428 = (let _159_427 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in (name, _159_427, sort, Some ("Constructor")))
in DeclFun (_159_428))
in (let n_bvars = (FStar_List.length projectors)
in (let bvar_name = (fun i -> (let _159_431 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _159_431)))
in (let bvar_index = (fun i -> (n_bvars - (i + 1)))
in (let bvar = (fun i s -> (let _159_439 = (let _159_438 = (bvar_name i)
in (_159_438, s))
in (mkFreeV _159_439)))
in (let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _56_551 -> (match (_56_551) with
| (_56_549, s) -> begin
(bvar i s)
end))))
in (let bvar_names = (FStar_List.map fv_of_term bvars)
in (let capp = (mkApp (name, bvars))
in (let cid_app = (let _159_443 = (let _159_442 = (constr_id_of_sort sort)
in (_159_442, (capp)::[]))
in (mkApp _159_443))
in (let cid = (let _159_449 = (let _159_448 = (let _159_447 = (let _159_446 = (let _159_445 = (let _159_444 = (mkInteger id)
in (_159_444, cid_app))
in (mkEq _159_445))
in (((capp)::[])::[], bvar_names, _159_446))
in (mkForall _159_447))
in (_159_448, Some ("Constructor distinct")))
in Assume (_159_449))
in (let disc_name = (Prims.strcat "is-" name)
in (let xfv = ("x", sort)
in (let xx = (mkFreeV xfv)
in (let disc_eq = (let _159_454 = (let _159_453 = (let _159_451 = (let _159_450 = (constr_id_of_sort sort)
in (_159_450, (xx)::[]))
in (mkApp _159_451))
in (let _159_452 = (mkInteger id)
in (_159_453, _159_452)))
in (mkEq _159_454))
in (let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _56_563 -> (match (_56_563) with
| (proj, s) -> begin
(mkApp (proj, (xx)::[]))
end))))
in (let disc_inv_body = (let _159_457 = (let _159_456 = (mkApp (name, proj_terms))
in (xx, _159_456))
in (mkEq _159_457))
in (let disc_ax = (mkAnd (disc_eq, disc_inv_body))
in (let disc = (mkDefineFun (disc_name, (xfv)::[], Bool_sort, disc_ax, Some ("Discriminator definition")))
in (let projs = (let _159_468 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _56_571 -> (match (_56_571) with
| (name, s) -> begin
(let cproj_app = (mkApp (name, (capp)::[]))
in (let _159_467 = (let _159_466 = (let _159_465 = (let _159_464 = (let _159_463 = (let _159_462 = (let _159_461 = (let _159_460 = (bvar i s)
in (cproj_app, _159_460))
in (mkEq _159_461))
in (((capp)::[])::[], bvar_names, _159_462))
in (mkForall _159_463))
in (_159_464, Some ("Projection inverse")))
in Assume (_159_465))
in (_159_466)::[])
in (DeclFun ((name, (sort)::[], s, Some ("Projector"))))::_159_467))
end))))
in (FStar_All.pipe_right _159_468 FStar_List.flatten))
in (let _159_475 = (let _159_471 = (let _159_470 = (let _159_469 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_159_469))
in (_159_470)::(cdecl)::(cid)::projs)
in (FStar_List.append _159_471 ((disc)::[])))
in (let _159_474 = (let _159_473 = (let _159_472 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_159_472))
in (_159_473)::[])
in (FStar_List.append _159_475 _159_474)))))))))))))))))))))))
end))

let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (let _56_593 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _56_580 s -> (match (_56_580) with
| (names, binders, n) -> begin
(let prefix = (match (s) with
| Type_sort -> begin
"@a"
end
| Term_sort -> begin
"@x"
end
| _56_585 -> begin
"@u"
end)
in (let nm = (let _159_484 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _159_484))
in (let names = ((nm, s))::names
in (let b = (let _159_485 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _159_485))
in (names, (b)::binders, (n + 1))))))
end)) (outer_names, [], start)))
in (match (_56_593) with
| (names, binders, n) -> begin
(names, (FStar_List.rev binders), n)
end)))

let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (let _56_598 = (name_binders_inner [] 0 sorts)
in (match (_56_598) with
| (names, binders, n) -> begin
((FStar_List.rev names), binders)
end)))

let termToSmt : term  ->  Prims.string = (fun t -> (let rec aux = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _159_496 = (FStar_List.nth names i)
in (FStar_All.pipe_right _159_496 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _159_498 = (let _159_497 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _159_497 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _159_498))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _56_628 = (name_binders_inner names n sorts)
in (match (_56_628) with
| (names, binders, n) -> begin
(let binders = (FStar_All.pipe_right binders (FStar_String.concat " "))
in (let pats_str = (match (pats) with
| ([]::[]) | ([]) -> begin
""
end
| _56_634 -> begin
(let _159_504 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _159_503 = (let _159_502 = (FStar_List.map (fun p -> (let _159_501 = (aux n names p)
in (FStar_Util.format1 "%s" _159_501))) pats)
in (FStar_String.concat " " _159_502))
in (FStar_Util.format1 "\n:pattern (%s)" _159_503)))))
in (FStar_All.pipe_right _159_504 (FStar_String.concat "\n")))
end)
in (match ((pats, wopt)) with
| (([]::[], None)) | (([], None)) -> begin
(let _159_505 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _159_505))
end
| _56_646 -> begin
(let _159_507 = (aux n names body)
in (let _159_506 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _159_507 _159_506 pats_str)))
end)))
end))
end))
in (aux 0 [] t)))

let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun _56_6 -> (match (_56_6) with
| None -> begin
""
end
| Some (c) -> begin
(let _56_653 = (FStar_Util.splitlines c)
in (match (_56_653) with
| hd::tl -> begin
(let suffix = (match (tl) with
| [] -> begin
""
end
| _56_656 -> begin
"..."
end)
in (FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd suffix))
end))
end))

let rec declToSmt : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(let _159_516 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _56_7 -> (match (_56_7) with
| [] -> begin
""
end
| h::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _159_516))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(let l = (FStar_List.map strSort argsorts)
in (let _159_518 = (caption_to_string c)
in (let _159_517 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _159_518 f (FStar_String.concat " " l) _159_517))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(let _56_684 = (name_binders arg_sorts)
in (match (_56_684) with
| (names, binders) -> begin
(let body = (let _159_519 = (FStar_List.map mkFreeV names)
in (inst _159_519 body))
in (let _159_522 = (caption_to_string c)
in (let _159_521 = (strSort retsort)
in (let _159_520 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _159_522 f (FStar_String.concat " " binders) _159_521 _159_520)))))
end))
end
| Assume (t, c) -> begin
(let _159_524 = (caption_to_string c)
in (let _159_523 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _159_524 _159_523)))
end
| Eval (t) -> begin
(let _159_525 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _159_525))
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
and mkPrelude : Prims.string  ->  Prims.string = (fun z3options -> (let basic = (Prims.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort String)\n(declare-fun String_constr_id (String) Int)\n\n(declare-sort Kind)\n(declare-fun Kind_constr_id (Kind) Int)\n\n(declare-sort Type)\n(declare-fun Type_constr_id (Type) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreKind (Type) Kind)\n(declare-fun PreType (Term) Type)\n(declare-fun Valid (Type) Bool)\n(declare-fun HasKind (Type Kind) Bool)\n(declare-fun HasTypeFuel (Fuel Term Type) Bool)\n(define-fun HasTypeZ ((x Term) (t Type)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Type)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Type))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Type)) (HasTypeZ x t)))\n(declare-fun ApplyEF (Term Fuel) Term)\n(declare-fun ApplyEE (Term Term) Term)\n(declare-fun ApplyET (Term Type) Term)\n(declare-fun ApplyTE (Type Term) Type)\n(declare-fun ApplyTT (Type Type) Type)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsType (Type Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Type)\n(assert (forall ((t Type))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.Precedes ((a Type) (b Type) (t1 Term) (t2 Term)) Type\n(Precedes t1 t2))\n")
in (let constrs = (("String_const", (("String_const_proj_0", Int_sort))::[], String_sort, 0))::(("Kind_type", [], Kind_sort, 0))::(("Kind_arrow", (("Kind_arrow_id", Int_sort))::[], Kind_sort, 1))::(("Kind_uvar", (("Kind_uvar_fst", Int_sort))::[], Kind_sort, 2))::(("Typ_fun", (("Typ_fun_id", Int_sort))::[], Type_sort, 1))::(("Typ_app", (("Typ_app_fst", Type_sort))::(("Typ_app_snd", Type_sort))::[], Type_sort, 2))::(("Typ_dep", (("Typ_dep_fst", Type_sort))::(("Typ_dep_snd", Term_sort))::[], Type_sort, 3))::(("Typ_uvar", (("Typ_uvar_fst", Int_sort))::[], Type_sort, 4))::(("Term_unit", [], Term_sort, 0))::(("BoxInt", (("BoxInt_proj_0", Int_sort))::[], Term_sort, 1))::(("BoxBool", (("BoxBool_proj_0", Bool_sort))::[], Term_sort, 2))::(("BoxString", (("BoxString_proj_0", String_sort))::[], Term_sort, 3))::(("BoxRef", (("BoxRef_proj_0", Ref_sort))::[], Term_sort, 4))::(("Exp_uvar", (("Exp_uvar_fst", Int_sort))::[], Term_sort, 5))::(("LexCons", (("LexCons_0", Term_sort))::(("LexCons_1", Term_sort))::[], Term_sort, 6))::[]
in (let bcons = (let _159_528 = (let _159_527 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _159_527 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _159_528 (FStar_String.concat "\n")))
in (let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat (Prims.strcat basic bcons) lex_ordering))))))

let mk_Kind_type : term = (mkApp ("Kind_type", []))

let mk_Kind_uvar : Prims.int  ->  term = (fun i -> (let _159_533 = (let _159_532 = (let _159_531 = (mkInteger' i)
in (_159_531)::[])
in ("Kind_uvar", _159_532))
in (mkApp _159_533)))

let mk_Typ_app : term  ->  term  ->  term = (fun t1 t2 -> (mkApp ("Typ_app", (t1)::(t2)::[])))

let mk_Typ_dep : term  ->  term  ->  term = (fun t1 t2 -> (mkApp ("Typ_dep", (t1)::(t2)::[])))

let mk_Typ_uvar : Prims.int  ->  term = (fun i -> (let _159_546 = (let _159_545 = (let _159_544 = (mkInteger' i)
in (_159_544)::[])
in ("Typ_uvar", _159_545))
in (mkApp _159_546)))

let mk_Exp_uvar : Prims.int  ->  term = (fun i -> (let _159_551 = (let _159_550 = (let _159_549 = (mkInteger' i)
in (_159_549)::[])
in ("Exp_uvar", _159_550))
in (mkApp _159_551)))

let mk_Term_unit : term = (mkApp ("Term_unit", []))

let boxInt : term  ->  term = (fun t -> (mkApp ("BoxInt", (t)::[])))

let unboxInt : term  ->  term = (fun t -> (mkApp ("BoxInt_proj_0", (t)::[])))

let boxBool : term  ->  term = (fun t -> (mkApp ("BoxBool", (t)::[])))

let unboxBool : term  ->  term = (fun t -> (mkApp ("BoxBool_proj_0", (t)::[])))

let boxString : term  ->  term = (fun t -> (mkApp ("BoxString", (t)::[])))

let unboxString : term  ->  term = (fun t -> (mkApp ("BoxString_proj_0", (t)::[])))

let boxRef : term  ->  term = (fun t -> (mkApp ("BoxRef", (t)::[])))

let unboxRef : term  ->  term = (fun t -> (mkApp ("BoxRef_proj_0", (t)::[])))

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
| _56_724 -> begin
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
| _56_732 -> begin
(Prims.raise FStar_Util.Impos)
end))

let mk_PreKind : term  ->  term = (fun t -> (mkApp ("PreKind", (t)::[])))

let mk_PreType : term  ->  term = (fun t -> (mkApp ("PreType", (t)::[])))

let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_Equality"), _56_747::t1::t2::[]); hash = _56_741; freevars = _56_739}::[]) -> begin
(mkEq (t1, t2))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_disEquality"), _56_766::t1::t2::[]); hash = _56_760; freevars = _56_758}::[]) -> begin
(let _159_582 = (mkEq (t1, t2))
in (mkNot _159_582))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_LessThanOrEqual"), t1::t2::[]); hash = _56_779; freevars = _56_777}::[]) -> begin
(let _159_585 = (let _159_584 = (unboxInt t1)
in (let _159_583 = (unboxInt t2)
in (_159_584, _159_583)))
in (mkLTE _159_585))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_LessThan"), t1::t2::[]); hash = _56_796; freevars = _56_794}::[]) -> begin
(let _159_588 = (let _159_587 = (unboxInt t1)
in (let _159_586 = (unboxInt t2)
in (_159_587, _159_586)))
in (mkLT _159_588))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_GreaterThanOrEqual"), t1::t2::[]); hash = _56_813; freevars = _56_811}::[]) -> begin
(let _159_591 = (let _159_590 = (unboxInt t1)
in (let _159_589 = (unboxInt t2)
in (_159_590, _159_589)))
in (mkGTE _159_591))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_GreaterThan"), t1::t2::[]); hash = _56_830; freevars = _56_828}::[]) -> begin
(let _159_594 = (let _159_593 = (unboxInt t1)
in (let _159_592 = (unboxInt t2)
in (_159_593, _159_592)))
in (mkGT _159_594))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_AmpAmp"), t1::t2::[]); hash = _56_847; freevars = _56_845}::[]) -> begin
(let _159_597 = (let _159_596 = (unboxBool t1)
in (let _159_595 = (unboxBool t2)
in (_159_596, _159_595)))
in (mkAnd _159_597))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_BarBar"), t1::t2::[]); hash = _56_864; freevars = _56_862}::[]) -> begin
(let _159_600 = (let _159_599 = (unboxBool t1)
in (let _159_598 = (unboxBool t2)
in (_159_599, _159_598)))
in (mkOr _159_600))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_Negation"), t::[]); hash = _56_881; freevars = _56_879}::[]) -> begin
(let _159_601 = (unboxBool t)
in (mkNot _159_601))
end
| App (Var ("Prims.b2t"), t::[]) -> begin
(unboxBool t)
end
| _56_899 -> begin
(mkApp ("Valid", (t)::[]))
end))

let mk_HasType : term  ->  term  ->  term = (fun v t -> (mkApp ("HasType", (v)::(t)::[])))

let mk_HasTypeZ : term  ->  term  ->  term = (fun v t -> (mkApp ("HasTypeZ", (v)::(t)::[])))

let mk_IsTyped : term  ->  term = (fun v -> (mkApp ("IsTyped", (v)::[])))

let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v t -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(mk_HasType v t)
end else begin
(mkApp ("HasTypeFuel", (f)::(v)::(t)::[]))
end)

let mk_HasTypeWithFuel : term Prims.option  ->  term  ->  term  ->  term = (fun f v t -> (match (f) with
| None -> begin
(mk_HasType v t)
end
| Some (f) -> begin
(mk_HasTypeFuel f v t)
end))

let mk_Destruct : term  ->  term = (fun v -> (mkApp ("Destruct", (v)::[])))

let mk_HasKind : term  ->  term  ->  term = (fun t k -> (mkApp ("HasKind", (t)::(k)::[])))

let mk_Rank : term  ->  term = (fun x -> (mkApp ("Rank", (x)::[])))

let mk_tester : Prims.string  ->  term  ->  term = (fun n t -> (mkApp ((Prims.strcat "is-" n), (t)::[])))

let mk_ApplyTE : term  ->  term  ->  term = (fun t e -> (mkApp ("ApplyTE", (t)::(e)::[])))

let mk_ApplyTT : term  ->  term  ->  term = (fun t t' -> (mkApp ("ApplyTT", (t)::(t')::[])))

let mk_ApplyET : term  ->  term  ->  term = (fun e t -> (mkApp ("ApplyET", (e)::(t)::[])))

let mk_ApplyEE : term  ->  term  ->  term = (fun e e' -> (mkApp ("ApplyEE", (e)::(e')::[])))

let mk_ApplyEF : term  ->  term  ->  term = (fun e f -> (mkApp ("ApplyEF", (e)::(f)::[])))

let mk_String_const : Prims.int  ->  term = (fun i -> (let _159_660 = (let _159_659 = (let _159_658 = (mkInteger' i)
in (_159_658)::[])
in ("String_const", _159_659))
in (mkApp _159_660)))

let mk_Precedes : term  ->  term  ->  term = (fun x1 x2 -> (let _159_665 = (mkApp ("Precedes", (x1)::(x2)::[]))
in (FStar_All.pipe_right _159_665 mk_Valid)))

let mk_LexCons : term  ->  term  ->  term = (fun x1 x2 -> (mkApp ("LexCons", (x1)::(x2)::[])))

let rec n_fuel : Prims.int  ->  term = (fun n -> if (n = 0) then begin
(mkApp ("ZFuel", []))
end else begin
(let _159_674 = (let _159_673 = (let _159_672 = (n_fuel (n - 1))
in (_159_672)::[])
in ("SFuel", _159_673))
in (mkApp _159_674))
end)

let fuel_2 : term = (n_fuel 2)

let fuel_100 : term = (n_fuel 100)

let mk_and_opt : term Prims.option  ->  term Prims.option  ->  term Prims.option = (fun p1 p2 -> (match ((p1, p2)) with
| (Some (p1), Some (p2)) -> begin
(let _159_679 = (mkAnd (p1, p2))
in Some (_159_679))
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
| hd::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkAnd (p1, p2))) hd tl)
end))

let mk_or_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkFalse
end
| hd::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkOr (p1, p2))) hd tl)
end))

let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "Integer %s" n)
end
| BoundV (n) -> begin
(let _159_696 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "BoundV %s" _159_696))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "FreeV %s" (Prims.fst fv))
end
| App (op, l) -> begin
(let _159_697 = (print_smt_term_list l)
in (FStar_Util.format2 "App %s [ %s ]" (op_to_string op) _159_697))
end
| Quant (qop, l, _56_984, _56_986, t) -> begin
(let _159_699 = (print_smt_term_list_list l)
in (let _159_698 = (print_smt_term t)
in (FStar_Util.format3 "Quant %s %s %s" (qop_to_string qop) _159_699 _159_698)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s t -> (let _159_703 = (print_smt_term t)
in (Prims.strcat (Prims.strcat s "; ") _159_703))) "" l))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _159_708 = (let _159_707 = (print_smt_term_list l)
in (Prims.strcat (Prims.strcat s "; [ ") _159_707))
in (Prims.strcat _159_708 " ] "))) "" l))




