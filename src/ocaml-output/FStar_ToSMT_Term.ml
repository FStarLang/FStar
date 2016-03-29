
open Prims
# 25 "FStar.ToSMT.Term.fst"
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

# 26 "FStar.ToSMT.Term.fst"
let is_Bool_sort = (fun _discr_ -> (match (_discr_) with
| Bool_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 27 "FStar.ToSMT.Term.fst"
let is_Int_sort = (fun _discr_ -> (match (_discr_) with
| Int_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.ToSMT.Term.fst"
let is_Kind_sort = (fun _discr_ -> (match (_discr_) with
| Kind_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 29 "FStar.ToSMT.Term.fst"
let is_Type_sort = (fun _discr_ -> (match (_discr_) with
| Type_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "FStar.ToSMT.Term.fst"
let is_Term_sort = (fun _discr_ -> (match (_discr_) with
| Term_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "FStar.ToSMT.Term.fst"
let is_String_sort = (fun _discr_ -> (match (_discr_) with
| String_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 32 "FStar.ToSMT.Term.fst"
let is_Ref_sort = (fun _discr_ -> (match (_discr_) with
| Ref_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 33 "FStar.ToSMT.Term.fst"
let is_Fuel_sort = (fun _discr_ -> (match (_discr_) with
| Fuel_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "FStar.ToSMT.Term.fst"
let is_Array = (fun _discr_ -> (match (_discr_) with
| Array (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.ToSMT.Term.fst"
let is_Arrow = (fun _discr_ -> (match (_discr_) with
| Arrow (_) -> begin
true
end
| _ -> begin
false
end))

# 36 "FStar.ToSMT.Term.fst"
let is_Sort = (fun _discr_ -> (match (_discr_) with
| Sort (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "FStar.ToSMT.Term.fst"
let ___Array____0 = (fun projectee -> (match (projectee) with
| Array (_37_10) -> begin
_37_10
end))

# 35 "FStar.ToSMT.Term.fst"
let ___Arrow____0 = (fun projectee -> (match (projectee) with
| Arrow (_37_13) -> begin
_37_13
end))

# 36 "FStar.ToSMT.Term.fst"
let ___Sort____0 = (fun projectee -> (match (projectee) with
| Sort (_37_16) -> begin
_37_16
end))

# 38 "FStar.ToSMT.Term.fst"
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
(let _116_54 = (strSort s1)
in (let _116_53 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _116_54 _116_53)))
end
| Arrow (s1, s2) -> begin
(let _116_56 = (strSort s1)
in (let _116_55 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _116_56 _116_55)))
end
| Sort (s) -> begin
s
end))

# 51 "FStar.ToSMT.Term.fst"
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

# 52 "FStar.ToSMT.Term.fst"
let is_True = (fun _discr_ -> (match (_discr_) with
| True (_) -> begin
true
end
| _ -> begin
false
end))

# 53 "FStar.ToSMT.Term.fst"
let is_False = (fun _discr_ -> (match (_discr_) with
| False (_) -> begin
true
end
| _ -> begin
false
end))

# 54 "FStar.ToSMT.Term.fst"
let is_Not = (fun _discr_ -> (match (_discr_) with
| Not (_) -> begin
true
end
| _ -> begin
false
end))

# 55 "FStar.ToSMT.Term.fst"
let is_And = (fun _discr_ -> (match (_discr_) with
| And (_) -> begin
true
end
| _ -> begin
false
end))

# 56 "FStar.ToSMT.Term.fst"
let is_Or = (fun _discr_ -> (match (_discr_) with
| Or (_) -> begin
true
end
| _ -> begin
false
end))

# 57 "FStar.ToSMT.Term.fst"
let is_Imp = (fun _discr_ -> (match (_discr_) with
| Imp (_) -> begin
true
end
| _ -> begin
false
end))

# 58 "FStar.ToSMT.Term.fst"
let is_Iff = (fun _discr_ -> (match (_discr_) with
| Iff (_) -> begin
true
end
| _ -> begin
false
end))

# 59 "FStar.ToSMT.Term.fst"
let is_Eq = (fun _discr_ -> (match (_discr_) with
| Eq (_) -> begin
true
end
| _ -> begin
false
end))

# 60 "FStar.ToSMT.Term.fst"
let is_LT = (fun _discr_ -> (match (_discr_) with
| LT (_) -> begin
true
end
| _ -> begin
false
end))

# 61 "FStar.ToSMT.Term.fst"
let is_LTE = (fun _discr_ -> (match (_discr_) with
| LTE (_) -> begin
true
end
| _ -> begin
false
end))

# 62 "FStar.ToSMT.Term.fst"
let is_GT = (fun _discr_ -> (match (_discr_) with
| GT (_) -> begin
true
end
| _ -> begin
false
end))

# 63 "FStar.ToSMT.Term.fst"
let is_GTE = (fun _discr_ -> (match (_discr_) with
| GTE (_) -> begin
true
end
| _ -> begin
false
end))

# 64 "FStar.ToSMT.Term.fst"
let is_Add = (fun _discr_ -> (match (_discr_) with
| Add (_) -> begin
true
end
| _ -> begin
false
end))

# 65 "FStar.ToSMT.Term.fst"
let is_Sub = (fun _discr_ -> (match (_discr_) with
| Sub (_) -> begin
true
end
| _ -> begin
false
end))

# 66 "FStar.ToSMT.Term.fst"
let is_Div = (fun _discr_ -> (match (_discr_) with
| Div (_) -> begin
true
end
| _ -> begin
false
end))

# 67 "FStar.ToSMT.Term.fst"
let is_Mul = (fun _discr_ -> (match (_discr_) with
| Mul (_) -> begin
true
end
| _ -> begin
false
end))

# 68 "FStar.ToSMT.Term.fst"
let is_Minus = (fun _discr_ -> (match (_discr_) with
| Minus (_) -> begin
true
end
| _ -> begin
false
end))

# 69 "FStar.ToSMT.Term.fst"
let is_Mod = (fun _discr_ -> (match (_discr_) with
| Mod (_) -> begin
true
end
| _ -> begin
false
end))

# 70 "FStar.ToSMT.Term.fst"
let is_ITE = (fun _discr_ -> (match (_discr_) with
| ITE (_) -> begin
true
end
| _ -> begin
false
end))

# 71 "FStar.ToSMT.Term.fst"
let is_Var = (fun _discr_ -> (match (_discr_) with
| Var (_) -> begin
true
end
| _ -> begin
false
end))

# 71 "FStar.ToSMT.Term.fst"
let ___Var____0 = (fun projectee -> (match (projectee) with
| Var (_37_38) -> begin
_37_38
end))

# 73 "FStar.ToSMT.Term.fst"
type qop =
| Forall
| Exists

# 74 "FStar.ToSMT.Term.fst"
let is_Forall = (fun _discr_ -> (match (_discr_) with
| Forall (_) -> begin
true
end
| _ -> begin
false
end))

# 75 "FStar.ToSMT.Term.fst"
let is_Exists = (fun _discr_ -> (match (_discr_) with
| Exists (_) -> begin
true
end
| _ -> begin
false
end))

# 78 "FStar.ToSMT.Term.fst"
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

# 79 "FStar.ToSMT.Term.fst"
let is_Integer = (fun _discr_ -> (match (_discr_) with
| Integer (_) -> begin
true
end
| _ -> begin
false
end))

# 80 "FStar.ToSMT.Term.fst"
let is_BoundV = (fun _discr_ -> (match (_discr_) with
| BoundV (_) -> begin
true
end
| _ -> begin
false
end))

# 81 "FStar.ToSMT.Term.fst"
let is_FreeV = (fun _discr_ -> (match (_discr_) with
| FreeV (_) -> begin
true
end
| _ -> begin
false
end))

# 82 "FStar.ToSMT.Term.fst"
let is_App = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))

# 83 "FStar.ToSMT.Term.fst"
let is_Quant = (fun _discr_ -> (match (_discr_) with
| Quant (_) -> begin
true
end
| _ -> begin
false
end))

# 89 "FStar.ToSMT.Term.fst"
let is_Mkterm : term  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkterm"))))

# 79 "FStar.ToSMT.Term.fst"
let ___Integer____0 = (fun projectee -> (match (projectee) with
| Integer (_37_44) -> begin
_37_44
end))

# 80 "FStar.ToSMT.Term.fst"
let ___BoundV____0 = (fun projectee -> (match (projectee) with
| BoundV (_37_47) -> begin
_37_47
end))

# 81 "FStar.ToSMT.Term.fst"
let ___FreeV____0 = (fun projectee -> (match (projectee) with
| FreeV (_37_50) -> begin
_37_50
end))

# 82 "FStar.ToSMT.Term.fst"
let ___App____0 = (fun projectee -> (match (projectee) with
| App (_37_53) -> begin
_37_53
end))

# 83 "FStar.ToSMT.Term.fst"
let ___Quant____0 = (fun projectee -> (match (projectee) with
| Quant (_37_56) -> begin
_37_56
end))

# 94 "FStar.ToSMT.Term.fst"
type caption =
Prims.string Prims.option

# 95 "FStar.ToSMT.Term.fst"
type binders =
(Prims.string * sort) Prims.list

# 96 "FStar.ToSMT.Term.fst"
type projector =
(Prims.string * sort)

# 97 "FStar.ToSMT.Term.fst"
type constructor_t =
(Prims.string * projector Prims.list * sort * Prims.int)

# 98 "FStar.ToSMT.Term.fst"
type constructors =
constructor_t Prims.list

# 99 "FStar.ToSMT.Term.fst"
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

# 100 "FStar.ToSMT.Term.fst"
let is_DefPrelude = (fun _discr_ -> (match (_discr_) with
| DefPrelude (_) -> begin
true
end
| _ -> begin
false
end))

# 101 "FStar.ToSMT.Term.fst"
let is_DeclFun = (fun _discr_ -> (match (_discr_) with
| DeclFun (_) -> begin
true
end
| _ -> begin
false
end))

# 102 "FStar.ToSMT.Term.fst"
let is_DefineFun = (fun _discr_ -> (match (_discr_) with
| DefineFun (_) -> begin
true
end
| _ -> begin
false
end))

# 103 "FStar.ToSMT.Term.fst"
let is_Assume = (fun _discr_ -> (match (_discr_) with
| Assume (_) -> begin
true
end
| _ -> begin
false
end))

# 104 "FStar.ToSMT.Term.fst"
let is_Caption = (fun _discr_ -> (match (_discr_) with
| Caption (_) -> begin
true
end
| _ -> begin
false
end))

# 105 "FStar.ToSMT.Term.fst"
let is_Eval = (fun _discr_ -> (match (_discr_) with
| Eval (_) -> begin
true
end
| _ -> begin
false
end))

# 106 "FStar.ToSMT.Term.fst"
let is_Echo = (fun _discr_ -> (match (_discr_) with
| Echo (_) -> begin
true
end
| _ -> begin
false
end))

# 107 "FStar.ToSMT.Term.fst"
let is_Push = (fun _discr_ -> (match (_discr_) with
| Push (_) -> begin
true
end
| _ -> begin
false
end))

# 108 "FStar.ToSMT.Term.fst"
let is_Pop = (fun _discr_ -> (match (_discr_) with
| Pop (_) -> begin
true
end
| _ -> begin
false
end))

# 109 "FStar.ToSMT.Term.fst"
let is_CheckSat = (fun _discr_ -> (match (_discr_) with
| CheckSat (_) -> begin
true
end
| _ -> begin
false
end))

# 101 "FStar.ToSMT.Term.fst"
let ___DeclFun____0 = (fun projectee -> (match (projectee) with
| DeclFun (_37_60) -> begin
_37_60
end))

# 102 "FStar.ToSMT.Term.fst"
let ___DefineFun____0 = (fun projectee -> (match (projectee) with
| DefineFun (_37_63) -> begin
_37_63
end))

# 103 "FStar.ToSMT.Term.fst"
let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_37_66) -> begin
_37_66
end))

# 104 "FStar.ToSMT.Term.fst"
let ___Caption____0 = (fun projectee -> (match (projectee) with
| Caption (_37_69) -> begin
_37_69
end))

# 105 "FStar.ToSMT.Term.fst"
let ___Eval____0 = (fun projectee -> (match (projectee) with
| Eval (_37_72) -> begin
_37_72
end))

# 106 "FStar.ToSMT.Term.fst"
let ___Echo____0 = (fun projectee -> (match (projectee) with
| Echo (_37_75) -> begin
_37_75
end))

# 110 "FStar.ToSMT.Term.fst"
type decls_t =
decl Prims.list

# 194 "FStar.ToSMT.Term.fst"
let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> ((Prims.fst x) = (Prims.fst y)))

# 195 "FStar.ToSMT.Term.fst"
let fv_sort = (fun x -> (Prims.snd x))

# 196 "FStar.ToSMT.Term.fst"
let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match ((x.tm, y.tm)) with
| (FreeV (x), FreeV (y)) -> begin
(fv_eq x y)
end
| _37_87 -> begin
false
end))

# 199 "FStar.ToSMT.Term.fst"
let freevar_sort : term  ->  sort = (fun _37_1 -> (match (_37_1) with
| {tm = FreeV (x); hash = _37_92; freevars = _37_90} -> begin
(fv_sort x)
end
| _37_97 -> begin
(FStar_All.failwith "impossible")
end))

# 202 "FStar.ToSMT.Term.fst"
let fv_of_term : term  ->  fv = (fun _37_2 -> (match (_37_2) with
| {tm = FreeV (fv); hash = _37_102; freevars = _37_100} -> begin
fv
end
| _37_107 -> begin
(FStar_All.failwith "impossible")
end))

# 205 "FStar.ToSMT.Term.fst"
let rec freevars : term  ->  fv Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (_37_118, tms) -> begin
(FStar_List.collect freevars tms)
end
| Quant (_37_123, _37_125, _37_127, _37_129, t) -> begin
(freevars t)
end))

# 213 "FStar.ToSMT.Term.fst"
let free_variables : term  ->  fvs = (fun t -> (match ((FStar_ST.read t.freevars)) with
| Some (b) -> begin
b
end
| None -> begin
(
# 216 "FStar.ToSMT.Term.fst"
let fvs = (let _116_277 = (freevars t)
in (FStar_Util.remove_dups fv_eq _116_277))
in (
# 217 "FStar.ToSMT.Term.fst"
let _37_138 = (FStar_ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))

# 223 "FStar.ToSMT.Term.fst"
let qop_to_string : qop  ->  Prims.string = (fun _37_3 -> (match (_37_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))

# 227 "FStar.ToSMT.Term.fst"
let op_to_string : op  ->  Prims.string = (fun _37_4 -> (match (_37_4) with
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

# 249 "FStar.ToSMT.Term.fst"
let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun _37_5 -> (match (_37_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _116_284 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _116_284))
end))

# 253 "FStar.ToSMT.Term.fst"
let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _116_287 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _116_287))
end
| FreeV (x) -> begin
(let _116_288 = (strSort (Prims.snd x))
in (Prims.strcat (Prims.strcat (Prims.fst x) ":") _116_288))
end
| App (op, tms) -> begin
(let _116_292 = (let _116_291 = (let _116_290 = (FStar_List.map (fun t -> t.hash) tms)
in (FStar_All.pipe_right _116_290 (FStar_String.concat " ")))
in (Prims.strcat (Prims.strcat "(" (op_to_string op)) _116_291))
in (Prims.strcat _116_292 ")"))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _116_300 = (let _116_293 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _116_293 (FStar_String.concat " ")))
in (let _116_299 = (weightToSmt wopt)
in (let _116_298 = (let _116_297 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _116_296 = (FStar_List.map (fun p -> p.hash) pats)
in (FStar_All.pipe_right _116_296 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _116_297 (FStar_String.concat "; ")))
in (FStar_Util.format5 "(%s (%s)(! %s %s %s))" (qop_to_string qop) _116_300 body.hash _116_299 _116_298))))
end))

# 267 "FStar.ToSMT.Term.fst"
let __all_terms : term FStar_Util.smap FStar_ST.ref = (let _116_301 = (FStar_Util.smap_create 10000)
in (FStar_ST.alloc _116_301))

# 268 "FStar.ToSMT.Term.fst"
let all_terms : Prims.unit  ->  term FStar_Util.smap = (fun _37_190 -> (match (()) with
| () -> begin
(FStar_ST.read __all_terms)
end))

# 269 "FStar.ToSMT.Term.fst"
let mk : term'  ->  term = (fun t -> (
# 270 "FStar.ToSMT.Term.fst"
let key = (hash_of_term' t)
in (match ((let _116_306 = (all_terms ())
in (FStar_Util.smap_try_find _116_306 key))) with
| Some (tm) -> begin
tm
end
| None -> begin
(
# 274 "FStar.ToSMT.Term.fst"
let tm = (let _116_307 = (FStar_Util.mk_ref None)
in {tm = t; hash = key; freevars = _116_307})
in (
# 275 "FStar.ToSMT.Term.fst"
let _37_197 = (let _116_308 = (all_terms ())
in (FStar_Util.smap_add _116_308 key tm))
in tm))
end)))

# 278 "FStar.ToSMT.Term.fst"
let mkTrue : term = (mk (App ((True, []))))

# 279 "FStar.ToSMT.Term.fst"
let mkFalse : term = (mk (App ((False, []))))

# 280 "FStar.ToSMT.Term.fst"
let mkInteger : Prims.string  ->  term = (fun i -> (mk (Integer (i))))

# 281 "FStar.ToSMT.Term.fst"
let mkInteger32 : Prims.int32  ->  term = (fun i -> (mkInteger (FStar_Util.string_of_int32 i)))

# 282 "FStar.ToSMT.Term.fst"
let mkInteger' : Prims.int  ->  term = (fun i -> (let _116_315 = (FStar_Util.string_of_int i)
in (mkInteger _116_315)))

# 283 "FStar.ToSMT.Term.fst"
let mkBoundV : Prims.int  ->  term = (fun i -> (mk (BoundV (i))))

# 284 "FStar.ToSMT.Term.fst"
let mkFreeV : (Prims.string * sort)  ->  term = (fun x -> (mk (FreeV (x))))

# 285 "FStar.ToSMT.Term.fst"
let mkApp' : (op * term Prims.list)  ->  term = (fun f -> (mk (App (f))))

# 286 "FStar.ToSMT.Term.fst"
let mkApp : (Prims.string * term Prims.list)  ->  term = (fun _37_207 -> (match (_37_207) with
| (s, args) -> begin
(mk (App ((Var (s), args))))
end))

# 287 "FStar.ToSMT.Term.fst"
let mkNot : term  ->  term = (fun t -> (match (t.tm) with
| App (True, _37_211) -> begin
mkFalse
end
| App (False, _37_216) -> begin
mkTrue
end
| _37_220 -> begin
(mkApp' (Not, (t)::[]))
end))

# 291 "FStar.ToSMT.Term.fst"
let mkAnd : (term * term)  ->  term = (fun _37_223 -> (match (_37_223) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (App (True, _37_226), _37_230) -> begin
t2
end
| (_37_233, App (True, _37_236)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
mkFalse
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' (And, (FStar_List.append ts1 ts2)))
end
| (_37_266, App (And, ts2)) -> begin
(mkApp' (And, (t1)::ts2))
end
| (App (And, ts1), _37_277) -> begin
(mkApp' (And, (FStar_List.append ts1 ((t2)::[]))))
end
| _37_280 -> begin
(mkApp' (And, (t1)::(t2)::[]))
end)
end))

# 300 "FStar.ToSMT.Term.fst"
let mkOr : (term * term)  ->  term = (fun _37_283 -> (match (_37_283) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
mkTrue
end
| (App (False, _37_302), _37_306) -> begin
t2
end
| (_37_309, App (False, _37_312)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' (Or, (FStar_List.append ts1 ts2)))
end
| (_37_326, App (Or, ts2)) -> begin
(mkApp' (Or, (t1)::ts2))
end
| (App (Or, ts1), _37_337) -> begin
(mkApp' (Or, (FStar_List.append ts1 ((t2)::[]))))
end
| _37_340 -> begin
(mkApp' (Or, (t1)::(t2)::[]))
end)
end))

# 309 "FStar.ToSMT.Term.fst"
let mkImp : (term * term)  ->  term = (fun _37_343 -> (match (_37_343) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (_37_345, App (True, _37_348)) -> begin
mkTrue
end
| (App (True, _37_354), _37_358) -> begin
t2
end
| (_37_361, App (Imp, t1'::t2'::[])) -> begin
(let _116_334 = (let _116_333 = (let _116_332 = (mkAnd (t1, t1'))
in (_116_332)::(t2')::[])
in (Imp, _116_333))
in (mkApp' _116_334))
end
| _37_370 -> begin
(mkApp' (Imp, (t1)::(t2)::[]))
end)
end))

# 315 "FStar.ToSMT.Term.fst"
let mk_bin_op : op  ->  (term * term)  ->  term = (fun op _37_374 -> (match (_37_374) with
| (t1, t2) -> begin
(mkApp' (op, (t1)::(t2)::[]))
end))

# 316 "FStar.ToSMT.Term.fst"
let mkMinus : term  ->  term = (fun t -> (mkApp' (Minus, (t)::[])))

# 317 "FStar.ToSMT.Term.fst"
let mkIff : (term * term)  ->  term = (mk_bin_op Iff)

# 318 "FStar.ToSMT.Term.fst"
let mkEq : (term * term)  ->  term = (mk_bin_op Eq)

# 319 "FStar.ToSMT.Term.fst"
let mkLT : (term * term)  ->  term = (mk_bin_op LT)

# 320 "FStar.ToSMT.Term.fst"
let mkLTE : (term * term)  ->  term = (mk_bin_op LTE)

# 321 "FStar.ToSMT.Term.fst"
let mkGT : (term * term)  ->  term = (mk_bin_op GT)

# 322 "FStar.ToSMT.Term.fst"
let mkGTE : (term * term)  ->  term = (mk_bin_op GTE)

# 323 "FStar.ToSMT.Term.fst"
let mkAdd : (term * term)  ->  term = (mk_bin_op Add)

# 324 "FStar.ToSMT.Term.fst"
let mkSub : (term * term)  ->  term = (mk_bin_op Sub)

# 325 "FStar.ToSMT.Term.fst"
let mkDiv : (term * term)  ->  term = (mk_bin_op Div)

# 326 "FStar.ToSMT.Term.fst"
let mkMul : (term * term)  ->  term = (mk_bin_op Mul)

# 327 "FStar.ToSMT.Term.fst"
let mkMod : (term * term)  ->  term = (mk_bin_op Mod)

# 328 "FStar.ToSMT.Term.fst"
let mkITE : (term * term * term)  ->  term = (fun _37_379 -> (match (_37_379) with
| (t1, t2, t3) -> begin
(match ((t2.tm, t3.tm)) with
| (App (True, _37_382), App (True, _37_387)) -> begin
mkTrue
end
| (App (True, _37_393), _37_397) -> begin
(let _116_355 = (let _116_354 = (mkNot t1)
in (_116_354, t3))
in (mkImp _116_355))
end
| (_37_400, App (True, _37_403)) -> begin
(mkImp (t1, t2))
end
| (_37_408, _37_410) -> begin
(mkApp' (ITE, (t1)::(t2)::(t3)::[]))
end)
end))

# 334 "FStar.ToSMT.Term.fst"
let mkCases : term Prims.list  ->  term = (fun t -> (match (t) with
| [] -> begin
(FStar_All.failwith "Impos")
end
| hd::tl -> begin
(FStar_List.fold_left (fun out t -> (mkAnd (out, t))) hd tl)
end))

# 338 "FStar.ToSMT.Term.fst"
let mkQuant : (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _37_424 -> (match (_37_424) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = 0) then begin
body
end else begin
(match (body.tm) with
| App (True, _37_427) -> begin
body
end
| _37_431 -> begin
(mk (Quant ((qop, pats, wopt, vars, body))))
end)
end
end))

# 347 "FStar.ToSMT.Term.fst"
let abstr : fvs  ->  term  ->  term = (fun fvs t -> (
# 348 "FStar.ToSMT.Term.fst"
let nvars = (FStar_List.length fvs)
in (
# 349 "FStar.ToSMT.Term.fst"
let index_of = (fun fv -> (match ((FStar_Util.try_find_index (fv_eq fv) fvs)) with
| None -> begin
None
end
| Some (i) -> begin
Some ((nvars - (i + 1)))
end))
in (
# 352 "FStar.ToSMT.Term.fst"
let rec aux = (fun ix t -> (match ((FStar_ST.read t.freevars)) with
| Some ([]) -> begin
t
end
| _37_446 -> begin
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
(let _116_373 = (let _116_372 = (FStar_List.map (aux ix) tms)
in (op, _116_372))
in (mkApp' _116_373))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(
# 366 "FStar.ToSMT.Term.fst"
let n = (FStar_List.length vars)
in (let _116_376 = (let _116_375 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _116_374 = (aux (ix + n) body)
in (qop, _116_375, wopt, vars, _116_374)))
in (mkQuant _116_376)))
end)
end))
in (aux 0 t)))))

# 371 "FStar.ToSMT.Term.fst"
let inst : term Prims.list  ->  term  ->  term = (fun tms t -> (
# 372 "FStar.ToSMT.Term.fst"
let n = (FStar_List.length tms)
in (
# 373 "FStar.ToSMT.Term.fst"
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
(let _116_386 = (let _116_385 = (FStar_List.map (aux shift) tms)
in (op, _116_385))
in (mkApp' _116_386))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(
# 382 "FStar.ToSMT.Term.fst"
let m = (FStar_List.length vars)
in (
# 383 "FStar.ToSMT.Term.fst"
let shift = (shift + m)
in (let _116_389 = (let _116_388 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _116_387 = (aux shift body)
in (qop, _116_388, wopt, vars, _116_387)))
in (mkQuant _116_389))))
end))
in (aux 0 t))))

# 387 "FStar.ToSMT.Term.fst"
let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  term = (fun _37_502 -> (match (_37_502) with
| (qop, pats, wopt, vars, body) -> begin
(let _116_395 = (let _116_394 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _116_393 = (FStar_List.map fv_sort vars)
in (let _116_392 = (abstr vars body)
in (qop, _116_394, wopt, _116_393, _116_392))))
in (mkQuant _116_395))
end))

# 388 "FStar.ToSMT.Term.fst"
let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _37_507 -> (match (_37_507) with
| (pats, wopt, sorts, body) -> begin
(mkQuant (Forall, pats, wopt, sorts, body))
end))

# 389 "FStar.ToSMT.Term.fst"
let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  term = (fun _37_512 -> (match (_37_512) with
| (pats, wopt, vars, body) -> begin
(mkQuant' (Forall, pats, wopt, vars, body))
end))

# 392 "FStar.ToSMT.Term.fst"
let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _37_516 -> (match (_37_516) with
| (pats, vars, body) -> begin
(mkQuant' (Forall, pats, None, vars, body))
end))

# 393 "FStar.ToSMT.Term.fst"
let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _37_520 -> (match (_37_520) with
| (pats, vars, body) -> begin
(mkQuant' (Exists, pats, None, vars, body))
end))

# 394 "FStar.ToSMT.Term.fst"
let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun _37_526 -> (match (_37_526) with
| (nm, vars, s, tm, c) -> begin
(let _116_408 = (let _116_407 = (FStar_List.map fv_sort vars)
in (let _116_406 = (abstr vars tm)
in (nm, _116_407, s, _116_406, c)))
in DefineFun (_116_408))
end))

# 395 "FStar.ToSMT.Term.fst"
let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _116_411 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _116_411)))

# 396 "FStar.ToSMT.Term.fst"
let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun _37_530 id -> (match (_37_530) with
| (tok_name, sort) -> begin
(let _116_424 = (let _116_423 = (let _116_422 = (let _116_421 = (mkInteger' id)
in (let _116_420 = (let _116_419 = (let _116_418 = (constr_id_of_sort sort)
in (let _116_417 = (let _116_416 = (mkApp (tok_name, []))
in (_116_416)::[])
in (_116_418, _116_417)))
in (mkApp _116_419))
in (_116_421, _116_420)))
in (mkEq _116_422))
in (_116_423, Some ("fresh token")))
in Assume (_116_424))
end))

# 399 "FStar.ToSMT.Term.fst"
let constructor_to_decl : constructor_t  ->  decls_t = (fun _37_536 -> (match (_37_536) with
| (name, projectors, sort, id) -> begin
(
# 400 "FStar.ToSMT.Term.fst"
let id = (FStar_Util.string_of_int id)
in (
# 401 "FStar.ToSMT.Term.fst"
let cdecl = (let _116_428 = (let _116_427 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in (name, _116_427, sort, Some ("Constructor")))
in DeclFun (_116_428))
in (
# 402 "FStar.ToSMT.Term.fst"
let n_bvars = (FStar_List.length projectors)
in (
# 403 "FStar.ToSMT.Term.fst"
let bvar_name = (fun i -> (let _116_431 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _116_431)))
in (
# 404 "FStar.ToSMT.Term.fst"
let bvar_index = (fun i -> (n_bvars - (i + 1)))
in (
# 405 "FStar.ToSMT.Term.fst"
let bvar = (fun i s -> (let _116_439 = (let _116_438 = (bvar_name i)
in (_116_438, s))
in (mkFreeV _116_439)))
in (
# 406 "FStar.ToSMT.Term.fst"
let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _37_551 -> (match (_37_551) with
| (_37_549, s) -> begin
(bvar i s)
end))))
in (
# 407 "FStar.ToSMT.Term.fst"
let bvar_names = (FStar_List.map fv_of_term bvars)
in (
# 408 "FStar.ToSMT.Term.fst"
let capp = (mkApp (name, bvars))
in (
# 409 "FStar.ToSMT.Term.fst"
let cid_app = (let _116_443 = (let _116_442 = (constr_id_of_sort sort)
in (_116_442, (capp)::[]))
in (mkApp _116_443))
in (
# 410 "FStar.ToSMT.Term.fst"
let cid = (let _116_449 = (let _116_448 = (let _116_447 = (let _116_446 = (let _116_445 = (let _116_444 = (mkInteger id)
in (_116_444, cid_app))
in (mkEq _116_445))
in (((capp)::[])::[], bvar_names, _116_446))
in (mkForall _116_447))
in (_116_448, Some ("Constructor distinct")))
in Assume (_116_449))
in (
# 411 "FStar.ToSMT.Term.fst"
let disc_name = (Prims.strcat "is-" name)
in (
# 412 "FStar.ToSMT.Term.fst"
let xfv = ("x", sort)
in (
# 413 "FStar.ToSMT.Term.fst"
let xx = (mkFreeV xfv)
in (
# 414 "FStar.ToSMT.Term.fst"
let disc_eq = (let _116_454 = (let _116_453 = (let _116_451 = (let _116_450 = (constr_id_of_sort sort)
in (_116_450, (xx)::[]))
in (mkApp _116_451))
in (let _116_452 = (mkInteger id)
in (_116_453, _116_452)))
in (mkEq _116_454))
in (
# 415 "FStar.ToSMT.Term.fst"
let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _37_563 -> (match (_37_563) with
| (proj, s) -> begin
(mkApp (proj, (xx)::[]))
end))))
in (
# 416 "FStar.ToSMT.Term.fst"
let disc_inv_body = (let _116_457 = (let _116_456 = (mkApp (name, proj_terms))
in (xx, _116_456))
in (mkEq _116_457))
in (
# 417 "FStar.ToSMT.Term.fst"
let disc_ax = (mkAnd (disc_eq, disc_inv_body))
in (
# 418 "FStar.ToSMT.Term.fst"
let disc = (mkDefineFun (disc_name, (xfv)::[], Bool_sort, disc_ax, Some ("Discriminator definition")))
in (
# 421 "FStar.ToSMT.Term.fst"
let projs = (let _116_468 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _37_571 -> (match (_37_571) with
| (name, s) -> begin
(
# 422 "FStar.ToSMT.Term.fst"
let cproj_app = (mkApp (name, (capp)::[]))
in (let _116_467 = (let _116_466 = (let _116_465 = (let _116_464 = (let _116_463 = (let _116_462 = (let _116_461 = (let _116_460 = (bvar i s)
in (cproj_app, _116_460))
in (mkEq _116_461))
in (((capp)::[])::[], bvar_names, _116_462))
in (mkForall _116_463))
in (_116_464, Some ("Projection inverse")))
in Assume (_116_465))
in (_116_466)::[])
in (DeclFun ((name, (sort)::[], s, Some ("Projector"))))::_116_467))
end))))
in (FStar_All.pipe_right _116_468 FStar_List.flatten))
in (let _116_475 = (let _116_471 = (let _116_470 = (let _116_469 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_116_469))
in (_116_470)::(cdecl)::(cid)::projs)
in (FStar_List.append _116_471 ((disc)::[])))
in (let _116_474 = (let _116_473 = (let _116_472 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_116_472))
in (_116_473)::[])
in (FStar_List.append _116_475 _116_474)))))))))))))))))))))))
end))

# 431 "FStar.ToSMT.Term.fst"
let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (
# 432 "FStar.ToSMT.Term.fst"
let _37_593 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _37_580 s -> (match (_37_580) with
| (names, binders, n) -> begin
(
# 433 "FStar.ToSMT.Term.fst"
let prefix = (match (s) with
| Type_sort -> begin
"@a"
end
| Term_sort -> begin
"@x"
end
| _37_585 -> begin
"@u"
end)
in (
# 437 "FStar.ToSMT.Term.fst"
let nm = (let _116_484 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _116_484))
in (
# 438 "FStar.ToSMT.Term.fst"
let names = ((nm, s))::names
in (
# 439 "FStar.ToSMT.Term.fst"
let b = (let _116_485 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _116_485))
in (names, (b)::binders, (n + 1))))))
end)) (outer_names, [], start)))
in (match (_37_593) with
| (names, binders, n) -> begin
(names, (FStar_List.rev binders), n)
end)))

# 444 "FStar.ToSMT.Term.fst"
let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (
# 445 "FStar.ToSMT.Term.fst"
let _37_598 = (name_binders_inner [] 0 sorts)
in (match (_37_598) with
| (names, binders, n) -> begin
((FStar_List.rev names), binders)
end)))

# 448 "FStar.ToSMT.Term.fst"
let termToSmt : term  ->  Prims.string = (fun t -> (
# 449 "FStar.ToSMT.Term.fst"
let rec aux = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _116_496 = (FStar_List.nth names i)
in (FStar_All.pipe_right _116_496 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _116_498 = (let _116_497 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _116_497 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _116_498))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(
# 457 "FStar.ToSMT.Term.fst"
let _37_628 = (name_binders_inner names n sorts)
in (match (_37_628) with
| (names, binders, n) -> begin
(
# 458 "FStar.ToSMT.Term.fst"
let binders = (FStar_All.pipe_right binders (FStar_String.concat " "))
in (
# 459 "FStar.ToSMT.Term.fst"
let pats_str = (match (pats) with
| ([]::[]) | ([]) -> begin
""
end
| _37_634 -> begin
(let _116_504 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _116_503 = (let _116_502 = (FStar_List.map (fun p -> (let _116_501 = (aux n names p)
in (FStar_Util.format1 "%s" _116_501))) pats)
in (FStar_String.concat " " _116_502))
in (FStar_Util.format1 "\n:pattern (%s)" _116_503)))))
in (FStar_All.pipe_right _116_504 (FStar_String.concat "\n")))
end)
in (match ((pats, wopt)) with
| (([]::[], None)) | (([], None)) -> begin
(let _116_505 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _116_505))
end
| _37_646 -> begin
(let _116_507 = (aux n names body)
in (let _116_506 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _116_507 _116_506 pats_str)))
end)))
end))
end))
in (aux 0 [] t)))

# 471 "FStar.ToSMT.Term.fst"
let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun _37_6 -> (match (_37_6) with
| None -> begin
""
end
| Some (c) -> begin
(
# 474 "FStar.ToSMT.Term.fst"
let _37_653 = (FStar_Util.splitlines c)
in (match (_37_653) with
| hd::tl -> begin
(
# 475 "FStar.ToSMT.Term.fst"
let suffix = (match (tl) with
| [] -> begin
""
end
| _37_656 -> begin
"..."
end)
in (FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd suffix))
end))
end))

# 480 "FStar.ToSMT.Term.fst"
let rec declToSmt : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(let _116_516 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _37_7 -> (match (_37_7) with
| [] -> begin
""
end
| h::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _116_516))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(
# 485 "FStar.ToSMT.Term.fst"
let l = (FStar_List.map strSort argsorts)
in (let _116_518 = (caption_to_string c)
in (let _116_517 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _116_518 f (FStar_String.concat " " l) _116_517))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(
# 488 "FStar.ToSMT.Term.fst"
let _37_684 = (name_binders arg_sorts)
in (match (_37_684) with
| (names, binders) -> begin
(
# 489 "FStar.ToSMT.Term.fst"
let body = (let _116_519 = (FStar_List.map mkFreeV names)
in (inst _116_519 body))
in (let _116_522 = (caption_to_string c)
in (let _116_521 = (strSort retsort)
in (let _116_520 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _116_522 f (FStar_String.concat " " binders) _116_521 _116_520)))))
end))
end
| Assume (t, c) -> begin
(let _116_524 = (caption_to_string c)
in (let _116_523 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _116_524 _116_523)))
end
| Eval (t) -> begin
(let _116_525 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _116_525))
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
and mkPrelude : Prims.string  ->  Prims.string = (fun z3options -> (
# 502 "FStar.ToSMT.Term.fst"
let basic = (Prims.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort String)\n(declare-fun String_constr_id (String) Int)\n\n(declare-sort Kind)\n(declare-fun Kind_constr_id (Kind) Int)\n\n(declare-sort Type)\n(declare-fun Type_constr_id (Type) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreKind (Type) Kind)\n(declare-fun PreType (Term) Type)\n(declare-fun Valid (Type) Bool)\n(declare-fun HasKind (Type Kind) Bool)\n(declare-fun HasTypeFuel (Fuel Term Type) Bool)\n(define-fun HasTypeZ ((x Term) (t Type)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Type)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Type))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Type)) (HasTypeZ x t)))\n(declare-fun ApplyEF (Term Fuel) Term)\n(declare-fun ApplyEE (Term Term) Term)\n(declare-fun ApplyET (Term Type) Term)\n(declare-fun ApplyTE (Type Term) Type)\n(declare-fun ApplyTT (Type Type) Type)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsType (Type Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Type)\n(assert (forall ((t Type))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.Precedes ((a Type) (b Type) (t1 Term) (t2 Term)) Type\n(Precedes t1 t2))\n")
in (
# 559 "FStar.ToSMT.Term.fst"
let constrs = (("String_const", (("String_const_proj_0", Int_sort))::[], String_sort, 0))::(("Kind_type", [], Kind_sort, 0))::(("Kind_arrow", (("Kind_arrow_id", Int_sort))::[], Kind_sort, 1))::(("Kind_uvar", (("Kind_uvar_fst", Int_sort))::[], Kind_sort, 2))::(("Typ_fun", (("Typ_fun_id", Int_sort))::[], Type_sort, 1))::(("Typ_app", (("Typ_app_fst", Type_sort))::(("Typ_app_snd", Type_sort))::[], Type_sort, 2))::(("Typ_dep", (("Typ_dep_fst", Type_sort))::(("Typ_dep_snd", Term_sort))::[], Type_sort, 3))::(("Typ_uvar", (("Typ_uvar_fst", Int_sort))::[], Type_sort, 4))::(("Term_unit", [], Term_sort, 0))::(("BoxInt", (("BoxInt_proj_0", Int_sort))::[], Term_sort, 1))::(("BoxBool", (("BoxBool_proj_0", Bool_sort))::[], Term_sort, 2))::(("BoxString", (("BoxString_proj_0", String_sort))::[], Term_sort, 3))::(("BoxRef", (("BoxRef_proj_0", Ref_sort))::[], Term_sort, 4))::(("Exp_uvar", (("Exp_uvar_fst", Int_sort))::[], Term_sort, 5))::(("LexCons", (("LexCons_0", Term_sort))::(("LexCons_1", Term_sort))::[], Term_sort, 6))::[]
in (
# 576 "FStar.ToSMT.Term.fst"
let bcons = (let _116_528 = (let _116_527 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _116_527 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _116_528 (FStar_String.concat "\n")))
in (
# 577 "FStar.ToSMT.Term.fst"
let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat (Prims.strcat basic bcons) lex_ordering))))))

# 586 "FStar.ToSMT.Term.fst"
let mk_Kind_type : term = (mkApp ("Kind_type", []))

# 587 "FStar.ToSMT.Term.fst"
let mk_Kind_uvar : Prims.int  ->  term = (fun i -> (let _116_533 = (let _116_532 = (let _116_531 = (mkInteger' i)
in (_116_531)::[])
in ("Kind_uvar", _116_532))
in (mkApp _116_533)))

# 588 "FStar.ToSMT.Term.fst"
let mk_Typ_app : term  ->  term  ->  term = (fun t1 t2 -> (mkApp ("Typ_app", (t1)::(t2)::[])))

# 589 "FStar.ToSMT.Term.fst"
let mk_Typ_dep : term  ->  term  ->  term = (fun t1 t2 -> (mkApp ("Typ_dep", (t1)::(t2)::[])))

# 590 "FStar.ToSMT.Term.fst"
let mk_Typ_uvar : Prims.int  ->  term = (fun i -> (let _116_546 = (let _116_545 = (let _116_544 = (mkInteger' i)
in (_116_544)::[])
in ("Typ_uvar", _116_545))
in (mkApp _116_546)))

# 591 "FStar.ToSMT.Term.fst"
let mk_Exp_uvar : Prims.int  ->  term = (fun i -> (let _116_551 = (let _116_550 = (let _116_549 = (mkInteger' i)
in (_116_549)::[])
in ("Exp_uvar", _116_550))
in (mkApp _116_551)))

# 593 "FStar.ToSMT.Term.fst"
let mk_Term_unit : term = (mkApp ("Term_unit", []))

# 594 "FStar.ToSMT.Term.fst"
let boxInt : term  ->  term = (fun t -> (mkApp ("BoxInt", (t)::[])))

# 595 "FStar.ToSMT.Term.fst"
let unboxInt : term  ->  term = (fun t -> (mkApp ("BoxInt_proj_0", (t)::[])))

# 596 "FStar.ToSMT.Term.fst"
let boxBool : term  ->  term = (fun t -> (mkApp ("BoxBool", (t)::[])))

# 597 "FStar.ToSMT.Term.fst"
let unboxBool : term  ->  term = (fun t -> (mkApp ("BoxBool_proj_0", (t)::[])))

# 598 "FStar.ToSMT.Term.fst"
let boxString : term  ->  term = (fun t -> (mkApp ("BoxString", (t)::[])))

# 599 "FStar.ToSMT.Term.fst"
let unboxString : term  ->  term = (fun t -> (mkApp ("BoxString_proj_0", (t)::[])))

# 600 "FStar.ToSMT.Term.fst"
let boxRef : term  ->  term = (fun t -> (mkApp ("BoxRef", (t)::[])))

# 601 "FStar.ToSMT.Term.fst"
let unboxRef : term  ->  term = (fun t -> (mkApp ("BoxRef_proj_0", (t)::[])))

# 602 "FStar.ToSMT.Term.fst"
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
| _37_724 -> begin
(Prims.raise FStar_Util.Impos)
end))

# 608 "FStar.ToSMT.Term.fst"
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
| _37_732 -> begin
(Prims.raise FStar_Util.Impos)
end))

# 615 "FStar.ToSMT.Term.fst"
let mk_PreKind : term  ->  term = (fun t -> (mkApp ("PreKind", (t)::[])))

# 616 "FStar.ToSMT.Term.fst"
let mk_PreType : term  ->  term = (fun t -> (mkApp ("PreType", (t)::[])))

# 617 "FStar.ToSMT.Term.fst"
let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_Equality"), _37_747::t1::t2::[]); hash = _37_741; freevars = _37_739}::[]) -> begin
(mkEq (t1, t2))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_disEquality"), _37_766::t1::t2::[]); hash = _37_760; freevars = _37_758}::[]) -> begin
(let _116_582 = (mkEq (t1, t2))
in (mkNot _116_582))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_LessThanOrEqual"), t1::t2::[]); hash = _37_779; freevars = _37_777}::[]) -> begin
(let _116_585 = (let _116_584 = (unboxInt t1)
in (let _116_583 = (unboxInt t2)
in (_116_584, _116_583)))
in (mkLTE _116_585))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_LessThan"), t1::t2::[]); hash = _37_796; freevars = _37_794}::[]) -> begin
(let _116_588 = (let _116_587 = (unboxInt t1)
in (let _116_586 = (unboxInt t2)
in (_116_587, _116_586)))
in (mkLT _116_588))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_GreaterThanOrEqual"), t1::t2::[]); hash = _37_813; freevars = _37_811}::[]) -> begin
(let _116_591 = (let _116_590 = (unboxInt t1)
in (let _116_589 = (unboxInt t2)
in (_116_590, _116_589)))
in (mkGTE _116_591))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_GreaterThan"), t1::t2::[]); hash = _37_830; freevars = _37_828}::[]) -> begin
(let _116_594 = (let _116_593 = (unboxInt t1)
in (let _116_592 = (unboxInt t2)
in (_116_593, _116_592)))
in (mkGT _116_594))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_AmpAmp"), t1::t2::[]); hash = _37_847; freevars = _37_845}::[]) -> begin
(let _116_597 = (let _116_596 = (unboxBool t1)
in (let _116_595 = (unboxBool t2)
in (_116_596, _116_595)))
in (mkAnd _116_597))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_BarBar"), t1::t2::[]); hash = _37_864; freevars = _37_862}::[]) -> begin
(let _116_600 = (let _116_599 = (unboxBool t1)
in (let _116_598 = (unboxBool t2)
in (_116_599, _116_598)))
in (mkOr _116_600))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_Negation"), t::[]); hash = _37_881; freevars = _37_879}::[]) -> begin
(let _116_601 = (unboxBool t)
in (mkNot _116_601))
end
| App (Var ("Prims.b2t"), t::[]) -> begin
(unboxBool t)
end
| _37_899 -> begin
(mkApp ("Valid", (t)::[]))
end))

# 629 "FStar.ToSMT.Term.fst"
let mk_HasType : term  ->  term  ->  term = (fun v t -> (mkApp ("HasType", (v)::(t)::[])))

# 630 "FStar.ToSMT.Term.fst"
let mk_HasTypeZ : term  ->  term  ->  term = (fun v t -> (mkApp ("HasTypeZ", (v)::(t)::[])))

# 631 "FStar.ToSMT.Term.fst"
let mk_IsTyped : term  ->  term = (fun v -> (mkApp ("IsTyped", (v)::[])))

# 632 "FStar.ToSMT.Term.fst"
let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v t -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(mk_HasType v t)
end else begin
(mkApp ("HasTypeFuel", (f)::(v)::(t)::[]))
end)

# 636 "FStar.ToSMT.Term.fst"
let mk_HasTypeWithFuel : term Prims.option  ->  term  ->  term  ->  term = (fun f v t -> (match (f) with
| None -> begin
(mk_HasType v t)
end
| Some (f) -> begin
(mk_HasTypeFuel f v t)
end))

# 639 "FStar.ToSMT.Term.fst"
let mk_Destruct : term  ->  term = (fun v -> (mkApp ("Destruct", (v)::[])))

# 640 "FStar.ToSMT.Term.fst"
let mk_HasKind : term  ->  term  ->  term = (fun t k -> (mkApp ("HasKind", (t)::(k)::[])))

# 641 "FStar.ToSMT.Term.fst"
let mk_Rank : term  ->  term = (fun x -> (mkApp ("Rank", (x)::[])))

# 642 "FStar.ToSMT.Term.fst"
let mk_tester : Prims.string  ->  term  ->  term = (fun n t -> (mkApp ((Prims.strcat "is-" n), (t)::[])))

# 643 "FStar.ToSMT.Term.fst"
let mk_ApplyTE : term  ->  term  ->  term = (fun t e -> (mkApp ("ApplyTE", (t)::(e)::[])))

# 644 "FStar.ToSMT.Term.fst"
let mk_ApplyTT : term  ->  term  ->  term = (fun t t' -> (mkApp ("ApplyTT", (t)::(t')::[])))

# 645 "FStar.ToSMT.Term.fst"
let mk_ApplyET : term  ->  term  ->  term = (fun e t -> (mkApp ("ApplyET", (e)::(t)::[])))

# 646 "FStar.ToSMT.Term.fst"
let mk_ApplyEE : term  ->  term  ->  term = (fun e e' -> (mkApp ("ApplyEE", (e)::(e')::[])))

# 647 "FStar.ToSMT.Term.fst"
let mk_ApplyEF : term  ->  term  ->  term = (fun e f -> (mkApp ("ApplyEF", (e)::(f)::[])))

# 648 "FStar.ToSMT.Term.fst"
let mk_String_const : Prims.int  ->  term = (fun i -> (let _116_660 = (let _116_659 = (let _116_658 = (mkInteger' i)
in (_116_658)::[])
in ("String_const", _116_659))
in (mkApp _116_660)))

# 649 "FStar.ToSMT.Term.fst"
let mk_Precedes : term  ->  term  ->  term = (fun x1 x2 -> (let _116_665 = (mkApp ("Precedes", (x1)::(x2)::[]))
in (FStar_All.pipe_right _116_665 mk_Valid)))

# 650 "FStar.ToSMT.Term.fst"
let mk_LexCons : term  ->  term  ->  term = (fun x1 x2 -> (mkApp ("LexCons", (x1)::(x2)::[])))

# 651 "FStar.ToSMT.Term.fst"
let rec n_fuel : Prims.int  ->  term = (fun n -> if (n = 0) then begin
(mkApp ("ZFuel", []))
end else begin
(let _116_674 = (let _116_673 = (let _116_672 = (n_fuel (n - 1))
in (_116_672)::[])
in ("SFuel", _116_673))
in (mkApp _116_674))
end)

# 654 "FStar.ToSMT.Term.fst"
let fuel_2 : term = (n_fuel 2)

# 655 "FStar.ToSMT.Term.fst"
let fuel_100 : term = (n_fuel 100)

# 657 "FStar.ToSMT.Term.fst"
let mk_and_opt : term Prims.option  ->  term Prims.option  ->  term Prims.option = (fun p1 p2 -> (match ((p1, p2)) with
| (Some (p1), Some (p2)) -> begin
(let _116_679 = (mkAnd (p1, p2))
in Some (_116_679))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))

# 663 "FStar.ToSMT.Term.fst"
let mk_and_opt_l : term Prims.option Prims.list  ->  term Prims.option = (fun pl -> (FStar_List.fold_left (fun out p -> (mk_and_opt p out)) None pl))

# 666 "FStar.ToSMT.Term.fst"
let mk_and_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkTrue
end
| hd::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkAnd (p1, p2))) hd tl)
end))

# 670 "FStar.ToSMT.Term.fst"
let mk_or_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkFalse
end
| hd::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkOr (p1, p2))) hd tl)
end))

# 675 "FStar.ToSMT.Term.fst"
let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "Integer %s" n)
end
| BoundV (n) -> begin
(let _116_696 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "BoundV %s" _116_696))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "FreeV %s" (Prims.fst fv))
end
| App (op, l) -> begin
(let _116_697 = (print_smt_term_list l)
in (FStar_Util.format2 "App %s [ %s ]" (op_to_string op) _116_697))
end
| Quant (qop, l, _37_984, _37_986, t) -> begin
(let _116_699 = (print_smt_term_list_list l)
in (let _116_698 = (print_smt_term t)
in (FStar_Util.format3 "Quant %s %s %s" (qop_to_string qop) _116_699 _116_698)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s t -> (let _116_703 = (print_smt_term t)
in (Prims.strcat (Prims.strcat s "; ") _116_703))) "" l))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _116_708 = (let _116_707 = (print_smt_term_list l)
in (Prims.strcat (Prims.strcat s "; [ ") _116_707))
in (Prims.strcat _116_708 " ] "))) "" l))




