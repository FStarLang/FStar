
open Prims
# 23 "FStar.ToSMT.Term.fst"
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
| Array (_47_10) -> begin
_47_10
end))

# 35 "FStar.ToSMT.Term.fst"
let ___Arrow____0 = (fun projectee -> (match (projectee) with
| Arrow (_47_13) -> begin
_47_13
end))

# 36 "FStar.ToSMT.Term.fst"
let ___Sort____0 = (fun projectee -> (match (projectee) with
| Sort (_47_16) -> begin
_47_16
end))

# 36 "FStar.ToSMT.Term.fst"
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
(let _139_54 = (strSort s1)
in (let _139_53 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _139_54 _139_53)))
end
| Arrow (s1, s2) -> begin
(let _139_56 = (strSort s1)
in (let _139_55 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _139_56 _139_55)))
end
| Sort (s) -> begin
s
end))

# 49 "FStar.ToSMT.Term.fst"
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
| Var (_47_38) -> begin
_47_38
end))

# 71 "FStar.ToSMT.Term.fst"
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

# 75 "FStar.ToSMT.Term.fst"
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
| Integer (_47_44) -> begin
_47_44
end))

# 80 "FStar.ToSMT.Term.fst"
let ___BoundV____0 = (fun projectee -> (match (projectee) with
| BoundV (_47_47) -> begin
_47_47
end))

# 81 "FStar.ToSMT.Term.fst"
let ___FreeV____0 = (fun projectee -> (match (projectee) with
| FreeV (_47_50) -> begin
_47_50
end))

# 82 "FStar.ToSMT.Term.fst"
let ___App____0 = (fun projectee -> (match (projectee) with
| App (_47_53) -> begin
_47_53
end))

# 83 "FStar.ToSMT.Term.fst"
let ___Quant____0 = (fun projectee -> (match (projectee) with
| Quant (_47_56) -> begin
_47_56
end))

# 91 "FStar.ToSMT.Term.fst"
type caption =
Prims.string Prims.option

# 94 "FStar.ToSMT.Term.fst"
type binders =
(Prims.string * sort) Prims.list

# 95 "FStar.ToSMT.Term.fst"
type projector =
(Prims.string * sort)

# 96 "FStar.ToSMT.Term.fst"
type constructor_t =
(Prims.string * projector Prims.list * sort * Prims.int)

# 97 "FStar.ToSMT.Term.fst"
type constructors =
constructor_t Prims.list

# 98 "FStar.ToSMT.Term.fst"
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
| DeclFun (_47_60) -> begin
_47_60
end))

# 102 "FStar.ToSMT.Term.fst"
let ___DefineFun____0 = (fun projectee -> (match (projectee) with
| DefineFun (_47_63) -> begin
_47_63
end))

# 103 "FStar.ToSMT.Term.fst"
let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_47_66) -> begin
_47_66
end))

# 104 "FStar.ToSMT.Term.fst"
let ___Caption____0 = (fun projectee -> (match (projectee) with
| Caption (_47_69) -> begin
_47_69
end))

# 105 "FStar.ToSMT.Term.fst"
let ___Eval____0 = (fun projectee -> (match (projectee) with
| Eval (_47_72) -> begin
_47_72
end))

# 106 "FStar.ToSMT.Term.fst"
let ___Echo____0 = (fun projectee -> (match (projectee) with
| Echo (_47_75) -> begin
_47_75
end))

# 109 "FStar.ToSMT.Term.fst"
type decls_t =
decl Prims.list

# 191 "FStar.ToSMT.Term.fst"
let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> ((Prims.fst x) = (Prims.fst y)))

# 193 "FStar.ToSMT.Term.fst"
let fv_sort = (fun x -> (Prims.snd x))

# 194 "FStar.ToSMT.Term.fst"
let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match (((x.tm), (y.tm))) with
| (FreeV (x), FreeV (y)) -> begin
(fv_eq x y)
end
| _47_87 -> begin
false
end))

# 197 "FStar.ToSMT.Term.fst"
let freevar_sort : term  ->  sort = (fun _47_1 -> (match (_47_1) with
| {tm = FreeV (x); hash = _47_92; freevars = _47_90} -> begin
(fv_sort x)
end
| _47_97 -> begin
(FStar_All.failwith "impossible")
end))

# 200 "FStar.ToSMT.Term.fst"
let fv_of_term : term  ->  fv = (fun _47_2 -> (match (_47_2) with
| {tm = FreeV (fv); hash = _47_102; freevars = _47_100} -> begin
fv
end
| _47_107 -> begin
(FStar_All.failwith "impossible")
end))

# 203 "FStar.ToSMT.Term.fst"
let rec freevars : term  ->  fv Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (_47_118, tms) -> begin
(FStar_List.collect freevars tms)
end
| Quant (_47_123, _47_125, _47_127, _47_129, t) -> begin
(freevars t)
end))

# 209 "FStar.ToSMT.Term.fst"
let free_variables : term  ->  fvs = (fun t -> (match ((FStar_ST.read t.freevars)) with
| Some (b) -> begin
b
end
| None -> begin
(
# 215 "FStar.ToSMT.Term.fst"
let fvs = (let _139_277 = (freevars t)
in (FStar_Util.remove_dups fv_eq _139_277))
in (
# 216 "FStar.ToSMT.Term.fst"
let _47_138 = (FStar_ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))

# 217 "FStar.ToSMT.Term.fst"
let qop_to_string : qop  ->  Prims.string = (fun _47_3 -> (match (_47_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))

# 224 "FStar.ToSMT.Term.fst"
let op_to_string : op  ->  Prims.string = (fun _47_4 -> (match (_47_4) with
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

# 246 "FStar.ToSMT.Term.fst"
let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun _47_5 -> (match (_47_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _139_284 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _139_284))
end))

# 250 "FStar.ToSMT.Term.fst"
let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _139_287 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _139_287))
end
| FreeV (x) -> begin
(let _139_289 = (let _139_288 = (strSort (Prims.snd x))
in (Prims.strcat ":" _139_288))
in (Prims.strcat (Prims.fst x) _139_289))
end
| App (op, tms) -> begin
(let _139_294 = (let _139_293 = (let _139_292 = (let _139_291 = (FStar_List.map (fun t -> t.hash) tms)
in (FStar_All.pipe_right _139_291 (FStar_String.concat " ")))
in (Prims.strcat _139_292 ")"))
in (Prims.strcat (op_to_string op) _139_293))
in (Prims.strcat "(" _139_294))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _139_302 = (let _139_295 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _139_295 (FStar_String.concat " ")))
in (let _139_301 = (weightToSmt wopt)
in (let _139_300 = (let _139_299 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _139_298 = (FStar_List.map (fun p -> p.hash) pats)
in (FStar_All.pipe_right _139_298 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _139_299 (FStar_String.concat "; ")))
in (FStar_Util.format5 "(%s (%s)(! %s %s %s))" (qop_to_string qop) _139_302 body.hash _139_301 _139_300))))
end))

# 263 "FStar.ToSMT.Term.fst"
let __all_terms : term FStar_Util.smap FStar_ST.ref = (let _139_303 = (FStar_Util.smap_create 10000)
in (FStar_ST.alloc _139_303))

# 266 "FStar.ToSMT.Term.fst"
let all_terms : Prims.unit  ->  term FStar_Util.smap = (fun _47_190 -> (match (()) with
| () -> begin
(FStar_ST.read __all_terms)
end))

# 267 "FStar.ToSMT.Term.fst"
let mk : term'  ->  term = (fun t -> (
# 269 "FStar.ToSMT.Term.fst"
let key = (hash_of_term' t)
in (match ((let _139_308 = (all_terms ())
in (FStar_Util.smap_try_find _139_308 key))) with
| Some (tm) -> begin
tm
end
| None -> begin
(
# 273 "FStar.ToSMT.Term.fst"
let tm = (let _139_309 = (FStar_Util.mk_ref None)
in {tm = t; hash = key; freevars = _139_309})
in (
# 274 "FStar.ToSMT.Term.fst"
let _47_197 = (let _139_310 = (all_terms ())
in (FStar_Util.smap_add _139_310 key tm))
in tm))
end)))

# 275 "FStar.ToSMT.Term.fst"
let mkTrue : term = (mk (App (((True), ([])))))

# 277 "FStar.ToSMT.Term.fst"
let mkFalse : term = (mk (App (((False), ([])))))

# 278 "FStar.ToSMT.Term.fst"
let mkInteger : Prims.string  ->  term = (fun i -> (mk (Integer (i))))

# 279 "FStar.ToSMT.Term.fst"
let mkInteger' : Prims.int  ->  term = (fun i -> (let _139_316 = (let _139_315 = (FStar_Util.string_of_int i)
in Integer (_139_315))
in (mk _139_316)))

# 280 "FStar.ToSMT.Term.fst"
let mkBoundV : Prims.int  ->  term = (fun i -> (mk (BoundV (i))))

# 281 "FStar.ToSMT.Term.fst"
let mkFreeV : (Prims.string * sort)  ->  term = (fun x -> (mk (FreeV (x))))

# 282 "FStar.ToSMT.Term.fst"
let mkApp' : (op * term Prims.list)  ->  term = (fun f -> (mk (App (f))))

# 283 "FStar.ToSMT.Term.fst"
let mkApp : (Prims.string * term Prims.list)  ->  term = (fun _47_206 -> (match (_47_206) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))))
end))

# 284 "FStar.ToSMT.Term.fst"
let mkNot : term  ->  term = (fun t -> (match (t.tm) with
| App (True, _47_210) -> begin
mkFalse
end
| App (False, _47_215) -> begin
mkTrue
end
| _47_219 -> begin
(mkApp' ((Not), ((t)::[])))
end))

# 288 "FStar.ToSMT.Term.fst"
let mkAnd : (term * term)  ->  term = (fun _47_222 -> (match (_47_222) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (True, _47_225), _47_229) -> begin
t2
end
| (_47_232, App (True, _47_235)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
mkFalse
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))))
end
| (_47_265, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)))
end
| (App (And, ts1), _47_276) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))))
end
| _47_279 -> begin
(mkApp' ((And), ((t1)::(t2)::[])))
end)
end))

# 297 "FStar.ToSMT.Term.fst"
let mkOr : (term * term)  ->  term = (fun _47_282 -> (match (_47_282) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
mkTrue
end
| (App (False, _47_301), _47_305) -> begin
t2
end
| (_47_308, App (False, _47_311)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))))
end
| (_47_325, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)))
end
| (App (Or, ts1), _47_336) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))))
end
| _47_339 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])))
end)
end))

# 306 "FStar.ToSMT.Term.fst"
let mkImp : (term * term)  ->  term = (fun _47_342 -> (match (_47_342) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (_47_344, App (True, _47_347)) -> begin
mkTrue
end
| (App (True, _47_353), _47_357) -> begin
t2
end
| (_47_360, App (Imp, (t1')::(t2')::[])) -> begin
(let _139_335 = (let _139_334 = (let _139_333 = (mkAnd ((t1), (t1')))
in (_139_333)::(t2')::[])
in ((Imp), (_139_334)))
in (mkApp' _139_335))
end
| _47_369 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])))
end)
end))

# 311 "FStar.ToSMT.Term.fst"
let mk_bin_op : op  ->  (term * term)  ->  term = (fun op _47_373 -> (match (_47_373) with
| (t1, t2) -> begin
(mkApp' ((op), ((t1)::(t2)::[])))
end))

# 313 "FStar.ToSMT.Term.fst"
let mkMinus : term  ->  term = (fun t -> (mkApp' ((Minus), ((t)::[]))))

# 314 "FStar.ToSMT.Term.fst"
let mkIff : (term * term)  ->  term = (mk_bin_op Iff)

# 315 "FStar.ToSMT.Term.fst"
let mkEq : (term * term)  ->  term = (mk_bin_op Eq)

# 316 "FStar.ToSMT.Term.fst"
let mkLT : (term * term)  ->  term = (mk_bin_op LT)

# 317 "FStar.ToSMT.Term.fst"
let mkLTE : (term * term)  ->  term = (mk_bin_op LTE)

# 318 "FStar.ToSMT.Term.fst"
let mkGT : (term * term)  ->  term = (mk_bin_op GT)

# 319 "FStar.ToSMT.Term.fst"
let mkGTE : (term * term)  ->  term = (mk_bin_op GTE)

# 320 "FStar.ToSMT.Term.fst"
let mkAdd : (term * term)  ->  term = (mk_bin_op Add)

# 321 "FStar.ToSMT.Term.fst"
let mkSub : (term * term)  ->  term = (mk_bin_op Sub)

# 322 "FStar.ToSMT.Term.fst"
let mkDiv : (term * term)  ->  term = (mk_bin_op Div)

# 323 "FStar.ToSMT.Term.fst"
let mkMul : (term * term)  ->  term = (mk_bin_op Mul)

# 324 "FStar.ToSMT.Term.fst"
let mkMod : (term * term)  ->  term = (mk_bin_op Mod)

# 325 "FStar.ToSMT.Term.fst"
let mkITE : (term * term * term)  ->  term = (fun _47_378 -> (match (_47_378) with
| (t1, t2, t3) -> begin
(match (((t2.tm), (t3.tm))) with
| (App (True, _47_381), App (True, _47_386)) -> begin
mkTrue
end
| (App (True, _47_392), _47_396) -> begin
(let _139_356 = (let _139_355 = (mkNot t1)
in ((_139_355), (t3)))
in (mkImp _139_356))
end
| (_47_399, App (True, _47_402)) -> begin
(mkImp ((t1), (t2)))
end
| (_47_407, _47_409) -> begin
(mkApp' ((ITE), ((t1)::(t2)::(t3)::[])))
end)
end))

# 331 "FStar.ToSMT.Term.fst"
let mkCases : term Prims.list  ->  term = (fun t -> (match (t) with
| [] -> begin
(FStar_All.failwith "Impos")
end
| (hd)::tl -> begin
(FStar_List.fold_left (fun out t -> (mkAnd ((out), (t)))) hd tl)
end))

# 334 "FStar.ToSMT.Term.fst"
let mkQuant : (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _47_423 -> (match (_47_423) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = 0) then begin
body
end else begin
(match (body.tm) with
| App (True, _47_426) -> begin
body
end
| _47_430 -> begin
(mk (Quant (((qop), (pats), (wopt), (vars), (body)))))
end)
end
end))

# 340 "FStar.ToSMT.Term.fst"
let abstr : fvs  ->  term  ->  term = (fun fvs t -> (
# 346 "FStar.ToSMT.Term.fst"
let nvars = (FStar_List.length fvs)
in (
# 347 "FStar.ToSMT.Term.fst"
let index_of = (fun fv -> (match ((FStar_Util.try_find_index (fv_eq fv) fvs)) with
| None -> begin
None
end
| Some (i) -> begin
Some ((nvars - (i + 1)))
end))
in (
# 350 "FStar.ToSMT.Term.fst"
let rec aux = (fun ix t -> (match ((FStar_ST.read t.freevars)) with
| Some ([]) -> begin
t
end
| _47_445 -> begin
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
(let _139_374 = (let _139_373 = (FStar_List.map (aux ix) tms)
in ((op), (_139_373)))
in (mkApp' _139_374))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(
# 364 "FStar.ToSMT.Term.fst"
let n = (FStar_List.length vars)
in (let _139_377 = (let _139_376 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _139_375 = (aux (ix + n) body)
in ((qop), (_139_376), (wopt), (vars), (_139_375))))
in (mkQuant _139_377)))
end)
end))
in (aux 0 t)))))

# 367 "FStar.ToSMT.Term.fst"
let inst : term Prims.list  ->  term  ->  term = (fun tms t -> (
# 370 "FStar.ToSMT.Term.fst"
let n = (FStar_List.length tms)
in (
# 371 "FStar.ToSMT.Term.fst"
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
(let _139_387 = (let _139_386 = (FStar_List.map (aux shift) tms)
in ((op), (_139_386)))
in (mkApp' _139_387))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(
# 380 "FStar.ToSMT.Term.fst"
let m = (FStar_List.length vars)
in (
# 381 "FStar.ToSMT.Term.fst"
let shift = (shift + m)
in (let _139_390 = (let _139_389 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _139_388 = (aux shift body)
in ((qop), (_139_389), (wopt), (vars), (_139_388))))
in (mkQuant _139_390))))
end))
in (aux 0 t))))

# 383 "FStar.ToSMT.Term.fst"
let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  term = (fun _47_501 -> (match (_47_501) with
| (qop, pats, wopt, vars, body) -> begin
(let _139_396 = (let _139_395 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _139_394 = (FStar_List.map fv_sort vars)
in (let _139_393 = (abstr vars body)
in ((qop), (_139_395), (wopt), (_139_394), (_139_393)))))
in (mkQuant _139_396))
end))

# 385 "FStar.ToSMT.Term.fst"
let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _47_506 -> (match (_47_506) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)))
end))

# 386 "FStar.ToSMT.Term.fst"
let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  term = (fun _47_511 -> (match (_47_511) with
| (pats, wopt, vars, body) -> begin
(mkQuant' ((Forall), (pats), (wopt), (vars), (body)))
end))

# 387 "FStar.ToSMT.Term.fst"
let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _47_515 -> (match (_47_515) with
| (pats, vars, body) -> begin
(mkQuant' ((Forall), (pats), (None), (vars), (body)))
end))

# 390 "FStar.ToSMT.Term.fst"
let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _47_519 -> (match (_47_519) with
| (pats, vars, body) -> begin
(mkQuant' ((Exists), (pats), (None), (vars), (body)))
end))

# 391 "FStar.ToSMT.Term.fst"
let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun _47_525 -> (match (_47_525) with
| (nm, vars, s, tm, c) -> begin
(let _139_409 = (let _139_408 = (FStar_List.map fv_sort vars)
in (let _139_407 = (abstr vars tm)
in ((nm), (_139_408), (s), (_139_407), (c))))
in DefineFun (_139_409))
end))

# 392 "FStar.ToSMT.Term.fst"
let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _139_412 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _139_412)))

# 393 "FStar.ToSMT.Term.fst"
let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun _47_529 id -> (match (_47_529) with
| (tok_name, sort) -> begin
(let _139_425 = (let _139_424 = (let _139_423 = (let _139_422 = (mkInteger' id)
in (let _139_421 = (let _139_420 = (let _139_419 = (constr_id_of_sort sort)
in (let _139_418 = (let _139_417 = (mkApp ((tok_name), ([])))
in (_139_417)::[])
in ((_139_419), (_139_418))))
in (mkApp _139_420))
in ((_139_422), (_139_421))))
in (mkEq _139_423))
in ((_139_424), (Some ("fresh token"))))
in Assume (_139_425))
end))

# 395 "FStar.ToSMT.Term.fst"
let constructor_to_decl : constructor_t  ->  decls_t = (fun _47_535 -> (match (_47_535) with
| (name, projectors, sort, id) -> begin
(
# 398 "FStar.ToSMT.Term.fst"
let id = (FStar_Util.string_of_int id)
in (
# 399 "FStar.ToSMT.Term.fst"
let cdecl = (let _139_429 = (let _139_428 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_139_428), (sort), (Some ("Constructor"))))
in DeclFun (_139_429))
in (
# 400 "FStar.ToSMT.Term.fst"
let n_bvars = (FStar_List.length projectors)
in (
# 401 "FStar.ToSMT.Term.fst"
let bvar_name = (fun i -> (let _139_432 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _139_432)))
in (
# 402 "FStar.ToSMT.Term.fst"
let bvar_index = (fun i -> (n_bvars - (i + 1)))
in (
# 403 "FStar.ToSMT.Term.fst"
let bvar = (fun i s -> (let _139_440 = (let _139_439 = (bvar_name i)
in ((_139_439), (s)))
in (mkFreeV _139_440)))
in (
# 404 "FStar.ToSMT.Term.fst"
let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _47_550 -> (match (_47_550) with
| (_47_548, s) -> begin
(bvar i s)
end))))
in (
# 405 "FStar.ToSMT.Term.fst"
let bvar_names = (FStar_List.map fv_of_term bvars)
in (
# 406 "FStar.ToSMT.Term.fst"
let capp = (mkApp ((name), (bvars)))
in (
# 407 "FStar.ToSMT.Term.fst"
let cid_app = (let _139_444 = (let _139_443 = (constr_id_of_sort sort)
in ((_139_443), ((capp)::[])))
in (mkApp _139_444))
in (
# 408 "FStar.ToSMT.Term.fst"
let cid = (let _139_450 = (let _139_449 = (let _139_448 = (let _139_447 = (let _139_446 = (let _139_445 = (mkInteger id)
in ((_139_445), (cid_app)))
in (mkEq _139_446))
in ((((capp)::[])::[]), (bvar_names), (_139_447)))
in (mkForall _139_448))
in ((_139_449), (Some ("Constructor distinct"))))
in Assume (_139_450))
in (
# 409 "FStar.ToSMT.Term.fst"
let disc_name = (Prims.strcat "is-" name)
in (
# 410 "FStar.ToSMT.Term.fst"
let xfv = (("x"), (sort))
in (
# 411 "FStar.ToSMT.Term.fst"
let xx = (mkFreeV xfv)
in (
# 412 "FStar.ToSMT.Term.fst"
let disc_eq = (let _139_455 = (let _139_454 = (let _139_452 = (let _139_451 = (constr_id_of_sort sort)
in ((_139_451), ((xx)::[])))
in (mkApp _139_452))
in (let _139_453 = (mkInteger id)
in ((_139_454), (_139_453))))
in (mkEq _139_455))
in (
# 413 "FStar.ToSMT.Term.fst"
let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _47_562 -> (match (_47_562) with
| (proj, s) -> begin
(mkApp ((proj), ((xx)::[])))
end))))
in (
# 414 "FStar.ToSMT.Term.fst"
let disc_inv_body = (let _139_458 = (let _139_457 = (mkApp ((name), (proj_terms)))
in ((xx), (_139_457)))
in (mkEq _139_458))
in (
# 415 "FStar.ToSMT.Term.fst"
let disc_ax = (mkAnd ((disc_eq), (disc_inv_body)))
in (
# 416 "FStar.ToSMT.Term.fst"
let disc = (mkDefineFun ((disc_name), ((xfv)::[]), (Bool_sort), (disc_ax), (Some ("Discriminator definition"))))
in (
# 419 "FStar.ToSMT.Term.fst"
let projs = (let _139_469 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _47_570 -> (match (_47_570) with
| (name, s) -> begin
(
# 420 "FStar.ToSMT.Term.fst"
let cproj_app = (mkApp ((name), ((capp)::[])))
in (let _139_468 = (let _139_467 = (let _139_466 = (let _139_465 = (let _139_464 = (let _139_463 = (let _139_462 = (let _139_461 = (bvar i s)
in ((cproj_app), (_139_461)))
in (mkEq _139_462))
in ((((capp)::[])::[]), (bvar_names), (_139_463)))
in (mkForall _139_464))
in ((_139_465), (Some ("Projection inverse"))))
in Assume (_139_466))
in (_139_467)::[])
in (DeclFun (((name), ((sort)::[]), (s), (Some ("Projector")))))::_139_468))
end))))
in (FStar_All.pipe_right _139_469 FStar_List.flatten))
in (let _139_476 = (let _139_471 = (let _139_470 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_139_470))
in (_139_471)::(cdecl)::(cid)::projs)
in (let _139_475 = (let _139_474 = (let _139_473 = (let _139_472 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_139_472))
in (_139_473)::[])
in (FStar_List.append ((disc)::[]) _139_474))
in (FStar_List.append _139_476 _139_475)))))))))))))))))))))))
end))

# 423 "FStar.ToSMT.Term.fst"
let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (
# 430 "FStar.ToSMT.Term.fst"
let _47_592 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _47_579 s -> (match (_47_579) with
| (names, binders, n) -> begin
(
# 431 "FStar.ToSMT.Term.fst"
let prefix = (match (s) with
| Type_sort -> begin
"@a"
end
| Term_sort -> begin
"@x"
end
| _47_584 -> begin
"@u"
end)
in (
# 435 "FStar.ToSMT.Term.fst"
let nm = (let _139_485 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _139_485))
in (
# 436 "FStar.ToSMT.Term.fst"
let names = (((nm), (s)))::names
in (
# 437 "FStar.ToSMT.Term.fst"
let b = (let _139_486 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _139_486))
in ((names), ((b)::binders), ((n + 1)))))))
end)) ((outer_names), ([]), (start))))
in (match (_47_592) with
| (names, binders, n) -> begin
((names), ((FStar_List.rev binders)), (n))
end)))

# 440 "FStar.ToSMT.Term.fst"
let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (
# 443 "FStar.ToSMT.Term.fst"
let _47_597 = (name_binders_inner [] 0 sorts)
in (match (_47_597) with
| (names, binders, n) -> begin
(((FStar_List.rev names)), (binders))
end)))

# 444 "FStar.ToSMT.Term.fst"
let termToSmt : term  ->  Prims.string = (fun t -> (
# 447 "FStar.ToSMT.Term.fst"
let rec aux = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _139_497 = (FStar_List.nth names i)
in (FStar_All.pipe_right _139_497 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _139_499 = (let _139_498 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _139_498 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _139_499))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(
# 455 "FStar.ToSMT.Term.fst"
let _47_627 = (name_binders_inner names n sorts)
in (match (_47_627) with
| (names, binders, n) -> begin
(
# 456 "FStar.ToSMT.Term.fst"
let binders = (FStar_All.pipe_right binders (FStar_String.concat " "))
in (
# 457 "FStar.ToSMT.Term.fst"
let pats_str = (match (pats) with
| (([])::[]) | ([]) -> begin
""
end
| _47_633 -> begin
(let _139_505 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _139_504 = (let _139_503 = (FStar_List.map (fun p -> (let _139_502 = (aux n names p)
in (FStar_Util.format1 "%s" _139_502))) pats)
in (FStar_String.concat " " _139_503))
in (FStar_Util.format1 "\n:pattern (%s)" _139_504)))))
in (FStar_All.pipe_right _139_505 (FStar_String.concat "\n")))
end)
in (match (((pats), (wopt))) with
| ((([])::[], None)) | (([], None)) -> begin
(let _139_506 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _139_506))
end
| _47_645 -> begin
(let _139_508 = (aux n names body)
in (let _139_507 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _139_508 _139_507 pats_str)))
end)))
end))
end))
in (aux 0 [] t)))

# 466 "FStar.ToSMT.Term.fst"
let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun _47_6 -> (match (_47_6) with
| None -> begin
""
end
| Some (c) -> begin
(
# 472 "FStar.ToSMT.Term.fst"
let _47_652 = (FStar_Util.splitlines c)
in (match (_47_652) with
| (hd)::tl -> begin
(
# 473 "FStar.ToSMT.Term.fst"
let suffix = (match (tl) with
| [] -> begin
""
end
| _47_655 -> begin
"..."
end)
in (FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd suffix))
end))
end))

# 476 "FStar.ToSMT.Term.fst"
let rec declToSmt : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(let _139_517 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _47_7 -> (match (_47_7) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _139_517))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(
# 483 "FStar.ToSMT.Term.fst"
let l = (FStar_List.map strSort argsorts)
in (let _139_519 = (caption_to_string c)
in (let _139_518 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _139_519 f (FStar_String.concat " " l) _139_518))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(
# 486 "FStar.ToSMT.Term.fst"
let _47_683 = (name_binders arg_sorts)
in (match (_47_683) with
| (names, binders) -> begin
(
# 487 "FStar.ToSMT.Term.fst"
let body = (let _139_520 = (FStar_List.map mkFreeV names)
in (inst _139_520 body))
in (let _139_523 = (caption_to_string c)
in (let _139_522 = (strSort retsort)
in (let _139_521 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _139_523 f (FStar_String.concat " " binders) _139_522 _139_521)))))
end))
end
| Assume (t, c) -> begin
(let _139_525 = (caption_to_string c)
in (let _139_524 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _139_525 _139_524)))
end
| Eval (t) -> begin
(let _139_526 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _139_526))
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
# 500 "FStar.ToSMT.Term.fst"
let basic = (Prims.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort String)\n(declare-fun String_constr_id (String) Int)\n\n(declare-sort Kind)\n(declare-fun Kind_constr_id (Kind) Int)\n\n(declare-sort Type)\n(declare-fun Type_constr_id (Type) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreKind (Type) Kind)\n(declare-fun PreType (Term) Type)\n(declare-fun Valid (Type) Bool)\n(declare-fun HasKind (Type Kind) Bool)\n(declare-fun HasTypeFuel (Fuel Term Type) Bool)\n(define-fun HasTypeZ ((x Term) (t Type)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Type)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Type))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Type)) (HasTypeZ x t)))\n(declare-fun ApplyEF (Term Fuel) Term)\n(declare-fun ApplyEE (Term Term) Term)\n(declare-fun ApplyET (Term Type) Term)\n(declare-fun ApplyTE (Type Term) Type)\n(declare-fun ApplyTT (Type Type) Type)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsType (Type Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Type)\n(assert (forall ((t Type))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.Precedes ((a Type) (b Type) (t1 Term) (t2 Term)) Type\n(Precedes t1 t2))\n")
in (
# 557 "FStar.ToSMT.Term.fst"
let constrs = ((("String_const"), (((("String_const_proj_0"), (Int_sort)))::[]), (String_sort), (0)))::((("Kind_type"), ([]), (Kind_sort), (0)))::((("Kind_arrow"), (((("Kind_arrow_id"), (Int_sort)))::[]), (Kind_sort), (1)))::((("Kind_uvar"), (((("Kind_uvar_fst"), (Int_sort)))::[]), (Kind_sort), (2)))::((("Typ_fun"), (((("Typ_fun_id"), (Int_sort)))::[]), (Type_sort), (1)))::((("Typ_app"), (((("Typ_app_fst"), (Type_sort)))::((("Typ_app_snd"), (Type_sort)))::[]), (Type_sort), (2)))::((("Typ_dep"), (((("Typ_dep_fst"), (Type_sort)))::((("Typ_dep_snd"), (Term_sort)))::[]), (Type_sort), (3)))::((("Typ_uvar"), (((("Typ_uvar_fst"), (Int_sort)))::[]), (Type_sort), (4)))::((("Term_unit"), ([]), (Term_sort), (0)))::((("BoxInt"), (((("BoxInt_proj_0"), (Int_sort)))::[]), (Term_sort), (1)))::((("BoxBool"), (((("BoxBool_proj_0"), (Bool_sort)))::[]), (Term_sort), (2)))::((("BoxString"), (((("BoxString_proj_0"), (String_sort)))::[]), (Term_sort), (3)))::((("BoxRef"), (((("BoxRef_proj_0"), (Ref_sort)))::[]), (Term_sort), (4)))::((("Exp_uvar"), (((("Exp_uvar_fst"), (Int_sort)))::[]), (Term_sort), (5)))::((("LexCons"), (((("LexCons_0"), (Term_sort)))::((("LexCons_1"), (Term_sort)))::[]), (Term_sort), (6)))::[]
in (
# 574 "FStar.ToSMT.Term.fst"
let bcons = (let _139_529 = (let _139_528 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _139_528 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _139_529 (FStar_String.concat "\n")))
in (
# 575 "FStar.ToSMT.Term.fst"
let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))

# 582 "FStar.ToSMT.Term.fst"
let mk_Kind_type : term = (mkApp (("Kind_type"), ([])))

# 584 "FStar.ToSMT.Term.fst"
let mk_Kind_uvar : Prims.int  ->  term = (fun i -> (let _139_534 = (let _139_533 = (let _139_532 = (mkInteger' i)
in (_139_532)::[])
in (("Kind_uvar"), (_139_533)))
in (mkApp _139_534)))

# 585 "FStar.ToSMT.Term.fst"
let mk_Typ_app : term  ->  term  ->  term = (fun t1 t2 -> (mkApp (("Typ_app"), ((t1)::(t2)::[]))))

# 586 "FStar.ToSMT.Term.fst"
let mk_Typ_dep : term  ->  term  ->  term = (fun t1 t2 -> (mkApp (("Typ_dep"), ((t1)::(t2)::[]))))

# 587 "FStar.ToSMT.Term.fst"
let mk_Typ_uvar : Prims.int  ->  term = (fun i -> (let _139_547 = (let _139_546 = (let _139_545 = (mkInteger' i)
in (_139_545)::[])
in (("Typ_uvar"), (_139_546)))
in (mkApp _139_547)))

# 588 "FStar.ToSMT.Term.fst"
let mk_Exp_uvar : Prims.int  ->  term = (fun i -> (let _139_552 = (let _139_551 = (let _139_550 = (mkInteger' i)
in (_139_550)::[])
in (("Exp_uvar"), (_139_551)))
in (mkApp _139_552)))

# 589 "FStar.ToSMT.Term.fst"
let mk_Term_unit : term = (mkApp (("Term_unit"), ([])))

# 591 "FStar.ToSMT.Term.fst"
let boxInt : term  ->  term = (fun t -> (mkApp (("BoxInt"), ((t)::[]))))

# 592 "FStar.ToSMT.Term.fst"
let unboxInt : term  ->  term = (fun t -> (mkApp (("BoxInt_proj_0"), ((t)::[]))))

# 593 "FStar.ToSMT.Term.fst"
let boxBool : term  ->  term = (fun t -> (mkApp (("BoxBool"), ((t)::[]))))

# 594 "FStar.ToSMT.Term.fst"
let unboxBool : term  ->  term = (fun t -> (mkApp (("BoxBool_proj_0"), ((t)::[]))))

# 595 "FStar.ToSMT.Term.fst"
let boxString : term  ->  term = (fun t -> (mkApp (("BoxString"), ((t)::[]))))

# 596 "FStar.ToSMT.Term.fst"
let unboxString : term  ->  term = (fun t -> (mkApp (("BoxString_proj_0"), ((t)::[]))))

# 597 "FStar.ToSMT.Term.fst"
let boxRef : term  ->  term = (fun t -> (mkApp (("BoxRef"), ((t)::[]))))

# 598 "FStar.ToSMT.Term.fst"
let unboxRef : term  ->  term = (fun t -> (mkApp (("BoxRef_proj_0"), ((t)::[]))))

# 599 "FStar.ToSMT.Term.fst"
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
| _47_723 -> begin
(Prims.raise FStar_Util.Impos)
end))

# 605 "FStar.ToSMT.Term.fst"
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
| _47_731 -> begin
(Prims.raise FStar_Util.Impos)
end))

# 611 "FStar.ToSMT.Term.fst"
let mk_PreKind : term  ->  term = (fun t -> (mkApp (("PreKind"), ((t)::[]))))

# 613 "FStar.ToSMT.Term.fst"
let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[]))))

# 614 "FStar.ToSMT.Term.fst"
let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (_47_746)::(t1)::(t2)::[]); hash = _47_740; freevars = _47_738})::[]) -> begin
(mkEq ((t1), (t2)))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (_47_765)::(t1)::(t2)::[]); hash = _47_759; freevars = _47_757})::[]) -> begin
(let _139_583 = (mkEq ((t1), (t2)))
in (mkNot _139_583))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); hash = _47_778; freevars = _47_776})::[]) -> begin
(let _139_586 = (let _139_585 = (unboxInt t1)
in (let _139_584 = (unboxInt t2)
in ((_139_585), (_139_584))))
in (mkLTE _139_586))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); hash = _47_795; freevars = _47_793})::[]) -> begin
(let _139_589 = (let _139_588 = (unboxInt t1)
in (let _139_587 = (unboxInt t2)
in ((_139_588), (_139_587))))
in (mkLT _139_589))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); hash = _47_812; freevars = _47_810})::[]) -> begin
(let _139_592 = (let _139_591 = (unboxInt t1)
in (let _139_590 = (unboxInt t2)
in ((_139_591), (_139_590))))
in (mkGTE _139_592))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); hash = _47_829; freevars = _47_827})::[]) -> begin
(let _139_595 = (let _139_594 = (unboxInt t1)
in (let _139_593 = (unboxInt t2)
in ((_139_594), (_139_593))))
in (mkGT _139_595))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); hash = _47_846; freevars = _47_844})::[]) -> begin
(let _139_598 = (let _139_597 = (unboxBool t1)
in (let _139_596 = (unboxBool t2)
in ((_139_597), (_139_596))))
in (mkAnd _139_598))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); hash = _47_863; freevars = _47_861})::[]) -> begin
(let _139_601 = (let _139_600 = (unboxBool t1)
in (let _139_599 = (unboxBool t2)
in ((_139_600), (_139_599))))
in (mkOr _139_601))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t)::[]); hash = _47_880; freevars = _47_878})::[]) -> begin
(let _139_602 = (unboxBool t)
in (mkNot _139_602))
end
| App (Var ("Prims.b2t"), (t)::[]) -> begin
(unboxBool t)
end
| _47_898 -> begin
(mkApp (("Valid"), ((t)::[])))
end))

# 626 "FStar.ToSMT.Term.fst"
let mk_HasType : term  ->  term  ->  term = (fun v t -> (mkApp (("HasType"), ((v)::(t)::[]))))

# 627 "FStar.ToSMT.Term.fst"
let mk_HasTypeZ : term  ->  term  ->  term = (fun v t -> (mkApp (("HasTypeZ"), ((v)::(t)::[]))))

# 628 "FStar.ToSMT.Term.fst"
let mk_IsTyped : term  ->  term = (fun v -> (mkApp (("IsTyped"), ((v)::[]))))

# 629 "FStar.ToSMT.Term.fst"
let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v t -> if (FStar_Options.unthrottle_inductives ()) then begin
(mk_HasType v t)
end else begin
(mkApp (("HasTypeFuel"), ((f)::(v)::(t)::[])))
end)

# 633 "FStar.ToSMT.Term.fst"
let mk_HasTypeWithFuel : term Prims.option  ->  term  ->  term  ->  term = (fun f v t -> (match (f) with
| None -> begin
(mk_HasType v t)
end
| Some (f) -> begin
(mk_HasTypeFuel f v t)
end))

# 636 "FStar.ToSMT.Term.fst"
let mk_Destruct : term  ->  term = (fun v -> (mkApp (("Destruct"), ((v)::[]))))

# 637 "FStar.ToSMT.Term.fst"
let mk_HasKind : term  ->  term  ->  term = (fun t k -> (mkApp (("HasKind"), ((t)::(k)::[]))))

# 638 "FStar.ToSMT.Term.fst"
let mk_Rank : term  ->  term = (fun x -> (mkApp (("Rank"), ((x)::[]))))

# 639 "FStar.ToSMT.Term.fst"
let mk_tester : Prims.string  ->  term  ->  term = (fun n t -> (mkApp (((Prims.strcat "is-" n)), ((t)::[]))))

# 640 "FStar.ToSMT.Term.fst"
let mk_ApplyTE : term  ->  term  ->  term = (fun t e -> (mkApp (("ApplyTE"), ((t)::(e)::[]))))

# 641 "FStar.ToSMT.Term.fst"
let mk_ApplyTT : term  ->  term  ->  term = (fun t t' -> (mkApp (("ApplyTT"), ((t)::(t')::[]))))

# 642 "FStar.ToSMT.Term.fst"
let mk_ApplyET : term  ->  term  ->  term = (fun e t -> (mkApp (("ApplyET"), ((e)::(t)::[]))))

# 643 "FStar.ToSMT.Term.fst"
let mk_ApplyEE : term  ->  term  ->  term = (fun e e' -> (mkApp (("ApplyEE"), ((e)::(e')::[]))))

# 644 "FStar.ToSMT.Term.fst"
let mk_ApplyEF : term  ->  term  ->  term = (fun e f -> (mkApp (("ApplyEF"), ((e)::(f)::[]))))

# 645 "FStar.ToSMT.Term.fst"
let mk_String_const : Prims.int  ->  term = (fun i -> (let _139_661 = (let _139_660 = (let _139_659 = (mkInteger' i)
in (_139_659)::[])
in (("String_const"), (_139_660)))
in (mkApp _139_661)))

# 646 "FStar.ToSMT.Term.fst"
let mk_Precedes : term  ->  term  ->  term = (fun x1 x2 -> (let _139_666 = (mkApp (("Precedes"), ((x1)::(x2)::[])))
in (FStar_All.pipe_right _139_666 mk_Valid)))

# 647 "FStar.ToSMT.Term.fst"
let mk_LexCons : term  ->  term  ->  term = (fun x1 x2 -> (mkApp (("LexCons"), ((x1)::(x2)::[]))))

# 648 "FStar.ToSMT.Term.fst"
let rec n_fuel : Prims.int  ->  term = (fun n -> if (n = 0) then begin
(mkApp (("ZFuel"), ([])))
end else begin
(let _139_675 = (let _139_674 = (let _139_673 = (n_fuel (n - 1))
in (_139_673)::[])
in (("SFuel"), (_139_674)))
in (mkApp _139_675))
end)

# 651 "FStar.ToSMT.Term.fst"
let fuel_2 : term = (n_fuel 2)

# 652 "FStar.ToSMT.Term.fst"
let fuel_100 : term = (n_fuel 100)

# 653 "FStar.ToSMT.Term.fst"
let mk_and_opt : term Prims.option  ->  term Prims.option  ->  term Prims.option = (fun p1 p2 -> (match (((p1), (p2))) with
| (Some (p1), Some (p2)) -> begin
(let _139_680 = (mkAnd ((p1), (p2)))
in Some (_139_680))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))

# 659 "FStar.ToSMT.Term.fst"
let mk_and_opt_l : term Prims.option Prims.list  ->  term Prims.option = (fun pl -> (FStar_List.fold_left (fun out p -> (mk_and_opt p out)) None pl))

# 662 "FStar.ToSMT.Term.fst"
let mk_and_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkTrue
end
| (hd)::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkAnd ((p1), (p2)))) hd tl)
end))

# 666 "FStar.ToSMT.Term.fst"
let mk_or_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkFalse
end
| (hd)::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkOr ((p1), (p2)))) hd tl)
end))

# 670 "FStar.ToSMT.Term.fst"
let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "Integer %s" n)
end
| BoundV (n) -> begin
(let _139_697 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "BoundV %s" _139_697))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "FreeV %s" (Prims.fst fv))
end
| App (op, l) -> begin
(let _139_698 = (print_smt_term_list l)
in (FStar_Util.format2 "App %s [ %s ]" (op_to_string op) _139_698))
end
| Quant (qop, l, _47_983, _47_985, t) -> begin
(let _139_700 = (print_smt_term_list_list l)
in (let _139_699 = (print_smt_term t)
in (FStar_Util.format3 "Quant %s %s %s" (qop_to_string qop) _139_700 _139_699)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s t -> (let _139_705 = (let _139_704 = (print_smt_term t)
in (Prims.strcat "; " _139_704))
in (Prims.strcat s _139_705))) "" l))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _139_711 = (let _139_710 = (let _139_709 = (print_smt_term_list l)
in (Prims.strcat _139_709 " ] "))
in (Prims.strcat "; [ " _139_710))
in (Prims.strcat s _139_711))) "" l))




