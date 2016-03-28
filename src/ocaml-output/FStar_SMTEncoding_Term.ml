
open Prims
# 24 "FStar.SMTEncoding.Term.fst"
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

# 27 "FStar.SMTEncoding.Term.fst"
let is_Bool_sort = (fun _discr_ -> (match (_discr_) with
| Bool_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.SMTEncoding.Term.fst"
let is_Int_sort = (fun _discr_ -> (match (_discr_) with
| Int_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 29 "FStar.SMTEncoding.Term.fst"
let is_String_sort = (fun _discr_ -> (match (_discr_) with
| String_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "FStar.SMTEncoding.Term.fst"
let is_Ref_sort = (fun _discr_ -> (match (_discr_) with
| Ref_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "FStar.SMTEncoding.Term.fst"
let is_Term_sort = (fun _discr_ -> (match (_discr_) with
| Term_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 32 "FStar.SMTEncoding.Term.fst"
let is_Fuel_sort = (fun _discr_ -> (match (_discr_) with
| Fuel_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 33 "FStar.SMTEncoding.Term.fst"
let is_Array = (fun _discr_ -> (match (_discr_) with
| Array (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "FStar.SMTEncoding.Term.fst"
let is_Arrow = (fun _discr_ -> (match (_discr_) with
| Arrow (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.SMTEncoding.Term.fst"
let is_Sort = (fun _discr_ -> (match (_discr_) with
| Sort (_) -> begin
true
end
| _ -> begin
false
end))

# 33 "FStar.SMTEncoding.Term.fst"
let ___Array____0 = (fun projectee -> (match (projectee) with
| Array (_75_10) -> begin
_75_10
end))

# 34 "FStar.SMTEncoding.Term.fst"
let ___Arrow____0 = (fun projectee -> (match (projectee) with
| Arrow (_75_13) -> begin
_75_13
end))

# 35 "FStar.SMTEncoding.Term.fst"
let ___Sort____0 = (fun projectee -> (match (projectee) with
| Sort (_75_16) -> begin
_75_16
end))

# 35 "FStar.SMTEncoding.Term.fst"
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
(let _160_52 = (strSort s1)
in (let _160_51 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _160_52 _160_51)))
end
| Arrow (s1, s2) -> begin
(let _160_54 = (strSort s1)
in (let _160_53 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _160_54 _160_53)))
end
| Sort (s) -> begin
s
end))

# 46 "FStar.SMTEncoding.Term.fst"
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

# 49 "FStar.SMTEncoding.Term.fst"
let is_True = (fun _discr_ -> (match (_discr_) with
| True (_) -> begin
true
end
| _ -> begin
false
end))

# 50 "FStar.SMTEncoding.Term.fst"
let is_False = (fun _discr_ -> (match (_discr_) with
| False (_) -> begin
true
end
| _ -> begin
false
end))

# 51 "FStar.SMTEncoding.Term.fst"
let is_Not = (fun _discr_ -> (match (_discr_) with
| Not (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "FStar.SMTEncoding.Term.fst"
let is_And = (fun _discr_ -> (match (_discr_) with
| And (_) -> begin
true
end
| _ -> begin
false
end))

# 53 "FStar.SMTEncoding.Term.fst"
let is_Or = (fun _discr_ -> (match (_discr_) with
| Or (_) -> begin
true
end
| _ -> begin
false
end))

# 54 "FStar.SMTEncoding.Term.fst"
let is_Imp = (fun _discr_ -> (match (_discr_) with
| Imp (_) -> begin
true
end
| _ -> begin
false
end))

# 55 "FStar.SMTEncoding.Term.fst"
let is_Iff = (fun _discr_ -> (match (_discr_) with
| Iff (_) -> begin
true
end
| _ -> begin
false
end))

# 56 "FStar.SMTEncoding.Term.fst"
let is_Eq = (fun _discr_ -> (match (_discr_) with
| Eq (_) -> begin
true
end
| _ -> begin
false
end))

# 57 "FStar.SMTEncoding.Term.fst"
let is_LT = (fun _discr_ -> (match (_discr_) with
| LT (_) -> begin
true
end
| _ -> begin
false
end))

# 58 "FStar.SMTEncoding.Term.fst"
let is_LTE = (fun _discr_ -> (match (_discr_) with
| LTE (_) -> begin
true
end
| _ -> begin
false
end))

# 59 "FStar.SMTEncoding.Term.fst"
let is_GT = (fun _discr_ -> (match (_discr_) with
| GT (_) -> begin
true
end
| _ -> begin
false
end))

# 60 "FStar.SMTEncoding.Term.fst"
let is_GTE = (fun _discr_ -> (match (_discr_) with
| GTE (_) -> begin
true
end
| _ -> begin
false
end))

# 61 "FStar.SMTEncoding.Term.fst"
let is_Add = (fun _discr_ -> (match (_discr_) with
| Add (_) -> begin
true
end
| _ -> begin
false
end))

# 62 "FStar.SMTEncoding.Term.fst"
let is_Sub = (fun _discr_ -> (match (_discr_) with
| Sub (_) -> begin
true
end
| _ -> begin
false
end))

# 63 "FStar.SMTEncoding.Term.fst"
let is_Div = (fun _discr_ -> (match (_discr_) with
| Div (_) -> begin
true
end
| _ -> begin
false
end))

# 64 "FStar.SMTEncoding.Term.fst"
let is_Mul = (fun _discr_ -> (match (_discr_) with
| Mul (_) -> begin
true
end
| _ -> begin
false
end))

# 65 "FStar.SMTEncoding.Term.fst"
let is_Minus = (fun _discr_ -> (match (_discr_) with
| Minus (_) -> begin
true
end
| _ -> begin
false
end))

# 66 "FStar.SMTEncoding.Term.fst"
let is_Mod = (fun _discr_ -> (match (_discr_) with
| Mod (_) -> begin
true
end
| _ -> begin
false
end))

# 67 "FStar.SMTEncoding.Term.fst"
let is_ITE = (fun _discr_ -> (match (_discr_) with
| ITE (_) -> begin
true
end
| _ -> begin
false
end))

# 68 "FStar.SMTEncoding.Term.fst"
let is_Var = (fun _discr_ -> (match (_discr_) with
| Var (_) -> begin
true
end
| _ -> begin
false
end))

# 68 "FStar.SMTEncoding.Term.fst"
let ___Var____0 = (fun projectee -> (match (projectee) with
| Var (_75_36) -> begin
_75_36
end))

# 68 "FStar.SMTEncoding.Term.fst"
type qop =
| Forall
| Exists

# 71 "FStar.SMTEncoding.Term.fst"
let is_Forall = (fun _discr_ -> (match (_discr_) with
| Forall (_) -> begin
true
end
| _ -> begin
false
end))

# 72 "FStar.SMTEncoding.Term.fst"
let is_Exists = (fun _discr_ -> (match (_discr_) with
| Exists (_) -> begin
true
end
| _ -> begin
false
end))

# 72 "FStar.SMTEncoding.Term.fst"
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

# 82 "FStar.SMTEncoding.Term.fst"
let is_Integer = (fun _discr_ -> (match (_discr_) with
| Integer (_) -> begin
true
end
| _ -> begin
false
end))

# 83 "FStar.SMTEncoding.Term.fst"
let is_BoundV = (fun _discr_ -> (match (_discr_) with
| BoundV (_) -> begin
true
end
| _ -> begin
false
end))

# 84 "FStar.SMTEncoding.Term.fst"
let is_FreeV = (fun _discr_ -> (match (_discr_) with
| FreeV (_) -> begin
true
end
| _ -> begin
false
end))

# 85 "FStar.SMTEncoding.Term.fst"
let is_App = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "FStar.SMTEncoding.Term.fst"
let is_Quant = (fun _discr_ -> (match (_discr_) with
| Quant (_) -> begin
true
end
| _ -> begin
false
end))

# 91 "FStar.SMTEncoding.Term.fst"
let is_Labeled = (fun _discr_ -> (match (_discr_) with
| Labeled (_) -> begin
true
end
| _ -> begin
false
end))

# 93 "FStar.SMTEncoding.Term.fst"
let is_Mkterm : term  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkterm"))))

# 82 "FStar.SMTEncoding.Term.fst"
let ___Integer____0 = (fun projectee -> (match (projectee) with
| Integer (_75_42) -> begin
_75_42
end))

# 83 "FStar.SMTEncoding.Term.fst"
let ___BoundV____0 = (fun projectee -> (match (projectee) with
| BoundV (_75_45) -> begin
_75_45
end))

# 84 "FStar.SMTEncoding.Term.fst"
let ___FreeV____0 = (fun projectee -> (match (projectee) with
| FreeV (_75_48) -> begin
_75_48
end))

# 85 "FStar.SMTEncoding.Term.fst"
let ___App____0 = (fun projectee -> (match (projectee) with
| App (_75_51) -> begin
_75_51
end))

# 86 "FStar.SMTEncoding.Term.fst"
let ___Quant____0 = (fun projectee -> (match (projectee) with
| Quant (_75_54) -> begin
_75_54
end))

# 91 "FStar.SMTEncoding.Term.fst"
let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_75_57) -> begin
_75_57
end))

# 95 "FStar.SMTEncoding.Term.fst"
type caption =
Prims.string Prims.option

# 97 "FStar.SMTEncoding.Term.fst"
type binders =
(Prims.string * sort) Prims.list

# 98 "FStar.SMTEncoding.Term.fst"
type projector =
(Prims.string * sort)

# 99 "FStar.SMTEncoding.Term.fst"
type constructor_t =
(Prims.string * projector Prims.list * sort * Prims.int * Prims.bool)

# 100 "FStar.SMTEncoding.Term.fst"
type constructors =
constructor_t Prims.list

# 101 "FStar.SMTEncoding.Term.fst"
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

# 103 "FStar.SMTEncoding.Term.fst"
let is_DefPrelude = (fun _discr_ -> (match (_discr_) with
| DefPrelude (_) -> begin
true
end
| _ -> begin
false
end))

# 104 "FStar.SMTEncoding.Term.fst"
let is_DeclFun = (fun _discr_ -> (match (_discr_) with
| DeclFun (_) -> begin
true
end
| _ -> begin
false
end))

# 105 "FStar.SMTEncoding.Term.fst"
let is_DefineFun = (fun _discr_ -> (match (_discr_) with
| DefineFun (_) -> begin
true
end
| _ -> begin
false
end))

# 106 "FStar.SMTEncoding.Term.fst"
let is_Assume = (fun _discr_ -> (match (_discr_) with
| Assume (_) -> begin
true
end
| _ -> begin
false
end))

# 107 "FStar.SMTEncoding.Term.fst"
let is_Caption = (fun _discr_ -> (match (_discr_) with
| Caption (_) -> begin
true
end
| _ -> begin
false
end))

# 108 "FStar.SMTEncoding.Term.fst"
let is_Eval = (fun _discr_ -> (match (_discr_) with
| Eval (_) -> begin
true
end
| _ -> begin
false
end))

# 109 "FStar.SMTEncoding.Term.fst"
let is_Echo = (fun _discr_ -> (match (_discr_) with
| Echo (_) -> begin
true
end
| _ -> begin
false
end))

# 110 "FStar.SMTEncoding.Term.fst"
let is_Push = (fun _discr_ -> (match (_discr_) with
| Push (_) -> begin
true
end
| _ -> begin
false
end))

# 111 "FStar.SMTEncoding.Term.fst"
let is_Pop = (fun _discr_ -> (match (_discr_) with
| Pop (_) -> begin
true
end
| _ -> begin
false
end))

# 112 "FStar.SMTEncoding.Term.fst"
let is_CheckSat = (fun _discr_ -> (match (_discr_) with
| CheckSat (_) -> begin
true
end
| _ -> begin
false
end))

# 104 "FStar.SMTEncoding.Term.fst"
let ___DeclFun____0 = (fun projectee -> (match (projectee) with
| DeclFun (_75_61) -> begin
_75_61
end))

# 105 "FStar.SMTEncoding.Term.fst"
let ___DefineFun____0 = (fun projectee -> (match (projectee) with
| DefineFun (_75_64) -> begin
_75_64
end))

# 106 "FStar.SMTEncoding.Term.fst"
let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_75_67) -> begin
_75_67
end))

# 107 "FStar.SMTEncoding.Term.fst"
let ___Caption____0 = (fun projectee -> (match (projectee) with
| Caption (_75_70) -> begin
_75_70
end))

# 108 "FStar.SMTEncoding.Term.fst"
let ___Eval____0 = (fun projectee -> (match (projectee) with
| Eval (_75_73) -> begin
_75_73
end))

# 109 "FStar.SMTEncoding.Term.fst"
let ___Echo____0 = (fun projectee -> (match (projectee) with
| Echo (_75_76) -> begin
_75_76
end))

# 112 "FStar.SMTEncoding.Term.fst"
type decls_t =
decl Prims.list

# 113 "FStar.SMTEncoding.Term.fst"
type error_label =
(fv * Prims.string * FStar_Range.range)

# 115 "FStar.SMTEncoding.Term.fst"
type error_labels =
error_label Prims.list

# 192 "FStar.SMTEncoding.Term.fst"
let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> ((Prims.fst x) = (Prims.fst y)))

# 194 "FStar.SMTEncoding.Term.fst"
let fv_sort = (fun x -> (Prims.snd x))

# 195 "FStar.SMTEncoding.Term.fst"
let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match ((x.tm, y.tm)) with
| (FreeV (x), FreeV (y)) -> begin
(fv_eq x y)
end
| _75_88 -> begin
false
end))

# 198 "FStar.SMTEncoding.Term.fst"
let freevar_sort : term  ->  sort = (fun _75_1 -> (match (_75_1) with
| {tm = FreeV (x); hash = _75_93; freevars = _75_91} -> begin
(fv_sort x)
end
| _75_98 -> begin
(FStar_All.failwith "impossible")
end))

# 201 "FStar.SMTEncoding.Term.fst"
let fv_of_term : term  ->  fv = (fun _75_2 -> (match (_75_2) with
| {tm = FreeV (fv); hash = _75_103; freevars = _75_101} -> begin
fv
end
| _75_108 -> begin
(FStar_All.failwith "impossible")
end))

# 204 "FStar.SMTEncoding.Term.fst"
let rec freevars : term  ->  fv Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (_75_119, tms) -> begin
(FStar_List.collect freevars tms)
end
| (Quant (_, _, _, _, t)) | (Labeled (t, _, _)) -> begin
(freevars t)
end))

# 211 "FStar.SMTEncoding.Term.fst"
let free_variables : term  ->  fvs = (fun t -> (match ((FStar_ST.read t.freevars)) with
| Some (b) -> begin
b
end
| None -> begin
(
# 217 "FStar.SMTEncoding.Term.fst"
let fvs = (let _160_289 = (freevars t)
in (FStar_Util.remove_dups fv_eq _160_289))
in (
# 218 "FStar.SMTEncoding.Term.fst"
let _75_145 = (FStar_ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))

# 219 "FStar.SMTEncoding.Term.fst"
let qop_to_string : qop  ->  Prims.string = (fun _75_3 -> (match (_75_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))

# 226 "FStar.SMTEncoding.Term.fst"
let op_to_string : op  ->  Prims.string = (fun _75_4 -> (match (_75_4) with
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

# 248 "FStar.SMTEncoding.Term.fst"
let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun _75_5 -> (match (_75_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _160_296 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _160_296))
end))

# 252 "FStar.SMTEncoding.Term.fst"
let hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _160_299 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _160_299))
end
| FreeV (x) -> begin
(let _160_300 = (strSort (Prims.snd x))
in (Prims.strcat (Prims.strcat (Prims.fst x) ":") _160_300))
end
| App (op, tms) -> begin
(let _160_304 = (let _160_303 = (let _160_302 = (FStar_List.map (fun t -> t.hash) tms)
in (FStar_All.pipe_right _160_302 (FStar_String.concat " ")))
in (Prims.strcat (Prims.strcat "(" (op_to_string op)) _160_303))
in (Prims.strcat _160_304 ")"))
end
| Labeled (t, r1, r2) -> begin
(let _160_305 = (FStar_Range.string_of_range r2)
in (Prims.strcat (Prims.strcat t.hash r1) _160_305))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _160_313 = (let _160_306 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _160_306 (FStar_String.concat " ")))
in (let _160_312 = (weightToSmt wopt)
in (let _160_311 = (let _160_310 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _160_309 = (FStar_List.map (fun p -> p.hash) pats)
in (FStar_All.pipe_right _160_309 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _160_310 (FStar_String.concat "; ")))
in (FStar_Util.format5 "(%s (%s)(! %s %s %s))" (qop_to_string qop) _160_313 body.hash _160_312 _160_311))))
end))

# 266 "FStar.SMTEncoding.Term.fst"
let __all_terms : term FStar_Util.smap FStar_ST.ref = (let _160_314 = (FStar_Util.smap_create 10000)
in (FStar_ST.alloc _160_314))

# 269 "FStar.SMTEncoding.Term.fst"
let all_terms : Prims.unit  ->  term FStar_Util.smap = (fun _75_202 -> (match (()) with
| () -> begin
(FStar_ST.read __all_terms)
end))

# 270 "FStar.SMTEncoding.Term.fst"
let mk : term'  ->  term = (fun t -> (
# 272 "FStar.SMTEncoding.Term.fst"
let key = (hash_of_term' t)
in (match ((let _160_319 = (all_terms ())
in (FStar_Util.smap_try_find _160_319 key))) with
| Some (tm) -> begin
tm
end
| None -> begin
(
# 276 "FStar.SMTEncoding.Term.fst"
let tm = (let _160_320 = (FStar_Util.mk_ref None)
in {tm = t; hash = key; freevars = _160_320})
in (
# 277 "FStar.SMTEncoding.Term.fst"
let _75_209 = (let _160_321 = (all_terms ())
in (FStar_Util.smap_add _160_321 key tm))
in tm))
end)))

# 278 "FStar.SMTEncoding.Term.fst"
let mkTrue : term = (mk (App ((True, []))))

# 280 "FStar.SMTEncoding.Term.fst"
let mkFalse : term = (mk (App ((False, []))))

# 281 "FStar.SMTEncoding.Term.fst"
let mkInteger : Prims.string  ->  term = (fun i -> (mk (Integer (i))))

# 282 "FStar.SMTEncoding.Term.fst"
let mkInteger32 : Prims.int32  ->  term = (fun i -> (mkInteger (FStar_Util.string_of_int32 i)))

# 283 "FStar.SMTEncoding.Term.fst"
let mkInteger' : Prims.int  ->  term = (fun i -> (let _160_328 = (FStar_Util.string_of_int i)
in (mkInteger _160_328)))

# 284 "FStar.SMTEncoding.Term.fst"
let mkBoundV : Prims.int  ->  term = (fun i -> (mk (BoundV (i))))

# 285 "FStar.SMTEncoding.Term.fst"
let mkFreeV : (Prims.string * sort)  ->  term = (fun x -> (mk (FreeV (x))))

# 286 "FStar.SMTEncoding.Term.fst"
let mkApp' : (op * term Prims.list)  ->  term = (fun f -> (mk (App (f))))

# 287 "FStar.SMTEncoding.Term.fst"
let mkApp : (Prims.string * term Prims.list)  ->  term = (fun _75_219 -> (match (_75_219) with
| (s, args) -> begin
(mk (App ((Var (s), args))))
end))

# 288 "FStar.SMTEncoding.Term.fst"
let mkNot : term  ->  term = (fun t -> (match (t.tm) with
| App (True, _75_223) -> begin
mkFalse
end
| App (False, _75_228) -> begin
mkTrue
end
| _75_232 -> begin
(mkApp' (Not, (t)::[]))
end))

# 292 "FStar.SMTEncoding.Term.fst"
let mkAnd : (term * term)  ->  term = (fun _75_235 -> (match (_75_235) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (App (True, _75_238), _75_242) -> begin
t2
end
| (_75_245, App (True, _75_248)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
mkFalse
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' (And, (FStar_List.append ts1 ts2)))
end
| (_75_278, App (And, ts2)) -> begin
(mkApp' (And, (t1)::ts2))
end
| (App (And, ts1), _75_289) -> begin
(mkApp' (And, (FStar_List.append ts1 ((t2)::[]))))
end
| _75_292 -> begin
(mkApp' (And, (t1)::(t2)::[]))
end)
end))

# 301 "FStar.SMTEncoding.Term.fst"
let mkOr : (term * term)  ->  term = (fun _75_295 -> (match (_75_295) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
mkTrue
end
| (App (False, _75_314), _75_318) -> begin
t2
end
| (_75_321, App (False, _75_324)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' (Or, (FStar_List.append ts1 ts2)))
end
| (_75_338, App (Or, ts2)) -> begin
(mkApp' (Or, (t1)::ts2))
end
| (App (Or, ts1), _75_349) -> begin
(mkApp' (Or, (FStar_List.append ts1 ((t2)::[]))))
end
| _75_352 -> begin
(mkApp' (Or, (t1)::(t2)::[]))
end)
end))

# 310 "FStar.SMTEncoding.Term.fst"
let mkImp : (term * term)  ->  term = (fun _75_355 -> (match (_75_355) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (_75_357, App (True, _75_360)) -> begin
mkTrue
end
| (App (True, _75_366), _75_370) -> begin
t2
end
| (_75_373, App (Imp, t1'::t2'::[])) -> begin
(let _160_347 = (let _160_346 = (let _160_345 = (mkAnd (t1, t1'))
in (_160_345)::(t2')::[])
in (Imp, _160_346))
in (mkApp' _160_347))
end
| _75_382 -> begin
(mkApp' (Imp, (t1)::(t2)::[]))
end)
end))

# 315 "FStar.SMTEncoding.Term.fst"
let mk_bin_op : op  ->  (term * term)  ->  term = (fun op _75_386 -> (match (_75_386) with
| (t1, t2) -> begin
(mkApp' (op, (t1)::(t2)::[]))
end))

# 317 "FStar.SMTEncoding.Term.fst"
let mkMinus : term  ->  term = (fun t -> (mkApp' (Minus, (t)::[])))

# 318 "FStar.SMTEncoding.Term.fst"
let mkIff : (term * term)  ->  term = (mk_bin_op Iff)

# 319 "FStar.SMTEncoding.Term.fst"
let mkEq : (term * term)  ->  term = (mk_bin_op Eq)

# 320 "FStar.SMTEncoding.Term.fst"
let mkLT : (term * term)  ->  term = (mk_bin_op LT)

# 321 "FStar.SMTEncoding.Term.fst"
let mkLTE : (term * term)  ->  term = (mk_bin_op LTE)

# 322 "FStar.SMTEncoding.Term.fst"
let mkGT : (term * term)  ->  term = (mk_bin_op GT)

# 323 "FStar.SMTEncoding.Term.fst"
let mkGTE : (term * term)  ->  term = (mk_bin_op GTE)

# 324 "FStar.SMTEncoding.Term.fst"
let mkAdd : (term * term)  ->  term = (mk_bin_op Add)

# 325 "FStar.SMTEncoding.Term.fst"
let mkSub : (term * term)  ->  term = (mk_bin_op Sub)

# 326 "FStar.SMTEncoding.Term.fst"
let mkDiv : (term * term)  ->  term = (mk_bin_op Div)

# 327 "FStar.SMTEncoding.Term.fst"
let mkMul : (term * term)  ->  term = (mk_bin_op Mul)

# 328 "FStar.SMTEncoding.Term.fst"
let mkMod : (term * term)  ->  term = (mk_bin_op Mod)

# 329 "FStar.SMTEncoding.Term.fst"
let mkITE : (term * term * term)  ->  term = (fun _75_391 -> (match (_75_391) with
| (t1, t2, t3) -> begin
(match ((t2.tm, t3.tm)) with
| (App (True, _75_394), App (True, _75_399)) -> begin
mkTrue
end
| (App (True, _75_405), _75_409) -> begin
(let _160_368 = (let _160_367 = (mkNot t1)
in (_160_367, t3))
in (mkImp _160_368))
end
| (_75_412, App (True, _75_415)) -> begin
(mkImp (t1, t2))
end
| (_75_420, _75_422) -> begin
(mkApp' (ITE, (t1)::(t2)::(t3)::[]))
end)
end))

# 335 "FStar.SMTEncoding.Term.fst"
let mkCases : term Prims.list  ->  term = (fun t -> (match (t) with
| [] -> begin
(FStar_All.failwith "Impos")
end
| hd::tl -> begin
(FStar_List.fold_left (fun out t -> (mkAnd (out, t))) hd tl)
end))

# 338 "FStar.SMTEncoding.Term.fst"
let mkQuant : (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _75_436 -> (match (_75_436) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = 0) then begin
body
end else begin
(match (body.tm) with
| App (True, _75_439) -> begin
body
end
| _75_443 -> begin
(mk (Quant ((qop, pats, wopt, vars, body))))
end)
end
end))

# 344 "FStar.SMTEncoding.Term.fst"
let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (
# 350 "FStar.SMTEncoding.Term.fst"
let nvars = (FStar_List.length fvs)
in (
# 351 "FStar.SMTEncoding.Term.fst"
let index_of = (fun fv -> (match ((FStar_Util.try_find_index (fv_eq fv) fvs)) with
| None -> begin
None
end
| Some (i) -> begin
Some ((nvars - (i + 1)))
end))
in (
# 354 "FStar.SMTEncoding.Term.fst"
let rec aux = (fun ix t -> (match ((FStar_ST.read t.freevars)) with
| Some ([]) -> begin
t
end
| _75_458 -> begin
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
(let _160_386 = (let _160_385 = (FStar_List.map (aux ix) tms)
in (op, _160_385))
in (mkApp' _160_386))
end
| Labeled (t, r1, r2) -> begin
(let _160_389 = (let _160_388 = (let _160_387 = (aux ix t)
in (_160_387, r1, r2))
in Labeled (_160_388))
in (mk _160_389))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(
# 369 "FStar.SMTEncoding.Term.fst"
let n = (FStar_List.length vars)
in (let _160_392 = (let _160_391 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _160_390 = (aux (ix + n) body)
in (qop, _160_391, wopt, vars, _160_390)))
in (mkQuant _160_392)))
end)
end))
in (aux 0 t)))))

# 372 "FStar.SMTEncoding.Term.fst"
let inst : term Prims.list  ->  term  ->  term = (fun tms t -> (
# 375 "FStar.SMTEncoding.Term.fst"
let n = (FStar_List.length tms)
in (
# 376 "FStar.SMTEncoding.Term.fst"
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
(let _160_402 = (let _160_401 = (FStar_List.map (aux shift) tms)
in (op, _160_401))
in (mkApp' _160_402))
end
| Labeled (t, r1, r2) -> begin
(let _160_405 = (let _160_404 = (let _160_403 = (aux shift t)
in (_160_403, r1, r2))
in Labeled (_160_404))
in (mk _160_405))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(
# 386 "FStar.SMTEncoding.Term.fst"
let m = (FStar_List.length vars)
in (
# 387 "FStar.SMTEncoding.Term.fst"
let shift = (shift + m)
in (let _160_408 = (let _160_407 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _160_406 = (aux shift body)
in (qop, _160_407, wopt, vars, _160_406)))
in (mkQuant _160_408))))
end))
in (aux 0 t))))

# 389 "FStar.SMTEncoding.Term.fst"
let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list * term)  ->  term = (fun _75_524 -> (match (_75_524) with
| (qop, pats, wopt, vars, body) -> begin
(let _160_414 = (let _160_413 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _160_412 = (FStar_List.map fv_sort vars)
in (let _160_411 = (abstr vars body)
in (qop, _160_413, wopt, _160_412, _160_411))))
in (mkQuant _160_414))
end))

# 391 "FStar.SMTEncoding.Term.fst"
let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _75_529 -> (match (_75_529) with
| (pats, wopt, sorts, body) -> begin
(mkQuant (Forall, pats, wopt, sorts, body))
end))

# 392 "FStar.SMTEncoding.Term.fst"
let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  term = (fun _75_534 -> (match (_75_534) with
| (pats, wopt, vars, body) -> begin
(mkQuant' (Forall, pats, wopt, vars, body))
end))

# 393 "FStar.SMTEncoding.Term.fst"
let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _75_538 -> (match (_75_538) with
| (pats, vars, body) -> begin
(mkQuant' (Forall, pats, None, vars, body))
end))

# 396 "FStar.SMTEncoding.Term.fst"
let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _75_542 -> (match (_75_542) with
| (pats, vars, body) -> begin
(mkQuant' (Exists, pats, None, vars, body))
end))

# 397 "FStar.SMTEncoding.Term.fst"
let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun _75_548 -> (match (_75_548) with
| (nm, vars, s, tm, c) -> begin
(let _160_427 = (let _160_426 = (FStar_List.map fv_sort vars)
in (let _160_425 = (abstr vars tm)
in (nm, _160_426, s, _160_425, c)))
in DefineFun (_160_427))
end))

# 400 "FStar.SMTEncoding.Term.fst"
let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _160_430 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _160_430)))

# 401 "FStar.SMTEncoding.Term.fst"
let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun _75_552 id -> (match (_75_552) with
| (tok_name, sort) -> begin
(let _160_443 = (let _160_442 = (let _160_441 = (let _160_440 = (mkInteger' id)
in (let _160_439 = (let _160_438 = (let _160_437 = (constr_id_of_sort sort)
in (let _160_436 = (let _160_435 = (mkApp (tok_name, []))
in (_160_435)::[])
in (_160_437, _160_436)))
in (mkApp _160_438))
in (_160_440, _160_439)))
in (mkEq _160_441))
in (_160_442, Some ("fresh token")))
in Assume (_160_443))
end))

# 403 "FStar.SMTEncoding.Term.fst"
let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun _75_558 -> (match (_75_558) with
| (name, arg_sorts, sort, id) -> begin
(
# 406 "FStar.SMTEncoding.Term.fst"
let id = (FStar_Util.string_of_int id)
in (
# 407 "FStar.SMTEncoding.Term.fst"
let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (let _160_450 = (let _160_449 = (let _160_448 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _160_448))
in (_160_449, s))
in (mkFreeV _160_450)))))
in (
# 408 "FStar.SMTEncoding.Term.fst"
let bvar_names = (FStar_List.map fv_of_term bvars)
in (
# 409 "FStar.SMTEncoding.Term.fst"
let capp = (mkApp (name, bvars))
in (
# 410 "FStar.SMTEncoding.Term.fst"
let cid_app = (let _160_452 = (let _160_451 = (constr_id_of_sort sort)
in (_160_451, (capp)::[]))
in (mkApp _160_452))
in (let _160_458 = (let _160_457 = (let _160_456 = (let _160_455 = (let _160_454 = (let _160_453 = (mkInteger id)
in (_160_453, cid_app))
in (mkEq _160_454))
in (((capp)::[])::[], bvar_names, _160_455))
in (mkForall _160_456))
in (_160_457, Some ("Constructor distinct")))
in Assume (_160_458)))))))
end))

# 411 "FStar.SMTEncoding.Term.fst"
let injective_constructor : (Prims.string * (Prims.string * sort) Prims.list * sort)  ->  decls_t = (fun _75_569 -> (match (_75_569) with
| (name, projectors, sort) -> begin
(
# 414 "FStar.SMTEncoding.Term.fst"
let n_bvars = (FStar_List.length projectors)
in (
# 415 "FStar.SMTEncoding.Term.fst"
let bvar_name = (fun i -> (let _160_463 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _160_463)))
in (
# 416 "FStar.SMTEncoding.Term.fst"
let bvar_index = (fun i -> (n_bvars - (i + 1)))
in (
# 417 "FStar.SMTEncoding.Term.fst"
let bvar = (fun i s -> (let _160_471 = (let _160_470 = (bvar_name i)
in (_160_470, s))
in (mkFreeV _160_471)))
in (
# 418 "FStar.SMTEncoding.Term.fst"
let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _75_582 -> (match (_75_582) with
| (_75_580, s) -> begin
(bvar i s)
end))))
in (
# 419 "FStar.SMTEncoding.Term.fst"
let bvar_names = (FStar_List.map fv_of_term bvars)
in (
# 420 "FStar.SMTEncoding.Term.fst"
let capp = (mkApp (name, bvars))
in (let _160_484 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _75_589 -> (match (_75_589) with
| (name, s) -> begin
(
# 423 "FStar.SMTEncoding.Term.fst"
let cproj_app = (mkApp (name, (capp)::[]))
in (
# 424 "FStar.SMTEncoding.Term.fst"
let proj_name = DeclFun ((name, (sort)::[], s, Some ("Projector")))
in (let _160_483 = (let _160_482 = (let _160_481 = (let _160_480 = (let _160_479 = (let _160_478 = (let _160_477 = (let _160_476 = (bvar i s)
in (cproj_app, _160_476))
in (mkEq _160_477))
in (((capp)::[])::[], bvar_names, _160_478))
in (mkForall _160_479))
in (_160_480, Some ("Projection inverse")))
in Assume (_160_481))
in (_160_482)::[])
in (proj_name)::_160_483)))
end))))
in (FStar_All.pipe_right _160_484 FStar_List.flatten)))))))))
end))

# 427 "FStar.SMTEncoding.Term.fst"
let constructor_to_decl : constructor_t  ->  decls_t = (fun _75_597 -> (match (_75_597) with
| (name, projectors, sort, id, injective) -> begin
(
# 430 "FStar.SMTEncoding.Term.fst"
let injective = (injective || true)
in (
# 431 "FStar.SMTEncoding.Term.fst"
let cdecl = (let _160_488 = (let _160_487 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in (name, _160_487, sort, Some ("Constructor")))
in DeclFun (_160_488))
in (
# 432 "FStar.SMTEncoding.Term.fst"
let cid = (let _160_490 = (let _160_489 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in (name, _160_489, sort, id))
in (fresh_constructor _160_490))
in (
# 433 "FStar.SMTEncoding.Term.fst"
let disc = (
# 434 "FStar.SMTEncoding.Term.fst"
let disc_name = (Prims.strcat "is-" name)
in (
# 435 "FStar.SMTEncoding.Term.fst"
let xfv = ("x", sort)
in (
# 436 "FStar.SMTEncoding.Term.fst"
let xx = (mkFreeV xfv)
in (
# 437 "FStar.SMTEncoding.Term.fst"
let disc_eq = (let _160_496 = (let _160_495 = (let _160_492 = (let _160_491 = (constr_id_of_sort sort)
in (_160_491, (xx)::[]))
in (mkApp _160_492))
in (let _160_494 = (let _160_493 = (FStar_Util.string_of_int id)
in (mkInteger _160_493))
in (_160_495, _160_494)))
in (mkEq _160_496))
in (
# 438 "FStar.SMTEncoding.Term.fst"
let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _75_607 -> (match (_75_607) with
| (proj, s) -> begin
(mkApp (proj, (xx)::[]))
end))))
in (
# 439 "FStar.SMTEncoding.Term.fst"
let disc_inv_body = (let _160_499 = (let _160_498 = (mkApp (name, proj_terms))
in (xx, _160_498))
in (mkEq _160_499))
in (
# 440 "FStar.SMTEncoding.Term.fst"
let disc_ax = (mkAnd (disc_eq, disc_inv_body))
in (mkDefineFun (disc_name, (xfv)::[], Bool_sort, disc_ax, Some ("Discriminator definition"))))))))))
in (
# 444 "FStar.SMTEncoding.Term.fst"
let projs = if injective then begin
(injective_constructor (name, projectors, sort))
end else begin
[]
end
in (let _160_506 = (let _160_502 = (let _160_501 = (let _160_500 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_160_500))
in (_160_501)::(cdecl)::(cid)::projs)
in (FStar_List.append _160_502 ((disc)::[])))
in (let _160_505 = (let _160_504 = (let _160_503 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_160_503))
in (_160_504)::[])
in (FStar_List.append _160_506 _160_505))))))))
end))

# 448 "FStar.SMTEncoding.Term.fst"
let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (
# 455 "FStar.SMTEncoding.Term.fst"
let _75_631 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _75_619 s -> (match (_75_619) with
| (names, binders, n) -> begin
(
# 456 "FStar.SMTEncoding.Term.fst"
let prefix = (match (s) with
| Term_sort -> begin
"@x"
end
| _75_623 -> begin
"@u"
end)
in (
# 459 "FStar.SMTEncoding.Term.fst"
let nm = (let _160_515 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _160_515))
in (
# 460 "FStar.SMTEncoding.Term.fst"
let names = ((nm, s))::names
in (
# 461 "FStar.SMTEncoding.Term.fst"
let b = (let _160_516 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _160_516))
in (names, (b)::binders, (n + 1))))))
end)) (outer_names, [], start)))
in (match (_75_631) with
| (names, binders, n) -> begin
(names, (FStar_List.rev binders), n)
end)))

# 464 "FStar.SMTEncoding.Term.fst"
let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (
# 467 "FStar.SMTEncoding.Term.fst"
let _75_636 = (name_binders_inner [] 0 sorts)
in (match (_75_636) with
| (names, binders, n) -> begin
((FStar_List.rev names), binders)
end)))

# 468 "FStar.SMTEncoding.Term.fst"
let termToSmt : term  ->  Prims.string = (fun t -> (
# 471 "FStar.SMTEncoding.Term.fst"
let rec aux = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _160_527 = (FStar_List.nth names i)
in (FStar_All.pipe_right _160_527 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _160_529 = (let _160_528 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _160_528 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _160_529))
end
| Labeled (t, _75_658, _75_660) -> begin
(aux n names t)
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(
# 480 "FStar.SMTEncoding.Term.fst"
let _75_673 = (name_binders_inner names n sorts)
in (match (_75_673) with
| (names, binders, n) -> begin
(
# 481 "FStar.SMTEncoding.Term.fst"
let binders = (FStar_All.pipe_right binders (FStar_String.concat " "))
in (
# 482 "FStar.SMTEncoding.Term.fst"
let pats_str = (match (pats) with
| ([]::[]) | ([]) -> begin
""
end
| _75_679 -> begin
(let _160_535 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _160_534 = (let _160_533 = (FStar_List.map (fun p -> (let _160_532 = (aux n names p)
in (FStar_Util.format1 "%s" _160_532))) pats)
in (FStar_String.concat " " _160_533))
in (FStar_Util.format1 "\n:pattern (%s)" _160_534)))))
in (FStar_All.pipe_right _160_535 (FStar_String.concat "\n")))
end)
in (match ((pats, wopt)) with
| (([]::[], None)) | (([], None)) -> begin
(let _160_536 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _160_536))
end
| _75_691 -> begin
(let _160_538 = (aux n names body)
in (let _160_537 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _160_538 _160_537 pats_str)))
end)))
end))
end))
in (aux 0 [] t)))

# 491 "FStar.SMTEncoding.Term.fst"
let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun _75_6 -> (match (_75_6) with
| None -> begin
""
end
| Some (c) -> begin
(
# 497 "FStar.SMTEncoding.Term.fst"
let _75_705 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::[] -> begin
(hd, "")
end
| hd::_75_700 -> begin
(hd, "...")
end)
in (match (_75_705) with
| (hd, suffix) -> begin
(FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd suffix)
end))
end))

# 501 "FStar.SMTEncoding.Term.fst"
let rec declToSmt : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(let _160_547 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _75_7 -> (match (_75_7) with
| [] -> begin
""
end
| h::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _160_547))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(
# 508 "FStar.SMTEncoding.Term.fst"
let l = (FStar_List.map strSort argsorts)
in (let _160_549 = (caption_to_string c)
in (let _160_548 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _160_549 f (FStar_String.concat " " l) _160_548))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(
# 511 "FStar.SMTEncoding.Term.fst"
let _75_732 = (name_binders arg_sorts)
in (match (_75_732) with
| (names, binders) -> begin
(
# 512 "FStar.SMTEncoding.Term.fst"
let body = (let _160_550 = (FStar_List.map mkFreeV names)
in (inst _160_550 body))
in (let _160_553 = (caption_to_string c)
in (let _160_552 = (strSort retsort)
in (let _160_551 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _160_553 f (FStar_String.concat " " binders) _160_552 _160_551)))))
end))
end
| Assume (t, c) -> begin
(let _160_555 = (caption_to_string c)
in (let _160_554 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _160_555 _160_554)))
end
| Eval (t) -> begin
(let _160_556 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _160_556))
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
# 525 "FStar.SMTEncoding.Term.fst"
let basic = (Prims.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort String)\n(declare-fun String_constr_id (String) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n")
in (
# 571 "FStar.SMTEncoding.Term.fst"
let constrs = (("String_const", (("String_const_proj_0", Int_sort))::[], String_sort, 0, true))::(("Tm_type", [], Term_sort, 2, true))::(("Tm_arrow", (("Tm_arrow_id", Int_sort))::[], Term_sort, 3, false))::(("Tm_uvar", (("Tm_uvar_fst", Int_sort))::[], Term_sort, 5, true))::(("Tm_unit", [], Term_sort, 6, true))::(("BoxInt", (("BoxInt_proj_0", Int_sort))::[], Term_sort, 7, true))::(("BoxBool", (("BoxBool_proj_0", Bool_sort))::[], Term_sort, 8, true))::(("BoxString", (("BoxString_proj_0", String_sort))::[], Term_sort, 9, true))::(("BoxRef", (("BoxRef_proj_0", Ref_sort))::[], Term_sort, 10, true))::(("LexCons", (("LexCons_0", Term_sort))::(("LexCons_1", Term_sort))::[], Term_sort, 11, true))::[]
in (
# 581 "FStar.SMTEncoding.Term.fst"
let bcons = (let _160_559 = (let _160_558 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _160_558 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _160_559 (FStar_String.concat "\n")))
in (
# 582 "FStar.SMTEncoding.Term.fst"
let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat (Prims.strcat basic bcons) lex_ordering))))))

# 589 "FStar.SMTEncoding.Term.fst"
let mk_Range_const : term = (mkApp ("Range_const", []))

# 591 "FStar.SMTEncoding.Term.fst"
let mk_Term_type : term = (mkApp ("Tm_type", []))

# 592 "FStar.SMTEncoding.Term.fst"
let mk_Term_app : term  ->  term  ->  term = (fun t1 t2 -> (mkApp ("Tm_app", (t1)::(t2)::[])))

# 593 "FStar.SMTEncoding.Term.fst"
let mk_Term_uvar : Prims.int  ->  term = (fun i -> (let _160_568 = (let _160_567 = (let _160_566 = (mkInteger' i)
in (_160_566)::[])
in ("Tm_uvar", _160_567))
in (mkApp _160_568)))

# 594 "FStar.SMTEncoding.Term.fst"
let mk_Term_unit : term = (mkApp ("Tm_unit", []))

# 595 "FStar.SMTEncoding.Term.fst"
let boxInt : term  ->  term = (fun t -> (mkApp ("BoxInt", (t)::[])))

# 596 "FStar.SMTEncoding.Term.fst"
let unboxInt : term  ->  term = (fun t -> (mkApp ("BoxInt_proj_0", (t)::[])))

# 597 "FStar.SMTEncoding.Term.fst"
let boxBool : term  ->  term = (fun t -> (mkApp ("BoxBool", (t)::[])))

# 598 "FStar.SMTEncoding.Term.fst"
let unboxBool : term  ->  term = (fun t -> (mkApp ("BoxBool_proj_0", (t)::[])))

# 599 "FStar.SMTEncoding.Term.fst"
let boxString : term  ->  term = (fun t -> (mkApp ("BoxString", (t)::[])))

# 600 "FStar.SMTEncoding.Term.fst"
let unboxString : term  ->  term = (fun t -> (mkApp ("BoxString_proj_0", (t)::[])))

# 601 "FStar.SMTEncoding.Term.fst"
let boxRef : term  ->  term = (fun t -> (mkApp ("BoxRef", (t)::[])))

# 602 "FStar.SMTEncoding.Term.fst"
let unboxRef : term  ->  term = (fun t -> (mkApp ("BoxRef_proj_0", (t)::[])))

# 603 "FStar.SMTEncoding.Term.fst"
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
| _75_768 -> begin
(Prims.raise FStar_Util.Impos)
end))

# 609 "FStar.SMTEncoding.Term.fst"
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
| _75_776 -> begin
(Prims.raise FStar_Util.Impos)
end))

# 615 "FStar.SMTEncoding.Term.fst"
let mk_PreType : term  ->  term = (fun t -> (mkApp ("PreType", (t)::[])))

# 617 "FStar.SMTEncoding.Term.fst"
let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_Equality"), _75_790::t1::t2::[]); hash = _75_784; freevars = _75_782}::[]) -> begin
(mkEq (t1, t2))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_disEquality"), _75_809::t1::t2::[]); hash = _75_803; freevars = _75_801}::[]) -> begin
(let _160_597 = (mkEq (t1, t2))
in (mkNot _160_597))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_LessThanOrEqual"), t1::t2::[]); hash = _75_822; freevars = _75_820}::[]) -> begin
(let _160_600 = (let _160_599 = (unboxInt t1)
in (let _160_598 = (unboxInt t2)
in (_160_599, _160_598)))
in (mkLTE _160_600))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_LessThan"), t1::t2::[]); hash = _75_839; freevars = _75_837}::[]) -> begin
(let _160_603 = (let _160_602 = (unboxInt t1)
in (let _160_601 = (unboxInt t2)
in (_160_602, _160_601)))
in (mkLT _160_603))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_GreaterThanOrEqual"), t1::t2::[]); hash = _75_856; freevars = _75_854}::[]) -> begin
(let _160_606 = (let _160_605 = (unboxInt t1)
in (let _160_604 = (unboxInt t2)
in (_160_605, _160_604)))
in (mkGTE _160_606))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_GreaterThan"), t1::t2::[]); hash = _75_873; freevars = _75_871}::[]) -> begin
(let _160_609 = (let _160_608 = (unboxInt t1)
in (let _160_607 = (unboxInt t2)
in (_160_608, _160_607)))
in (mkGT _160_609))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_AmpAmp"), t1::t2::[]); hash = _75_890; freevars = _75_888}::[]) -> begin
(let _160_612 = (let _160_611 = (unboxBool t1)
in (let _160_610 = (unboxBool t2)
in (_160_611, _160_610)))
in (mkAnd _160_612))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_BarBar"), t1::t2::[]); hash = _75_907; freevars = _75_905}::[]) -> begin
(let _160_615 = (let _160_614 = (unboxBool t1)
in (let _160_613 = (unboxBool t2)
in (_160_614, _160_613)))
in (mkOr _160_615))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_Negation"), t::[]); hash = _75_924; freevars = _75_922}::[]) -> begin
(let _160_616 = (unboxBool t)
in (mkNot _160_616))
end
| App (Var ("Prims.b2t"), t::[]) -> begin
(unboxBool t)
end
| _75_942 -> begin
(mkApp ("Valid", (t)::[]))
end))

# 629 "FStar.SMTEncoding.Term.fst"
let mk_HasType : term  ->  term  ->  term = (fun v t -> (mkApp ("HasType", (v)::(t)::[])))

# 630 "FStar.SMTEncoding.Term.fst"
let mk_HasTypeZ : term  ->  term  ->  term = (fun v t -> (mkApp ("HasTypeZ", (v)::(t)::[])))

# 631 "FStar.SMTEncoding.Term.fst"
let mk_IsTyped : term  ->  term = (fun v -> (mkApp ("IsTyped", (v)::[])))

# 632 "FStar.SMTEncoding.Term.fst"
let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v t -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(mk_HasType v t)
end else begin
(mkApp ("HasTypeFuel", (f)::(v)::(t)::[]))
end)

# 636 "FStar.SMTEncoding.Term.fst"
let mk_HasTypeWithFuel : term Prims.option  ->  term  ->  term  ->  term = (fun f v t -> (match (f) with
| None -> begin
(mk_HasType v t)
end
| Some (f) -> begin
(mk_HasTypeFuel f v t)
end))

# 639 "FStar.SMTEncoding.Term.fst"
let mk_Destruct : term  ->  term = (fun v -> (mkApp ("Destruct", (v)::[])))

# 640 "FStar.SMTEncoding.Term.fst"
let mk_Rank : term  ->  term = (fun x -> (mkApp ("Rank", (x)::[])))

# 641 "FStar.SMTEncoding.Term.fst"
let mk_tester : Prims.string  ->  term  ->  term = (fun n t -> (mkApp ((Prims.strcat "is-" n), (t)::[])))

# 642 "FStar.SMTEncoding.Term.fst"
let mk_ApplyTF : term  ->  term  ->  term = (fun t t' -> (mkApp ("ApplyTF", (t)::(t')::[])))

# 643 "FStar.SMTEncoding.Term.fst"
let mk_ApplyTT : term  ->  term  ->  term = (fun t t' -> (mkApp ("ApplyTT", (t)::(t')::[])))

# 644 "FStar.SMTEncoding.Term.fst"
let mk_String_const : Prims.int  ->  term = (fun i -> (let _160_659 = (let _160_658 = (let _160_657 = (mkInteger' i)
in (_160_657)::[])
in ("String_const", _160_658))
in (mkApp _160_659)))

# 645 "FStar.SMTEncoding.Term.fst"
let mk_Precedes : term  ->  term  ->  term = (fun x1 x2 -> (let _160_664 = (mkApp ("Precedes", (x1)::(x2)::[]))
in (FStar_All.pipe_right _160_664 mk_Valid)))

# 646 "FStar.SMTEncoding.Term.fst"
let mk_LexCons : term  ->  term  ->  term = (fun x1 x2 -> (mkApp ("LexCons", (x1)::(x2)::[])))

# 647 "FStar.SMTEncoding.Term.fst"
let rec n_fuel : Prims.int  ->  term = (fun n -> if (n = 0) then begin
(mkApp ("ZFuel", []))
end else begin
(let _160_673 = (let _160_672 = (let _160_671 = (n_fuel (n - 1))
in (_160_671)::[])
in ("SFuel", _160_672))
in (mkApp _160_673))
end)

# 650 "FStar.SMTEncoding.Term.fst"
let fuel_2 : term = (n_fuel 2)

# 651 "FStar.SMTEncoding.Term.fst"
let fuel_100 : term = (n_fuel 100)

# 652 "FStar.SMTEncoding.Term.fst"
let mk_and_opt : term Prims.option  ->  term Prims.option  ->  term Prims.option = (fun p1 p2 -> (match ((p1, p2)) with
| (Some (p1), Some (p2)) -> begin
(let _160_678 = (mkAnd (p1, p2))
in Some (_160_678))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))

# 658 "FStar.SMTEncoding.Term.fst"
let mk_and_opt_l : term Prims.option Prims.list  ->  term Prims.option = (fun pl -> (FStar_List.fold_left (fun out p -> (mk_and_opt p out)) None pl))

# 661 "FStar.SMTEncoding.Term.fst"
let mk_and_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkTrue
end
| hd::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkAnd (p1, p2))) hd tl)
end))

# 665 "FStar.SMTEncoding.Term.fst"
let mk_or_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkFalse
end
| hd::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkOr (p1, p2))) hd tl)
end))

# 669 "FStar.SMTEncoding.Term.fst"
let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "(Integer %s)" n)
end
| BoundV (n) -> begin
(let _160_695 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "(BoundV %s)" _160_695))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (Prims.fst fv))
end
| App (op, l) -> begin
(let _160_696 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _160_696))
end
| Labeled (t, r1, r2) -> begin
(let _160_697 = (print_smt_term t)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 _160_697))
end
| Quant (qop, l, _75_1024, _75_1026, t) -> begin
(let _160_699 = (print_smt_term_list_list l)
in (let _160_698 = (print_smt_term t)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) _160_699 _160_698)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (let _160_701 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right _160_701 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _160_706 = (let _160_705 = (print_smt_term_list l)
in (Prims.strcat (Prims.strcat s "; [ ") _160_705))
in (Prims.strcat _160_706 " ] "))) "" l))




