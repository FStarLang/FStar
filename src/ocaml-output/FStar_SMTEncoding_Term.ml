
open Prims
# 23 "FStar.SMTEncoding.Term.fst"
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

# 26 "FStar.SMTEncoding.Term.fst"
let is_Bool_sort = (fun _discr_ -> (match (_discr_) with
| Bool_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 27 "FStar.SMTEncoding.Term.fst"
let is_Int_sort = (fun _discr_ -> (match (_discr_) with
| Int_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.SMTEncoding.Term.fst"
let is_String_sort = (fun _discr_ -> (match (_discr_) with
| String_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 29 "FStar.SMTEncoding.Term.fst"
let is_Ref_sort = (fun _discr_ -> (match (_discr_) with
| Ref_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "FStar.SMTEncoding.Term.fst"
let is_Term_sort = (fun _discr_ -> (match (_discr_) with
| Term_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "FStar.SMTEncoding.Term.fst"
let is_Fuel_sort = (fun _discr_ -> (match (_discr_) with
| Fuel_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 32 "FStar.SMTEncoding.Term.fst"
let is_Array = (fun _discr_ -> (match (_discr_) with
| Array (_) -> begin
true
end
| _ -> begin
false
end))

# 33 "FStar.SMTEncoding.Term.fst"
let is_Arrow = (fun _discr_ -> (match (_discr_) with
| Arrow (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "FStar.SMTEncoding.Term.fst"
let is_Sort = (fun _discr_ -> (match (_discr_) with
| Sort (_) -> begin
true
end
| _ -> begin
false
end))

# 32 "FStar.SMTEncoding.Term.fst"
let ___Array____0 = (fun projectee -> (match (projectee) with
| Array (_82_10) -> begin
_82_10
end))

# 33 "FStar.SMTEncoding.Term.fst"
let ___Arrow____0 = (fun projectee -> (match (projectee) with
| Arrow (_82_13) -> begin
_82_13
end))

# 34 "FStar.SMTEncoding.Term.fst"
let ___Sort____0 = (fun projectee -> (match (projectee) with
| Sort (_82_16) -> begin
_82_16
end))

# 34 "FStar.SMTEncoding.Term.fst"
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
(let _175_52 = (strSort s1)
in (let _175_51 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _175_52 _175_51)))
end
| Arrow (s1, s2) -> begin
(let _175_54 = (strSort s1)
in (let _175_53 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _175_54 _175_53)))
end
| Sort (s) -> begin
s
end))

# 45 "FStar.SMTEncoding.Term.fst"
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

# 48 "FStar.SMTEncoding.Term.fst"
let is_True = (fun _discr_ -> (match (_discr_) with
| True (_) -> begin
true
end
| _ -> begin
false
end))

# 49 "FStar.SMTEncoding.Term.fst"
let is_False = (fun _discr_ -> (match (_discr_) with
| False (_) -> begin
true
end
| _ -> begin
false
end))

# 50 "FStar.SMTEncoding.Term.fst"
let is_Not = (fun _discr_ -> (match (_discr_) with
| Not (_) -> begin
true
end
| _ -> begin
false
end))

# 51 "FStar.SMTEncoding.Term.fst"
let is_And = (fun _discr_ -> (match (_discr_) with
| And (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "FStar.SMTEncoding.Term.fst"
let is_Or = (fun _discr_ -> (match (_discr_) with
| Or (_) -> begin
true
end
| _ -> begin
false
end))

# 53 "FStar.SMTEncoding.Term.fst"
let is_Imp = (fun _discr_ -> (match (_discr_) with
| Imp (_) -> begin
true
end
| _ -> begin
false
end))

# 54 "FStar.SMTEncoding.Term.fst"
let is_Iff = (fun _discr_ -> (match (_discr_) with
| Iff (_) -> begin
true
end
| _ -> begin
false
end))

# 55 "FStar.SMTEncoding.Term.fst"
let is_Eq = (fun _discr_ -> (match (_discr_) with
| Eq (_) -> begin
true
end
| _ -> begin
false
end))

# 56 "FStar.SMTEncoding.Term.fst"
let is_LT = (fun _discr_ -> (match (_discr_) with
| LT (_) -> begin
true
end
| _ -> begin
false
end))

# 57 "FStar.SMTEncoding.Term.fst"
let is_LTE = (fun _discr_ -> (match (_discr_) with
| LTE (_) -> begin
true
end
| _ -> begin
false
end))

# 58 "FStar.SMTEncoding.Term.fst"
let is_GT = (fun _discr_ -> (match (_discr_) with
| GT (_) -> begin
true
end
| _ -> begin
false
end))

# 59 "FStar.SMTEncoding.Term.fst"
let is_GTE = (fun _discr_ -> (match (_discr_) with
| GTE (_) -> begin
true
end
| _ -> begin
false
end))

# 60 "FStar.SMTEncoding.Term.fst"
let is_Add = (fun _discr_ -> (match (_discr_) with
| Add (_) -> begin
true
end
| _ -> begin
false
end))

# 61 "FStar.SMTEncoding.Term.fst"
let is_Sub = (fun _discr_ -> (match (_discr_) with
| Sub (_) -> begin
true
end
| _ -> begin
false
end))

# 62 "FStar.SMTEncoding.Term.fst"
let is_Div = (fun _discr_ -> (match (_discr_) with
| Div (_) -> begin
true
end
| _ -> begin
false
end))

# 63 "FStar.SMTEncoding.Term.fst"
let is_Mul = (fun _discr_ -> (match (_discr_) with
| Mul (_) -> begin
true
end
| _ -> begin
false
end))

# 64 "FStar.SMTEncoding.Term.fst"
let is_Minus = (fun _discr_ -> (match (_discr_) with
| Minus (_) -> begin
true
end
| _ -> begin
false
end))

# 65 "FStar.SMTEncoding.Term.fst"
let is_Mod = (fun _discr_ -> (match (_discr_) with
| Mod (_) -> begin
true
end
| _ -> begin
false
end))

# 66 "FStar.SMTEncoding.Term.fst"
let is_ITE = (fun _discr_ -> (match (_discr_) with
| ITE (_) -> begin
true
end
| _ -> begin
false
end))

# 67 "FStar.SMTEncoding.Term.fst"
let is_Var = (fun _discr_ -> (match (_discr_) with
| Var (_) -> begin
true
end
| _ -> begin
false
end))

# 67 "FStar.SMTEncoding.Term.fst"
let ___Var____0 = (fun projectee -> (match (projectee) with
| Var (_82_36) -> begin
_82_36
end))

# 67 "FStar.SMTEncoding.Term.fst"
type qop =
| Forall
| Exists

# 70 "FStar.SMTEncoding.Term.fst"
let is_Forall = (fun _discr_ -> (match (_discr_) with
| Forall (_) -> begin
true
end
| _ -> begin
false
end))

# 71 "FStar.SMTEncoding.Term.fst"
let is_Exists = (fun _discr_ -> (match (_discr_) with
| Exists (_) -> begin
true
end
| _ -> begin
false
end))

# 71 "FStar.SMTEncoding.Term.fst"
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

# 81 "FStar.SMTEncoding.Term.fst"
let is_Integer = (fun _discr_ -> (match (_discr_) with
| Integer (_) -> begin
true
end
| _ -> begin
false
end))

# 82 "FStar.SMTEncoding.Term.fst"
let is_BoundV = (fun _discr_ -> (match (_discr_) with
| BoundV (_) -> begin
true
end
| _ -> begin
false
end))

# 83 "FStar.SMTEncoding.Term.fst"
let is_FreeV = (fun _discr_ -> (match (_discr_) with
| FreeV (_) -> begin
true
end
| _ -> begin
false
end))

# 84 "FStar.SMTEncoding.Term.fst"
let is_App = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))

# 85 "FStar.SMTEncoding.Term.fst"
let is_Quant = (fun _discr_ -> (match (_discr_) with
| Quant (_) -> begin
true
end
| _ -> begin
false
end))

# 90 "FStar.SMTEncoding.Term.fst"
let is_Labeled = (fun _discr_ -> (match (_discr_) with
| Labeled (_) -> begin
true
end
| _ -> begin
false
end))

# 92 "FStar.SMTEncoding.Term.fst"
let is_Mkterm : term  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkterm"))))

# 81 "FStar.SMTEncoding.Term.fst"
let ___Integer____0 = (fun projectee -> (match (projectee) with
| Integer (_82_42) -> begin
_82_42
end))

# 82 "FStar.SMTEncoding.Term.fst"
let ___BoundV____0 = (fun projectee -> (match (projectee) with
| BoundV (_82_45) -> begin
_82_45
end))

# 83 "FStar.SMTEncoding.Term.fst"
let ___FreeV____0 = (fun projectee -> (match (projectee) with
| FreeV (_82_48) -> begin
_82_48
end))

# 84 "FStar.SMTEncoding.Term.fst"
let ___App____0 = (fun projectee -> (match (projectee) with
| App (_82_51) -> begin
_82_51
end))

# 85 "FStar.SMTEncoding.Term.fst"
let ___Quant____0 = (fun projectee -> (match (projectee) with
| Quant (_82_54) -> begin
_82_54
end))

# 90 "FStar.SMTEncoding.Term.fst"
let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_82_57) -> begin
_82_57
end))

# 94 "FStar.SMTEncoding.Term.fst"
type caption =
Prims.string Prims.option

# 96 "FStar.SMTEncoding.Term.fst"
type binders =
(Prims.string * sort) Prims.list

# 97 "FStar.SMTEncoding.Term.fst"
type projector =
(Prims.string * sort)

# 98 "FStar.SMTEncoding.Term.fst"
type constructor_t =
(Prims.string * projector Prims.list * sort * Prims.int * Prims.bool)

# 99 "FStar.SMTEncoding.Term.fst"
type constructors =
constructor_t Prims.list

# 100 "FStar.SMTEncoding.Term.fst"
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

# 102 "FStar.SMTEncoding.Term.fst"
let is_DefPrelude = (fun _discr_ -> (match (_discr_) with
| DefPrelude (_) -> begin
true
end
| _ -> begin
false
end))

# 103 "FStar.SMTEncoding.Term.fst"
let is_DeclFun = (fun _discr_ -> (match (_discr_) with
| DeclFun (_) -> begin
true
end
| _ -> begin
false
end))

# 104 "FStar.SMTEncoding.Term.fst"
let is_DefineFun = (fun _discr_ -> (match (_discr_) with
| DefineFun (_) -> begin
true
end
| _ -> begin
false
end))

# 105 "FStar.SMTEncoding.Term.fst"
let is_Assume = (fun _discr_ -> (match (_discr_) with
| Assume (_) -> begin
true
end
| _ -> begin
false
end))

# 106 "FStar.SMTEncoding.Term.fst"
let is_Caption = (fun _discr_ -> (match (_discr_) with
| Caption (_) -> begin
true
end
| _ -> begin
false
end))

# 107 "FStar.SMTEncoding.Term.fst"
let is_Eval = (fun _discr_ -> (match (_discr_) with
| Eval (_) -> begin
true
end
| _ -> begin
false
end))

# 108 "FStar.SMTEncoding.Term.fst"
let is_Echo = (fun _discr_ -> (match (_discr_) with
| Echo (_) -> begin
true
end
| _ -> begin
false
end))

# 109 "FStar.SMTEncoding.Term.fst"
let is_Push = (fun _discr_ -> (match (_discr_) with
| Push (_) -> begin
true
end
| _ -> begin
false
end))

# 110 "FStar.SMTEncoding.Term.fst"
let is_Pop = (fun _discr_ -> (match (_discr_) with
| Pop (_) -> begin
true
end
| _ -> begin
false
end))

# 111 "FStar.SMTEncoding.Term.fst"
let is_CheckSat = (fun _discr_ -> (match (_discr_) with
| CheckSat (_) -> begin
true
end
| _ -> begin
false
end))

# 112 "FStar.SMTEncoding.Term.fst"
let is_GetUnsatCore = (fun _discr_ -> (match (_discr_) with
| GetUnsatCore (_) -> begin
true
end
| _ -> begin
false
end))

# 113 "FStar.SMTEncoding.Term.fst"
let is_SetOption = (fun _discr_ -> (match (_discr_) with
| SetOption (_) -> begin
true
end
| _ -> begin
false
end))

# 103 "FStar.SMTEncoding.Term.fst"
let ___DeclFun____0 = (fun projectee -> (match (projectee) with
| DeclFun (_82_61) -> begin
_82_61
end))

# 104 "FStar.SMTEncoding.Term.fst"
let ___DefineFun____0 = (fun projectee -> (match (projectee) with
| DefineFun (_82_64) -> begin
_82_64
end))

# 105 "FStar.SMTEncoding.Term.fst"
let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_82_67) -> begin
_82_67
end))

# 106 "FStar.SMTEncoding.Term.fst"
let ___Caption____0 = (fun projectee -> (match (projectee) with
| Caption (_82_70) -> begin
_82_70
end))

# 107 "FStar.SMTEncoding.Term.fst"
let ___Eval____0 = (fun projectee -> (match (projectee) with
| Eval (_82_73) -> begin
_82_73
end))

# 108 "FStar.SMTEncoding.Term.fst"
let ___Echo____0 = (fun projectee -> (match (projectee) with
| Echo (_82_76) -> begin
_82_76
end))

# 113 "FStar.SMTEncoding.Term.fst"
let ___SetOption____0 = (fun projectee -> (match (projectee) with
| SetOption (_82_79) -> begin
_82_79
end))

# 113 "FStar.SMTEncoding.Term.fst"
type decls_t =
decl Prims.list

# 114 "FStar.SMTEncoding.Term.fst"
type error_label =
(fv * Prims.string * FStar_Range.range)

# 116 "FStar.SMTEncoding.Term.fst"
type error_labels =
error_label Prims.list

# 193 "FStar.SMTEncoding.Term.fst"
let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> ((Prims.fst x) = (Prims.fst y)))

# 195 "FStar.SMTEncoding.Term.fst"
let fv_sort = (fun x -> (Prims.snd x))

# 196 "FStar.SMTEncoding.Term.fst"
let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match (((x.tm), (y.tm))) with
| (FreeV (x), FreeV (y)) -> begin
(fv_eq x y)
end
| _82_91 -> begin
false
end))

# 199 "FStar.SMTEncoding.Term.fst"
let freevar_sort : term  ->  sort = (fun _82_1 -> (match (_82_1) with
| {tm = FreeV (x); hash = _82_96; freevars = _82_94} -> begin
(fv_sort x)
end
| _82_101 -> begin
(FStar_All.failwith "impossible")
end))

# 202 "FStar.SMTEncoding.Term.fst"
let fv_of_term : term  ->  fv = (fun _82_2 -> (match (_82_2) with
| {tm = FreeV (fv); hash = _82_106; freevars = _82_104} -> begin
fv
end
| _82_111 -> begin
(FStar_All.failwith "impossible")
end))

# 205 "FStar.SMTEncoding.Term.fst"
let rec freevars : term  ->  fv Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (_82_122, tms) -> begin
(FStar_List.collect freevars tms)
end
| (Quant (_, _, _, _, t)) | (Labeled (t, _, _)) -> begin
(freevars t)
end))

# 212 "FStar.SMTEncoding.Term.fst"
let free_variables : term  ->  fvs = (fun t -> (match ((FStar_ST.read t.freevars)) with
| Some (b) -> begin
b
end
| None -> begin
(
# 218 "FStar.SMTEncoding.Term.fst"
let fvs = (let _175_304 = (freevars t)
in (FStar_Util.remove_dups fv_eq _175_304))
in (
# 219 "FStar.SMTEncoding.Term.fst"
let _82_148 = (FStar_ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))

# 220 "FStar.SMTEncoding.Term.fst"
let qop_to_string : qop  ->  Prims.string = (fun _82_3 -> (match (_82_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))

# 227 "FStar.SMTEncoding.Term.fst"
let op_to_string : op  ->  Prims.string = (fun _82_4 -> (match (_82_4) with
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

# 249 "FStar.SMTEncoding.Term.fst"
let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun _82_5 -> (match (_82_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _175_311 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _175_311))
end))

# 253 "FStar.SMTEncoding.Term.fst"
let hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _175_314 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _175_314))
end
| FreeV (x) -> begin
(let _175_316 = (let _175_315 = (strSort (Prims.snd x))
in (Prims.strcat ":" _175_315))
in (Prims.strcat (Prims.fst x) _175_316))
end
| App (op, tms) -> begin
(let _175_321 = (let _175_320 = (let _175_319 = (let _175_318 = (FStar_List.map (fun t -> t.hash) tms)
in (FStar_All.pipe_right _175_318 (FStar_String.concat " ")))
in (Prims.strcat _175_319 ")"))
in (Prims.strcat (op_to_string op) _175_320))
in (Prims.strcat "(" _175_321))
end
| Labeled (t, r1, r2) -> begin
(let _175_323 = (let _175_322 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 _175_322))
in (Prims.strcat t.hash _175_323))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _175_331 = (let _175_324 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _175_324 (FStar_String.concat " ")))
in (let _175_330 = (weightToSmt wopt)
in (let _175_329 = (let _175_328 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _175_327 = (FStar_List.map (fun p -> p.hash) pats)
in (FStar_All.pipe_right _175_327 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _175_328 (FStar_String.concat "; ")))
in (FStar_Util.format5 "(%s (%s)(! %s %s %s))" (qop_to_string qop) _175_331 body.hash _175_330 _175_329))))
end))

# 267 "FStar.SMTEncoding.Term.fst"
let __all_terms : term FStar_Util.smap FStar_ST.ref = (let _175_332 = (FStar_Util.smap_create 10000)
in (FStar_ST.alloc _175_332))

# 270 "FStar.SMTEncoding.Term.fst"
let all_terms : Prims.unit  ->  term FStar_Util.smap = (fun _82_205 -> (match (()) with
| () -> begin
(FStar_ST.read __all_terms)
end))

# 271 "FStar.SMTEncoding.Term.fst"
let mk : term'  ->  term = (fun t -> (
# 273 "FStar.SMTEncoding.Term.fst"
let key = (hash_of_term' t)
in (match ((let _175_337 = (all_terms ())
in (FStar_Util.smap_try_find _175_337 key))) with
| Some (tm) -> begin
tm
end
| None -> begin
(
# 277 "FStar.SMTEncoding.Term.fst"
let tm = (let _175_338 = (FStar_Util.mk_ref None)
in {tm = t; hash = key; freevars = _175_338})
in (
# 278 "FStar.SMTEncoding.Term.fst"
let _82_212 = (let _175_339 = (all_terms ())
in (FStar_Util.smap_add _175_339 key tm))
in tm))
end)))

# 279 "FStar.SMTEncoding.Term.fst"
let mkTrue : term = (mk (App (((True), ([])))))

# 281 "FStar.SMTEncoding.Term.fst"
let mkFalse : term = (mk (App (((False), ([])))))

# 282 "FStar.SMTEncoding.Term.fst"
let mkInteger : Prims.string  ->  term = (fun i -> (let _175_343 = (let _175_342 = (FStar_Util.ensure_decimal i)
in Integer (_175_342))
in (mk _175_343)))

# 283 "FStar.SMTEncoding.Term.fst"
let mkInteger' : Prims.int  ->  term = (fun i -> (let _175_346 = (FStar_Util.string_of_int i)
in (mkInteger _175_346)))

# 284 "FStar.SMTEncoding.Term.fst"
let mkBoundV : Prims.int  ->  term = (fun i -> (mk (BoundV (i))))

# 285 "FStar.SMTEncoding.Term.fst"
let mkFreeV : (Prims.string * sort)  ->  term = (fun x -> (mk (FreeV (x))))

# 286 "FStar.SMTEncoding.Term.fst"
let mkApp' : (op * term Prims.list)  ->  term = (fun f -> (mk (App (f))))

# 287 "FStar.SMTEncoding.Term.fst"
let mkApp : (Prims.string * term Prims.list)  ->  term = (fun _82_221 -> (match (_82_221) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))))
end))

# 288 "FStar.SMTEncoding.Term.fst"
let mkNot : term  ->  term = (fun t -> (match (t.tm) with
| App (True, _82_225) -> begin
mkFalse
end
| App (False, _82_230) -> begin
mkTrue
end
| _82_234 -> begin
(mkApp' ((Not), ((t)::[])))
end))

# 292 "FStar.SMTEncoding.Term.fst"
let mkAnd : (term * term)  ->  term = (fun _82_237 -> (match (_82_237) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (True, _82_240), _82_244) -> begin
t2
end
| (_82_247, App (True, _82_250)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
mkFalse
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))))
end
| (_82_280, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)))
end
| (App (And, ts1), _82_291) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))))
end
| _82_294 -> begin
(mkApp' ((And), ((t1)::(t2)::[])))
end)
end))

# 301 "FStar.SMTEncoding.Term.fst"
let mkOr : (term * term)  ->  term = (fun _82_297 -> (match (_82_297) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
mkTrue
end
| (App (False, _82_316), _82_320) -> begin
t2
end
| (_82_323, App (False, _82_326)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))))
end
| (_82_340, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)))
end
| (App (Or, ts1), _82_351) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))))
end
| _82_354 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])))
end)
end))

# 310 "FStar.SMTEncoding.Term.fst"
let mkImp : (term * term)  ->  term = (fun _82_357 -> (match (_82_357) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((_, App (True, _))) | ((App (False, _), _)) -> begin
mkTrue
end
| (App (True, _82_376), _82_380) -> begin
t2
end
| (_82_383, App (Imp, (t1')::(t2')::[])) -> begin
(let _175_365 = (let _175_364 = (let _175_363 = (mkAnd ((t1), (t1')))
in (_175_363)::(t2')::[])
in ((Imp), (_175_364)))
in (mkApp' _175_365))
end
| _82_392 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])))
end)
end))

# 316 "FStar.SMTEncoding.Term.fst"
let mk_bin_op : op  ->  (term * term)  ->  term = (fun op _82_396 -> (match (_82_396) with
| (t1, t2) -> begin
(mkApp' ((op), ((t1)::(t2)::[])))
end))

# 318 "FStar.SMTEncoding.Term.fst"
let mkMinus : term  ->  term = (fun t -> (mkApp' ((Minus), ((t)::[]))))

# 319 "FStar.SMTEncoding.Term.fst"
let mkIff : (term * term)  ->  term = (mk_bin_op Iff)

# 320 "FStar.SMTEncoding.Term.fst"
let mkEq : (term * term)  ->  term = (mk_bin_op Eq)

# 321 "FStar.SMTEncoding.Term.fst"
let mkLT : (term * term)  ->  term = (mk_bin_op LT)

# 322 "FStar.SMTEncoding.Term.fst"
let mkLTE : (term * term)  ->  term = (mk_bin_op LTE)

# 323 "FStar.SMTEncoding.Term.fst"
let mkGT : (term * term)  ->  term = (mk_bin_op GT)

# 324 "FStar.SMTEncoding.Term.fst"
let mkGTE : (term * term)  ->  term = (mk_bin_op GTE)

# 325 "FStar.SMTEncoding.Term.fst"
let mkAdd : (term * term)  ->  term = (mk_bin_op Add)

# 326 "FStar.SMTEncoding.Term.fst"
let mkSub : (term * term)  ->  term = (mk_bin_op Sub)

# 327 "FStar.SMTEncoding.Term.fst"
let mkDiv : (term * term)  ->  term = (mk_bin_op Div)

# 328 "FStar.SMTEncoding.Term.fst"
let mkMul : (term * term)  ->  term = (mk_bin_op Mul)

# 329 "FStar.SMTEncoding.Term.fst"
let mkMod : (term * term)  ->  term = (mk_bin_op Mod)

# 330 "FStar.SMTEncoding.Term.fst"
let mkITE : (term * term * term)  ->  term = (fun _82_401 -> (match (_82_401) with
| (t1, t2, t3) -> begin
(match (((t2.tm), (t3.tm))) with
| (App (True, _82_404), App (True, _82_409)) -> begin
mkTrue
end
| (App (True, _82_415), _82_419) -> begin
(let _175_386 = (let _175_385 = (mkNot t1)
in ((_175_385), (t3)))
in (mkImp _175_386))
end
| (_82_422, App (True, _82_425)) -> begin
(mkImp ((t1), (t2)))
end
| (_82_430, _82_432) -> begin
(mkApp' ((ITE), ((t1)::(t2)::(t3)::[])))
end)
end))

# 336 "FStar.SMTEncoding.Term.fst"
let mkCases : term Prims.list  ->  term = (fun t -> (match (t) with
| [] -> begin
(FStar_All.failwith "Impos")
end
| (hd)::tl -> begin
(FStar_List.fold_left (fun out t -> (mkAnd ((out), (t)))) hd tl)
end))

# 339 "FStar.SMTEncoding.Term.fst"
let mkQuant : (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _82_446 -> (match (_82_446) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = 0) then begin
body
end else begin
(match (body.tm) with
| App (True, _82_449) -> begin
body
end
| _82_453 -> begin
(mk (Quant (((qop), (pats), (wopt), (vars), (body)))))
end)
end
end))

# 345 "FStar.SMTEncoding.Term.fst"
let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (
# 351 "FStar.SMTEncoding.Term.fst"
let nvars = (FStar_List.length fvs)
in (
# 352 "FStar.SMTEncoding.Term.fst"
let index_of = (fun fv -> (match ((FStar_Util.try_find_index (fv_eq fv) fvs)) with
| None -> begin
None
end
| Some (i) -> begin
Some ((nvars - (i + 1)))
end))
in (
# 355 "FStar.SMTEncoding.Term.fst"
let rec aux = (fun ix t -> (match ((FStar_ST.read t.freevars)) with
| Some ([]) -> begin
t
end
| _82_468 -> begin
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
(let _175_404 = (let _175_403 = (FStar_List.map (aux ix) tms)
in ((op), (_175_403)))
in (mkApp' _175_404))
end
| Labeled (t, r1, r2) -> begin
(let _175_407 = (let _175_406 = (let _175_405 = (aux ix t)
in ((_175_405), (r1), (r2)))
in Labeled (_175_406))
in (mk _175_407))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(
# 370 "FStar.SMTEncoding.Term.fst"
let n = (FStar_List.length vars)
in (let _175_410 = (let _175_409 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _175_408 = (aux (ix + n) body)
in ((qop), (_175_409), (wopt), (vars), (_175_408))))
in (mkQuant _175_410)))
end)
end))
in (aux 0 t)))))

# 373 "FStar.SMTEncoding.Term.fst"
let inst : term Prims.list  ->  term  ->  term = (fun tms t -> (
# 376 "FStar.SMTEncoding.Term.fst"
let n = (FStar_List.length tms)
in (
# 377 "FStar.SMTEncoding.Term.fst"
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
(let _175_420 = (let _175_419 = (FStar_List.map (aux shift) tms)
in ((op), (_175_419)))
in (mkApp' _175_420))
end
| Labeled (t, r1, r2) -> begin
(let _175_423 = (let _175_422 = (let _175_421 = (aux shift t)
in ((_175_421), (r1), (r2)))
in Labeled (_175_422))
in (mk _175_423))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(
# 387 "FStar.SMTEncoding.Term.fst"
let m = (FStar_List.length vars)
in (
# 388 "FStar.SMTEncoding.Term.fst"
let shift = (shift + m)
in (let _175_426 = (let _175_425 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _175_424 = (aux shift body)
in ((qop), (_175_425), (wopt), (vars), (_175_424))))
in (mkQuant _175_426))))
end))
in (aux 0 t))))

# 390 "FStar.SMTEncoding.Term.fst"
let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list * term)  ->  term = (fun _82_534 -> (match (_82_534) with
| (qop, pats, wopt, vars, body) -> begin
(let _175_432 = (let _175_431 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _175_430 = (FStar_List.map fv_sort vars)
in (let _175_429 = (abstr vars body)
in ((qop), (_175_431), (wopt), (_175_430), (_175_429)))))
in (mkQuant _175_432))
end))

# 392 "FStar.SMTEncoding.Term.fst"
let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _82_539 -> (match (_82_539) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)))
end))

# 393 "FStar.SMTEncoding.Term.fst"
let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  term = (fun _82_544 -> (match (_82_544) with
| (pats, wopt, vars, body) -> begin
(mkQuant' ((Forall), (pats), (wopt), (vars), (body)))
end))

# 394 "FStar.SMTEncoding.Term.fst"
let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _82_548 -> (match (_82_548) with
| (pats, vars, body) -> begin
(mkQuant' ((Forall), (pats), (None), (vars), (body)))
end))

# 397 "FStar.SMTEncoding.Term.fst"
let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _82_552 -> (match (_82_552) with
| (pats, vars, body) -> begin
(mkQuant' ((Exists), (pats), (None), (vars), (body)))
end))

# 398 "FStar.SMTEncoding.Term.fst"
let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun _82_558 -> (match (_82_558) with
| (nm, vars, s, tm, c) -> begin
(let _175_445 = (let _175_444 = (FStar_List.map fv_sort vars)
in (let _175_443 = (abstr vars tm)
in ((nm), (_175_444), (s), (_175_443), (c))))
in DefineFun (_175_445))
end))

# 401 "FStar.SMTEncoding.Term.fst"
let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _175_448 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _175_448)))

# 402 "FStar.SMTEncoding.Term.fst"
let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun _82_562 id -> (match (_82_562) with
| (tok_name, sort) -> begin
(
# 404 "FStar.SMTEncoding.Term.fst"
let a_name = (Prims.strcat "fresh_token_" tok_name)
in (let _175_461 = (let _175_460 = (let _175_459 = (let _175_458 = (mkInteger' id)
in (let _175_457 = (let _175_456 = (let _175_455 = (constr_id_of_sort sort)
in (let _175_454 = (let _175_453 = (mkApp ((tok_name), ([])))
in (_175_453)::[])
in ((_175_455), (_175_454))))
in (mkApp _175_456))
in ((_175_458), (_175_457))))
in (mkEq _175_459))
in ((_175_460), (Some ("fresh token")), (Some (a_name))))
in Assume (_175_461)))
end))

# 405 "FStar.SMTEncoding.Term.fst"
let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun _82_569 -> (match (_82_569) with
| (name, arg_sorts, sort, id) -> begin
(
# 408 "FStar.SMTEncoding.Term.fst"
let id = (FStar_Util.string_of_int id)
in (
# 409 "FStar.SMTEncoding.Term.fst"
let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (let _175_468 = (let _175_467 = (let _175_466 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _175_466))
in ((_175_467), (s)))
in (mkFreeV _175_468)))))
in (
# 410 "FStar.SMTEncoding.Term.fst"
let bvar_names = (FStar_List.map fv_of_term bvars)
in (
# 411 "FStar.SMTEncoding.Term.fst"
let capp = (mkApp ((name), (bvars)))
in (
# 412 "FStar.SMTEncoding.Term.fst"
let cid_app = (let _175_470 = (let _175_469 = (constr_id_of_sort sort)
in ((_175_469), ((capp)::[])))
in (mkApp _175_470))
in (
# 413 "FStar.SMTEncoding.Term.fst"
let a_name = (Prims.strcat "constructor_distinct_" name)
in (let _175_476 = (let _175_475 = (let _175_474 = (let _175_473 = (let _175_472 = (let _175_471 = (mkInteger id)
in ((_175_471), (cid_app)))
in (mkEq _175_472))
in ((((capp)::[])::[]), (bvar_names), (_175_473)))
in (mkForall _175_474))
in ((_175_475), (Some ("Constructor distinct")), (Some (a_name))))
in Assume (_175_476))))))))
end))

# 414 "FStar.SMTEncoding.Term.fst"
let injective_constructor : (Prims.string * (Prims.string * sort) Prims.list * sort)  ->  decls_t = (fun _82_581 -> (match (_82_581) with
| (name, projectors, sort) -> begin
(
# 417 "FStar.SMTEncoding.Term.fst"
let n_bvars = (FStar_List.length projectors)
in (
# 418 "FStar.SMTEncoding.Term.fst"
let bvar_name = (fun i -> (let _175_481 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _175_481)))
in (
# 419 "FStar.SMTEncoding.Term.fst"
let bvar_index = (fun i -> (n_bvars - (i + 1)))
in (
# 420 "FStar.SMTEncoding.Term.fst"
let bvar = (fun i s -> (let _175_489 = (let _175_488 = (bvar_name i)
in ((_175_488), (s)))
in (mkFreeV _175_489)))
in (
# 421 "FStar.SMTEncoding.Term.fst"
let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _82_594 -> (match (_82_594) with
| (_82_592, s) -> begin
(bvar i s)
end))))
in (
# 422 "FStar.SMTEncoding.Term.fst"
let bvar_names = (FStar_List.map fv_of_term bvars)
in (
# 423 "FStar.SMTEncoding.Term.fst"
let capp = (mkApp ((name), (bvars)))
in (let _175_502 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _82_601 -> (match (_82_601) with
| (name, s) -> begin
(
# 426 "FStar.SMTEncoding.Term.fst"
let cproj_app = (mkApp ((name), ((capp)::[])))
in (
# 427 "FStar.SMTEncoding.Term.fst"
let proj_name = DeclFun (((name), ((sort)::[]), (s), (Some ("Projector"))))
in (
# 428 "FStar.SMTEncoding.Term.fst"
let a_name = (Prims.strcat "projection_inverse_" name)
in (let _175_501 = (let _175_500 = (let _175_499 = (let _175_498 = (let _175_497 = (let _175_496 = (let _175_495 = (let _175_494 = (bvar i s)
in ((cproj_app), (_175_494)))
in (mkEq _175_495))
in ((((capp)::[])::[]), (bvar_names), (_175_496)))
in (mkForall _175_497))
in ((_175_498), (Some ("Projection inverse")), (Some (a_name))))
in Assume (_175_499))
in (_175_500)::[])
in (proj_name)::_175_501))))
end))))
in (FStar_All.pipe_right _175_502 FStar_List.flatten)))))))))
end))

# 431 "FStar.SMTEncoding.Term.fst"
let constructor_to_decl : constructor_t  ->  decls_t = (fun _82_610 -> (match (_82_610) with
| (name, projectors, sort, id, injective) -> begin
(
# 434 "FStar.SMTEncoding.Term.fst"
let injective = (injective || true)
in (
# 435 "FStar.SMTEncoding.Term.fst"
let cdecl = (let _175_506 = (let _175_505 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_175_505), (sort), (Some ("Constructor"))))
in DeclFun (_175_506))
in (
# 436 "FStar.SMTEncoding.Term.fst"
let cid = (let _175_508 = (let _175_507 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_175_507), (sort), (id)))
in (fresh_constructor _175_508))
in (
# 437 "FStar.SMTEncoding.Term.fst"
let disc = (
# 438 "FStar.SMTEncoding.Term.fst"
let disc_name = (Prims.strcat "is-" name)
in (
# 439 "FStar.SMTEncoding.Term.fst"
let xfv = (("x"), (sort))
in (
# 440 "FStar.SMTEncoding.Term.fst"
let xx = (mkFreeV xfv)
in (
# 441 "FStar.SMTEncoding.Term.fst"
let disc_eq = (let _175_514 = (let _175_513 = (let _175_510 = (let _175_509 = (constr_id_of_sort sort)
in ((_175_509), ((xx)::[])))
in (mkApp _175_510))
in (let _175_512 = (let _175_511 = (FStar_Util.string_of_int id)
in (mkInteger _175_511))
in ((_175_513), (_175_512))))
in (mkEq _175_514))
in (
# 442 "FStar.SMTEncoding.Term.fst"
let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _82_620 -> (match (_82_620) with
| (proj, s) -> begin
(mkApp ((proj), ((xx)::[])))
end))))
in (
# 443 "FStar.SMTEncoding.Term.fst"
let disc_inv_body = (let _175_517 = (let _175_516 = (mkApp ((name), (proj_terms)))
in ((xx), (_175_516)))
in (mkEq _175_517))
in (
# 444 "FStar.SMTEncoding.Term.fst"
let disc_ax = (mkAnd ((disc_eq), (disc_inv_body)))
in (mkDefineFun ((disc_name), ((xfv)::[]), (Bool_sort), (disc_ax), (Some ("Discriminator definition")))))))))))
in (
# 448 "FStar.SMTEncoding.Term.fst"
let projs = if injective then begin
(injective_constructor ((name), (projectors), (sort)))
end else begin
[]
end
in (let _175_524 = (let _175_519 = (let _175_518 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_175_518))
in (_175_519)::(cdecl)::(cid)::projs)
in (let _175_523 = (let _175_522 = (let _175_521 = (let _175_520 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_175_520))
in (_175_521)::[])
in (FStar_List.append ((disc)::[]) _175_522))
in (FStar_List.append _175_524 _175_523))))))))
end))

# 452 "FStar.SMTEncoding.Term.fst"
let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (
# 459 "FStar.SMTEncoding.Term.fst"
let _82_644 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _82_632 s -> (match (_82_632) with
| (names, binders, n) -> begin
(
# 460 "FStar.SMTEncoding.Term.fst"
let prefix = (match (s) with
| Term_sort -> begin
"@x"
end
| _82_636 -> begin
"@u"
end)
in (
# 463 "FStar.SMTEncoding.Term.fst"
let nm = (let _175_533 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _175_533))
in (
# 464 "FStar.SMTEncoding.Term.fst"
let names = (((nm), (s)))::names
in (
# 465 "FStar.SMTEncoding.Term.fst"
let b = (let _175_534 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _175_534))
in ((names), ((b)::binders), ((n + 1)))))))
end)) ((outer_names), ([]), (start))))
in (match (_82_644) with
| (names, binders, n) -> begin
((names), ((FStar_List.rev binders)), (n))
end)))

# 468 "FStar.SMTEncoding.Term.fst"
let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (
# 471 "FStar.SMTEncoding.Term.fst"
let _82_649 = (name_binders_inner [] 0 sorts)
in (match (_82_649) with
| (names, binders, n) -> begin
(((FStar_List.rev names)), (binders))
end)))

# 472 "FStar.SMTEncoding.Term.fst"
let termToSmt : term  ->  Prims.string = (fun t -> (
# 475 "FStar.SMTEncoding.Term.fst"
let rec aux = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _175_545 = (FStar_List.nth names i)
in (FStar_All.pipe_right _175_545 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _175_547 = (let _175_546 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _175_546 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _175_547))
end
| Labeled (t, _82_671, _82_673) -> begin
(aux n names t)
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(
# 484 "FStar.SMTEncoding.Term.fst"
let _82_686 = (name_binders_inner names n sorts)
in (match (_82_686) with
| (names, binders, n) -> begin
(
# 485 "FStar.SMTEncoding.Term.fst"
let binders = (FStar_All.pipe_right binders (FStar_String.concat " "))
in (
# 486 "FStar.SMTEncoding.Term.fst"
let pats_str = (match (pats) with
| (([])::[]) | ([]) -> begin
""
end
| _82_692 -> begin
(let _175_553 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _175_552 = (let _175_551 = (FStar_List.map (fun p -> (let _175_550 = (aux n names p)
in (FStar_Util.format1 "%s" _175_550))) pats)
in (FStar_String.concat " " _175_551))
in (FStar_Util.format1 "\n:pattern (%s)" _175_552)))))
in (FStar_All.pipe_right _175_553 (FStar_String.concat "\n")))
end)
in (match (((pats), (wopt))) with
| ((([])::[], None)) | (([], None)) -> begin
(let _175_554 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _175_554))
end
| _82_704 -> begin
(let _175_556 = (aux n names body)
in (let _175_555 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _175_556 _175_555 pats_str)))
end)))
end))
end))
in (aux 0 [] t)))

# 495 "FStar.SMTEncoding.Term.fst"
let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun _82_6 -> (match (_82_6) with
| None -> begin
""
end
| Some (c) -> begin
(
# 501 "FStar.SMTEncoding.Term.fst"
let _82_718 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::[] -> begin
((hd), (""))
end
| (hd)::_82_713 -> begin
((hd), ("..."))
end)
in (match (_82_718) with
| (hd, suffix) -> begin
(FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd suffix)
end))
end))

# 505 "FStar.SMTEncoding.Term.fst"
let rec declToSmt : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (
# 508 "FStar.SMTEncoding.Term.fst"
let escape = (fun s -> (FStar_Util.replace_char s '\'' '_'))
in (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(let _175_567 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _82_7 -> (match (_82_7) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _175_567))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(
# 514 "FStar.SMTEncoding.Term.fst"
let l = (FStar_List.map strSort argsorts)
in (let _175_569 = (caption_to_string c)
in (let _175_568 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _175_569 f (FStar_String.concat " " l) _175_568))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(
# 517 "FStar.SMTEncoding.Term.fst"
let _82_747 = (name_binders arg_sorts)
in (match (_82_747) with
| (names, binders) -> begin
(
# 518 "FStar.SMTEncoding.Term.fst"
let body = (let _175_570 = (FStar_List.map mkFreeV names)
in (inst _175_570 body))
in (let _175_573 = (caption_to_string c)
in (let _175_572 = (strSort retsort)
in (let _175_571 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _175_573 f (FStar_String.concat " " binders) _175_572 _175_571)))))
end))
end
| Assume (t, c, Some (n)) -> begin
(let _175_575 = (caption_to_string c)
in (let _175_574 = (termToSmt t)
in (FStar_Util.format3 "%s(assert (!\n%s\n:named %s))" _175_575 _175_574 (escape n))))
end
| Assume (t, c, None) -> begin
(let _175_577 = (caption_to_string c)
in (let _175_576 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _175_577 _175_576)))
end
| Eval (t) -> begin
(let _175_578 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _175_578))
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
# 535 "FStar.SMTEncoding.Term.fst"
let basic = (Prims.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort String)\n(declare-fun String_constr_id (String) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n")
in (
# 582 "FStar.SMTEncoding.Term.fst"
let constrs = ((("String_const"), (((("String_const_proj_0"), (Int_sort)))::[]), (String_sort), (0), (true)))::((("Tm_type"), ([]), (Term_sort), (2), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort)))::[]), (Term_sort), (3), (false)))::((("Tm_uvar"), (((("Tm_uvar_fst"), (Int_sort)))::[]), (Term_sort), (5), (true)))::((("Tm_unit"), ([]), (Term_sort), (6), (true)))::((("BoxInt"), (((("BoxInt_proj_0"), (Int_sort)))::[]), (Term_sort), (7), (true)))::((("BoxBool"), (((("BoxBool_proj_0"), (Bool_sort)))::[]), (Term_sort), (8), (true)))::((("BoxString"), (((("BoxString_proj_0"), (String_sort)))::[]), (Term_sort), (9), (true)))::((("BoxRef"), (((("BoxRef_proj_0"), (Ref_sort)))::[]), (Term_sort), (10), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort)))::((("LexCons_1"), (Term_sort)))::[]), (Term_sort), (11), (true)))::[]
in (
# 592 "FStar.SMTEncoding.Term.fst"
let bcons = (let _175_581 = (let _175_580 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _175_580 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _175_581 (FStar_String.concat "\n")))
in (
# 593 "FStar.SMTEncoding.Term.fst"
let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))

# 600 "FStar.SMTEncoding.Term.fst"
let mk_Range_const : term = (mkApp (("Range_const"), ([])))

# 602 "FStar.SMTEncoding.Term.fst"
let mk_Term_type : term = (mkApp (("Tm_type"), ([])))

# 603 "FStar.SMTEncoding.Term.fst"
let mk_Term_app : term  ->  term  ->  term = (fun t1 t2 -> (mkApp (("Tm_app"), ((t1)::(t2)::[]))))

# 604 "FStar.SMTEncoding.Term.fst"
let mk_Term_uvar : Prims.int  ->  term = (fun i -> (let _175_590 = (let _175_589 = (let _175_588 = (mkInteger' i)
in (_175_588)::[])
in (("Tm_uvar"), (_175_589)))
in (mkApp _175_590)))

# 605 "FStar.SMTEncoding.Term.fst"
let mk_Term_unit : term = (mkApp (("Tm_unit"), ([])))

# 606 "FStar.SMTEncoding.Term.fst"
let boxInt : term  ->  term = (fun t -> (mkApp (("BoxInt"), ((t)::[]))))

# 607 "FStar.SMTEncoding.Term.fst"
let unboxInt : term  ->  term = (fun t -> (mkApp (("BoxInt_proj_0"), ((t)::[]))))

# 608 "FStar.SMTEncoding.Term.fst"
let boxBool : term  ->  term = (fun t -> (mkApp (("BoxBool"), ((t)::[]))))

# 609 "FStar.SMTEncoding.Term.fst"
let unboxBool : term  ->  term = (fun t -> (mkApp (("BoxBool_proj_0"), ((t)::[]))))

# 610 "FStar.SMTEncoding.Term.fst"
let boxString : term  ->  term = (fun t -> (mkApp (("BoxString"), ((t)::[]))))

# 611 "FStar.SMTEncoding.Term.fst"
let unboxString : term  ->  term = (fun t -> (mkApp (("BoxString_proj_0"), ((t)::[]))))

# 612 "FStar.SMTEncoding.Term.fst"
let boxRef : term  ->  term = (fun t -> (mkApp (("BoxRef"), ((t)::[]))))

# 613 "FStar.SMTEncoding.Term.fst"
let unboxRef : term  ->  term = (fun t -> (mkApp (("BoxRef_proj_0"), ((t)::[]))))

# 614 "FStar.SMTEncoding.Term.fst"
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
| _82_795 -> begin
(Prims.raise FStar_Util.Impos)
end))

# 620 "FStar.SMTEncoding.Term.fst"
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
| _82_803 -> begin
(Prims.raise FStar_Util.Impos)
end))

# 626 "FStar.SMTEncoding.Term.fst"
let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[]))))

# 628 "FStar.SMTEncoding.Term.fst"
let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (_82_817)::(t1)::(t2)::[]); hash = _82_811; freevars = _82_809})::[]) -> begin
(mkEq ((t1), (t2)))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (_82_836)::(t1)::(t2)::[]); hash = _82_830; freevars = _82_828})::[]) -> begin
(let _175_619 = (mkEq ((t1), (t2)))
in (mkNot _175_619))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); hash = _82_849; freevars = _82_847})::[]) -> begin
(let _175_622 = (let _175_621 = (unboxInt t1)
in (let _175_620 = (unboxInt t2)
in ((_175_621), (_175_620))))
in (mkLTE _175_622))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); hash = _82_866; freevars = _82_864})::[]) -> begin
(let _175_625 = (let _175_624 = (unboxInt t1)
in (let _175_623 = (unboxInt t2)
in ((_175_624), (_175_623))))
in (mkLT _175_625))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); hash = _82_883; freevars = _82_881})::[]) -> begin
(let _175_628 = (let _175_627 = (unboxInt t1)
in (let _175_626 = (unboxInt t2)
in ((_175_627), (_175_626))))
in (mkGTE _175_628))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); hash = _82_900; freevars = _82_898})::[]) -> begin
(let _175_631 = (let _175_630 = (unboxInt t1)
in (let _175_629 = (unboxInt t2)
in ((_175_630), (_175_629))))
in (mkGT _175_631))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); hash = _82_917; freevars = _82_915})::[]) -> begin
(let _175_634 = (let _175_633 = (unboxBool t1)
in (let _175_632 = (unboxBool t2)
in ((_175_633), (_175_632))))
in (mkAnd _175_634))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); hash = _82_934; freevars = _82_932})::[]) -> begin
(let _175_637 = (let _175_636 = (unboxBool t1)
in (let _175_635 = (unboxBool t2)
in ((_175_636), (_175_635))))
in (mkOr _175_637))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t)::[]); hash = _82_951; freevars = _82_949})::[]) -> begin
(let _175_638 = (unboxBool t)
in (mkNot _175_638))
end
| App (Var ("Prims.b2t"), (t)::[]) -> begin
(unboxBool t)
end
| _82_969 -> begin
(mkApp (("Valid"), ((t)::[])))
end))

# 640 "FStar.SMTEncoding.Term.fst"
let mk_HasType : term  ->  term  ->  term = (fun v t -> (mkApp (("HasType"), ((v)::(t)::[]))))

# 641 "FStar.SMTEncoding.Term.fst"
let mk_HasTypeZ : term  ->  term  ->  term = (fun v t -> (mkApp (("HasTypeZ"), ((v)::(t)::[]))))

# 642 "FStar.SMTEncoding.Term.fst"
let mk_IsTyped : term  ->  term = (fun v -> (mkApp (("IsTyped"), ((v)::[]))))

# 643 "FStar.SMTEncoding.Term.fst"
let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v t -> if (FStar_Options.unthrottle_inductives ()) then begin
(mk_HasType v t)
end else begin
(mkApp (("HasTypeFuel"), ((f)::(v)::(t)::[])))
end)

# 647 "FStar.SMTEncoding.Term.fst"
let mk_HasTypeWithFuel : term Prims.option  ->  term  ->  term  ->  term = (fun f v t -> (match (f) with
| None -> begin
(mk_HasType v t)
end
| Some (f) -> begin
(mk_HasTypeFuel f v t)
end))

# 650 "FStar.SMTEncoding.Term.fst"
let mk_Destruct : term  ->  term = (fun v -> (mkApp (("Destruct"), ((v)::[]))))

# 651 "FStar.SMTEncoding.Term.fst"
let mk_Rank : term  ->  term = (fun x -> (mkApp (("Rank"), ((x)::[]))))

# 652 "FStar.SMTEncoding.Term.fst"
let mk_tester : Prims.string  ->  term  ->  term = (fun n t -> (mkApp (((Prims.strcat "is-" n)), ((t)::[]))))

# 653 "FStar.SMTEncoding.Term.fst"
let mk_ApplyTF : term  ->  term  ->  term = (fun t t' -> (mkApp (("ApplyTF"), ((t)::(t')::[]))))

# 654 "FStar.SMTEncoding.Term.fst"
let mk_ApplyTT : term  ->  term  ->  term = (fun t t' -> (mkApp (("ApplyTT"), ((t)::(t')::[]))))

# 655 "FStar.SMTEncoding.Term.fst"
let mk_String_const : Prims.int  ->  term = (fun i -> (let _175_681 = (let _175_680 = (let _175_679 = (mkInteger' i)
in (_175_679)::[])
in (("String_const"), (_175_680)))
in (mkApp _175_681)))

# 656 "FStar.SMTEncoding.Term.fst"
let mk_Precedes : term  ->  term  ->  term = (fun x1 x2 -> (let _175_686 = (mkApp (("Precedes"), ((x1)::(x2)::[])))
in (FStar_All.pipe_right _175_686 mk_Valid)))

# 657 "FStar.SMTEncoding.Term.fst"
let mk_LexCons : term  ->  term  ->  term = (fun x1 x2 -> (mkApp (("LexCons"), ((x1)::(x2)::[]))))

# 658 "FStar.SMTEncoding.Term.fst"
let rec n_fuel : Prims.int  ->  term = (fun n -> if (n = 0) then begin
(mkApp (("ZFuel"), ([])))
end else begin
(let _175_695 = (let _175_694 = (let _175_693 = (n_fuel (n - 1))
in (_175_693)::[])
in (("SFuel"), (_175_694)))
in (mkApp _175_695))
end)

# 661 "FStar.SMTEncoding.Term.fst"
let fuel_2 : term = (n_fuel 2)

# 662 "FStar.SMTEncoding.Term.fst"
let fuel_100 : term = (n_fuel 100)

# 663 "FStar.SMTEncoding.Term.fst"
let mk_and_opt : term Prims.option  ->  term Prims.option  ->  term Prims.option = (fun p1 p2 -> (match (((p1), (p2))) with
| (Some (p1), Some (p2)) -> begin
(let _175_700 = (mkAnd ((p1), (p2)))
in Some (_175_700))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))

# 669 "FStar.SMTEncoding.Term.fst"
let mk_and_opt_l : term Prims.option Prims.list  ->  term Prims.option = (fun pl -> (FStar_List.fold_left (fun out p -> (mk_and_opt p out)) None pl))

# 672 "FStar.SMTEncoding.Term.fst"
let mk_and_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkTrue
end
| (hd)::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkAnd ((p1), (p2)))) hd tl)
end))

# 676 "FStar.SMTEncoding.Term.fst"
let mk_or_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkFalse
end
| (hd)::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkOr ((p1), (p2)))) hd tl)
end))

# 680 "FStar.SMTEncoding.Term.fst"
let mk_haseq : term  ->  term = (fun t -> (let _175_715 = (mkApp (("Prims.hasEq"), ((t)::[])))
in (mk_Valid _175_715)))

# 682 "FStar.SMTEncoding.Term.fst"
let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "(Integer %s)" n)
end
| BoundV (n) -> begin
(let _175_720 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "(BoundV %s)" _175_720))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (Prims.fst fv))
end
| App (op, l) -> begin
(let _175_721 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _175_721))
end
| Labeled (t, r1, r2) -> begin
(let _175_722 = (print_smt_term t)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 _175_722))
end
| Quant (qop, l, _82_1052, _82_1054, t) -> begin
(let _175_724 = (print_smt_term_list_list l)
in (let _175_723 = (print_smt_term t)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) _175_724 _175_723)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (let _175_726 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right _175_726 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _175_732 = (let _175_731 = (let _175_730 = (print_smt_term_list l)
in (Prims.strcat _175_730 " ] "))
in (Prims.strcat "; [ " _175_731))
in (Prims.strcat s _175_732))) "" l))




