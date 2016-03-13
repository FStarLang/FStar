
open Prims
# 26 "FStar.SMTEncoding.Term.fst"
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
let ___Array____0 : sort  ->  (sort * sort) = (fun projectee -> (match (projectee) with
| Array (_72_10) -> begin
_72_10
end))

# 34 "FStar.SMTEncoding.Term.fst"
let ___Arrow____0 : sort  ->  (sort * sort) = (fun projectee -> (match (projectee) with
| Arrow (_72_13) -> begin
_72_13
end))

# 35 "FStar.SMTEncoding.Term.fst"
let ___Sort____0 : sort  ->  Prims.string = (fun projectee -> (match (projectee) with
| Sort (_72_16) -> begin
_72_16
end))

# 37 "FStar.SMTEncoding.Term.fst"
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
(let _154_52 = (strSort s1)
in (let _154_51 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _154_52 _154_51)))
end
| Arrow (s1, s2) -> begin
(let _154_54 = (strSort s1)
in (let _154_53 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _154_54 _154_53)))
end
| Sort (s) -> begin
s
end))

# 48 "FStar.SMTEncoding.Term.fst"
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
let ___Var____0 : op  ->  Prims.string = (fun projectee -> (match (projectee) with
| Var (_72_36) -> begin
_72_36
end))

# 70 "FStar.SMTEncoding.Term.fst"
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

# 75 "FStar.SMTEncoding.Term.fst"
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

# 76 "FStar.SMTEncoding.Term.fst"
let is_Integer = (fun _discr_ -> (match (_discr_) with
| Integer (_) -> begin
true
end
| _ -> begin
false
end))

# 77 "FStar.SMTEncoding.Term.fst"
let is_BoundV = (fun _discr_ -> (match (_discr_) with
| BoundV (_) -> begin
true
end
| _ -> begin
false
end))

# 78 "FStar.SMTEncoding.Term.fst"
let is_FreeV = (fun _discr_ -> (match (_discr_) with
| FreeV (_) -> begin
true
end
| _ -> begin
false
end))

# 79 "FStar.SMTEncoding.Term.fst"
let is_App = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))

# 80 "FStar.SMTEncoding.Term.fst"
let is_Quant = (fun _discr_ -> (match (_discr_) with
| Quant (_) -> begin
true
end
| _ -> begin
false
end))

# 85 "FStar.SMTEncoding.Term.fst"
let is_Labeled = (fun _discr_ -> (match (_discr_) with
| Labeled (_) -> begin
true
end
| _ -> begin
false
end))

# 87 "FStar.SMTEncoding.Term.fst"
let is_Mkterm : term  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkterm"))))

# 76 "FStar.SMTEncoding.Term.fst"
let ___Integer____0 : term'  ->  Prims.string = (fun projectee -> (match (projectee) with
| Integer (_72_42) -> begin
_72_42
end))

# 77 "FStar.SMTEncoding.Term.fst"
let ___BoundV____0 : term'  ->  Prims.int = (fun projectee -> (match (projectee) with
| BoundV (_72_45) -> begin
_72_45
end))

# 78 "FStar.SMTEncoding.Term.fst"
let ___FreeV____0 : term'  ->  fv = (fun projectee -> (match (projectee) with
| FreeV (_72_48) -> begin
_72_48
end))

# 79 "FStar.SMTEncoding.Term.fst"
let ___App____0 : term'  ->  (op * term Prims.list) = (fun projectee -> (match (projectee) with
| App (_72_51) -> begin
_72_51
end))

# 80 "FStar.SMTEncoding.Term.fst"
let ___Quant____0 : term'  ->  (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term) = (fun projectee -> (match (projectee) with
| Quant (_72_54) -> begin
_72_54
end))

# 85 "FStar.SMTEncoding.Term.fst"
let ___Labeled____0 : term'  ->  (term * Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Labeled (_72_57) -> begin
_72_57
end))

# 91 "FStar.SMTEncoding.Term.fst"
type caption =
Prims.string Prims.option

# 92 "FStar.SMTEncoding.Term.fst"
type binders =
(Prims.string * sort) Prims.list

# 93 "FStar.SMTEncoding.Term.fst"
type projector =
(Prims.string * sort)

# 94 "FStar.SMTEncoding.Term.fst"
type constructor_t =
(Prims.string * projector Prims.list * sort * Prims.int * Prims.bool)

# 95 "FStar.SMTEncoding.Term.fst"
type constructors =
constructor_t Prims.list

# 96 "FStar.SMTEncoding.Term.fst"
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

# 97 "FStar.SMTEncoding.Term.fst"
let is_DefPrelude = (fun _discr_ -> (match (_discr_) with
| DefPrelude (_) -> begin
true
end
| _ -> begin
false
end))

# 98 "FStar.SMTEncoding.Term.fst"
let is_DeclFun = (fun _discr_ -> (match (_discr_) with
| DeclFun (_) -> begin
true
end
| _ -> begin
false
end))

# 99 "FStar.SMTEncoding.Term.fst"
let is_DefineFun = (fun _discr_ -> (match (_discr_) with
| DefineFun (_) -> begin
true
end
| _ -> begin
false
end))

# 100 "FStar.SMTEncoding.Term.fst"
let is_Assume = (fun _discr_ -> (match (_discr_) with
| Assume (_) -> begin
true
end
| _ -> begin
false
end))

# 101 "FStar.SMTEncoding.Term.fst"
let is_Caption = (fun _discr_ -> (match (_discr_) with
| Caption (_) -> begin
true
end
| _ -> begin
false
end))

# 102 "FStar.SMTEncoding.Term.fst"
let is_Eval = (fun _discr_ -> (match (_discr_) with
| Eval (_) -> begin
true
end
| _ -> begin
false
end))

# 103 "FStar.SMTEncoding.Term.fst"
let is_Echo = (fun _discr_ -> (match (_discr_) with
| Echo (_) -> begin
true
end
| _ -> begin
false
end))

# 104 "FStar.SMTEncoding.Term.fst"
let is_Push = (fun _discr_ -> (match (_discr_) with
| Push (_) -> begin
true
end
| _ -> begin
false
end))

# 105 "FStar.SMTEncoding.Term.fst"
let is_Pop = (fun _discr_ -> (match (_discr_) with
| Pop (_) -> begin
true
end
| _ -> begin
false
end))

# 106 "FStar.SMTEncoding.Term.fst"
let is_CheckSat = (fun _discr_ -> (match (_discr_) with
| CheckSat (_) -> begin
true
end
| _ -> begin
false
end))

# 98 "FStar.SMTEncoding.Term.fst"
let ___DeclFun____0 : decl  ->  (Prims.string * sort Prims.list * sort * caption) = (fun projectee -> (match (projectee) with
| DeclFun (_72_61) -> begin
_72_61
end))

# 99 "FStar.SMTEncoding.Term.fst"
let ___DefineFun____0 : decl  ->  (Prims.string * sort Prims.list * sort * term * caption) = (fun projectee -> (match (projectee) with
| DefineFun (_72_64) -> begin
_72_64
end))

# 100 "FStar.SMTEncoding.Term.fst"
let ___Assume____0 : decl  ->  (term * caption) = (fun projectee -> (match (projectee) with
| Assume (_72_67) -> begin
_72_67
end))

# 101 "FStar.SMTEncoding.Term.fst"
let ___Caption____0 : decl  ->  Prims.string = (fun projectee -> (match (projectee) with
| Caption (_72_70) -> begin
_72_70
end))

# 102 "FStar.SMTEncoding.Term.fst"
let ___Eval____0 : decl  ->  term = (fun projectee -> (match (projectee) with
| Eval (_72_73) -> begin
_72_73
end))

# 103 "FStar.SMTEncoding.Term.fst"
let ___Echo____0 : decl  ->  Prims.string = (fun projectee -> (match (projectee) with
| Echo (_72_76) -> begin
_72_76
end))

# 107 "FStar.SMTEncoding.Term.fst"
type decls_t =
decl Prims.list

# 185 "FStar.SMTEncoding.Term.fst"
let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> ((Prims.fst x) = (Prims.fst y)))

# 186 "FStar.SMTEncoding.Term.fst"
let fv_sort = (fun x -> (Prims.snd x))

# 187 "FStar.SMTEncoding.Term.fst"
let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match ((x.tm, y.tm)) with
| (FreeV (x), FreeV (y)) -> begin
(fv_eq x y)
end
| _72_88 -> begin
false
end))

# 190 "FStar.SMTEncoding.Term.fst"
let freevar_sort : term  ->  sort = (fun _72_1 -> (match (_72_1) with
| {tm = FreeV (x); hash = _72_93; freevars = _72_91} -> begin
(fv_sort x)
end
| _72_98 -> begin
(FStar_All.failwith "impossible")
end))

# 193 "FStar.SMTEncoding.Term.fst"
let fv_of_term : term  ->  fv = (fun _72_2 -> (match (_72_2) with
| {tm = FreeV (fv); hash = _72_103; freevars = _72_101} -> begin
fv
end
| _72_108 -> begin
(FStar_All.failwith "impossible")
end))

# 196 "FStar.SMTEncoding.Term.fst"
let rec freevars : term  ->  fv Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (_72_119, tms) -> begin
(FStar_List.collect freevars tms)
end
| (Quant (_, _, _, _, t)) | (Labeled (t, _, _)) -> begin
(freevars t)
end))

# 205 "FStar.SMTEncoding.Term.fst"
let free_variables : term  ->  fvs = (fun t -> (match ((FStar_ST.read t.freevars)) with
| Some (b) -> begin
b
end
| None -> begin
(
# 208 "FStar.SMTEncoding.Term.fst"
let fvs = (let _154_289 = (freevars t)
in (FStar_Util.remove_dups fv_eq _154_289))
in (
# 209 "FStar.SMTEncoding.Term.fst"
let _72_145 = (FStar_ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))

# 215 "FStar.SMTEncoding.Term.fst"
let qop_to_string : qop  ->  Prims.string = (fun _72_3 -> (match (_72_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))

# 219 "FStar.SMTEncoding.Term.fst"
let op_to_string : op  ->  Prims.string = (fun _72_4 -> (match (_72_4) with
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

# 241 "FStar.SMTEncoding.Term.fst"
let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun _72_5 -> (match (_72_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _154_296 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _154_296))
end))

# 245 "FStar.SMTEncoding.Term.fst"
let hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _154_299 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _154_299))
end
| FreeV (x) -> begin
(let _154_300 = (strSort (Prims.snd x))
in (Prims.strcat (Prims.strcat (Prims.fst x) ":") _154_300))
end
| App (op, tms) -> begin
(let _154_304 = (let _154_303 = (let _154_302 = (FStar_List.map (fun t -> t.hash) tms)
in (FStar_All.pipe_right _154_302 (FStar_String.concat " ")))
in (Prims.strcat (Prims.strcat "(" (op_to_string op)) _154_303))
in (Prims.strcat _154_304 ")"))
end
| Labeled (t, r1, r2) -> begin
(let _154_305 = (FStar_Range.string_of_range r2)
in (Prims.strcat (Prims.strcat t.hash r1) _154_305))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _154_313 = (let _154_306 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _154_306 (FStar_String.concat " ")))
in (let _154_312 = (weightToSmt wopt)
in (let _154_311 = (let _154_310 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _154_309 = (FStar_List.map (fun p -> p.hash) pats)
in (FStar_All.pipe_right _154_309 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _154_310 (FStar_String.concat "; ")))
in (FStar_Util.format5 "(%s (%s)(! %s %s %s))" (qop_to_string qop) _154_313 body.hash _154_312 _154_311))))
end))

# 260 "FStar.SMTEncoding.Term.fst"
let __all_terms : term FStar_Util.smap FStar_ST.ref = (let _154_314 = (FStar_Util.smap_create 10000)
in (FStar_ST.alloc _154_314))

# 261 "FStar.SMTEncoding.Term.fst"
let all_terms : Prims.unit  ->  term FStar_Util.smap = (fun _72_202 -> (match (()) with
| () -> begin
(FStar_ST.read __all_terms)
end))

# 262 "FStar.SMTEncoding.Term.fst"
let mk : term'  ->  term = (fun t -> (
# 263 "FStar.SMTEncoding.Term.fst"
let key = (hash_of_term' t)
in (match ((let _154_319 = (all_terms ())
in (FStar_Util.smap_try_find _154_319 key))) with
| Some (tm) -> begin
tm
end
| None -> begin
(
# 267 "FStar.SMTEncoding.Term.fst"
let tm = (let _154_320 = (FStar_Util.mk_ref None)
in {tm = t; hash = key; freevars = _154_320})
in (
# 268 "FStar.SMTEncoding.Term.fst"
let _72_209 = (let _154_321 = (all_terms ())
in (FStar_Util.smap_add _154_321 key tm))
in tm))
end)))

# 271 "FStar.SMTEncoding.Term.fst"
let mkTrue : term = (mk (App ((True, []))))

# 272 "FStar.SMTEncoding.Term.fst"
let mkFalse : term = (mk (App ((False, []))))

# 273 "FStar.SMTEncoding.Term.fst"
let mkInteger : Prims.string  ->  term = (fun i -> (mk (Integer (i))))

# 274 "FStar.SMTEncoding.Term.fst"
let mkInteger32 : Prims.int32  ->  term = (fun i -> (mkInteger (FStar_Util.string_of_int32 i)))

# 275 "FStar.SMTEncoding.Term.fst"
let mkInteger' : Prims.int  ->  term = (fun i -> (let _154_328 = (FStar_Util.string_of_int i)
in (mkInteger _154_328)))

# 276 "FStar.SMTEncoding.Term.fst"
let mkBoundV : Prims.int  ->  term = (fun i -> (mk (BoundV (i))))

# 277 "FStar.SMTEncoding.Term.fst"
let mkFreeV : (Prims.string * sort)  ->  term = (fun x -> (mk (FreeV (x))))

# 278 "FStar.SMTEncoding.Term.fst"
let mkApp' : (op * term Prims.list)  ->  term = (fun f -> (mk (App (f))))

# 279 "FStar.SMTEncoding.Term.fst"
let mkApp : (Prims.string * term Prims.list)  ->  term = (fun _72_219 -> (match (_72_219) with
| (s, args) -> begin
(mk (App ((Var (s), args))))
end))

# 280 "FStar.SMTEncoding.Term.fst"
let mkNot : term  ->  term = (fun t -> (match (t.tm) with
| App (True, _72_223) -> begin
mkFalse
end
| App (False, _72_228) -> begin
mkTrue
end
| _72_232 -> begin
(mkApp' (Not, (t)::[]))
end))

# 284 "FStar.SMTEncoding.Term.fst"
let mkAnd : (term * term)  ->  term = (fun _72_235 -> (match (_72_235) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (App (True, _72_238), _72_242) -> begin
t2
end
| (_72_245, App (True, _72_248)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
mkFalse
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' (And, (FStar_List.append ts1 ts2)))
end
| (_72_278, App (And, ts2)) -> begin
(mkApp' (And, (t1)::ts2))
end
| (App (And, ts1), _72_289) -> begin
(mkApp' (And, (FStar_List.append ts1 ((t2)::[]))))
end
| _72_292 -> begin
(mkApp' (And, (t1)::(t2)::[]))
end)
end))

# 293 "FStar.SMTEncoding.Term.fst"
let mkOr : (term * term)  ->  term = (fun _72_295 -> (match (_72_295) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
mkTrue
end
| (App (False, _72_314), _72_318) -> begin
t2
end
| (_72_321, App (False, _72_324)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' (Or, (FStar_List.append ts1 ts2)))
end
| (_72_338, App (Or, ts2)) -> begin
(mkApp' (Or, (t1)::ts2))
end
| (App (Or, ts1), _72_349) -> begin
(mkApp' (Or, (FStar_List.append ts1 ((t2)::[]))))
end
| _72_352 -> begin
(mkApp' (Or, (t1)::(t2)::[]))
end)
end))

# 302 "FStar.SMTEncoding.Term.fst"
let mkImp : (term * term)  ->  term = (fun _72_355 -> (match (_72_355) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (_72_357, App (True, _72_360)) -> begin
mkTrue
end
| (App (True, _72_366), _72_370) -> begin
t2
end
| (_72_373, App (Imp, t1'::t2'::[])) -> begin
(let _154_347 = (let _154_346 = (let _154_345 = (mkAnd (t1, t1'))
in (_154_345)::(t2')::[])
in (Imp, _154_346))
in (mkApp' _154_347))
end
| _72_382 -> begin
(mkApp' (Imp, (t1)::(t2)::[]))
end)
end))

# 308 "FStar.SMTEncoding.Term.fst"
let mk_bin_op : op  ->  (term * term)  ->  term = (fun op _72_386 -> (match (_72_386) with
| (t1, t2) -> begin
(mkApp' (op, (t1)::(t2)::[]))
end))

# 309 "FStar.SMTEncoding.Term.fst"
let mkMinus : term  ->  term = (fun t -> (mkApp' (Minus, (t)::[])))

# 310 "FStar.SMTEncoding.Term.fst"
let mkIff : (term * term)  ->  term = (mk_bin_op Iff)

# 311 "FStar.SMTEncoding.Term.fst"
let mkEq : (term * term)  ->  term = (mk_bin_op Eq)

# 312 "FStar.SMTEncoding.Term.fst"
let mkLT : (term * term)  ->  term = (mk_bin_op LT)

# 313 "FStar.SMTEncoding.Term.fst"
let mkLTE : (term * term)  ->  term = (mk_bin_op LTE)

# 314 "FStar.SMTEncoding.Term.fst"
let mkGT : (term * term)  ->  term = (mk_bin_op GT)

# 315 "FStar.SMTEncoding.Term.fst"
let mkGTE : (term * term)  ->  term = (mk_bin_op GTE)

# 316 "FStar.SMTEncoding.Term.fst"
let mkAdd : (term * term)  ->  term = (mk_bin_op Add)

# 317 "FStar.SMTEncoding.Term.fst"
let mkSub : (term * term)  ->  term = (mk_bin_op Sub)

# 318 "FStar.SMTEncoding.Term.fst"
let mkDiv : (term * term)  ->  term = (mk_bin_op Div)

# 319 "FStar.SMTEncoding.Term.fst"
let mkMul : (term * term)  ->  term = (mk_bin_op Mul)

# 320 "FStar.SMTEncoding.Term.fst"
let mkMod : (term * term)  ->  term = (mk_bin_op Mod)

# 321 "FStar.SMTEncoding.Term.fst"
let mkITE : (term * term * term)  ->  term = (fun _72_391 -> (match (_72_391) with
| (t1, t2, t3) -> begin
(match ((t2.tm, t3.tm)) with
| (App (True, _72_394), App (True, _72_399)) -> begin
mkTrue
end
| (App (True, _72_405), _72_409) -> begin
(let _154_368 = (let _154_367 = (mkNot t1)
in (_154_367, t3))
in (mkImp _154_368))
end
| (_72_412, App (True, _72_415)) -> begin
(mkImp (t1, t2))
end
| (_72_420, _72_422) -> begin
(mkApp' (ITE, (t1)::(t2)::(t3)::[]))
end)
end))

# 327 "FStar.SMTEncoding.Term.fst"
let mkCases : term Prims.list  ->  term = (fun t -> (match (t) with
| [] -> begin
(FStar_All.failwith "Impos")
end
| hd::tl -> begin
(FStar_List.fold_left (fun out t -> (mkAnd (out, t))) hd tl)
end))

# 331 "FStar.SMTEncoding.Term.fst"
let mkQuant : (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _72_436 -> (match (_72_436) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = 0) then begin
body
end else begin
(match (body.tm) with
| App (True, _72_439) -> begin
body
end
| _72_443 -> begin
(mk (Quant ((qop, pats, wopt, vars, body))))
end)
end
end))

# 340 "FStar.SMTEncoding.Term.fst"
let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (
# 341 "FStar.SMTEncoding.Term.fst"
let nvars = (FStar_List.length fvs)
in (
# 342 "FStar.SMTEncoding.Term.fst"
let index_of = (fun fv -> (match ((FStar_Util.try_find_index (fv_eq fv) fvs)) with
| None -> begin
None
end
| Some (i) -> begin
Some ((nvars - (i + 1)))
end))
in (
# 345 "FStar.SMTEncoding.Term.fst"
let rec aux = (fun ix t -> (match ((FStar_ST.read t.freevars)) with
| Some ([]) -> begin
t
end
| _72_458 -> begin
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
(let _154_386 = (let _154_385 = (FStar_List.map (aux ix) tms)
in (op, _154_385))
in (mkApp' _154_386))
end
| Labeled (t, r1, r2) -> begin
(let _154_389 = (let _154_388 = (let _154_387 = (aux ix t)
in (_154_387, r1, r2))
in Labeled (_154_388))
in (mk _154_389))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(
# 360 "FStar.SMTEncoding.Term.fst"
let n = (FStar_List.length vars)
in (let _154_392 = (let _154_391 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _154_390 = (aux (ix + n) body)
in (qop, _154_391, wopt, vars, _154_390)))
in (mkQuant _154_392)))
end)
end))
in (aux 0 t)))))

# 365 "FStar.SMTEncoding.Term.fst"
let inst : term Prims.list  ->  term  ->  term = (fun tms t -> (
# 366 "FStar.SMTEncoding.Term.fst"
let n = (FStar_List.length tms)
in (
# 367 "FStar.SMTEncoding.Term.fst"
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
(let _154_402 = (let _154_401 = (FStar_List.map (aux shift) tms)
in (op, _154_401))
in (mkApp' _154_402))
end
| Labeled (t, r1, r2) -> begin
(let _154_405 = (let _154_404 = (let _154_403 = (aux shift t)
in (_154_403, r1, r2))
in Labeled (_154_404))
in (mk _154_405))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(
# 377 "FStar.SMTEncoding.Term.fst"
let m = (FStar_List.length vars)
in (
# 378 "FStar.SMTEncoding.Term.fst"
let shift = (shift + m)
in (let _154_408 = (let _154_407 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _154_406 = (aux shift body)
in (qop, _154_407, wopt, vars, _154_406)))
in (mkQuant _154_408))))
end))
in (aux 0 t))))

# 382 "FStar.SMTEncoding.Term.fst"
let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list * term)  ->  term = (fun _72_524 -> (match (_72_524) with
| (qop, pats, wopt, vars, body) -> begin
(let _154_414 = (let _154_413 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _154_412 = (FStar_List.map fv_sort vars)
in (let _154_411 = (abstr vars body)
in (qop, _154_413, wopt, _154_412, _154_411))))
in (mkQuant _154_414))
end))

# 383 "FStar.SMTEncoding.Term.fst"
let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _72_529 -> (match (_72_529) with
| (pats, wopt, sorts, body) -> begin
(mkQuant (Forall, pats, wopt, sorts, body))
end))

# 384 "FStar.SMTEncoding.Term.fst"
let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  term = (fun _72_534 -> (match (_72_534) with
| (pats, wopt, vars, body) -> begin
(mkQuant' (Forall, pats, wopt, vars, body))
end))

# 387 "FStar.SMTEncoding.Term.fst"
let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _72_538 -> (match (_72_538) with
| (pats, vars, body) -> begin
(mkQuant' (Forall, pats, None, vars, body))
end))

# 388 "FStar.SMTEncoding.Term.fst"
let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _72_542 -> (match (_72_542) with
| (pats, vars, body) -> begin
(mkQuant' (Exists, pats, None, vars, body))
end))

# 391 "FStar.SMTEncoding.Term.fst"
let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun _72_548 -> (match (_72_548) with
| (nm, vars, s, tm, c) -> begin
(let _154_427 = (let _154_426 = (FStar_List.map fv_sort vars)
in (let _154_425 = (abstr vars tm)
in (nm, _154_426, s, _154_425, c)))
in DefineFun (_154_427))
end))

# 392 "FStar.SMTEncoding.Term.fst"
let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _154_430 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _154_430)))

# 393 "FStar.SMTEncoding.Term.fst"
let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun _72_552 id -> (match (_72_552) with
| (tok_name, sort) -> begin
(let _154_443 = (let _154_442 = (let _154_441 = (let _154_440 = (mkInteger' id)
in (let _154_439 = (let _154_438 = (let _154_437 = (constr_id_of_sort sort)
in (let _154_436 = (let _154_435 = (mkApp (tok_name, []))
in (_154_435)::[])
in (_154_437, _154_436)))
in (mkApp _154_438))
in (_154_440, _154_439)))
in (mkEq _154_441))
in (_154_442, Some ("fresh token")))
in Assume (_154_443))
end))

# 396 "FStar.SMTEncoding.Term.fst"
let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun _72_558 -> (match (_72_558) with
| (name, arg_sorts, sort, id) -> begin
(
# 397 "FStar.SMTEncoding.Term.fst"
let id = (FStar_Util.string_of_int id)
in (
# 398 "FStar.SMTEncoding.Term.fst"
let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (let _154_450 = (let _154_449 = (let _154_448 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _154_448))
in (_154_449, s))
in (mkFreeV _154_450)))))
in (
# 399 "FStar.SMTEncoding.Term.fst"
let bvar_names = (FStar_List.map fv_of_term bvars)
in (
# 400 "FStar.SMTEncoding.Term.fst"
let capp = (mkApp (name, bvars))
in (
# 401 "FStar.SMTEncoding.Term.fst"
let cid_app = (let _154_452 = (let _154_451 = (constr_id_of_sort sort)
in (_154_451, (capp)::[]))
in (mkApp _154_452))
in (let _154_458 = (let _154_457 = (let _154_456 = (let _154_455 = (let _154_454 = (let _154_453 = (mkInteger id)
in (_154_453, cid_app))
in (mkEq _154_454))
in (((capp)::[])::[], bvar_names, _154_455))
in (mkForall _154_456))
in (_154_457, Some ("Constructor distinct")))
in Assume (_154_458)))))))
end))

# 404 "FStar.SMTEncoding.Term.fst"
let injective_constructor : (Prims.string * (Prims.string * sort) Prims.list * sort)  ->  decls_t = (fun _72_569 -> (match (_72_569) with
| (name, projectors, sort) -> begin
(
# 405 "FStar.SMTEncoding.Term.fst"
let n_bvars = (FStar_List.length projectors)
in (
# 406 "FStar.SMTEncoding.Term.fst"
let bvar_name = (fun i -> (let _154_463 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _154_463)))
in (
# 407 "FStar.SMTEncoding.Term.fst"
let bvar_index = (fun i -> (n_bvars - (i + 1)))
in (
# 408 "FStar.SMTEncoding.Term.fst"
let bvar = (fun i s -> (let _154_471 = (let _154_470 = (bvar_name i)
in (_154_470, s))
in (mkFreeV _154_471)))
in (
# 409 "FStar.SMTEncoding.Term.fst"
let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _72_582 -> (match (_72_582) with
| (_72_580, s) -> begin
(bvar i s)
end))))
in (
# 410 "FStar.SMTEncoding.Term.fst"
let bvar_names = (FStar_List.map fv_of_term bvars)
in (
# 411 "FStar.SMTEncoding.Term.fst"
let capp = (mkApp (name, bvars))
in (let _154_484 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _72_589 -> (match (_72_589) with
| (name, s) -> begin
(
# 414 "FStar.SMTEncoding.Term.fst"
let cproj_app = (mkApp (name, (capp)::[]))
in (
# 415 "FStar.SMTEncoding.Term.fst"
let proj_name = DeclFun ((name, (sort)::[], s, Some ("Projector")))
in (let _154_483 = (let _154_482 = (let _154_481 = (let _154_480 = (let _154_479 = (let _154_478 = (let _154_477 = (let _154_476 = (bvar i s)
in (cproj_app, _154_476))
in (mkEq _154_477))
in (((capp)::[])::[], bvar_names, _154_478))
in (mkForall _154_479))
in (_154_480, Some ("Projection inverse")))
in Assume (_154_481))
in (_154_482)::[])
in (proj_name)::_154_483)))
end))))
in (FStar_All.pipe_right _154_484 FStar_List.flatten)))))))))
end))

# 420 "FStar.SMTEncoding.Term.fst"
let constructor_to_decl : constructor_t  ->  decls_t = (fun _72_597 -> (match (_72_597) with
| (name, projectors, sort, id, injective) -> begin
(
# 421 "FStar.SMTEncoding.Term.fst"
let injective = (injective || true)
in (
# 422 "FStar.SMTEncoding.Term.fst"
let cdecl = (let _154_488 = (let _154_487 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in (name, _154_487, sort, Some ("Constructor")))
in DeclFun (_154_488))
in (
# 423 "FStar.SMTEncoding.Term.fst"
let cid = (let _154_490 = (let _154_489 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in (name, _154_489, sort, id))
in (fresh_constructor _154_490))
in (
# 424 "FStar.SMTEncoding.Term.fst"
let disc = (
# 425 "FStar.SMTEncoding.Term.fst"
let disc_name = (Prims.strcat "is-" name)
in (
# 426 "FStar.SMTEncoding.Term.fst"
let xfv = ("x", sort)
in (
# 427 "FStar.SMTEncoding.Term.fst"
let xx = (mkFreeV xfv)
in (
# 428 "FStar.SMTEncoding.Term.fst"
let disc_eq = (let _154_496 = (let _154_495 = (let _154_492 = (let _154_491 = (constr_id_of_sort sort)
in (_154_491, (xx)::[]))
in (mkApp _154_492))
in (let _154_494 = (let _154_493 = (FStar_Util.string_of_int id)
in (mkInteger _154_493))
in (_154_495, _154_494)))
in (mkEq _154_496))
in (
# 429 "FStar.SMTEncoding.Term.fst"
let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _72_607 -> (match (_72_607) with
| (proj, s) -> begin
(mkApp (proj, (xx)::[]))
end))))
in (
# 430 "FStar.SMTEncoding.Term.fst"
let disc_inv_body = (let _154_499 = (let _154_498 = (mkApp (name, proj_terms))
in (xx, _154_498))
in (mkEq _154_499))
in (
# 431 "FStar.SMTEncoding.Term.fst"
let disc_ax = (mkAnd (disc_eq, disc_inv_body))
in (mkDefineFun (disc_name, (xfv)::[], Bool_sort, disc_ax, Some ("Discriminator definition"))))))))))
in (
# 435 "FStar.SMTEncoding.Term.fst"
let projs = if injective then begin
(injective_constructor (name, projectors, sort))
end else begin
[]
end
in (let _154_506 = (let _154_502 = (let _154_501 = (let _154_500 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_154_500))
in (_154_501)::(cdecl)::(cid)::projs)
in (FStar_List.append _154_502 ((disc)::[])))
in (let _154_505 = (let _154_504 = (let _154_503 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_154_503))
in (_154_504)::[])
in (FStar_List.append _154_506 _154_505))))))))
end))

# 445 "FStar.SMTEncoding.Term.fst"
let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (
# 446 "FStar.SMTEncoding.Term.fst"
let _72_631 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _72_619 s -> (match (_72_619) with
| (names, binders, n) -> begin
(
# 447 "FStar.SMTEncoding.Term.fst"
let prefix = (match (s) with
| Term_sort -> begin
"@x"
end
| _72_623 -> begin
"@u"
end)
in (
# 450 "FStar.SMTEncoding.Term.fst"
let nm = (let _154_515 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _154_515))
in (
# 451 "FStar.SMTEncoding.Term.fst"
let names = ((nm, s))::names
in (
# 452 "FStar.SMTEncoding.Term.fst"
let b = (let _154_516 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _154_516))
in (names, (b)::binders, (n + 1))))))
end)) (outer_names, [], start)))
in (match (_72_631) with
| (names, binders, n) -> begin
(names, (FStar_List.rev binders), n)
end)))

# 457 "FStar.SMTEncoding.Term.fst"
let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (
# 458 "FStar.SMTEncoding.Term.fst"
let _72_636 = (name_binders_inner [] 0 sorts)
in (match (_72_636) with
| (names, binders, n) -> begin
((FStar_List.rev names), binders)
end)))

# 461 "FStar.SMTEncoding.Term.fst"
let termToSmt : term  ->  Prims.string = (fun t -> (
# 462 "FStar.SMTEncoding.Term.fst"
let rec aux = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _154_527 = (FStar_List.nth names i)
in (FStar_All.pipe_right _154_527 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _154_529 = (let _154_528 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _154_528 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _154_529))
end
| Labeled (t, _72_658, _72_660) -> begin
(aux n names t)
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(
# 471 "FStar.SMTEncoding.Term.fst"
let _72_673 = (name_binders_inner names n sorts)
in (match (_72_673) with
| (names, binders, n) -> begin
(
# 472 "FStar.SMTEncoding.Term.fst"
let binders = (FStar_All.pipe_right binders (FStar_String.concat " "))
in (
# 473 "FStar.SMTEncoding.Term.fst"
let pats_str = (match (pats) with
| ([]::[]) | ([]) -> begin
""
end
| _72_679 -> begin
(let _154_535 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _154_534 = (let _154_533 = (FStar_List.map (fun p -> (let _154_532 = (aux n names p)
in (FStar_Util.format1 "%s" _154_532))) pats)
in (FStar_String.concat " " _154_533))
in (FStar_Util.format1 "\n:pattern (%s)" _154_534)))))
in (FStar_All.pipe_right _154_535 (FStar_String.concat "\n")))
end)
in (match ((pats, wopt)) with
| (([]::[], None)) | (([], None)) -> begin
(let _154_536 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _154_536))
end
| _72_691 -> begin
(let _154_538 = (aux n names body)
in (let _154_537 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _154_538 _154_537 pats_str)))
end)))
end))
end))
in (aux 0 [] t)))

# 485 "FStar.SMTEncoding.Term.fst"
let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun _72_6 -> (match (_72_6) with
| None -> begin
""
end
| Some (c) -> begin
(
# 488 "FStar.SMTEncoding.Term.fst"
let _72_705 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::[] -> begin
(hd, "")
end
| hd::_72_700 -> begin
(hd, "...")
end)
in (match (_72_705) with
| (hd, suffix) -> begin
(FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd suffix)
end))
end))

# 494 "FStar.SMTEncoding.Term.fst"
let rec declToSmt : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(let _154_547 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _72_7 -> (match (_72_7) with
| [] -> begin
""
end
| h::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _154_547))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(
# 499 "FStar.SMTEncoding.Term.fst"
let l = (FStar_List.map strSort argsorts)
in (let _154_549 = (caption_to_string c)
in (let _154_548 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _154_549 f (FStar_String.concat " " l) _154_548))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(
# 502 "FStar.SMTEncoding.Term.fst"
let _72_732 = (name_binders arg_sorts)
in (match (_72_732) with
| (names, binders) -> begin
(
# 503 "FStar.SMTEncoding.Term.fst"
let body = (let _154_550 = (FStar_List.map mkFreeV names)
in (inst _154_550 body))
in (let _154_553 = (caption_to_string c)
in (let _154_552 = (strSort retsort)
in (let _154_551 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _154_553 f (FStar_String.concat " " binders) _154_552 _154_551)))))
end))
end
| Assume (t, c) -> begin
(let _154_555 = (caption_to_string c)
in (let _154_554 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _154_555 _154_554)))
end
| Eval (t) -> begin
(let _154_556 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _154_556))
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
# 516 "FStar.SMTEncoding.Term.fst"
let basic = (Prims.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort String)\n(declare-fun String_constr_id (String) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n")
in (
# 562 "FStar.SMTEncoding.Term.fst"
let constrs = (("String_const", (("String_const_proj_0", Int_sort))::[], String_sort, 0, true))::(("Tm_type", [], Term_sort, 2, true))::(("Tm_arrow", (("Tm_arrow_id", Int_sort))::[], Term_sort, 3, false))::(("Tm_uvar", (("Tm_uvar_fst", Int_sort))::[], Term_sort, 5, true))::(("Tm_unit", [], Term_sort, 6, true))::(("BoxInt", (("BoxInt_proj_0", Int_sort))::[], Term_sort, 7, true))::(("BoxBool", (("BoxBool_proj_0", Bool_sort))::[], Term_sort, 8, true))::(("BoxString", (("BoxString_proj_0", String_sort))::[], Term_sort, 9, true))::(("BoxRef", (("BoxRef_proj_0", Ref_sort))::[], Term_sort, 10, true))::(("LexCons", (("LexCons_0", Term_sort))::(("LexCons_1", Term_sort))::[], Term_sort, 11, true))::[]
in (
# 572 "FStar.SMTEncoding.Term.fst"
let bcons = (let _154_559 = (let _154_558 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _154_558 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _154_559 (FStar_String.concat "\n")))
in (
# 573 "FStar.SMTEncoding.Term.fst"
let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat (Prims.strcat basic bcons) lex_ordering))))))

# 582 "FStar.SMTEncoding.Term.fst"
let mk_Range_const : term = (mkApp ("Range_const", []))

# 583 "FStar.SMTEncoding.Term.fst"
let mk_Term_type : term = (mkApp ("Tm_type", []))

# 584 "FStar.SMTEncoding.Term.fst"
let mk_Term_app : term  ->  term  ->  term = (fun t1 t2 -> (mkApp ("Tm_app", (t1)::(t2)::[])))

# 585 "FStar.SMTEncoding.Term.fst"
let mk_Term_uvar : Prims.int  ->  term = (fun i -> (let _154_568 = (let _154_567 = (let _154_566 = (mkInteger' i)
in (_154_566)::[])
in ("Tm_uvar", _154_567))
in (mkApp _154_568)))

# 586 "FStar.SMTEncoding.Term.fst"
let mk_Term_unit : term = (mkApp ("Tm_unit", []))

# 587 "FStar.SMTEncoding.Term.fst"
let boxInt : term  ->  term = (fun t -> (mkApp ("BoxInt", (t)::[])))

# 588 "FStar.SMTEncoding.Term.fst"
let unboxInt : term  ->  term = (fun t -> (mkApp ("BoxInt_proj_0", (t)::[])))

# 589 "FStar.SMTEncoding.Term.fst"
let boxBool : term  ->  term = (fun t -> (mkApp ("BoxBool", (t)::[])))

# 590 "FStar.SMTEncoding.Term.fst"
let unboxBool : term  ->  term = (fun t -> (mkApp ("BoxBool_proj_0", (t)::[])))

# 591 "FStar.SMTEncoding.Term.fst"
let boxString : term  ->  term = (fun t -> (mkApp ("BoxString", (t)::[])))

# 592 "FStar.SMTEncoding.Term.fst"
let unboxString : term  ->  term = (fun t -> (mkApp ("BoxString_proj_0", (t)::[])))

# 593 "FStar.SMTEncoding.Term.fst"
let boxRef : term  ->  term = (fun t -> (mkApp ("BoxRef", (t)::[])))

# 594 "FStar.SMTEncoding.Term.fst"
let unboxRef : term  ->  term = (fun t -> (mkApp ("BoxRef_proj_0", (t)::[])))

# 595 "FStar.SMTEncoding.Term.fst"
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
| _72_768 -> begin
(Prims.raise FStar_Util.Impos)
end))

# 601 "FStar.SMTEncoding.Term.fst"
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
| _72_776 -> begin
(Prims.raise FStar_Util.Impos)
end))

# 608 "FStar.SMTEncoding.Term.fst"
let mk_PreType : term  ->  term = (fun t -> (mkApp ("PreType", (t)::[])))

# 609 "FStar.SMTEncoding.Term.fst"
let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_Equality"), _72_790::t1::t2::[]); hash = _72_784; freevars = _72_782}::[]) -> begin
(mkEq (t1, t2))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_disEquality"), _72_809::t1::t2::[]); hash = _72_803; freevars = _72_801}::[]) -> begin
(let _154_597 = (mkEq (t1, t2))
in (mkNot _154_597))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_LessThanOrEqual"), t1::t2::[]); hash = _72_822; freevars = _72_820}::[]) -> begin
(let _154_600 = (let _154_599 = (unboxInt t1)
in (let _154_598 = (unboxInt t2)
in (_154_599, _154_598)))
in (mkLTE _154_600))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_LessThan"), t1::t2::[]); hash = _72_839; freevars = _72_837}::[]) -> begin
(let _154_603 = (let _154_602 = (unboxInt t1)
in (let _154_601 = (unboxInt t2)
in (_154_602, _154_601)))
in (mkLT _154_603))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_GreaterThanOrEqual"), t1::t2::[]); hash = _72_856; freevars = _72_854}::[]) -> begin
(let _154_606 = (let _154_605 = (unboxInt t1)
in (let _154_604 = (unboxInt t2)
in (_154_605, _154_604)))
in (mkGTE _154_606))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_GreaterThan"), t1::t2::[]); hash = _72_873; freevars = _72_871}::[]) -> begin
(let _154_609 = (let _154_608 = (unboxInt t1)
in (let _154_607 = (unboxInt t2)
in (_154_608, _154_607)))
in (mkGT _154_609))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_AmpAmp"), t1::t2::[]); hash = _72_890; freevars = _72_888}::[]) -> begin
(let _154_612 = (let _154_611 = (unboxBool t1)
in (let _154_610 = (unboxBool t2)
in (_154_611, _154_610)))
in (mkAnd _154_612))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_BarBar"), t1::t2::[]); hash = _72_907; freevars = _72_905}::[]) -> begin
(let _154_615 = (let _154_614 = (unboxBool t1)
in (let _154_613 = (unboxBool t2)
in (_154_614, _154_613)))
in (mkOr _154_615))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_Negation"), t::[]); hash = _72_924; freevars = _72_922}::[]) -> begin
(let _154_616 = (unboxBool t)
in (mkNot _154_616))
end
| App (Var ("Prims.b2t"), t::[]) -> begin
(unboxBool t)
end
| _72_942 -> begin
(mkApp ("Valid", (t)::[]))
end))

# 621 "FStar.SMTEncoding.Term.fst"
let mk_HasType : term  ->  term  ->  term = (fun v t -> (mkApp ("HasType", (v)::(t)::[])))

# 622 "FStar.SMTEncoding.Term.fst"
let mk_HasTypeZ : term  ->  term  ->  term = (fun v t -> (mkApp ("HasTypeZ", (v)::(t)::[])))

# 623 "FStar.SMTEncoding.Term.fst"
let mk_IsTyped : term  ->  term = (fun v -> (mkApp ("IsTyped", (v)::[])))

# 624 "FStar.SMTEncoding.Term.fst"
let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v t -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(mk_HasType v t)
end else begin
(mkApp ("HasTypeFuel", (f)::(v)::(t)::[]))
end)

# 628 "FStar.SMTEncoding.Term.fst"
let mk_HasTypeWithFuel : term Prims.option  ->  term  ->  term  ->  term = (fun f v t -> (match (f) with
| None -> begin
(mk_HasType v t)
end
| Some (f) -> begin
(mk_HasTypeFuel f v t)
end))

# 631 "FStar.SMTEncoding.Term.fst"
let mk_Destruct : term  ->  term = (fun v -> (mkApp ("Destruct", (v)::[])))

# 632 "FStar.SMTEncoding.Term.fst"
let mk_Rank : term  ->  term = (fun x -> (mkApp ("Rank", (x)::[])))

# 633 "FStar.SMTEncoding.Term.fst"
let mk_tester : Prims.string  ->  term  ->  term = (fun n t -> (mkApp ((Prims.strcat "is-" n), (t)::[])))

# 634 "FStar.SMTEncoding.Term.fst"
let mk_ApplyTF : term  ->  term  ->  term = (fun t t' -> (mkApp ("ApplyTF", (t)::(t')::[])))

# 635 "FStar.SMTEncoding.Term.fst"
let mk_ApplyTT : term  ->  term  ->  term = (fun t t' -> (mkApp ("ApplyTT", (t)::(t')::[])))

# 636 "FStar.SMTEncoding.Term.fst"
let mk_String_const : Prims.int  ->  term = (fun i -> (let _154_659 = (let _154_658 = (let _154_657 = (mkInteger' i)
in (_154_657)::[])
in ("String_const", _154_658))
in (mkApp _154_659)))

# 637 "FStar.SMTEncoding.Term.fst"
let mk_Precedes : term  ->  term  ->  term = (fun x1 x2 -> (let _154_664 = (mkApp ("Precedes", (x1)::(x2)::[]))
in (FStar_All.pipe_right _154_664 mk_Valid)))

# 638 "FStar.SMTEncoding.Term.fst"
let mk_LexCons : term  ->  term  ->  term = (fun x1 x2 -> (mkApp ("LexCons", (x1)::(x2)::[])))

# 639 "FStar.SMTEncoding.Term.fst"
let rec n_fuel : Prims.int  ->  term = (fun n -> if (n = 0) then begin
(mkApp ("ZFuel", []))
end else begin
(let _154_673 = (let _154_672 = (let _154_671 = (n_fuel (n - 1))
in (_154_671)::[])
in ("SFuel", _154_672))
in (mkApp _154_673))
end)

# 642 "FStar.SMTEncoding.Term.fst"
let fuel_2 : term = (n_fuel 2)

# 643 "FStar.SMTEncoding.Term.fst"
let fuel_100 : term = (n_fuel 100)

# 645 "FStar.SMTEncoding.Term.fst"
let mk_and_opt : term Prims.option  ->  term Prims.option  ->  term Prims.option = (fun p1 p2 -> (match ((p1, p2)) with
| (Some (p1), Some (p2)) -> begin
(let _154_678 = (mkAnd (p1, p2))
in Some (_154_678))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))

# 651 "FStar.SMTEncoding.Term.fst"
let mk_and_opt_l : term Prims.option Prims.list  ->  term Prims.option = (fun pl -> (FStar_List.fold_left (fun out p -> (mk_and_opt p out)) None pl))

# 654 "FStar.SMTEncoding.Term.fst"
let mk_and_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkTrue
end
| hd::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkAnd (p1, p2))) hd tl)
end))

# 658 "FStar.SMTEncoding.Term.fst"
let mk_or_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkFalse
end
| hd::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkOr (p1, p2))) hd tl)
end))

# 663 "FStar.SMTEncoding.Term.fst"
let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "(Integer %s)" n)
end
| BoundV (n) -> begin
(let _154_695 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "(BoundV %s)" _154_695))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (Prims.fst fv))
end
| App (op, l) -> begin
(let _154_696 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _154_696))
end
| Labeled (t, r1, r2) -> begin
(let _154_697 = (print_smt_term t)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 _154_697))
end
| Quant (qop, l, _72_1024, _72_1026, t) -> begin
(let _154_699 = (print_smt_term_list_list l)
in (let _154_698 = (print_smt_term t)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) _154_699 _154_698)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (let _154_701 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right _154_701 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _154_706 = (let _154_705 = (print_smt_term_list l)
in (Prims.strcat (Prims.strcat s "; [ ") _154_705))
in (Prims.strcat _154_706 " ] "))) "" l))




