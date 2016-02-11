
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
| Array (_73_10) -> begin
_73_10
end))

# 34 "FStar.SMTEncoding.Term.fst"
let ___Arrow____0 : sort  ->  (sort * sort) = (fun projectee -> (match (projectee) with
| Arrow (_73_13) -> begin
_73_13
end))

# 35 "FStar.SMTEncoding.Term.fst"
let ___Sort____0 : sort  ->  Prims.string = (fun projectee -> (match (projectee) with
| Sort (_73_16) -> begin
_73_16
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
(let _152_52 = (strSort s1)
in (let _152_51 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _152_52 _152_51)))
end
| Arrow (s1, s2) -> begin
(let _152_54 = (strSort s1)
in (let _152_53 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _152_54 _152_53)))
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
| Var (_73_36) -> begin
_73_36
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
| Integer (_73_42) -> begin
_73_42
end))

# 77 "FStar.SMTEncoding.Term.fst"
let ___BoundV____0 : term'  ->  Prims.int = (fun projectee -> (match (projectee) with
| BoundV (_73_45) -> begin
_73_45
end))

# 78 "FStar.SMTEncoding.Term.fst"
let ___FreeV____0 : term'  ->  fv = (fun projectee -> (match (projectee) with
| FreeV (_73_48) -> begin
_73_48
end))

# 79 "FStar.SMTEncoding.Term.fst"
let ___App____0 : term'  ->  (op * term Prims.list) = (fun projectee -> (match (projectee) with
| App (_73_51) -> begin
_73_51
end))

# 80 "FStar.SMTEncoding.Term.fst"
let ___Quant____0 : term'  ->  (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term) = (fun projectee -> (match (projectee) with
| Quant (_73_54) -> begin
_73_54
end))

# 85 "FStar.SMTEncoding.Term.fst"
let ___Labeled____0 : term'  ->  (term * Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Labeled (_73_57) -> begin
_73_57
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
(Prims.string * projector Prims.list * sort * Prims.int)

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
| DeclFun (_73_61) -> begin
_73_61
end))

# 99 "FStar.SMTEncoding.Term.fst"
let ___DefineFun____0 : decl  ->  (Prims.string * sort Prims.list * sort * term * caption) = (fun projectee -> (match (projectee) with
| DefineFun (_73_64) -> begin
_73_64
end))

# 100 "FStar.SMTEncoding.Term.fst"
let ___Assume____0 : decl  ->  (term * caption) = (fun projectee -> (match (projectee) with
| Assume (_73_67) -> begin
_73_67
end))

# 101 "FStar.SMTEncoding.Term.fst"
let ___Caption____0 : decl  ->  Prims.string = (fun projectee -> (match (projectee) with
| Caption (_73_70) -> begin
_73_70
end))

# 102 "FStar.SMTEncoding.Term.fst"
let ___Eval____0 : decl  ->  term = (fun projectee -> (match (projectee) with
| Eval (_73_73) -> begin
_73_73
end))

# 103 "FStar.SMTEncoding.Term.fst"
let ___Echo____0 : decl  ->  Prims.string = (fun projectee -> (match (projectee) with
| Echo (_73_76) -> begin
_73_76
end))

# 107 "FStar.SMTEncoding.Term.fst"
type decls_t =
decl Prims.list

# 182 "FStar.SMTEncoding.Term.fst"
let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> ((Prims.fst x) = (Prims.fst y)))

# 183 "FStar.SMTEncoding.Term.fst"
let fv_sort = (fun x -> (Prims.snd x))

# 184 "FStar.SMTEncoding.Term.fst"
let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match ((x.tm, y.tm)) with
| (FreeV (x), FreeV (y)) -> begin
(fv_eq x y)
end
| _73_88 -> begin
false
end))

# 187 "FStar.SMTEncoding.Term.fst"
let freevar_sort : term  ->  sort = (fun _73_1 -> (match (_73_1) with
| {tm = FreeV (x); hash = _73_93; freevars = _73_91} -> begin
(fv_sort x)
end
| _73_98 -> begin
(FStar_All.failwith "impossible")
end))

# 190 "FStar.SMTEncoding.Term.fst"
let fv_of_term : term  ->  fv = (fun _73_2 -> (match (_73_2) with
| {tm = FreeV (fv); hash = _73_103; freevars = _73_101} -> begin
fv
end
| _73_108 -> begin
(FStar_All.failwith "impossible")
end))

# 193 "FStar.SMTEncoding.Term.fst"
let rec freevars : term  ->  fv Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (_73_119, tms) -> begin
(FStar_List.collect freevars tms)
end
| (Quant (_, _, _, _, t)) | (Labeled (t, _, _)) -> begin
(freevars t)
end))

# 202 "FStar.SMTEncoding.Term.fst"
let free_variables : term  ->  fvs = (fun t -> (match ((FStar_ST.read t.freevars)) with
| Some (b) -> begin
b
end
| None -> begin
(
# 205 "FStar.SMTEncoding.Term.fst"
let fvs = (let _152_289 = (freevars t)
in (FStar_Util.remove_dups fv_eq _152_289))
in (
# 206 "FStar.SMTEncoding.Term.fst"
let _73_145 = (FStar_ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))

# 212 "FStar.SMTEncoding.Term.fst"
let qop_to_string : qop  ->  Prims.string = (fun _73_3 -> (match (_73_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))

# 216 "FStar.SMTEncoding.Term.fst"
let op_to_string : op  ->  Prims.string = (fun _73_4 -> (match (_73_4) with
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

# 238 "FStar.SMTEncoding.Term.fst"
let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun _73_5 -> (match (_73_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _152_296 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _152_296))
end))

# 242 "FStar.SMTEncoding.Term.fst"
let hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _152_299 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _152_299))
end
| FreeV (x) -> begin
(let _152_300 = (strSort (Prims.snd x))
in (Prims.strcat (Prims.strcat (Prims.fst x) ":") _152_300))
end
| App (op, tms) -> begin
(let _152_304 = (let _152_303 = (let _152_302 = (FStar_List.map (fun t -> t.hash) tms)
in (FStar_All.pipe_right _152_302 (FStar_String.concat " ")))
in (Prims.strcat (Prims.strcat "(" (op_to_string op)) _152_303))
in (Prims.strcat _152_304 ")"))
end
| Labeled (t, r1, r2) -> begin
(let _152_305 = (FStar_Range.string_of_range r2)
in (Prims.strcat (Prims.strcat t.hash r1) _152_305))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _152_313 = (let _152_306 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _152_306 (FStar_String.concat " ")))
in (let _152_312 = (weightToSmt wopt)
in (let _152_311 = (let _152_310 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _152_309 = (FStar_List.map (fun p -> p.hash) pats)
in (FStar_All.pipe_right _152_309 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _152_310 (FStar_String.concat "; ")))
in (FStar_Util.format5 "(%s (%s)(! %s %s %s))" (qop_to_string qop) _152_313 body.hash _152_312 _152_311))))
end))

# 257 "FStar.SMTEncoding.Term.fst"
let __all_terms : term FStar_Util.smap FStar_ST.ref = (let _152_314 = (FStar_Util.smap_create 10000)
in (FStar_ST.alloc _152_314))

# 258 "FStar.SMTEncoding.Term.fst"
let all_terms : Prims.unit  ->  term FStar_Util.smap = (fun _73_202 -> (match (()) with
| () -> begin
(FStar_ST.read __all_terms)
end))

# 259 "FStar.SMTEncoding.Term.fst"
let mk : term'  ->  term = (fun t -> (
# 260 "FStar.SMTEncoding.Term.fst"
let key = (hash_of_term' t)
in (match ((let _152_319 = (all_terms ())
in (FStar_Util.smap_try_find _152_319 key))) with
| Some (tm) -> begin
tm
end
| None -> begin
(
# 264 "FStar.SMTEncoding.Term.fst"
let tm = (let _152_320 = (FStar_Util.mk_ref None)
in {tm = t; hash = key; freevars = _152_320})
in (
# 265 "FStar.SMTEncoding.Term.fst"
let _73_209 = (let _152_321 = (all_terms ())
in (FStar_Util.smap_add _152_321 key tm))
in tm))
end)))

# 268 "FStar.SMTEncoding.Term.fst"
let mkTrue : term = (mk (App ((True, []))))

# 269 "FStar.SMTEncoding.Term.fst"
let mkFalse : term = (mk (App ((False, []))))

# 270 "FStar.SMTEncoding.Term.fst"
let mkInteger : Prims.string  ->  term = (fun i -> (mk (Integer (i))))

# 271 "FStar.SMTEncoding.Term.fst"
let mkInteger32 : Prims.int32  ->  term = (fun i -> (mkInteger (FStar_Util.string_of_int32 i)))

# 272 "FStar.SMTEncoding.Term.fst"
let mkInteger' : Prims.int  ->  term = (fun i -> (let _152_328 = (FStar_Util.string_of_int i)
in (mkInteger _152_328)))

# 273 "FStar.SMTEncoding.Term.fst"
let mkBoundV : Prims.int  ->  term = (fun i -> (mk (BoundV (i))))

# 274 "FStar.SMTEncoding.Term.fst"
let mkFreeV : (Prims.string * sort)  ->  term = (fun x -> (mk (FreeV (x))))

# 275 "FStar.SMTEncoding.Term.fst"
let mkApp' : (op * term Prims.list)  ->  term = (fun f -> (mk (App (f))))

# 276 "FStar.SMTEncoding.Term.fst"
let mkApp : (Prims.string * term Prims.list)  ->  term = (fun _73_219 -> (match (_73_219) with
| (s, args) -> begin
(mk (App ((Var (s), args))))
end))

# 277 "FStar.SMTEncoding.Term.fst"
let mkNot : term  ->  term = (fun t -> (match (t.tm) with
| App (True, _73_223) -> begin
mkFalse
end
| App (False, _73_228) -> begin
mkTrue
end
| _73_232 -> begin
(mkApp' (Not, (t)::[]))
end))

# 281 "FStar.SMTEncoding.Term.fst"
let mkAnd : (term * term)  ->  term = (fun _73_235 -> (match (_73_235) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (App (True, _73_238), _73_242) -> begin
t2
end
| (_73_245, App (True, _73_248)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
mkFalse
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' (And, (FStar_List.append ts1 ts2)))
end
| (_73_278, App (And, ts2)) -> begin
(mkApp' (And, (t1)::ts2))
end
| (App (And, ts1), _73_289) -> begin
(mkApp' (And, (FStar_List.append ts1 ((t2)::[]))))
end
| _73_292 -> begin
(mkApp' (And, (t1)::(t2)::[]))
end)
end))

# 290 "FStar.SMTEncoding.Term.fst"
let mkOr : (term * term)  ->  term = (fun _73_295 -> (match (_73_295) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
mkTrue
end
| (App (False, _73_314), _73_318) -> begin
t2
end
| (_73_321, App (False, _73_324)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' (Or, (FStar_List.append ts1 ts2)))
end
| (_73_338, App (Or, ts2)) -> begin
(mkApp' (Or, (t1)::ts2))
end
| (App (Or, ts1), _73_349) -> begin
(mkApp' (Or, (FStar_List.append ts1 ((t2)::[]))))
end
| _73_352 -> begin
(mkApp' (Or, (t1)::(t2)::[]))
end)
end))

# 299 "FStar.SMTEncoding.Term.fst"
let mkImp : (term * term)  ->  term = (fun _73_355 -> (match (_73_355) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (_73_357, App (True, _73_360)) -> begin
mkTrue
end
| (App (True, _73_366), _73_370) -> begin
t2
end
| (_73_373, App (Imp, t1'::t2'::[])) -> begin
(let _152_347 = (let _152_346 = (let _152_345 = (mkAnd (t1, t1'))
in (_152_345)::(t2')::[])
in (Imp, _152_346))
in (mkApp' _152_347))
end
| _73_382 -> begin
(mkApp' (Imp, (t1)::(t2)::[]))
end)
end))

# 305 "FStar.SMTEncoding.Term.fst"
let mk_bin_op : op  ->  (term * term)  ->  term = (fun op _73_386 -> (match (_73_386) with
| (t1, t2) -> begin
(mkApp' (op, (t1)::(t2)::[]))
end))

# 306 "FStar.SMTEncoding.Term.fst"
let mkMinus : term  ->  term = (fun t -> (mkApp' (Minus, (t)::[])))

# 307 "FStar.SMTEncoding.Term.fst"
let mkIff : (term * term)  ->  term = (mk_bin_op Iff)

# 308 "FStar.SMTEncoding.Term.fst"
let mkEq : (term * term)  ->  term = (mk_bin_op Eq)

# 309 "FStar.SMTEncoding.Term.fst"
let mkLT : (term * term)  ->  term = (mk_bin_op LT)

# 310 "FStar.SMTEncoding.Term.fst"
let mkLTE : (term * term)  ->  term = (mk_bin_op LTE)

# 311 "FStar.SMTEncoding.Term.fst"
let mkGT : (term * term)  ->  term = (mk_bin_op GT)

# 312 "FStar.SMTEncoding.Term.fst"
let mkGTE : (term * term)  ->  term = (mk_bin_op GTE)

# 313 "FStar.SMTEncoding.Term.fst"
let mkAdd : (term * term)  ->  term = (mk_bin_op Add)

# 314 "FStar.SMTEncoding.Term.fst"
let mkSub : (term * term)  ->  term = (mk_bin_op Sub)

# 315 "FStar.SMTEncoding.Term.fst"
let mkDiv : (term * term)  ->  term = (mk_bin_op Div)

# 316 "FStar.SMTEncoding.Term.fst"
let mkMul : (term * term)  ->  term = (mk_bin_op Mul)

# 317 "FStar.SMTEncoding.Term.fst"
let mkMod : (term * term)  ->  term = (mk_bin_op Mod)

# 318 "FStar.SMTEncoding.Term.fst"
let mkITE : (term * term * term)  ->  term = (fun _73_391 -> (match (_73_391) with
| (t1, t2, t3) -> begin
(match ((t2.tm, t3.tm)) with
| (App (True, _73_394), App (True, _73_399)) -> begin
mkTrue
end
| (App (True, _73_405), _73_409) -> begin
(let _152_368 = (let _152_367 = (mkNot t1)
in (_152_367, t3))
in (mkImp _152_368))
end
| (_73_412, App (True, _73_415)) -> begin
(mkImp (t1, t2))
end
| (_73_420, _73_422) -> begin
(mkApp' (ITE, (t1)::(t2)::(t3)::[]))
end)
end))

# 324 "FStar.SMTEncoding.Term.fst"
let mkCases : term Prims.list  ->  term = (fun t -> (match (t) with
| [] -> begin
(FStar_All.failwith "Impos")
end
| hd::tl -> begin
(FStar_List.fold_left (fun out t -> (mkAnd (out, t))) hd tl)
end))

# 328 "FStar.SMTEncoding.Term.fst"
let mkQuant : (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _73_436 -> (match (_73_436) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = 0) then begin
body
end else begin
(match (body.tm) with
| App (True, _73_439) -> begin
body
end
| _73_443 -> begin
(mk (Quant ((qop, pats, wopt, vars, body))))
end)
end
end))

# 337 "FStar.SMTEncoding.Term.fst"
let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (
# 338 "FStar.SMTEncoding.Term.fst"
let nvars = (FStar_List.length fvs)
in (
# 339 "FStar.SMTEncoding.Term.fst"
let index_of = (fun fv -> (match ((FStar_Util.try_find_index (fv_eq fv) fvs)) with
| None -> begin
None
end
| Some (i) -> begin
Some ((nvars - (i + 1)))
end))
in (
# 342 "FStar.SMTEncoding.Term.fst"
let rec aux = (fun ix t -> (match ((FStar_ST.read t.freevars)) with
| Some ([]) -> begin
t
end
| _73_458 -> begin
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
(let _152_386 = (let _152_385 = (FStar_List.map (aux ix) tms)
in (op, _152_385))
in (mkApp' _152_386))
end
| Labeled (t, r1, r2) -> begin
(let _152_389 = (let _152_388 = (let _152_387 = (aux ix t)
in (_152_387, r1, r2))
in Labeled (_152_388))
in (mk _152_389))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(
# 357 "FStar.SMTEncoding.Term.fst"
let n = (FStar_List.length vars)
in (let _152_392 = (let _152_391 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _152_390 = (aux (ix + n) body)
in (qop, _152_391, wopt, vars, _152_390)))
in (mkQuant _152_392)))
end)
end))
in (aux 0 t)))))

# 362 "FStar.SMTEncoding.Term.fst"
let inst : term Prims.list  ->  term  ->  term = (fun tms t -> (
# 363 "FStar.SMTEncoding.Term.fst"
let n = (FStar_List.length tms)
in (
# 364 "FStar.SMTEncoding.Term.fst"
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
(let _152_402 = (let _152_401 = (FStar_List.map (aux shift) tms)
in (op, _152_401))
in (mkApp' _152_402))
end
| Labeled (t, r1, r2) -> begin
(let _152_405 = (let _152_404 = (let _152_403 = (aux shift t)
in (_152_403, r1, r2))
in Labeled (_152_404))
in (mk _152_405))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(
# 374 "FStar.SMTEncoding.Term.fst"
let m = (FStar_List.length vars)
in (
# 375 "FStar.SMTEncoding.Term.fst"
let shift = (shift + m)
in (let _152_408 = (let _152_407 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _152_406 = (aux shift body)
in (qop, _152_407, wopt, vars, _152_406)))
in (mkQuant _152_408))))
end))
in (aux 0 t))))

# 379 "FStar.SMTEncoding.Term.fst"
let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list * term)  ->  term = (fun _73_524 -> (match (_73_524) with
| (qop, pats, wopt, vars, body) -> begin
(let _152_414 = (let _152_413 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _152_412 = (FStar_List.map fv_sort vars)
in (let _152_411 = (abstr vars body)
in (qop, _152_413, wopt, _152_412, _152_411))))
in (mkQuant _152_414))
end))

# 380 "FStar.SMTEncoding.Term.fst"
let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _73_529 -> (match (_73_529) with
| (pats, wopt, sorts, body) -> begin
(mkQuant (Forall, pats, wopt, sorts, body))
end))

# 381 "FStar.SMTEncoding.Term.fst"
let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  term = (fun _73_534 -> (match (_73_534) with
| (pats, wopt, vars, body) -> begin
(mkQuant' (Forall, pats, wopt, vars, body))
end))

# 384 "FStar.SMTEncoding.Term.fst"
let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _73_538 -> (match (_73_538) with
| (pats, vars, body) -> begin
(mkQuant' (Forall, pats, None, vars, body))
end))

# 385 "FStar.SMTEncoding.Term.fst"
let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _73_542 -> (match (_73_542) with
| (pats, vars, body) -> begin
(mkQuant' (Exists, pats, None, vars, body))
end))

# 388 "FStar.SMTEncoding.Term.fst"
let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun _73_548 -> (match (_73_548) with
| (nm, vars, s, tm, c) -> begin
(let _152_427 = (let _152_426 = (FStar_List.map fv_sort vars)
in (let _152_425 = (abstr vars tm)
in (nm, _152_426, s, _152_425, c)))
in DefineFun (_152_427))
end))

# 389 "FStar.SMTEncoding.Term.fst"
let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _152_430 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _152_430)))

# 390 "FStar.SMTEncoding.Term.fst"
let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun _73_552 id -> (match (_73_552) with
| (tok_name, sort) -> begin
(let _152_443 = (let _152_442 = (let _152_441 = (let _152_440 = (mkInteger' id)
in (let _152_439 = (let _152_438 = (let _152_437 = (constr_id_of_sort sort)
in (let _152_436 = (let _152_435 = (mkApp (tok_name, []))
in (_152_435)::[])
in (_152_437, _152_436)))
in (mkApp _152_438))
in (_152_440, _152_439)))
in (mkEq _152_441))
in (_152_442, Some ("fresh token")))
in Assume (_152_443))
end))

# 393 "FStar.SMTEncoding.Term.fst"
let constructor_to_decl : constructor_t  ->  decls_t = (fun _73_558 -> (match (_73_558) with
| (name, projectors, sort, id) -> begin
(
# 394 "FStar.SMTEncoding.Term.fst"
let id = (FStar_Util.string_of_int id)
in (
# 395 "FStar.SMTEncoding.Term.fst"
let cdecl = (let _152_447 = (let _152_446 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in (name, _152_446, sort, Some ("Constructor")))
in DeclFun (_152_447))
in (
# 396 "FStar.SMTEncoding.Term.fst"
let n_bvars = (FStar_List.length projectors)
in (
# 397 "FStar.SMTEncoding.Term.fst"
let bvar_name = (fun i -> (let _152_450 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _152_450)))
in (
# 398 "FStar.SMTEncoding.Term.fst"
let bvar_index = (fun i -> (n_bvars - (i + 1)))
in (
# 399 "FStar.SMTEncoding.Term.fst"
let bvar = (fun i s -> (let _152_458 = (let _152_457 = (bvar_name i)
in (_152_457, s))
in (mkFreeV _152_458)))
in (
# 400 "FStar.SMTEncoding.Term.fst"
let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _73_573 -> (match (_73_573) with
| (_73_571, s) -> begin
(bvar i s)
end))))
in (
# 401 "FStar.SMTEncoding.Term.fst"
let bvar_names = (FStar_List.map fv_of_term bvars)
in (
# 402 "FStar.SMTEncoding.Term.fst"
let capp = (mkApp (name, bvars))
in (
# 403 "FStar.SMTEncoding.Term.fst"
let cid_app = (let _152_462 = (let _152_461 = (constr_id_of_sort sort)
in (_152_461, (capp)::[]))
in (mkApp _152_462))
in (
# 404 "FStar.SMTEncoding.Term.fst"
let cid = (let _152_468 = (let _152_467 = (let _152_466 = (let _152_465 = (let _152_464 = (let _152_463 = (mkInteger id)
in (_152_463, cid_app))
in (mkEq _152_464))
in (((capp)::[])::[], bvar_names, _152_465))
in (mkForall _152_466))
in (_152_467, Some ("Constructor distinct")))
in Assume (_152_468))
in (
# 405 "FStar.SMTEncoding.Term.fst"
let disc_name = (Prims.strcat "is-" name)
in (
# 406 "FStar.SMTEncoding.Term.fst"
let xfv = ("x", sort)
in (
# 407 "FStar.SMTEncoding.Term.fst"
let xx = (mkFreeV xfv)
in (
# 408 "FStar.SMTEncoding.Term.fst"
let disc_eq = (let _152_473 = (let _152_472 = (let _152_470 = (let _152_469 = (constr_id_of_sort sort)
in (_152_469, (xx)::[]))
in (mkApp _152_470))
in (let _152_471 = (mkInteger id)
in (_152_472, _152_471)))
in (mkEq _152_473))
in (
# 409 "FStar.SMTEncoding.Term.fst"
let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _73_585 -> (match (_73_585) with
| (proj, s) -> begin
(mkApp (proj, (xx)::[]))
end))))
in (
# 410 "FStar.SMTEncoding.Term.fst"
let disc_inv_body = (let _152_476 = (let _152_475 = (mkApp (name, proj_terms))
in (xx, _152_475))
in (mkEq _152_476))
in (
# 411 "FStar.SMTEncoding.Term.fst"
let disc_ax = (mkAnd (disc_eq, disc_inv_body))
in (
# 412 "FStar.SMTEncoding.Term.fst"
let disc = (mkDefineFun (disc_name, (xfv)::[], Bool_sort, disc_ax, Some ("Discriminator definition")))
in (
# 415 "FStar.SMTEncoding.Term.fst"
let projs = (let _152_487 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _73_593 -> (match (_73_593) with
| (name, s) -> begin
(
# 416 "FStar.SMTEncoding.Term.fst"
let cproj_app = (mkApp (name, (capp)::[]))
in (let _152_486 = (let _152_485 = (let _152_484 = (let _152_483 = (let _152_482 = (let _152_481 = (let _152_480 = (let _152_479 = (bvar i s)
in (cproj_app, _152_479))
in (mkEq _152_480))
in (((capp)::[])::[], bvar_names, _152_481))
in (mkForall _152_482))
in (_152_483, Some ("Projection inverse")))
in Assume (_152_484))
in (_152_485)::[])
in (DeclFun ((name, (sort)::[], s, Some ("Projector"))))::_152_486))
end))))
in (FStar_All.pipe_right _152_487 FStar_List.flatten))
in (let _152_494 = (let _152_490 = (let _152_489 = (let _152_488 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_152_488))
in (_152_489)::(cdecl)::(cid)::projs)
in (FStar_List.append _152_490 ((disc)::[])))
in (let _152_493 = (let _152_492 = (let _152_491 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_152_491))
in (_152_492)::[])
in (FStar_List.append _152_494 _152_493)))))))))))))))))))))))
end))

# 425 "FStar.SMTEncoding.Term.fst"
let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (
# 426 "FStar.SMTEncoding.Term.fst"
let _73_614 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _73_602 s -> (match (_73_602) with
| (names, binders, n) -> begin
(
# 427 "FStar.SMTEncoding.Term.fst"
let prefix = (match (s) with
| Term_sort -> begin
"@x"
end
| _73_606 -> begin
"@u"
end)
in (
# 430 "FStar.SMTEncoding.Term.fst"
let nm = (let _152_503 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _152_503))
in (
# 431 "FStar.SMTEncoding.Term.fst"
let names = ((nm, s))::names
in (
# 432 "FStar.SMTEncoding.Term.fst"
let b = (let _152_504 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _152_504))
in (names, (b)::binders, (n + 1))))))
end)) (outer_names, [], start)))
in (match (_73_614) with
| (names, binders, n) -> begin
(names, (FStar_List.rev binders), n)
end)))

# 437 "FStar.SMTEncoding.Term.fst"
let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (
# 438 "FStar.SMTEncoding.Term.fst"
let _73_619 = (name_binders_inner [] 0 sorts)
in (match (_73_619) with
| (names, binders, n) -> begin
((FStar_List.rev names), binders)
end)))

# 441 "FStar.SMTEncoding.Term.fst"
let termToSmt : term  ->  Prims.string = (fun t -> (
# 442 "FStar.SMTEncoding.Term.fst"
let rec aux = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _152_515 = (FStar_List.nth names i)
in (FStar_All.pipe_right _152_515 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _152_517 = (let _152_516 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _152_516 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _152_517))
end
| Labeled (t, _73_641, _73_643) -> begin
(aux n names t)
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(
# 451 "FStar.SMTEncoding.Term.fst"
let _73_656 = (name_binders_inner names n sorts)
in (match (_73_656) with
| (names, binders, n) -> begin
(
# 452 "FStar.SMTEncoding.Term.fst"
let binders = (FStar_All.pipe_right binders (FStar_String.concat " "))
in (
# 453 "FStar.SMTEncoding.Term.fst"
let pats_str = (match (pats) with
| ([]::[]) | ([]) -> begin
""
end
| _73_662 -> begin
(let _152_523 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _152_522 = (let _152_521 = (FStar_List.map (fun p -> (let _152_520 = (aux n names p)
in (FStar_Util.format1 "%s" _152_520))) pats)
in (FStar_String.concat " " _152_521))
in (FStar_Util.format1 "\n:pattern (%s)" _152_522)))))
in (FStar_All.pipe_right _152_523 (FStar_String.concat "\n")))
end)
in (match ((pats, wopt)) with
| (([]::[], None)) | (([], None)) -> begin
(let _152_524 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _152_524))
end
| _73_674 -> begin
(let _152_526 = (aux n names body)
in (let _152_525 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _152_526 _152_525 pats_str)))
end)))
end))
end))
in (aux 0 [] t)))

# 465 "FStar.SMTEncoding.Term.fst"
let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun _73_6 -> (match (_73_6) with
| None -> begin
""
end
| Some (c) -> begin
(
# 468 "FStar.SMTEncoding.Term.fst"
let _73_688 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::[] -> begin
(hd, "")
end
| hd::_73_683 -> begin
(hd, "...")
end)
in (match (_73_688) with
| (hd, suffix) -> begin
(FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd suffix)
end))
end))

# 474 "FStar.SMTEncoding.Term.fst"
let rec declToSmt : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(let _152_535 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _73_7 -> (match (_73_7) with
| [] -> begin
""
end
| h::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _152_535))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(
# 479 "FStar.SMTEncoding.Term.fst"
let l = (FStar_List.map strSort argsorts)
in (let _152_537 = (caption_to_string c)
in (let _152_536 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _152_537 f (FStar_String.concat " " l) _152_536))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(
# 482 "FStar.SMTEncoding.Term.fst"
let _73_715 = (name_binders arg_sorts)
in (match (_73_715) with
| (names, binders) -> begin
(
# 483 "FStar.SMTEncoding.Term.fst"
let body = (let _152_538 = (FStar_List.map mkFreeV names)
in (inst _152_538 body))
in (let _152_541 = (caption_to_string c)
in (let _152_540 = (strSort retsort)
in (let _152_539 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _152_541 f (FStar_String.concat " " binders) _152_540 _152_539)))))
end))
end
| Assume (t, c) -> begin
(let _152_543 = (caption_to_string c)
in (let _152_542 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _152_543 _152_542)))
end
| Eval (t) -> begin
(let _152_544 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _152_544))
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
# 496 "FStar.SMTEncoding.Term.fst"
let basic = (Prims.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort String)\n(declare-fun String_constr_id (String) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n")
in (
# 541 "FStar.SMTEncoding.Term.fst"
let constrs = (("String_const", (("String_const_proj_0", Int_sort))::[], String_sort, 0))::(("Tm_type", [], Term_sort, 0))::(("Tm_arrow", (("Tm_arrow_id", Int_sort))::[], Term_sort, 1))::(("Tm_app", (("Tm_app_fst", Term_sort))::(("Tm_app_snd", Term_sort))::[], Term_sort, 2))::(("Tm_uvar", (("Tm_uvar_fst", Int_sort))::[], Term_sort, 4))::(("Tm_unit", [], Term_sort, 0))::(("BoxInt", (("BoxInt_proj_0", Int_sort))::[], Term_sort, 1))::(("BoxBool", (("BoxBool_proj_0", Bool_sort))::[], Term_sort, 2))::(("BoxString", (("BoxString_proj_0", String_sort))::[], Term_sort, 3))::(("BoxRef", (("BoxRef_proj_0", Ref_sort))::[], Term_sort, 4))::(("Exp_uvar", (("Exp_uvar_fst", Int_sort))::[], Term_sort, 5))::(("LexCons", (("LexCons_0", Term_sort))::(("LexCons_1", Term_sort))::[], Term_sort, 6))::[]
in (
# 554 "FStar.SMTEncoding.Term.fst"
let bcons = (let _152_547 = (let _152_546 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _152_546 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _152_547 (FStar_String.concat "\n")))
in (
# 555 "FStar.SMTEncoding.Term.fst"
let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat (Prims.strcat basic bcons) lex_ordering))))))

# 564 "FStar.SMTEncoding.Term.fst"
let mk_Term_type : term = (mkApp ("Tm_type", []))

# 565 "FStar.SMTEncoding.Term.fst"
let mk_Term_app : term  ->  term  ->  term = (fun t1 t2 -> (mkApp ("Tm_app", (t1)::(t2)::[])))

# 566 "FStar.SMTEncoding.Term.fst"
let mk_Term_uvar : Prims.int  ->  term = (fun i -> (let _152_556 = (let _152_555 = (let _152_554 = (mkInteger' i)
in (_152_554)::[])
in ("Tm_uvar", _152_555))
in (mkApp _152_556)))

# 567 "FStar.SMTEncoding.Term.fst"
let mk_Term_unit : term = (mkApp ("Tm_unit", []))

# 568 "FStar.SMTEncoding.Term.fst"
let boxInt : term  ->  term = (fun t -> (mkApp ("BoxInt", (t)::[])))

# 569 "FStar.SMTEncoding.Term.fst"
let unboxInt : term  ->  term = (fun t -> (mkApp ("BoxInt_proj_0", (t)::[])))

# 570 "FStar.SMTEncoding.Term.fst"
let boxBool : term  ->  term = (fun t -> (mkApp ("BoxBool", (t)::[])))

# 571 "FStar.SMTEncoding.Term.fst"
let unboxBool : term  ->  term = (fun t -> (mkApp ("BoxBool_proj_0", (t)::[])))

# 572 "FStar.SMTEncoding.Term.fst"
let boxString : term  ->  term = (fun t -> (mkApp ("BoxString", (t)::[])))

# 573 "FStar.SMTEncoding.Term.fst"
let unboxString : term  ->  term = (fun t -> (mkApp ("BoxString_proj_0", (t)::[])))

# 574 "FStar.SMTEncoding.Term.fst"
let boxRef : term  ->  term = (fun t -> (mkApp ("BoxRef", (t)::[])))

# 575 "FStar.SMTEncoding.Term.fst"
let unboxRef : term  ->  term = (fun t -> (mkApp ("BoxRef_proj_0", (t)::[])))

# 576 "FStar.SMTEncoding.Term.fst"
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
| _73_751 -> begin
(Prims.raise FStar_Util.Impos)
end))

# 582 "FStar.SMTEncoding.Term.fst"
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
| _73_759 -> begin
(Prims.raise FStar_Util.Impos)
end))

# 589 "FStar.SMTEncoding.Term.fst"
let mk_PreType : term  ->  term = (fun t -> (mkApp ("PreType", (t)::[])))

# 590 "FStar.SMTEncoding.Term.fst"
let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_Equality"), _73_773::t1::t2::[]); hash = _73_767; freevars = _73_765}::[]) -> begin
(mkEq (t1, t2))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_disEquality"), _73_792::t1::t2::[]); hash = _73_786; freevars = _73_784}::[]) -> begin
(let _152_585 = (mkEq (t1, t2))
in (mkNot _152_585))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_LessThanOrEqual"), t1::t2::[]); hash = _73_805; freevars = _73_803}::[]) -> begin
(let _152_588 = (let _152_587 = (unboxInt t1)
in (let _152_586 = (unboxInt t2)
in (_152_587, _152_586)))
in (mkLTE _152_588))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_LessThan"), t1::t2::[]); hash = _73_822; freevars = _73_820}::[]) -> begin
(let _152_591 = (let _152_590 = (unboxInt t1)
in (let _152_589 = (unboxInt t2)
in (_152_590, _152_589)))
in (mkLT _152_591))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_GreaterThanOrEqual"), t1::t2::[]); hash = _73_839; freevars = _73_837}::[]) -> begin
(let _152_594 = (let _152_593 = (unboxInt t1)
in (let _152_592 = (unboxInt t2)
in (_152_593, _152_592)))
in (mkGTE _152_594))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_GreaterThan"), t1::t2::[]); hash = _73_856; freevars = _73_854}::[]) -> begin
(let _152_597 = (let _152_596 = (unboxInt t1)
in (let _152_595 = (unboxInt t2)
in (_152_596, _152_595)))
in (mkGT _152_597))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_AmpAmp"), t1::t2::[]); hash = _73_873; freevars = _73_871}::[]) -> begin
(let _152_600 = (let _152_599 = (unboxBool t1)
in (let _152_598 = (unboxBool t2)
in (_152_599, _152_598)))
in (mkAnd _152_600))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_BarBar"), t1::t2::[]); hash = _73_890; freevars = _73_888}::[]) -> begin
(let _152_603 = (let _152_602 = (unboxBool t1)
in (let _152_601 = (unboxBool t2)
in (_152_602, _152_601)))
in (mkOr _152_603))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_Negation"), t::[]); hash = _73_907; freevars = _73_905}::[]) -> begin
(let _152_604 = (unboxBool t)
in (mkNot _152_604))
end
| App (Var ("Prims.b2t"), t::[]) -> begin
(unboxBool t)
end
| _73_925 -> begin
(mkApp ("Valid", (t)::[]))
end))

# 602 "FStar.SMTEncoding.Term.fst"
let mk_HasType : term  ->  term  ->  term = (fun v t -> (mkApp ("HasType", (v)::(t)::[])))

# 603 "FStar.SMTEncoding.Term.fst"
let mk_HasTypeZ : term  ->  term  ->  term = (fun v t -> (mkApp ("HasTypeZ", (v)::(t)::[])))

# 604 "FStar.SMTEncoding.Term.fst"
let mk_IsTyped : term  ->  term = (fun v -> (mkApp ("IsTyped", (v)::[])))

# 605 "FStar.SMTEncoding.Term.fst"
let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v t -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(mk_HasType v t)
end else begin
(mkApp ("HasTypeFuel", (f)::(v)::(t)::[]))
end)

# 609 "FStar.SMTEncoding.Term.fst"
let mk_HasTypeWithFuel : term Prims.option  ->  term  ->  term  ->  term = (fun f v t -> (match (f) with
| None -> begin
(mk_HasType v t)
end
| Some (f) -> begin
(mk_HasTypeFuel f v t)
end))

# 612 "FStar.SMTEncoding.Term.fst"
let mk_Destruct : term  ->  term = (fun v -> (mkApp ("Destruct", (v)::[])))

# 613 "FStar.SMTEncoding.Term.fst"
let mk_Rank : term  ->  term = (fun x -> (mkApp ("Rank", (x)::[])))

# 614 "FStar.SMTEncoding.Term.fst"
let mk_tester : Prims.string  ->  term  ->  term = (fun n t -> (mkApp ((Prims.strcat "is-" n), (t)::[])))

# 615 "FStar.SMTEncoding.Term.fst"
let mk_ApplyTF : term  ->  term  ->  term = (fun t t' -> (mkApp ("ApplyTF", (t)::(t')::[])))

# 616 "FStar.SMTEncoding.Term.fst"
let mk_ApplyTT : term  ->  term  ->  term = (fun t t' -> (mkApp ("ApplyTT", (t)::(t')::[])))

# 617 "FStar.SMTEncoding.Term.fst"
let mk_String_const : Prims.int  ->  term = (fun i -> (let _152_647 = (let _152_646 = (let _152_645 = (mkInteger' i)
in (_152_645)::[])
in ("String_const", _152_646))
in (mkApp _152_647)))

# 618 "FStar.SMTEncoding.Term.fst"
let mk_Precedes : term  ->  term  ->  term = (fun x1 x2 -> (let _152_652 = (mkApp ("Precedes", (x1)::(x2)::[]))
in (FStar_All.pipe_right _152_652 mk_Valid)))

# 619 "FStar.SMTEncoding.Term.fst"
let mk_LexCons : term  ->  term  ->  term = (fun x1 x2 -> (mkApp ("LexCons", (x1)::(x2)::[])))

# 620 "FStar.SMTEncoding.Term.fst"
let rec n_fuel : Prims.int  ->  term = (fun n -> if (n = 0) then begin
(mkApp ("ZFuel", []))
end else begin
(let _152_661 = (let _152_660 = (let _152_659 = (n_fuel (n - 1))
in (_152_659)::[])
in ("SFuel", _152_660))
in (mkApp _152_661))
end)

# 623 "FStar.SMTEncoding.Term.fst"
let fuel_2 : term = (n_fuel 2)

# 624 "FStar.SMTEncoding.Term.fst"
let fuel_100 : term = (n_fuel 100)

# 626 "FStar.SMTEncoding.Term.fst"
let mk_and_opt : term Prims.option  ->  term Prims.option  ->  term Prims.option = (fun p1 p2 -> (match ((p1, p2)) with
| (Some (p1), Some (p2)) -> begin
(let _152_666 = (mkAnd (p1, p2))
in Some (_152_666))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))

# 632 "FStar.SMTEncoding.Term.fst"
let mk_and_opt_l : term Prims.option Prims.list  ->  term Prims.option = (fun pl -> (FStar_List.fold_left (fun out p -> (mk_and_opt p out)) None pl))

# 635 "FStar.SMTEncoding.Term.fst"
let mk_and_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkTrue
end
| hd::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkAnd (p1, p2))) hd tl)
end))

# 639 "FStar.SMTEncoding.Term.fst"
let mk_or_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkFalse
end
| hd::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkOr (p1, p2))) hd tl)
end))

# 644 "FStar.SMTEncoding.Term.fst"
let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "(Integer %s)" n)
end
| BoundV (n) -> begin
(let _152_683 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "(BoundV %s)" _152_683))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (Prims.fst fv))
end
| App (op, l) -> begin
(let _152_684 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _152_684))
end
| Labeled (t, r1, r2) -> begin
(let _152_685 = (print_smt_term t)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 _152_685))
end
| Quant (qop, l, _73_1007, _73_1009, t) -> begin
(let _152_687 = (print_smt_term_list_list l)
in (let _152_686 = (print_smt_term t)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) _152_687 _152_686)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (let _152_689 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right _152_689 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _152_694 = (let _152_693 = (print_smt_term_list l)
in (Prims.strcat (Prims.strcat s "; [ ") _152_693))
in (Prims.strcat _152_694 " ] "))) "" l))




