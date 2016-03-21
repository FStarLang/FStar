
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
let ___Array____0 = (fun projectee -> (match (projectee) with
| Array (_74_10) -> begin
_74_10
end))

# 34 "FStar.SMTEncoding.Term.fst"
let ___Arrow____0 = (fun projectee -> (match (projectee) with
| Arrow (_74_13) -> begin
_74_13
end))

# 35 "FStar.SMTEncoding.Term.fst"
let ___Sort____0 = (fun projectee -> (match (projectee) with
| Sort (_74_16) -> begin
_74_16
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
(let _158_52 = (strSort s1)
in (let _158_51 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _158_52 _158_51)))
end
| Arrow (s1, s2) -> begin
(let _158_54 = (strSort s1)
in (let _158_53 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _158_54 _158_53)))
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
let ___Var____0 = (fun projectee -> (match (projectee) with
| Var (_74_36) -> begin
_74_36
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

# 81 "FStar.SMTEncoding.Term.fst"
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
| Integer (_74_42) -> begin
_74_42
end))

# 83 "FStar.SMTEncoding.Term.fst"
let ___BoundV____0 = (fun projectee -> (match (projectee) with
| BoundV (_74_45) -> begin
_74_45
end))

# 84 "FStar.SMTEncoding.Term.fst"
let ___FreeV____0 = (fun projectee -> (match (projectee) with
| FreeV (_74_48) -> begin
_74_48
end))

# 85 "FStar.SMTEncoding.Term.fst"
let ___App____0 = (fun projectee -> (match (projectee) with
| App (_74_51) -> begin
_74_51
end))

# 86 "FStar.SMTEncoding.Term.fst"
let ___Quant____0 = (fun projectee -> (match (projectee) with
| Quant (_74_54) -> begin
_74_54
end))

# 91 "FStar.SMTEncoding.Term.fst"
let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_74_57) -> begin
_74_57
end))

# 97 "FStar.SMTEncoding.Term.fst"
type caption =
Prims.string Prims.option

# 98 "FStar.SMTEncoding.Term.fst"
type binders =
(Prims.string * sort) Prims.list

# 99 "FStar.SMTEncoding.Term.fst"
type projector =
(Prims.string * sort)

# 100 "FStar.SMTEncoding.Term.fst"
type constructor_t =
(Prims.string * projector Prims.list * sort * Prims.int * Prims.bool)

# 101 "FStar.SMTEncoding.Term.fst"
type constructors =
constructor_t Prims.list

# 102 "FStar.SMTEncoding.Term.fst"
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
| DeclFun (_74_61) -> begin
_74_61
end))

# 105 "FStar.SMTEncoding.Term.fst"
let ___DefineFun____0 = (fun projectee -> (match (projectee) with
| DefineFun (_74_64) -> begin
_74_64
end))

# 106 "FStar.SMTEncoding.Term.fst"
let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_74_67) -> begin
_74_67
end))

# 107 "FStar.SMTEncoding.Term.fst"
let ___Caption____0 = (fun projectee -> (match (projectee) with
| Caption (_74_70) -> begin
_74_70
end))

# 108 "FStar.SMTEncoding.Term.fst"
let ___Eval____0 = (fun projectee -> (match (projectee) with
| Eval (_74_73) -> begin
_74_73
end))

# 109 "FStar.SMTEncoding.Term.fst"
let ___Echo____0 = (fun projectee -> (match (projectee) with
| Echo (_74_76) -> begin
_74_76
end))

# 113 "FStar.SMTEncoding.Term.fst"
type decls_t =
decl Prims.list

# 115 "FStar.SMTEncoding.Term.fst"
type error_label =
(fv * Prims.string * FStar_Range.range)

# 116 "FStar.SMTEncoding.Term.fst"
type error_labels =
error_label Prims.list

# 194 "FStar.SMTEncoding.Term.fst"
let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> ((Prims.fst x) = (Prims.fst y)))

# 195 "FStar.SMTEncoding.Term.fst"
let fv_sort = (fun x -> (Prims.snd x))

# 196 "FStar.SMTEncoding.Term.fst"
let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match ((x.tm, y.tm)) with
| (FreeV (x), FreeV (y)) -> begin
(fv_eq x y)
end
| _74_88 -> begin
false
end))

# 199 "FStar.SMTEncoding.Term.fst"
let freevar_sort : term  ->  sort = (fun _74_1 -> (match (_74_1) with
| {tm = FreeV (x); hash = _74_93; freevars = _74_91} -> begin
(fv_sort x)
end
| _74_98 -> begin
(FStar_All.failwith "impossible")
end))

# 202 "FStar.SMTEncoding.Term.fst"
let fv_of_term : term  ->  fv = (fun _74_2 -> (match (_74_2) with
| {tm = FreeV (fv); hash = _74_103; freevars = _74_101} -> begin
fv
end
| _74_108 -> begin
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
| App (_74_119, tms) -> begin
(FStar_List.collect freevars tms)
end
| (Quant (_, _, _, _, t)) | (Labeled (t, _, _)) -> begin
(freevars t)
end))

# 214 "FStar.SMTEncoding.Term.fst"
let free_variables : term  ->  fvs = (fun t -> (match ((FStar_ST.read t.freevars)) with
| Some (b) -> begin
b
end
| None -> begin
(
# 217 "FStar.SMTEncoding.Term.fst"
let fvs = (let _158_289 = (freevars t)
in (FStar_Util.remove_dups fv_eq _158_289))
in (
# 218 "FStar.SMTEncoding.Term.fst"
let _74_145 = (FStar_ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))

# 224 "FStar.SMTEncoding.Term.fst"
let qop_to_string : qop  ->  Prims.string = (fun _74_3 -> (match (_74_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))

# 228 "FStar.SMTEncoding.Term.fst"
let op_to_string : op  ->  Prims.string = (fun _74_4 -> (match (_74_4) with
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

# 250 "FStar.SMTEncoding.Term.fst"
let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun _74_5 -> (match (_74_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _158_296 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _158_296))
end))

# 254 "FStar.SMTEncoding.Term.fst"
let hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _158_299 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _158_299))
end
| FreeV (x) -> begin
(let _158_300 = (strSort (Prims.snd x))
in (Prims.strcat (Prims.strcat (Prims.fst x) ":") _158_300))
end
| App (op, tms) -> begin
(let _158_304 = (let _158_303 = (let _158_302 = (FStar_List.map (fun t -> t.hash) tms)
in (FStar_All.pipe_right _158_302 (FStar_String.concat " ")))
in (Prims.strcat (Prims.strcat "(" (op_to_string op)) _158_303))
in (Prims.strcat _158_304 ")"))
end
| Labeled (t, r1, r2) -> begin
(let _158_305 = (FStar_Range.string_of_range r2)
in (Prims.strcat (Prims.strcat t.hash r1) _158_305))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _158_313 = (let _158_306 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _158_306 (FStar_String.concat " ")))
in (let _158_312 = (weightToSmt wopt)
in (let _158_311 = (let _158_310 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _158_309 = (FStar_List.map (fun p -> p.hash) pats)
in (FStar_All.pipe_right _158_309 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _158_310 (FStar_String.concat "; ")))
in (FStar_Util.format5 "(%s (%s)(! %s %s %s))" (qop_to_string qop) _158_313 body.hash _158_312 _158_311))))
end))

# 269 "FStar.SMTEncoding.Term.fst"
let __all_terms : term FStar_Util.smap FStar_ST.ref = (let _158_314 = (FStar_Util.smap_create 10000)
in (FStar_ST.alloc _158_314))

# 270 "FStar.SMTEncoding.Term.fst"
let all_terms : Prims.unit  ->  term FStar_Util.smap = (fun _74_202 -> (match (()) with
| () -> begin
(FStar_ST.read __all_terms)
end))

# 271 "FStar.SMTEncoding.Term.fst"
let mk : term'  ->  term = (fun t -> (
# 272 "FStar.SMTEncoding.Term.fst"
let key = (hash_of_term' t)
in (match ((let _158_319 = (all_terms ())
in (FStar_Util.smap_try_find _158_319 key))) with
| Some (tm) -> begin
tm
end
| None -> begin
(
# 276 "FStar.SMTEncoding.Term.fst"
let tm = (let _158_320 = (FStar_Util.mk_ref None)
in {tm = t; hash = key; freevars = _158_320})
in (
# 277 "FStar.SMTEncoding.Term.fst"
let _74_209 = (let _158_321 = (all_terms ())
in (FStar_Util.smap_add _158_321 key tm))
in tm))
end)))

# 280 "FStar.SMTEncoding.Term.fst"
let mkTrue : term = (mk (App ((True, []))))

# 281 "FStar.SMTEncoding.Term.fst"
let mkFalse : term = (mk (App ((False, []))))

# 282 "FStar.SMTEncoding.Term.fst"
let mkInteger : Prims.string  ->  term = (fun i -> (mk (Integer (i))))

# 283 "FStar.SMTEncoding.Term.fst"
let mkInteger32 : Prims.int32  ->  term = (fun i -> (mkInteger (FStar_Util.string_of_int32 i)))

# 284 "FStar.SMTEncoding.Term.fst"
let mkInteger' : Prims.int  ->  term = (fun i -> (let _158_328 = (FStar_Util.string_of_int i)
in (mkInteger _158_328)))

# 285 "FStar.SMTEncoding.Term.fst"
let mkBoundV : Prims.int  ->  term = (fun i -> (mk (BoundV (i))))

# 286 "FStar.SMTEncoding.Term.fst"
let mkFreeV : (Prims.string * sort)  ->  term = (fun x -> (mk (FreeV (x))))

# 287 "FStar.SMTEncoding.Term.fst"
let mkApp' : (op * term Prims.list)  ->  term = (fun f -> (mk (App (f))))

# 288 "FStar.SMTEncoding.Term.fst"
let mkApp : (Prims.string * term Prims.list)  ->  term = (fun _74_219 -> (match (_74_219) with
| (s, args) -> begin
(mk (App ((Var (s), args))))
end))

# 289 "FStar.SMTEncoding.Term.fst"
let mkNot : term  ->  term = (fun t -> (match (t.tm) with
| App (True, _74_223) -> begin
mkFalse
end
| App (False, _74_228) -> begin
mkTrue
end
| _74_232 -> begin
(mkApp' (Not, (t)::[]))
end))

# 293 "FStar.SMTEncoding.Term.fst"
let mkAnd : (term * term)  ->  term = (fun _74_235 -> (match (_74_235) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (App (True, _74_238), _74_242) -> begin
t2
end
| (_74_245, App (True, _74_248)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
mkFalse
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' (And, (FStar_List.append ts1 ts2)))
end
| (_74_278, App (And, ts2)) -> begin
(mkApp' (And, (t1)::ts2))
end
| (App (And, ts1), _74_289) -> begin
(mkApp' (And, (FStar_List.append ts1 ((t2)::[]))))
end
| _74_292 -> begin
(mkApp' (And, (t1)::(t2)::[]))
end)
end))

# 302 "FStar.SMTEncoding.Term.fst"
let mkOr : (term * term)  ->  term = (fun _74_295 -> (match (_74_295) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
mkTrue
end
| (App (False, _74_314), _74_318) -> begin
t2
end
| (_74_321, App (False, _74_324)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' (Or, (FStar_List.append ts1 ts2)))
end
| (_74_338, App (Or, ts2)) -> begin
(mkApp' (Or, (t1)::ts2))
end
| (App (Or, ts1), _74_349) -> begin
(mkApp' (Or, (FStar_List.append ts1 ((t2)::[]))))
end
| _74_352 -> begin
(mkApp' (Or, (t1)::(t2)::[]))
end)
end))

# 311 "FStar.SMTEncoding.Term.fst"
let mkImp : (term * term)  ->  term = (fun _74_355 -> (match (_74_355) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (_74_357, App (True, _74_360)) -> begin
mkTrue
end
| (App (True, _74_366), _74_370) -> begin
t2
end
| (_74_373, App (Imp, t1'::t2'::[])) -> begin
(let _158_347 = (let _158_346 = (let _158_345 = (mkAnd (t1, t1'))
in (_158_345)::(t2')::[])
in (Imp, _158_346))
in (mkApp' _158_347))
end
| _74_382 -> begin
(mkApp' (Imp, (t1)::(t2)::[]))
end)
end))

# 317 "FStar.SMTEncoding.Term.fst"
let mk_bin_op : op  ->  (term * term)  ->  term = (fun op _74_386 -> (match (_74_386) with
| (t1, t2) -> begin
(mkApp' (op, (t1)::(t2)::[]))
end))

# 318 "FStar.SMTEncoding.Term.fst"
let mkMinus : term  ->  term = (fun t -> (mkApp' (Minus, (t)::[])))

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
let mkITE : (term * term * term)  ->  term = (fun _74_391 -> (match (_74_391) with
| (t1, t2, t3) -> begin
(match ((t2.tm, t3.tm)) with
| (App (True, _74_394), App (True, _74_399)) -> begin
mkTrue
end
| (App (True, _74_405), _74_409) -> begin
(let _158_368 = (let _158_367 = (mkNot t1)
in (_158_367, t3))
in (mkImp _158_368))
end
| (_74_412, App (True, _74_415)) -> begin
(mkImp (t1, t2))
end
| (_74_420, _74_422) -> begin
(mkApp' (ITE, (t1)::(t2)::(t3)::[]))
end)
end))

# 336 "FStar.SMTEncoding.Term.fst"
let mkCases : term Prims.list  ->  term = (fun t -> (match (t) with
| [] -> begin
(FStar_All.failwith "Impos")
end
| hd::tl -> begin
(FStar_List.fold_left (fun out t -> (mkAnd (out, t))) hd tl)
end))

# 340 "FStar.SMTEncoding.Term.fst"
let mkQuant : (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _74_436 -> (match (_74_436) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = 0) then begin
body
end else begin
(match (body.tm) with
| App (True, _74_439) -> begin
body
end
| _74_443 -> begin
(mk (Quant ((qop, pats, wopt, vars, body))))
end)
end
end))

# 349 "FStar.SMTEncoding.Term.fst"
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
| _74_458 -> begin
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
(let _158_386 = (let _158_385 = (FStar_List.map (aux ix) tms)
in (op, _158_385))
in (mkApp' _158_386))
end
| Labeled (t, r1, r2) -> begin
(let _158_389 = (let _158_388 = (let _158_387 = (aux ix t)
in (_158_387, r1, r2))
in Labeled (_158_388))
in (mk _158_389))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(
# 369 "FStar.SMTEncoding.Term.fst"
let n = (FStar_List.length vars)
in (let _158_392 = (let _158_391 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _158_390 = (aux (ix + n) body)
in (qop, _158_391, wopt, vars, _158_390)))
in (mkQuant _158_392)))
end)
end))
in (aux 0 t)))))

# 374 "FStar.SMTEncoding.Term.fst"
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
(let _158_402 = (let _158_401 = (FStar_List.map (aux shift) tms)
in (op, _158_401))
in (mkApp' _158_402))
end
| Labeled (t, r1, r2) -> begin
(let _158_405 = (let _158_404 = (let _158_403 = (aux shift t)
in (_158_403, r1, r2))
in Labeled (_158_404))
in (mk _158_405))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(
# 386 "FStar.SMTEncoding.Term.fst"
let m = (FStar_List.length vars)
in (
# 387 "FStar.SMTEncoding.Term.fst"
let shift = (shift + m)
in (let _158_408 = (let _158_407 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _158_406 = (aux shift body)
in (qop, _158_407, wopt, vars, _158_406)))
in (mkQuant _158_408))))
end))
in (aux 0 t))))

# 391 "FStar.SMTEncoding.Term.fst"
let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list * term)  ->  term = (fun _74_524 -> (match (_74_524) with
| (qop, pats, wopt, vars, body) -> begin
(let _158_414 = (let _158_413 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _158_412 = (FStar_List.map fv_sort vars)
in (let _158_411 = (abstr vars body)
in (qop, _158_413, wopt, _158_412, _158_411))))
in (mkQuant _158_414))
end))

# 392 "FStar.SMTEncoding.Term.fst"
let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _74_529 -> (match (_74_529) with
| (pats, wopt, sorts, body) -> begin
(mkQuant (Forall, pats, wopt, sorts, body))
end))

# 393 "FStar.SMTEncoding.Term.fst"
let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  term = (fun _74_534 -> (match (_74_534) with
| (pats, wopt, vars, body) -> begin
(mkQuant' (Forall, pats, wopt, vars, body))
end))

# 396 "FStar.SMTEncoding.Term.fst"
let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _74_538 -> (match (_74_538) with
| (pats, vars, body) -> begin
(mkQuant' (Forall, pats, None, vars, body))
end))

# 397 "FStar.SMTEncoding.Term.fst"
let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _74_542 -> (match (_74_542) with
| (pats, vars, body) -> begin
(mkQuant' (Exists, pats, None, vars, body))
end))

# 400 "FStar.SMTEncoding.Term.fst"
let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun _74_548 -> (match (_74_548) with
| (nm, vars, s, tm, c) -> begin
(let _158_427 = (let _158_426 = (FStar_List.map fv_sort vars)
in (let _158_425 = (abstr vars tm)
in (nm, _158_426, s, _158_425, c)))
in DefineFun (_158_427))
end))

# 401 "FStar.SMTEncoding.Term.fst"
let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _158_430 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _158_430)))

# 402 "FStar.SMTEncoding.Term.fst"
let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun _74_552 id -> (match (_74_552) with
| (tok_name, sort) -> begin
(let _158_443 = (let _158_442 = (let _158_441 = (let _158_440 = (mkInteger' id)
in (let _158_439 = (let _158_438 = (let _158_437 = (constr_id_of_sort sort)
in (let _158_436 = (let _158_435 = (mkApp (tok_name, []))
in (_158_435)::[])
in (_158_437, _158_436)))
in (mkApp _158_438))
in (_158_440, _158_439)))
in (mkEq _158_441))
in (_158_442, Some ("fresh token")))
in Assume (_158_443))
end))

# 405 "FStar.SMTEncoding.Term.fst"
let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun _74_558 -> (match (_74_558) with
| (name, arg_sorts, sort, id) -> begin
(
# 406 "FStar.SMTEncoding.Term.fst"
let id = (FStar_Util.string_of_int id)
in (
# 407 "FStar.SMTEncoding.Term.fst"
let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (let _158_450 = (let _158_449 = (let _158_448 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _158_448))
in (_158_449, s))
in (mkFreeV _158_450)))))
in (
# 408 "FStar.SMTEncoding.Term.fst"
let bvar_names = (FStar_List.map fv_of_term bvars)
in (
# 409 "FStar.SMTEncoding.Term.fst"
let capp = (mkApp (name, bvars))
in (
# 410 "FStar.SMTEncoding.Term.fst"
let cid_app = (let _158_452 = (let _158_451 = (constr_id_of_sort sort)
in (_158_451, (capp)::[]))
in (mkApp _158_452))
in (let _158_458 = (let _158_457 = (let _158_456 = (let _158_455 = (let _158_454 = (let _158_453 = (mkInteger id)
in (_158_453, cid_app))
in (mkEq _158_454))
in (((capp)::[])::[], bvar_names, _158_455))
in (mkForall _158_456))
in (_158_457, Some ("Constructor distinct")))
in Assume (_158_458)))))))
end))

# 413 "FStar.SMTEncoding.Term.fst"
let injective_constructor : (Prims.string * (Prims.string * sort) Prims.list * sort)  ->  decls_t = (fun _74_569 -> (match (_74_569) with
| (name, projectors, sort) -> begin
(
# 414 "FStar.SMTEncoding.Term.fst"
let n_bvars = (FStar_List.length projectors)
in (
# 415 "FStar.SMTEncoding.Term.fst"
let bvar_name = (fun i -> (let _158_463 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _158_463)))
in (
# 416 "FStar.SMTEncoding.Term.fst"
let bvar_index = (fun i -> (n_bvars - (i + 1)))
in (
# 417 "FStar.SMTEncoding.Term.fst"
let bvar = (fun i s -> (let _158_471 = (let _158_470 = (bvar_name i)
in (_158_470, s))
in (mkFreeV _158_471)))
in (
# 418 "FStar.SMTEncoding.Term.fst"
let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _74_582 -> (match (_74_582) with
| (_74_580, s) -> begin
(bvar i s)
end))))
in (
# 419 "FStar.SMTEncoding.Term.fst"
let bvar_names = (FStar_List.map fv_of_term bvars)
in (
# 420 "FStar.SMTEncoding.Term.fst"
let capp = (mkApp (name, bvars))
in (let _158_484 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _74_589 -> (match (_74_589) with
| (name, s) -> begin
(
# 423 "FStar.SMTEncoding.Term.fst"
let cproj_app = (mkApp (name, (capp)::[]))
in (
# 424 "FStar.SMTEncoding.Term.fst"
let proj_name = DeclFun ((name, (sort)::[], s, Some ("Projector")))
in (let _158_483 = (let _158_482 = (let _158_481 = (let _158_480 = (let _158_479 = (let _158_478 = (let _158_477 = (let _158_476 = (bvar i s)
in (cproj_app, _158_476))
in (mkEq _158_477))
in (((capp)::[])::[], bvar_names, _158_478))
in (mkForall _158_479))
in (_158_480, Some ("Projection inverse")))
in Assume (_158_481))
in (_158_482)::[])
in (proj_name)::_158_483)))
end))))
in (FStar_All.pipe_right _158_484 FStar_List.flatten)))))))))
end))

# 429 "FStar.SMTEncoding.Term.fst"
let constructor_to_decl : constructor_t  ->  decls_t = (fun _74_597 -> (match (_74_597) with
| (name, projectors, sort, id, injective) -> begin
(
# 430 "FStar.SMTEncoding.Term.fst"
let injective = (injective || true)
in (
# 431 "FStar.SMTEncoding.Term.fst"
let cdecl = (let _158_488 = (let _158_487 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in (name, _158_487, sort, Some ("Constructor")))
in DeclFun (_158_488))
in (
# 432 "FStar.SMTEncoding.Term.fst"
let cid = (let _158_490 = (let _158_489 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in (name, _158_489, sort, id))
in (fresh_constructor _158_490))
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
let disc_eq = (let _158_496 = (let _158_495 = (let _158_492 = (let _158_491 = (constr_id_of_sort sort)
in (_158_491, (xx)::[]))
in (mkApp _158_492))
in (let _158_494 = (let _158_493 = (FStar_Util.string_of_int id)
in (mkInteger _158_493))
in (_158_495, _158_494)))
in (mkEq _158_496))
in (
# 438 "FStar.SMTEncoding.Term.fst"
let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _74_607 -> (match (_74_607) with
| (proj, s) -> begin
(mkApp (proj, (xx)::[]))
end))))
in (
# 439 "FStar.SMTEncoding.Term.fst"
let disc_inv_body = (let _158_499 = (let _158_498 = (mkApp (name, proj_terms))
in (xx, _158_498))
in (mkEq _158_499))
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
in (let _158_506 = (let _158_502 = (let _158_501 = (let _158_500 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_158_500))
in (_158_501)::(cdecl)::(cid)::projs)
in (FStar_List.append _158_502 ((disc)::[])))
in (let _158_505 = (let _158_504 = (let _158_503 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_158_503))
in (_158_504)::[])
in (FStar_List.append _158_506 _158_505))))))))
end))

# 454 "FStar.SMTEncoding.Term.fst"
let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (
# 455 "FStar.SMTEncoding.Term.fst"
let _74_631 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _74_619 s -> (match (_74_619) with
| (names, binders, n) -> begin
(
# 456 "FStar.SMTEncoding.Term.fst"
let prefix = (match (s) with
| Term_sort -> begin
"@x"
end
| _74_623 -> begin
"@u"
end)
in (
# 459 "FStar.SMTEncoding.Term.fst"
let nm = (let _158_515 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _158_515))
in (
# 460 "FStar.SMTEncoding.Term.fst"
let names = ((nm, s))::names
in (
# 461 "FStar.SMTEncoding.Term.fst"
let b = (let _158_516 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _158_516))
in (names, (b)::binders, (n + 1))))))
end)) (outer_names, [], start)))
in (match (_74_631) with
| (names, binders, n) -> begin
(names, (FStar_List.rev binders), n)
end)))

# 466 "FStar.SMTEncoding.Term.fst"
let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (
# 467 "FStar.SMTEncoding.Term.fst"
let _74_636 = (name_binders_inner [] 0 sorts)
in (match (_74_636) with
| (names, binders, n) -> begin
((FStar_List.rev names), binders)
end)))

# 470 "FStar.SMTEncoding.Term.fst"
let termToSmt : term  ->  Prims.string = (fun t -> (
# 471 "FStar.SMTEncoding.Term.fst"
let rec aux = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _158_527 = (FStar_List.nth names i)
in (FStar_All.pipe_right _158_527 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _158_529 = (let _158_528 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _158_528 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _158_529))
end
| Labeled (t, _74_658, _74_660) -> begin
(aux n names t)
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(
# 480 "FStar.SMTEncoding.Term.fst"
let _74_673 = (name_binders_inner names n sorts)
in (match (_74_673) with
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
| _74_679 -> begin
(let _158_535 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _158_534 = (let _158_533 = (FStar_List.map (fun p -> (let _158_532 = (aux n names p)
in (FStar_Util.format1 "%s" _158_532))) pats)
in (FStar_String.concat " " _158_533))
in (FStar_Util.format1 "\n:pattern (%s)" _158_534)))))
in (FStar_All.pipe_right _158_535 (FStar_String.concat "\n")))
end)
in (match ((pats, wopt)) with
| (([]::[], None)) | (([], None)) -> begin
(let _158_536 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _158_536))
end
| _74_691 -> begin
(let _158_538 = (aux n names body)
in (let _158_537 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _158_538 _158_537 pats_str)))
end)))
end))
end))
in (aux 0 [] t)))

# 494 "FStar.SMTEncoding.Term.fst"
let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun _74_6 -> (match (_74_6) with
| None -> begin
""
end
| Some (c) -> begin
(
# 497 "FStar.SMTEncoding.Term.fst"
let _74_705 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::[] -> begin
(hd, "")
end
| hd::_74_700 -> begin
(hd, "...")
end)
in (match (_74_705) with
| (hd, suffix) -> begin
(FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd suffix)
end))
end))

# 503 "FStar.SMTEncoding.Term.fst"
let rec declToSmt : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(let _158_547 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _74_7 -> (match (_74_7) with
| [] -> begin
""
end
| h::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _158_547))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(
# 508 "FStar.SMTEncoding.Term.fst"
let l = (FStar_List.map strSort argsorts)
in (let _158_549 = (caption_to_string c)
in (let _158_548 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _158_549 f (FStar_String.concat " " l) _158_548))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(
# 511 "FStar.SMTEncoding.Term.fst"
let _74_732 = (name_binders arg_sorts)
in (match (_74_732) with
| (names, binders) -> begin
(
# 512 "FStar.SMTEncoding.Term.fst"
let body = (let _158_550 = (FStar_List.map mkFreeV names)
in (inst _158_550 body))
in (let _158_553 = (caption_to_string c)
in (let _158_552 = (strSort retsort)
in (let _158_551 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _158_553 f (FStar_String.concat " " binders) _158_552 _158_551)))))
end))
end
| Assume (t, c) -> begin
(let _158_555 = (caption_to_string c)
in (let _158_554 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _158_555 _158_554)))
end
| Eval (t) -> begin
(let _158_556 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _158_556))
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
let bcons = (let _158_559 = (let _158_558 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _158_558 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _158_559 (FStar_String.concat "\n")))
in (
# 582 "FStar.SMTEncoding.Term.fst"
let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat (Prims.strcat basic bcons) lex_ordering))))))

# 591 "FStar.SMTEncoding.Term.fst"
let mk_Range_const : term = (mkApp ("Range_const", []))

# 592 "FStar.SMTEncoding.Term.fst"
let mk_Term_type : term = (mkApp ("Tm_type", []))

# 593 "FStar.SMTEncoding.Term.fst"
let mk_Term_app : term  ->  term  ->  term = (fun t1 t2 -> (mkApp ("Tm_app", (t1)::(t2)::[])))

# 594 "FStar.SMTEncoding.Term.fst"
let mk_Term_uvar : Prims.int  ->  term = (fun i -> (let _158_568 = (let _158_567 = (let _158_566 = (mkInteger' i)
in (_158_566)::[])
in ("Tm_uvar", _158_567))
in (mkApp _158_568)))

# 595 "FStar.SMTEncoding.Term.fst"
let mk_Term_unit : term = (mkApp ("Tm_unit", []))

# 596 "FStar.SMTEncoding.Term.fst"
let boxInt : term  ->  term = (fun t -> (mkApp ("BoxInt", (t)::[])))

# 597 "FStar.SMTEncoding.Term.fst"
let unboxInt : term  ->  term = (fun t -> (mkApp ("BoxInt_proj_0", (t)::[])))

# 598 "FStar.SMTEncoding.Term.fst"
let boxBool : term  ->  term = (fun t -> (mkApp ("BoxBool", (t)::[])))

# 599 "FStar.SMTEncoding.Term.fst"
let unboxBool : term  ->  term = (fun t -> (mkApp ("BoxBool_proj_0", (t)::[])))

# 600 "FStar.SMTEncoding.Term.fst"
let boxString : term  ->  term = (fun t -> (mkApp ("BoxString", (t)::[])))

# 601 "FStar.SMTEncoding.Term.fst"
let unboxString : term  ->  term = (fun t -> (mkApp ("BoxString_proj_0", (t)::[])))

# 602 "FStar.SMTEncoding.Term.fst"
let boxRef : term  ->  term = (fun t -> (mkApp ("BoxRef", (t)::[])))

# 603 "FStar.SMTEncoding.Term.fst"
let unboxRef : term  ->  term = (fun t -> (mkApp ("BoxRef_proj_0", (t)::[])))

# 604 "FStar.SMTEncoding.Term.fst"
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
| _74_768 -> begin
(Prims.raise FStar_Util.Impos)
end))

# 610 "FStar.SMTEncoding.Term.fst"
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
| _74_776 -> begin
(Prims.raise FStar_Util.Impos)
end))

# 617 "FStar.SMTEncoding.Term.fst"
let mk_PreType : term  ->  term = (fun t -> (mkApp ("PreType", (t)::[])))

# 618 "FStar.SMTEncoding.Term.fst"
let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_Equality"), _74_790::t1::t2::[]); hash = _74_784; freevars = _74_782}::[]) -> begin
(mkEq (t1, t2))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_disEquality"), _74_809::t1::t2::[]); hash = _74_803; freevars = _74_801}::[]) -> begin
(let _158_597 = (mkEq (t1, t2))
in (mkNot _158_597))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_LessThanOrEqual"), t1::t2::[]); hash = _74_822; freevars = _74_820}::[]) -> begin
(let _158_600 = (let _158_599 = (unboxInt t1)
in (let _158_598 = (unboxInt t2)
in (_158_599, _158_598)))
in (mkLTE _158_600))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_LessThan"), t1::t2::[]); hash = _74_839; freevars = _74_837}::[]) -> begin
(let _158_603 = (let _158_602 = (unboxInt t1)
in (let _158_601 = (unboxInt t2)
in (_158_602, _158_601)))
in (mkLT _158_603))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_GreaterThanOrEqual"), t1::t2::[]); hash = _74_856; freevars = _74_854}::[]) -> begin
(let _158_606 = (let _158_605 = (unboxInt t1)
in (let _158_604 = (unboxInt t2)
in (_158_605, _158_604)))
in (mkGTE _158_606))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_GreaterThan"), t1::t2::[]); hash = _74_873; freevars = _74_871}::[]) -> begin
(let _158_609 = (let _158_608 = (unboxInt t1)
in (let _158_607 = (unboxInt t2)
in (_158_608, _158_607)))
in (mkGT _158_609))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_AmpAmp"), t1::t2::[]); hash = _74_890; freevars = _74_888}::[]) -> begin
(let _158_612 = (let _158_611 = (unboxBool t1)
in (let _158_610 = (unboxBool t2)
in (_158_611, _158_610)))
in (mkAnd _158_612))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_BarBar"), t1::t2::[]); hash = _74_907; freevars = _74_905}::[]) -> begin
(let _158_615 = (let _158_614 = (unboxBool t1)
in (let _158_613 = (unboxBool t2)
in (_158_614, _158_613)))
in (mkOr _158_615))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_Negation"), t::[]); hash = _74_924; freevars = _74_922}::[]) -> begin
(let _158_616 = (unboxBool t)
in (mkNot _158_616))
end
| App (Var ("Prims.b2t"), t::[]) -> begin
(unboxBool t)
end
| _74_942 -> begin
(mkApp ("Valid", (t)::[]))
end))

# 630 "FStar.SMTEncoding.Term.fst"
let mk_HasType : term  ->  term  ->  term = (fun v t -> (mkApp ("HasType", (v)::(t)::[])))

# 631 "FStar.SMTEncoding.Term.fst"
let mk_HasTypeZ : term  ->  term  ->  term = (fun v t -> (mkApp ("HasTypeZ", (v)::(t)::[])))

# 632 "FStar.SMTEncoding.Term.fst"
let mk_IsTyped : term  ->  term = (fun v -> (mkApp ("IsTyped", (v)::[])))

# 633 "FStar.SMTEncoding.Term.fst"
let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v t -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(mk_HasType v t)
end else begin
(mkApp ("HasTypeFuel", (f)::(v)::(t)::[]))
end)

# 637 "FStar.SMTEncoding.Term.fst"
let mk_HasTypeWithFuel : term Prims.option  ->  term  ->  term  ->  term = (fun f v t -> (match (f) with
| None -> begin
(mk_HasType v t)
end
| Some (f) -> begin
(mk_HasTypeFuel f v t)
end))

# 640 "FStar.SMTEncoding.Term.fst"
let mk_Destruct : term  ->  term = (fun v -> (mkApp ("Destruct", (v)::[])))

# 641 "FStar.SMTEncoding.Term.fst"
let mk_Rank : term  ->  term = (fun x -> (mkApp ("Rank", (x)::[])))

# 642 "FStar.SMTEncoding.Term.fst"
let mk_tester : Prims.string  ->  term  ->  term = (fun n t -> (mkApp ((Prims.strcat "is-" n), (t)::[])))

# 643 "FStar.SMTEncoding.Term.fst"
let mk_ApplyTF : term  ->  term  ->  term = (fun t t' -> (mkApp ("ApplyTF", (t)::(t')::[])))

# 644 "FStar.SMTEncoding.Term.fst"
let mk_ApplyTT : term  ->  term  ->  term = (fun t t' -> (mkApp ("ApplyTT", (t)::(t')::[])))

# 645 "FStar.SMTEncoding.Term.fst"
let mk_String_const : Prims.int  ->  term = (fun i -> (let _158_659 = (let _158_658 = (let _158_657 = (mkInteger' i)
in (_158_657)::[])
in ("String_const", _158_658))
in (mkApp _158_659)))

# 646 "FStar.SMTEncoding.Term.fst"
let mk_Precedes : term  ->  term  ->  term = (fun x1 x2 -> (let _158_664 = (mkApp ("Precedes", (x1)::(x2)::[]))
in (FStar_All.pipe_right _158_664 mk_Valid)))

# 647 "FStar.SMTEncoding.Term.fst"
let mk_LexCons : term  ->  term  ->  term = (fun x1 x2 -> (mkApp ("LexCons", (x1)::(x2)::[])))

# 648 "FStar.SMTEncoding.Term.fst"
let rec n_fuel : Prims.int  ->  term = (fun n -> if (n = 0) then begin
(mkApp ("ZFuel", []))
end else begin
(let _158_673 = (let _158_672 = (let _158_671 = (n_fuel (n - 1))
in (_158_671)::[])
in ("SFuel", _158_672))
in (mkApp _158_673))
end)

# 651 "FStar.SMTEncoding.Term.fst"
let fuel_2 : term = (n_fuel 2)

# 652 "FStar.SMTEncoding.Term.fst"
let fuel_100 : term = (n_fuel 100)

# 654 "FStar.SMTEncoding.Term.fst"
let mk_and_opt : term Prims.option  ->  term Prims.option  ->  term Prims.option = (fun p1 p2 -> (match ((p1, p2)) with
| (Some (p1), Some (p2)) -> begin
(let _158_678 = (mkAnd (p1, p2))
in Some (_158_678))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))

# 660 "FStar.SMTEncoding.Term.fst"
let mk_and_opt_l : term Prims.option Prims.list  ->  term Prims.option = (fun pl -> (FStar_List.fold_left (fun out p -> (mk_and_opt p out)) None pl))

# 663 "FStar.SMTEncoding.Term.fst"
let mk_and_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkTrue
end
| hd::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkAnd (p1, p2))) hd tl)
end))

# 667 "FStar.SMTEncoding.Term.fst"
let mk_or_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkFalse
end
| hd::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkOr (p1, p2))) hd tl)
end))

# 672 "FStar.SMTEncoding.Term.fst"
let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "(Integer %s)" n)
end
| BoundV (n) -> begin
(let _158_695 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "(BoundV %s)" _158_695))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (Prims.fst fv))
end
| App (op, l) -> begin
(let _158_696 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _158_696))
end
| Labeled (t, r1, r2) -> begin
(let _158_697 = (print_smt_term t)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 _158_697))
end
| Quant (qop, l, _74_1024, _74_1026, t) -> begin
(let _158_699 = (print_smt_term_list_list l)
in (let _158_698 = (print_smt_term t)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) _158_699 _158_698)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (let _158_701 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right _158_701 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _158_706 = (let _158_705 = (print_smt_term_list l)
in (Prims.strcat (Prims.strcat s "; [ ") _158_705))
in (Prims.strcat _158_706 " ] "))) "" l))




