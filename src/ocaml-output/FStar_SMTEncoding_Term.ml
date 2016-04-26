
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
| Array (_79_10) -> begin
_79_10
end))

# 33 "FStar.SMTEncoding.Term.fst"
let ___Arrow____0 = (fun projectee -> (match (projectee) with
| Arrow (_79_13) -> begin
_79_13
end))

# 34 "FStar.SMTEncoding.Term.fst"
let ___Sort____0 = (fun projectee -> (match (projectee) with
| Sort (_79_16) -> begin
_79_16
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
(let _168_52 = (strSort s1)
in (let _168_51 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _168_52 _168_51)))
end
| Arrow (s1, s2) -> begin
(let _168_54 = (strSort s1)
in (let _168_53 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _168_54 _168_53)))
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
| Var (_79_36) -> begin
_79_36
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
| Integer (_79_42) -> begin
_79_42
end))

# 82 "FStar.SMTEncoding.Term.fst"
let ___BoundV____0 = (fun projectee -> (match (projectee) with
| BoundV (_79_45) -> begin
_79_45
end))

# 83 "FStar.SMTEncoding.Term.fst"
let ___FreeV____0 = (fun projectee -> (match (projectee) with
| FreeV (_79_48) -> begin
_79_48
end))

# 84 "FStar.SMTEncoding.Term.fst"
let ___App____0 = (fun projectee -> (match (projectee) with
| App (_79_51) -> begin
_79_51
end))

# 85 "FStar.SMTEncoding.Term.fst"
let ___Quant____0 = (fun projectee -> (match (projectee) with
| Quant (_79_54) -> begin
_79_54
end))

# 90 "FStar.SMTEncoding.Term.fst"
let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_79_57) -> begin
_79_57
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
| Assume of (term * caption)
| Caption of Prims.string
| Eval of term
| Echo of Prims.string
| Push
| Pop
| CheckSat

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

# 103 "FStar.SMTEncoding.Term.fst"
let ___DeclFun____0 = (fun projectee -> (match (projectee) with
| DeclFun (_79_61) -> begin
_79_61
end))

# 104 "FStar.SMTEncoding.Term.fst"
let ___DefineFun____0 = (fun projectee -> (match (projectee) with
| DefineFun (_79_64) -> begin
_79_64
end))

# 105 "FStar.SMTEncoding.Term.fst"
let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_79_67) -> begin
_79_67
end))

# 106 "FStar.SMTEncoding.Term.fst"
let ___Caption____0 = (fun projectee -> (match (projectee) with
| Caption (_79_70) -> begin
_79_70
end))

# 107 "FStar.SMTEncoding.Term.fst"
let ___Eval____0 = (fun projectee -> (match (projectee) with
| Eval (_79_73) -> begin
_79_73
end))

# 108 "FStar.SMTEncoding.Term.fst"
let ___Echo____0 = (fun projectee -> (match (projectee) with
| Echo (_79_76) -> begin
_79_76
end))

# 111 "FStar.SMTEncoding.Term.fst"
type decls_t =
decl Prims.list

# 112 "FStar.SMTEncoding.Term.fst"
type error_label =
(fv * Prims.string * FStar_Range.range)

# 114 "FStar.SMTEncoding.Term.fst"
type error_labels =
error_label Prims.list

# 190 "FStar.SMTEncoding.Term.fst"
let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> ((Prims.fst x) = (Prims.fst y)))

# 192 "FStar.SMTEncoding.Term.fst"
let fv_sort = (fun x -> (Prims.snd x))

# 193 "FStar.SMTEncoding.Term.fst"
let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match ((x.tm, y.tm)) with
| (FreeV (x), FreeV (y)) -> begin
(fv_eq x y)
end
| _79_88 -> begin
false
end))

# 196 "FStar.SMTEncoding.Term.fst"
let freevar_sort : term  ->  sort = (fun _79_1 -> (match (_79_1) with
| {tm = FreeV (x); hash = _79_93; freevars = _79_91} -> begin
(fv_sort x)
end
| _79_98 -> begin
(FStar_All.failwith "impossible")
end))

# 199 "FStar.SMTEncoding.Term.fst"
let fv_of_term : term  ->  fv = (fun _79_2 -> (match (_79_2) with
| {tm = FreeV (fv); hash = _79_103; freevars = _79_101} -> begin
fv
end
| _79_108 -> begin
(FStar_All.failwith "impossible")
end))

# 202 "FStar.SMTEncoding.Term.fst"
let rec freevars : term  ->  fv Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (_79_119, tms) -> begin
(FStar_List.collect freevars tms)
end
| (Quant (_, _, _, _, t)) | (Labeled (t, _, _)) -> begin
(freevars t)
end))

# 209 "FStar.SMTEncoding.Term.fst"
let free_variables : term  ->  fvs = (fun t -> (match ((FStar_ST.read t.freevars)) with
| Some (b) -> begin
b
end
| None -> begin
(
# 215 "FStar.SMTEncoding.Term.fst"
let fvs = (let _168_289 = (freevars t)
in (FStar_Util.remove_dups fv_eq _168_289))
in (
# 216 "FStar.SMTEncoding.Term.fst"
let _79_145 = (FStar_ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))

# 217 "FStar.SMTEncoding.Term.fst"
let qop_to_string : qop  ->  Prims.string = (fun _79_3 -> (match (_79_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))

# 224 "FStar.SMTEncoding.Term.fst"
let op_to_string : op  ->  Prims.string = (fun _79_4 -> (match (_79_4) with
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

# 246 "FStar.SMTEncoding.Term.fst"
let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun _79_5 -> (match (_79_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _168_296 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _168_296))
end))

# 250 "FStar.SMTEncoding.Term.fst"
let hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _168_299 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _168_299))
end
| FreeV (x) -> begin
(let _168_300 = (strSort (Prims.snd x))
in (Prims.strcat (Prims.strcat (Prims.fst x) ":") _168_300))
end
| App (op, tms) -> begin
(let _168_304 = (let _168_303 = (let _168_302 = (FStar_List.map (fun t -> t.hash) tms)
in (FStar_All.pipe_right _168_302 (FStar_String.concat " ")))
in (Prims.strcat (Prims.strcat "(" (op_to_string op)) _168_303))
in (Prims.strcat _168_304 ")"))
end
| Labeled (t, r1, r2) -> begin
(let _168_305 = (FStar_Range.string_of_range r2)
in (Prims.strcat (Prims.strcat t.hash r1) _168_305))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _168_313 = (let _168_306 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _168_306 (FStar_String.concat " ")))
in (let _168_312 = (weightToSmt wopt)
in (let _168_311 = (let _168_310 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _168_309 = (FStar_List.map (fun p -> p.hash) pats)
in (FStar_All.pipe_right _168_309 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _168_310 (FStar_String.concat "; ")))
in (FStar_Util.format5 "(%s (%s)(! %s %s %s))" (qop_to_string qop) _168_313 body.hash _168_312 _168_311))))
end))

# 264 "FStar.SMTEncoding.Term.fst"
let __all_terms : term FStar_Util.smap FStar_ST.ref = (let _168_314 = (FStar_Util.smap_create 10000)
in (FStar_ST.alloc _168_314))

# 267 "FStar.SMTEncoding.Term.fst"
let all_terms : Prims.unit  ->  term FStar_Util.smap = (fun _79_202 -> (match (()) with
| () -> begin
(FStar_ST.read __all_terms)
end))

# 268 "FStar.SMTEncoding.Term.fst"
let mk : term'  ->  term = (fun t -> (
# 270 "FStar.SMTEncoding.Term.fst"
let key = (hash_of_term' t)
in (match ((let _168_319 = (all_terms ())
in (FStar_Util.smap_try_find _168_319 key))) with
| Some (tm) -> begin
tm
end
| None -> begin
(
# 274 "FStar.SMTEncoding.Term.fst"
let tm = (let _168_320 = (FStar_Util.mk_ref None)
in {tm = t; hash = key; freevars = _168_320})
in (
# 275 "FStar.SMTEncoding.Term.fst"
let _79_209 = (let _168_321 = (all_terms ())
in (FStar_Util.smap_add _168_321 key tm))
in tm))
end)))

# 276 "FStar.SMTEncoding.Term.fst"
let mkTrue : term = (mk (App ((True, []))))

# 278 "FStar.SMTEncoding.Term.fst"
let mkFalse : term = (mk (App ((False, []))))

# 279 "FStar.SMTEncoding.Term.fst"
let mkInteger : Prims.string  ->  term = (fun i -> (mk (Integer (i))))

# 280 "FStar.SMTEncoding.Term.fst"
let mkInteger' : Prims.int  ->  term = (fun i -> (let _168_326 = (FStar_Util.string_of_int i)
in (mkInteger _168_326)))

# 281 "FStar.SMTEncoding.Term.fst"
let mkBoundV : Prims.int  ->  term = (fun i -> (mk (BoundV (i))))

# 282 "FStar.SMTEncoding.Term.fst"
let mkFreeV : (Prims.string * sort)  ->  term = (fun x -> (mk (FreeV (x))))

# 283 "FStar.SMTEncoding.Term.fst"
let mkApp' : (op * term Prims.list)  ->  term = (fun f -> (mk (App (f))))

# 284 "FStar.SMTEncoding.Term.fst"
let mkApp : (Prims.string * term Prims.list)  ->  term = (fun _79_218 -> (match (_79_218) with
| (s, args) -> begin
(mk (App ((Var (s), args))))
end))

# 285 "FStar.SMTEncoding.Term.fst"
let mkNot : term  ->  term = (fun t -> (match (t.tm) with
| App (True, _79_222) -> begin
mkFalse
end
| App (False, _79_227) -> begin
mkTrue
end
| _79_231 -> begin
(mkApp' (Not, (t)::[]))
end))

# 289 "FStar.SMTEncoding.Term.fst"
let mkAnd : (term * term)  ->  term = (fun _79_234 -> (match (_79_234) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (App (True, _79_237), _79_241) -> begin
t2
end
| (_79_244, App (True, _79_247)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
mkFalse
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' (And, (FStar_List.append ts1 ts2)))
end
| (_79_277, App (And, ts2)) -> begin
(mkApp' (And, (t1)::ts2))
end
| (App (And, ts1), _79_288) -> begin
(mkApp' (And, (FStar_List.append ts1 ((t2)::[]))))
end
| _79_291 -> begin
(mkApp' (And, (t1)::(t2)::[]))
end)
end))

# 298 "FStar.SMTEncoding.Term.fst"
let mkOr : (term * term)  ->  term = (fun _79_294 -> (match (_79_294) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
mkTrue
end
| (App (False, _79_313), _79_317) -> begin
t2
end
| (_79_320, App (False, _79_323)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' (Or, (FStar_List.append ts1 ts2)))
end
| (_79_337, App (Or, ts2)) -> begin
(mkApp' (Or, (t1)::ts2))
end
| (App (Or, ts1), _79_348) -> begin
(mkApp' (Or, (FStar_List.append ts1 ((t2)::[]))))
end
| _79_351 -> begin
(mkApp' (Or, (t1)::(t2)::[]))
end)
end))

# 307 "FStar.SMTEncoding.Term.fst"
let mkImp : (term * term)  ->  term = (fun _79_354 -> (match (_79_354) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (_79_356, App (True, _79_359)) -> begin
mkTrue
end
| (App (True, _79_365), _79_369) -> begin
t2
end
| (_79_372, App (Imp, t1'::t2'::[])) -> begin
(let _168_345 = (let _168_344 = (let _168_343 = (mkAnd (t1, t1'))
in (_168_343)::(t2')::[])
in (Imp, _168_344))
in (mkApp' _168_345))
end
| _79_381 -> begin
(mkApp' (Imp, (t1)::(t2)::[]))
end)
end))

# 312 "FStar.SMTEncoding.Term.fst"
let mk_bin_op : op  ->  (term * term)  ->  term = (fun op _79_385 -> (match (_79_385) with
| (t1, t2) -> begin
(mkApp' (op, (t1)::(t2)::[]))
end))

# 314 "FStar.SMTEncoding.Term.fst"
let mkMinus : term  ->  term = (fun t -> (mkApp' (Minus, (t)::[])))

# 315 "FStar.SMTEncoding.Term.fst"
let mkIff : (term * term)  ->  term = (mk_bin_op Iff)

# 316 "FStar.SMTEncoding.Term.fst"
let mkEq : (term * term)  ->  term = (mk_bin_op Eq)

# 317 "FStar.SMTEncoding.Term.fst"
let mkLT : (term * term)  ->  term = (mk_bin_op LT)

# 318 "FStar.SMTEncoding.Term.fst"
let mkLTE : (term * term)  ->  term = (mk_bin_op LTE)

# 319 "FStar.SMTEncoding.Term.fst"
let mkGT : (term * term)  ->  term = (mk_bin_op GT)

# 320 "FStar.SMTEncoding.Term.fst"
let mkGTE : (term * term)  ->  term = (mk_bin_op GTE)

# 321 "FStar.SMTEncoding.Term.fst"
let mkAdd : (term * term)  ->  term = (mk_bin_op Add)

# 322 "FStar.SMTEncoding.Term.fst"
let mkSub : (term * term)  ->  term = (mk_bin_op Sub)

# 323 "FStar.SMTEncoding.Term.fst"
let mkDiv : (term * term)  ->  term = (mk_bin_op Div)

# 324 "FStar.SMTEncoding.Term.fst"
let mkMul : (term * term)  ->  term = (mk_bin_op Mul)

# 325 "FStar.SMTEncoding.Term.fst"
let mkMod : (term * term)  ->  term = (mk_bin_op Mod)

# 326 "FStar.SMTEncoding.Term.fst"
let mkITE : (term * term * term)  ->  term = (fun _79_390 -> (match (_79_390) with
| (t1, t2, t3) -> begin
(match ((t2.tm, t3.tm)) with
| (App (True, _79_393), App (True, _79_398)) -> begin
mkTrue
end
| (App (True, _79_404), _79_408) -> begin
(let _168_366 = (let _168_365 = (mkNot t1)
in (_168_365, t3))
in (mkImp _168_366))
end
| (_79_411, App (True, _79_414)) -> begin
(mkImp (t1, t2))
end
| (_79_419, _79_421) -> begin
(mkApp' (ITE, (t1)::(t2)::(t3)::[]))
end)
end))

# 332 "FStar.SMTEncoding.Term.fst"
let mkCases : term Prims.list  ->  term = (fun t -> (match (t) with
| [] -> begin
(FStar_All.failwith "Impos")
end
| hd::tl -> begin
(FStar_List.fold_left (fun out t -> (mkAnd (out, t))) hd tl)
end))

# 335 "FStar.SMTEncoding.Term.fst"
let mkQuant : (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _79_435 -> (match (_79_435) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = 0) then begin
body
end else begin
(match (body.tm) with
| App (True, _79_438) -> begin
body
end
| _79_442 -> begin
(mk (Quant ((qop, pats, wopt, vars, body))))
end)
end
end))

# 341 "FStar.SMTEncoding.Term.fst"
let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (
# 347 "FStar.SMTEncoding.Term.fst"
let nvars = (FStar_List.length fvs)
in (
# 348 "FStar.SMTEncoding.Term.fst"
let index_of = (fun fv -> (match ((FStar_Util.try_find_index (fv_eq fv) fvs)) with
| None -> begin
None
end
| Some (i) -> begin
Some ((nvars - (i + 1)))
end))
in (
# 351 "FStar.SMTEncoding.Term.fst"
let rec aux = (fun ix t -> (match ((FStar_ST.read t.freevars)) with
| Some ([]) -> begin
t
end
| _79_457 -> begin
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
(let _168_384 = (let _168_383 = (FStar_List.map (aux ix) tms)
in (op, _168_383))
in (mkApp' _168_384))
end
| Labeled (t, r1, r2) -> begin
(let _168_387 = (let _168_386 = (let _168_385 = (aux ix t)
in (_168_385, r1, r2))
in Labeled (_168_386))
in (mk _168_387))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(
# 366 "FStar.SMTEncoding.Term.fst"
let n = (FStar_List.length vars)
in (let _168_390 = (let _168_389 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _168_388 = (aux (ix + n) body)
in (qop, _168_389, wopt, vars, _168_388)))
in (mkQuant _168_390)))
end)
end))
in (aux 0 t)))))

# 369 "FStar.SMTEncoding.Term.fst"
let inst : term Prims.list  ->  term  ->  term = (fun tms t -> (
# 372 "FStar.SMTEncoding.Term.fst"
let n = (FStar_List.length tms)
in (
# 373 "FStar.SMTEncoding.Term.fst"
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
(let _168_400 = (let _168_399 = (FStar_List.map (aux shift) tms)
in (op, _168_399))
in (mkApp' _168_400))
end
| Labeled (t, r1, r2) -> begin
(let _168_403 = (let _168_402 = (let _168_401 = (aux shift t)
in (_168_401, r1, r2))
in Labeled (_168_402))
in (mk _168_403))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(
# 383 "FStar.SMTEncoding.Term.fst"
let m = (FStar_List.length vars)
in (
# 384 "FStar.SMTEncoding.Term.fst"
let shift = (shift + m)
in (let _168_406 = (let _168_405 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _168_404 = (aux shift body)
in (qop, _168_405, wopt, vars, _168_404)))
in (mkQuant _168_406))))
end))
in (aux 0 t))))

# 386 "FStar.SMTEncoding.Term.fst"
let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list * term)  ->  term = (fun _79_523 -> (match (_79_523) with
| (qop, pats, wopt, vars, body) -> begin
(let _168_412 = (let _168_411 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _168_410 = (FStar_List.map fv_sort vars)
in (let _168_409 = (abstr vars body)
in (qop, _168_411, wopt, _168_410, _168_409))))
in (mkQuant _168_412))
end))

# 388 "FStar.SMTEncoding.Term.fst"
let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _79_528 -> (match (_79_528) with
| (pats, wopt, sorts, body) -> begin
(mkQuant (Forall, pats, wopt, sorts, body))
end))

# 389 "FStar.SMTEncoding.Term.fst"
let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  term = (fun _79_533 -> (match (_79_533) with
| (pats, wopt, vars, body) -> begin
(mkQuant' (Forall, pats, wopt, vars, body))
end))

# 390 "FStar.SMTEncoding.Term.fst"
let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _79_537 -> (match (_79_537) with
| (pats, vars, body) -> begin
(mkQuant' (Forall, pats, None, vars, body))
end))

# 393 "FStar.SMTEncoding.Term.fst"
let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _79_541 -> (match (_79_541) with
| (pats, vars, body) -> begin
(mkQuant' (Exists, pats, None, vars, body))
end))

# 394 "FStar.SMTEncoding.Term.fst"
let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun _79_547 -> (match (_79_547) with
| (nm, vars, s, tm, c) -> begin
(let _168_425 = (let _168_424 = (FStar_List.map fv_sort vars)
in (let _168_423 = (abstr vars tm)
in (nm, _168_424, s, _168_423, c)))
in DefineFun (_168_425))
end))

# 397 "FStar.SMTEncoding.Term.fst"
let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _168_428 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _168_428)))

# 398 "FStar.SMTEncoding.Term.fst"
let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun _79_551 id -> (match (_79_551) with
| (tok_name, sort) -> begin
(let _168_441 = (let _168_440 = (let _168_439 = (let _168_438 = (mkInteger' id)
in (let _168_437 = (let _168_436 = (let _168_435 = (constr_id_of_sort sort)
in (let _168_434 = (let _168_433 = (mkApp (tok_name, []))
in (_168_433)::[])
in (_168_435, _168_434)))
in (mkApp _168_436))
in (_168_438, _168_437)))
in (mkEq _168_439))
in (_168_440, Some ("fresh token")))
in Assume (_168_441))
end))

# 400 "FStar.SMTEncoding.Term.fst"
let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun _79_557 -> (match (_79_557) with
| (name, arg_sorts, sort, id) -> begin
(
# 403 "FStar.SMTEncoding.Term.fst"
let id = (FStar_Util.string_of_int id)
in (
# 404 "FStar.SMTEncoding.Term.fst"
let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (let _168_448 = (let _168_447 = (let _168_446 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _168_446))
in (_168_447, s))
in (mkFreeV _168_448)))))
in (
# 405 "FStar.SMTEncoding.Term.fst"
let bvar_names = (FStar_List.map fv_of_term bvars)
in (
# 406 "FStar.SMTEncoding.Term.fst"
let capp = (mkApp (name, bvars))
in (
# 407 "FStar.SMTEncoding.Term.fst"
let cid_app = (let _168_450 = (let _168_449 = (constr_id_of_sort sort)
in (_168_449, (capp)::[]))
in (mkApp _168_450))
in (let _168_456 = (let _168_455 = (let _168_454 = (let _168_453 = (let _168_452 = (let _168_451 = (mkInteger id)
in (_168_451, cid_app))
in (mkEq _168_452))
in (((capp)::[])::[], bvar_names, _168_453))
in (mkForall _168_454))
in (_168_455, Some ("Constructor distinct")))
in Assume (_168_456)))))))
end))

# 408 "FStar.SMTEncoding.Term.fst"
let injective_constructor : (Prims.string * (Prims.string * sort) Prims.list * sort)  ->  decls_t = (fun _79_568 -> (match (_79_568) with
| (name, projectors, sort) -> begin
(
# 411 "FStar.SMTEncoding.Term.fst"
let n_bvars = (FStar_List.length projectors)
in (
# 412 "FStar.SMTEncoding.Term.fst"
let bvar_name = (fun i -> (let _168_461 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _168_461)))
in (
# 413 "FStar.SMTEncoding.Term.fst"
let bvar_index = (fun i -> (n_bvars - (i + 1)))
in (
# 414 "FStar.SMTEncoding.Term.fst"
let bvar = (fun i s -> (let _168_469 = (let _168_468 = (bvar_name i)
in (_168_468, s))
in (mkFreeV _168_469)))
in (
# 415 "FStar.SMTEncoding.Term.fst"
let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _79_581 -> (match (_79_581) with
| (_79_579, s) -> begin
(bvar i s)
end))))
in (
# 416 "FStar.SMTEncoding.Term.fst"
let bvar_names = (FStar_List.map fv_of_term bvars)
in (
# 417 "FStar.SMTEncoding.Term.fst"
let capp = (mkApp (name, bvars))
in (let _168_482 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _79_588 -> (match (_79_588) with
| (name, s) -> begin
(
# 420 "FStar.SMTEncoding.Term.fst"
let cproj_app = (mkApp (name, (capp)::[]))
in (
# 421 "FStar.SMTEncoding.Term.fst"
let proj_name = DeclFun ((name, (sort)::[], s, Some ("Projector")))
in (let _168_481 = (let _168_480 = (let _168_479 = (let _168_478 = (let _168_477 = (let _168_476 = (let _168_475 = (let _168_474 = (bvar i s)
in (cproj_app, _168_474))
in (mkEq _168_475))
in (((capp)::[])::[], bvar_names, _168_476))
in (mkForall _168_477))
in (_168_478, Some ("Projection inverse")))
in Assume (_168_479))
in (_168_480)::[])
in (proj_name)::_168_481)))
end))))
in (FStar_All.pipe_right _168_482 FStar_List.flatten)))))))))
end))

# 424 "FStar.SMTEncoding.Term.fst"
let constructor_to_decl : constructor_t  ->  decls_t = (fun _79_596 -> (match (_79_596) with
| (name, projectors, sort, id, injective) -> begin
(
# 427 "FStar.SMTEncoding.Term.fst"
let injective = (injective || true)
in (
# 428 "FStar.SMTEncoding.Term.fst"
let cdecl = (let _168_486 = (let _168_485 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in (name, _168_485, sort, Some ("Constructor")))
in DeclFun (_168_486))
in (
# 429 "FStar.SMTEncoding.Term.fst"
let cid = (let _168_488 = (let _168_487 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in (name, _168_487, sort, id))
in (fresh_constructor _168_488))
in (
# 430 "FStar.SMTEncoding.Term.fst"
let disc = (
# 431 "FStar.SMTEncoding.Term.fst"
let disc_name = (Prims.strcat "is-" name)
in (
# 432 "FStar.SMTEncoding.Term.fst"
let xfv = ("x", sort)
in (
# 433 "FStar.SMTEncoding.Term.fst"
let xx = (mkFreeV xfv)
in (
# 434 "FStar.SMTEncoding.Term.fst"
let disc_eq = (let _168_494 = (let _168_493 = (let _168_490 = (let _168_489 = (constr_id_of_sort sort)
in (_168_489, (xx)::[]))
in (mkApp _168_490))
in (let _168_492 = (let _168_491 = (FStar_Util.string_of_int id)
in (mkInteger _168_491))
in (_168_493, _168_492)))
in (mkEq _168_494))
in (
# 435 "FStar.SMTEncoding.Term.fst"
let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _79_606 -> (match (_79_606) with
| (proj, s) -> begin
(mkApp (proj, (xx)::[]))
end))))
in (
# 436 "FStar.SMTEncoding.Term.fst"
let disc_inv_body = (let _168_497 = (let _168_496 = (mkApp (name, proj_terms))
in (xx, _168_496))
in (mkEq _168_497))
in (
# 437 "FStar.SMTEncoding.Term.fst"
let disc_ax = (mkAnd (disc_eq, disc_inv_body))
in (mkDefineFun (disc_name, (xfv)::[], Bool_sort, disc_ax, Some ("Discriminator definition"))))))))))
in (
# 441 "FStar.SMTEncoding.Term.fst"
let projs = if injective then begin
(injective_constructor (name, projectors, sort))
end else begin
[]
end
in (let _168_504 = (let _168_500 = (let _168_499 = (let _168_498 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_168_498))
in (_168_499)::(cdecl)::(cid)::projs)
in (FStar_List.append _168_500 ((disc)::[])))
in (let _168_503 = (let _168_502 = (let _168_501 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_168_501))
in (_168_502)::[])
in (FStar_List.append _168_504 _168_503))))))))
end))

# 445 "FStar.SMTEncoding.Term.fst"
let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (
# 452 "FStar.SMTEncoding.Term.fst"
let _79_630 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _79_618 s -> (match (_79_618) with
| (names, binders, n) -> begin
(
# 453 "FStar.SMTEncoding.Term.fst"
let prefix = (match (s) with
| Term_sort -> begin
"@x"
end
| _79_622 -> begin
"@u"
end)
in (
# 456 "FStar.SMTEncoding.Term.fst"
let nm = (let _168_513 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _168_513))
in (
# 457 "FStar.SMTEncoding.Term.fst"
let names = ((nm, s))::names
in (
# 458 "FStar.SMTEncoding.Term.fst"
let b = (let _168_514 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _168_514))
in (names, (b)::binders, (n + 1))))))
end)) (outer_names, [], start)))
in (match (_79_630) with
| (names, binders, n) -> begin
(names, (FStar_List.rev binders), n)
end)))

# 461 "FStar.SMTEncoding.Term.fst"
let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (
# 464 "FStar.SMTEncoding.Term.fst"
let _79_635 = (name_binders_inner [] 0 sorts)
in (match (_79_635) with
| (names, binders, n) -> begin
((FStar_List.rev names), binders)
end)))

# 465 "FStar.SMTEncoding.Term.fst"
let termToSmt : term  ->  Prims.string = (fun t -> (
# 468 "FStar.SMTEncoding.Term.fst"
let rec aux = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _168_525 = (FStar_List.nth names i)
in (FStar_All.pipe_right _168_525 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _168_527 = (let _168_526 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _168_526 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _168_527))
end
| Labeled (t, _79_657, _79_659) -> begin
(aux n names t)
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(
# 477 "FStar.SMTEncoding.Term.fst"
let _79_672 = (name_binders_inner names n sorts)
in (match (_79_672) with
| (names, binders, n) -> begin
(
# 478 "FStar.SMTEncoding.Term.fst"
let binders = (FStar_All.pipe_right binders (FStar_String.concat " "))
in (
# 479 "FStar.SMTEncoding.Term.fst"
let pats_str = (match (pats) with
| ([]::[]) | ([]) -> begin
""
end
| _79_678 -> begin
(let _168_533 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _168_532 = (let _168_531 = (FStar_List.map (fun p -> (let _168_530 = (aux n names p)
in (FStar_Util.format1 "%s" _168_530))) pats)
in (FStar_String.concat " " _168_531))
in (FStar_Util.format1 "\n:pattern (%s)" _168_532)))))
in (FStar_All.pipe_right _168_533 (FStar_String.concat "\n")))
end)
in (match ((pats, wopt)) with
| (([]::[], None)) | (([], None)) -> begin
(let _168_534 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _168_534))
end
| _79_690 -> begin
(let _168_536 = (aux n names body)
in (let _168_535 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _168_536 _168_535 pats_str)))
end)))
end))
end))
in (aux 0 [] t)))

# 488 "FStar.SMTEncoding.Term.fst"
let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun _79_6 -> (match (_79_6) with
| None -> begin
""
end
| Some (c) -> begin
(
# 494 "FStar.SMTEncoding.Term.fst"
let _79_704 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::[] -> begin
(hd, "")
end
| hd::_79_699 -> begin
(hd, "...")
end)
in (match (_79_704) with
| (hd, suffix) -> begin
(FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd suffix)
end))
end))

# 498 "FStar.SMTEncoding.Term.fst"
let rec declToSmt : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(let _168_545 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _79_7 -> (match (_79_7) with
| [] -> begin
""
end
| h::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _168_545))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(
# 505 "FStar.SMTEncoding.Term.fst"
let l = (FStar_List.map strSort argsorts)
in (let _168_547 = (caption_to_string c)
in (let _168_546 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _168_547 f (FStar_String.concat " " l) _168_546))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(
# 508 "FStar.SMTEncoding.Term.fst"
let _79_731 = (name_binders arg_sorts)
in (match (_79_731) with
| (names, binders) -> begin
(
# 509 "FStar.SMTEncoding.Term.fst"
let body = (let _168_548 = (FStar_List.map mkFreeV names)
in (inst _168_548 body))
in (let _168_551 = (caption_to_string c)
in (let _168_550 = (strSort retsort)
in (let _168_549 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _168_551 f (FStar_String.concat " " binders) _168_550 _168_549)))))
end))
end
| Assume (t, c) -> begin
(let _168_553 = (caption_to_string c)
in (let _168_552 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _168_553 _168_552)))
end
| Eval (t) -> begin
(let _168_554 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _168_554))
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
# 522 "FStar.SMTEncoding.Term.fst"
let basic = (Prims.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort String)\n(declare-fun String_constr_id (String) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n")
in (
# 568 "FStar.SMTEncoding.Term.fst"
let constrs = (("String_const", (("String_const_proj_0", Int_sort))::[], String_sort, 0, true))::(("Tm_type", [], Term_sort, 2, true))::(("Tm_arrow", (("Tm_arrow_id", Int_sort))::[], Term_sort, 3, false))::(("Tm_uvar", (("Tm_uvar_fst", Int_sort))::[], Term_sort, 5, true))::(("Tm_unit", [], Term_sort, 6, true))::(("BoxInt", (("BoxInt_proj_0", Int_sort))::[], Term_sort, 7, true))::(("BoxBool", (("BoxBool_proj_0", Bool_sort))::[], Term_sort, 8, true))::(("BoxString", (("BoxString_proj_0", String_sort))::[], Term_sort, 9, true))::(("BoxRef", (("BoxRef_proj_0", Ref_sort))::[], Term_sort, 10, true))::(("LexCons", (("LexCons_0", Term_sort))::(("LexCons_1", Term_sort))::[], Term_sort, 11, true))::[]
in (
# 578 "FStar.SMTEncoding.Term.fst"
let bcons = (let _168_557 = (let _168_556 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _168_556 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _168_557 (FStar_String.concat "\n")))
in (
# 579 "FStar.SMTEncoding.Term.fst"
let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat (Prims.strcat basic bcons) lex_ordering))))))

# 586 "FStar.SMTEncoding.Term.fst"
let mk_Range_const : term = (mkApp ("Range_const", []))

# 588 "FStar.SMTEncoding.Term.fst"
let mk_Term_type : term = (mkApp ("Tm_type", []))

# 589 "FStar.SMTEncoding.Term.fst"
let mk_Term_app : term  ->  term  ->  term = (fun t1 t2 -> (mkApp ("Tm_app", (t1)::(t2)::[])))

# 590 "FStar.SMTEncoding.Term.fst"
let mk_Term_uvar : Prims.int  ->  term = (fun i -> (let _168_566 = (let _168_565 = (let _168_564 = (mkInteger' i)
in (_168_564)::[])
in ("Tm_uvar", _168_565))
in (mkApp _168_566)))

# 591 "FStar.SMTEncoding.Term.fst"
let mk_Term_unit : term = (mkApp ("Tm_unit", []))

# 592 "FStar.SMTEncoding.Term.fst"
let boxInt : term  ->  term = (fun t -> (mkApp ("BoxInt", (t)::[])))

# 593 "FStar.SMTEncoding.Term.fst"
let unboxInt : term  ->  term = (fun t -> (mkApp ("BoxInt_proj_0", (t)::[])))

# 594 "FStar.SMTEncoding.Term.fst"
let boxBool : term  ->  term = (fun t -> (mkApp ("BoxBool", (t)::[])))

# 595 "FStar.SMTEncoding.Term.fst"
let unboxBool : term  ->  term = (fun t -> (mkApp ("BoxBool_proj_0", (t)::[])))

# 596 "FStar.SMTEncoding.Term.fst"
let boxString : term  ->  term = (fun t -> (mkApp ("BoxString", (t)::[])))

# 597 "FStar.SMTEncoding.Term.fst"
let unboxString : term  ->  term = (fun t -> (mkApp ("BoxString_proj_0", (t)::[])))

# 598 "FStar.SMTEncoding.Term.fst"
let boxRef : term  ->  term = (fun t -> (mkApp ("BoxRef", (t)::[])))

# 599 "FStar.SMTEncoding.Term.fst"
let unboxRef : term  ->  term = (fun t -> (mkApp ("BoxRef_proj_0", (t)::[])))

# 600 "FStar.SMTEncoding.Term.fst"
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
| _79_767 -> begin
(Prims.raise FStar_Util.Impos)
end))

# 606 "FStar.SMTEncoding.Term.fst"
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
| _79_775 -> begin
(Prims.raise FStar_Util.Impos)
end))

# 612 "FStar.SMTEncoding.Term.fst"
let mk_PreType : term  ->  term = (fun t -> (mkApp ("PreType", (t)::[])))

# 614 "FStar.SMTEncoding.Term.fst"
let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_Equality"), _79_789::t1::t2::[]); hash = _79_783; freevars = _79_781}::[]) -> begin
(mkEq (t1, t2))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_disEquality"), _79_808::t1::t2::[]); hash = _79_802; freevars = _79_800}::[]) -> begin
(let _168_595 = (mkEq (t1, t2))
in (mkNot _168_595))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_LessThanOrEqual"), t1::t2::[]); hash = _79_821; freevars = _79_819}::[]) -> begin
(let _168_598 = (let _168_597 = (unboxInt t1)
in (let _168_596 = (unboxInt t2)
in (_168_597, _168_596)))
in (mkLTE _168_598))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_LessThan"), t1::t2::[]); hash = _79_838; freevars = _79_836}::[]) -> begin
(let _168_601 = (let _168_600 = (unboxInt t1)
in (let _168_599 = (unboxInt t2)
in (_168_600, _168_599)))
in (mkLT _168_601))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_GreaterThanOrEqual"), t1::t2::[]); hash = _79_855; freevars = _79_853}::[]) -> begin
(let _168_604 = (let _168_603 = (unboxInt t1)
in (let _168_602 = (unboxInt t2)
in (_168_603, _168_602)))
in (mkGTE _168_604))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_GreaterThan"), t1::t2::[]); hash = _79_872; freevars = _79_870}::[]) -> begin
(let _168_607 = (let _168_606 = (unboxInt t1)
in (let _168_605 = (unboxInt t2)
in (_168_606, _168_605)))
in (mkGT _168_607))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_AmpAmp"), t1::t2::[]); hash = _79_889; freevars = _79_887}::[]) -> begin
(let _168_610 = (let _168_609 = (unboxBool t1)
in (let _168_608 = (unboxBool t2)
in (_168_609, _168_608)))
in (mkAnd _168_610))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_BarBar"), t1::t2::[]); hash = _79_906; freevars = _79_904}::[]) -> begin
(let _168_613 = (let _168_612 = (unboxBool t1)
in (let _168_611 = (unboxBool t2)
in (_168_612, _168_611)))
in (mkOr _168_613))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_Negation"), t::[]); hash = _79_923; freevars = _79_921}::[]) -> begin
(let _168_614 = (unboxBool t)
in (mkNot _168_614))
end
| App (Var ("Prims.b2t"), t::[]) -> begin
(unboxBool t)
end
| _79_941 -> begin
(mkApp ("Valid", (t)::[]))
end))

# 626 "FStar.SMTEncoding.Term.fst"
let mk_HasType : term  ->  term  ->  term = (fun v t -> (mkApp ("HasType", (v)::(t)::[])))

# 627 "FStar.SMTEncoding.Term.fst"
let mk_HasTypeZ : term  ->  term  ->  term = (fun v t -> (mkApp ("HasTypeZ", (v)::(t)::[])))

# 628 "FStar.SMTEncoding.Term.fst"
let mk_IsTyped : term  ->  term = (fun v -> (mkApp ("IsTyped", (v)::[])))

# 629 "FStar.SMTEncoding.Term.fst"
let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v t -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(mk_HasType v t)
end else begin
(mkApp ("HasTypeFuel", (f)::(v)::(t)::[]))
end)

# 633 "FStar.SMTEncoding.Term.fst"
let mk_HasTypeWithFuel : term Prims.option  ->  term  ->  term  ->  term = (fun f v t -> (match (f) with
| None -> begin
(mk_HasType v t)
end
| Some (f) -> begin
(mk_HasTypeFuel f v t)
end))

# 636 "FStar.SMTEncoding.Term.fst"
let mk_Destruct : term  ->  term = (fun v -> (mkApp ("Destruct", (v)::[])))

# 637 "FStar.SMTEncoding.Term.fst"
let mk_Rank : term  ->  term = (fun x -> (mkApp ("Rank", (x)::[])))

# 638 "FStar.SMTEncoding.Term.fst"
let mk_tester : Prims.string  ->  term  ->  term = (fun n t -> (mkApp ((Prims.strcat "is-" n), (t)::[])))

# 639 "FStar.SMTEncoding.Term.fst"
let mk_ApplyTF : term  ->  term  ->  term = (fun t t' -> (mkApp ("ApplyTF", (t)::(t')::[])))

# 640 "FStar.SMTEncoding.Term.fst"
let mk_ApplyTT : term  ->  term  ->  term = (fun t t' -> (mkApp ("ApplyTT", (t)::(t')::[])))

# 641 "FStar.SMTEncoding.Term.fst"
let mk_String_const : Prims.int  ->  term = (fun i -> (let _168_657 = (let _168_656 = (let _168_655 = (mkInteger' i)
in (_168_655)::[])
in ("String_const", _168_656))
in (mkApp _168_657)))

# 642 "FStar.SMTEncoding.Term.fst"
let mk_Precedes : term  ->  term  ->  term = (fun x1 x2 -> (let _168_662 = (mkApp ("Precedes", (x1)::(x2)::[]))
in (FStar_All.pipe_right _168_662 mk_Valid)))

# 643 "FStar.SMTEncoding.Term.fst"
let mk_LexCons : term  ->  term  ->  term = (fun x1 x2 -> (mkApp ("LexCons", (x1)::(x2)::[])))

# 644 "FStar.SMTEncoding.Term.fst"
let rec n_fuel : Prims.int  ->  term = (fun n -> if (n = 0) then begin
(mkApp ("ZFuel", []))
end else begin
(let _168_671 = (let _168_670 = (let _168_669 = (n_fuel (n - 1))
in (_168_669)::[])
in ("SFuel", _168_670))
in (mkApp _168_671))
end)

# 647 "FStar.SMTEncoding.Term.fst"
let fuel_2 : term = (n_fuel 2)

# 648 "FStar.SMTEncoding.Term.fst"
let fuel_100 : term = (n_fuel 100)

# 649 "FStar.SMTEncoding.Term.fst"
let mk_and_opt : term Prims.option  ->  term Prims.option  ->  term Prims.option = (fun p1 p2 -> (match ((p1, p2)) with
| (Some (p1), Some (p2)) -> begin
(let _168_676 = (mkAnd (p1, p2))
in Some (_168_676))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))

# 655 "FStar.SMTEncoding.Term.fst"
let mk_and_opt_l : term Prims.option Prims.list  ->  term Prims.option = (fun pl -> (FStar_List.fold_left (fun out p -> (mk_and_opt p out)) None pl))

# 658 "FStar.SMTEncoding.Term.fst"
let mk_and_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkTrue
end
| hd::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkAnd (p1, p2))) hd tl)
end))

# 662 "FStar.SMTEncoding.Term.fst"
let mk_or_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkFalse
end
| hd::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkOr (p1, p2))) hd tl)
end))

# 666 "FStar.SMTEncoding.Term.fst"
let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "(Integer %s)" n)
end
| BoundV (n) -> begin
(let _168_693 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "(BoundV %s)" _168_693))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (Prims.fst fv))
end
| App (op, l) -> begin
(let _168_694 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _168_694))
end
| Labeled (t, r1, r2) -> begin
(let _168_695 = (print_smt_term t)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 _168_695))
end
| Quant (qop, l, _79_1023, _79_1025, t) -> begin
(let _168_697 = (print_smt_term_list_list l)
in (let _168_696 = (print_smt_term t)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) _168_697 _168_696)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (let _168_699 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right _168_699 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _168_704 = (let _168_703 = (print_smt_term_list l)
in (Prims.strcat (Prims.strcat s "; [ ") _168_703))
in (Prims.strcat _168_704 " ] "))) "" l))




