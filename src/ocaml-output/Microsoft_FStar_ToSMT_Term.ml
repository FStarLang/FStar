
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
(let _65_20267 = (strSort s1)
in (let _65_20266 = (strSort s2)
in (Support.Microsoft.FStar.Util.format2 "(Array %s %s)" _65_20267 _65_20266)))
end
| Arrow ((s1, s2)) -> begin
(let _65_20269 = (strSort s1)
in (let _65_20268 = (strSort s2)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _65_20269 _65_20268)))
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

let is_Mkterm = (fun ( _ ) -> (failwith ("Not yet implemented")))

let fv_eq = (fun ( x ) ( y ) -> ((Support.Prims.fst x) = (Support.Prims.fst y)))

let fv_sort = (fun ( x ) -> (Support.Prims.snd x))

let freevar_eq = (fun ( x ) ( y ) -> (match ((x.tm, y.tm)) with
| (FreeV (x), FreeV (y)) -> begin
(fv_eq x y)
end
| _ -> begin
false
end))

let freevar_sort = (fun ( _47_1 ) -> (match (_47_1) with
| {tm = FreeV (x); hash = _; freevars = _} -> begin
(fv_sort x)
end
| _ -> begin
(failwith ("impossible"))
end))

let fv_of_term = (fun ( _47_2 ) -> (match (_47_2) with
| {tm = FreeV (fv); hash = _; freevars = _} -> begin
fv
end
| _ -> begin
(failwith ("impossible"))
end))

let rec freevars = (fun ( t ) -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App ((_, tms)) -> begin
(Support.List.collect freevars tms)
end
| Quant ((_, _, _, _, t)) -> begin
(freevars t)
end))

let free_variables = (fun ( t ) -> (match ((Support.ST.read t.freevars)) with
| Some (b) -> begin
b
end
| None -> begin
(let fvs = (let _65_20360 = (freevars t)
in (Support.Microsoft.FStar.Util.remove_dups fv_eq _65_20360))
in (let _47_111 = (Support.ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))

let qop_to_string = (fun ( _47_3 ) -> (match (_47_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))

let op_to_string = (fun ( _47_4 ) -> (match (_47_4) with
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

let weightToSmt = (fun ( _47_5 ) -> (match (_47_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _65_20367 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format1 ":weight %s\n" _65_20367))
end))

let rec hash_of_term' = (fun ( t ) -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _65_20370 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.String.strcat "@" _65_20370))
end
| FreeV (x) -> begin
(let _65_20371 = (strSort (Support.Prims.snd x))
in (Support.String.strcat (Support.String.strcat (Support.Prims.fst x) ":") _65_20371))
end
| App ((op, tms)) -> begin
(let _65_20375 = (let _65_20374 = (let _65_20373 = (Support.List.map (fun ( t ) -> t.hash) tms)
in (Support.Prims.pipe_right _65_20373 (Support.String.concat " ")))
in (Support.String.strcat (Support.String.strcat "(" (op_to_string op)) _65_20374))
in (Support.String.strcat _65_20375 ")"))
end
| Quant ((qop, pats, wopt, sorts, body)) -> begin
(let _65_20383 = (let _65_20376 = (Support.List.map strSort sorts)
in (Support.Prims.pipe_right _65_20376 (Support.String.concat " ")))
in (let _65_20382 = (weightToSmt wopt)
in (let _65_20381 = (let _65_20380 = (Support.Prims.pipe_right pats (Support.List.map (fun ( pats ) -> (let _65_20379 = (Support.List.map (fun ( p ) -> p.hash) pats)
in (Support.Prims.pipe_right _65_20379 (Support.String.concat " "))))))
in (Support.Prims.pipe_right _65_20380 (Support.String.concat "; ")))
in (Support.Microsoft.FStar.Util.format5 "(%s (%s)(! %s %s %s))" (qop_to_string qop) _65_20383 body.hash _65_20382 _65_20381))))
end))

let all_terms_l = (let _65_20385 = (let _65_20384 = (Support.Microsoft.FStar.Util.smap_create 10000)
in (_65_20384)::[])
in (ref _65_20385))

let all_terms = (fun ( _47_163 ) -> (match (()) with
| () -> begin
(let _65_20388 = (Support.ST.read all_terms_l)
in (Support.List.hd _65_20388))
end))

let push = (fun ( _47_164 ) -> ())

let pop = (fun ( _47_165 ) -> ())

let commit_mark = (fun ( _47_166 ) -> ())

let mk = (fun ( t ) -> (let key = (hash_of_term' t)
in (match ((let _65_20397 = (all_terms ())
in (Support.Microsoft.FStar.Util.smap_try_find _65_20397 key))) with
| Some (tm) -> begin
tm
end
| None -> begin
(let tm = (let _65_20398 = (Support.Microsoft.FStar.Util.mk_ref None)
in {tm = t; hash = key; freevars = _65_20398})
in (let _47_173 = (let _65_20399 = (all_terms ())
in (Support.Microsoft.FStar.Util.smap_add _65_20399 key tm))
in tm))
end)))

let mkTrue = (mk (App ((True, []))))

let mkFalse = (mk (App ((False, []))))

let mkInteger = (fun ( i ) -> (mk (Integer (i))))

let mkInteger' = (fun ( i ) -> (let _65_20404 = (Support.Microsoft.FStar.Util.string_of_int i)
in (mkInteger _65_20404)))

let mkBoundV = (fun ( i ) -> (mk (BoundV (i))))

let mkFreeV = (fun ( x ) -> (mk (FreeV (x))))

let mkApp' = (fun ( f ) -> (mk (App (f))))

let mkApp = (fun ( _47_182 ) -> (match (_47_182) with
| (s, args) -> begin
(mk (App ((Var (s), args))))
end))

let mkNot = (fun ( t ) -> (match (t.tm) with
| App ((True, _)) -> begin
mkFalse
end
| App ((False, _)) -> begin
mkTrue
end
| _ -> begin
(mkApp' (Not, (t)::[]))
end))

let mkAnd = (fun ( _47_198 ) -> (match (_47_198) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (App ((True, _)), _) -> begin
t2
end
| (_, App ((True, _))) -> begin
t1
end
| ((App ((False, _)), _)) | ((_, App ((False, _)))) -> begin
mkFalse
end
| (App ((And, ts1)), App ((And, ts2))) -> begin
(mkApp' (And, (Support.List.append ts1 ts2)))
end
| (_, App ((And, ts2))) -> begin
(mkApp' (And, (t1)::ts2))
end
| (App ((And, ts1)), _) -> begin
(mkApp' (And, (Support.List.append ts1 ((t2)::[]))))
end
| _ -> begin
(mkApp' (And, (t1)::(t2)::[]))
end)
end))

let mkOr = (fun ( _47_258 ) -> (match (_47_258) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| ((App ((True, _)), _)) | ((_, App ((True, _)))) -> begin
mkTrue
end
| (App ((False, _)), _) -> begin
t2
end
| (_, App ((False, _))) -> begin
t1
end
| (App ((Or, ts1)), App ((Or, ts2))) -> begin
(mkApp' (Or, (Support.List.append ts1 ts2)))
end
| (_, App ((Or, ts2))) -> begin
(mkApp' (Or, (t1)::ts2))
end
| (App ((Or, ts1)), _) -> begin
(mkApp' (Or, (Support.List.append ts1 ((t2)::[]))))
end
| _ -> begin
(mkApp' (Or, (t1)::(t2)::[]))
end)
end))

let mkImp = (fun ( _47_318 ) -> (match (_47_318) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (_, App ((True, _))) -> begin
mkTrue
end
| (App ((True, _)), _) -> begin
t2
end
| (_, App ((Imp, t1'::t2'::[]))) -> begin
(let _65_20423 = (let _65_20422 = (let _65_20421 = (mkAnd (t1, t1'))
in (_65_20421)::(t2')::[])
in (Imp, _65_20422))
in (mkApp' _65_20423))
end
| _ -> begin
(mkApp' (Imp, (t1)::(t2)::[]))
end)
end))

let mk_bin_op = (fun ( op ) ( _47_349 ) -> (match (_47_349) with
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

let mkITE = (fun ( _47_354 ) -> (match (_47_354) with
| (t1, t2, t3) -> begin
(match ((t2.tm, t3.tm)) with
| (App ((True, _)), App ((True, _))) -> begin
mkTrue
end
| (App ((True, _)), _) -> begin
(let _65_20444 = (let _65_20443 = (mkNot t1)
in (_65_20443, t3))
in (mkImp _65_20444))
end
| (_, App ((True, _))) -> begin
(mkImp (t1, t2))
end
| (_, _) -> begin
(mkApp' (ITE, (t1)::(t2)::(t3)::[]))
end)
end))

let mkCases = (fun ( t ) -> (match (t) with
| [] -> begin
(failwith ("Impos"))
end
| hd::tl -> begin
(Support.List.fold_left (fun ( out ) ( t ) -> (mkAnd (out, t))) hd tl)
end))

let mkQuant = (fun ( _47_399 ) -> (match (_47_399) with
| (qop, pats, wopt, vars, body) -> begin
(match (((Support.List.length vars) = 0)) with
| true -> begin
body
end
| false -> begin
(match (body.tm) with
| App ((True, _)) -> begin
body
end
| _ -> begin
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
| _ -> begin
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
(let _65_20462 = (let _65_20461 = (Support.List.map (aux ix) tms)
in (op, _65_20461))
in (mkApp' _65_20462))
end
| Quant ((qop, pats, wopt, vars, body)) -> begin
(let n = (Support.List.length vars)
in (let _65_20465 = (let _65_20464 = (Support.Prims.pipe_right pats (Support.List.map (Support.List.map (aux (ix + n)))))
in (let _65_20463 = (aux (ix + n) body)
in (qop, _65_20464, wopt, vars, _65_20463)))
in (mkQuant _65_20465)))
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
(let _65_20475 = (let _65_20474 = (Support.List.map (aux shift) tms)
in (op, _65_20474))
in (mkApp' _65_20475))
end
| Quant ((qop, pats, wopt, vars, body)) -> begin
(let m = (Support.List.length vars)
in (let shift = (shift + m)
in (let _65_20478 = (let _65_20477 = (Support.Prims.pipe_right pats (Support.List.map (Support.List.map (aux shift))))
in (let _65_20476 = (aux shift body)
in (qop, _65_20477, wopt, vars, _65_20476)))
in (mkQuant _65_20478))))
end))
in (aux 0 t))))

let mkQuant' = (fun ( _47_477 ) -> (match (_47_477) with
| (qop, pats, wopt, vars, body) -> begin
(let _65_20484 = (let _65_20483 = (Support.Prims.pipe_right pats (Support.List.map (Support.List.map (abstr vars))))
in (let _65_20482 = (Support.List.map fv_sort vars)
in (let _65_20481 = (abstr vars body)
in (qop, _65_20483, wopt, _65_20482, _65_20481))))
in (mkQuant _65_20484))
end))

let mkForall'' = (fun ( _47_482 ) -> (match (_47_482) with
| (pats, wopt, sorts, body) -> begin
(mkQuant (Forall, pats, wopt, sorts, body))
end))

let mkForall' = (fun ( _47_487 ) -> (match (_47_487) with
| (pats, wopt, vars, body) -> begin
(mkQuant' (Forall, pats, wopt, vars, body))
end))

let mkForall = (fun ( _47_491 ) -> (match (_47_491) with
| (pats, vars, body) -> begin
(mkQuant' (Forall, (pats)::[], None, vars, body))
end))

let mkExists = (fun ( _47_495 ) -> (match (_47_495) with
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

type decls_t =
decl list

let mkDefineFun = (fun ( _47_513 ) -> (match (_47_513) with
| (nm, vars, s, tm, c) -> begin
(let _65_20543 = (let _65_20542 = (Support.List.map fv_sort vars)
in (let _65_20541 = (abstr vars tm)
in (nm, _65_20542, s, _65_20541, c)))
in DefineFun (_65_20543))
end))

let constr_id_of_sort = (fun ( sort ) -> (let _65_20546 = (strSort sort)
in (Support.Microsoft.FStar.Util.format1 "%s_constr_id" _65_20546)))

let fresh_token = (fun ( _47_517 ) ( id ) -> (match (_47_517) with
| (tok_name, sort) -> begin
(let _65_20559 = (let _65_20558 = (let _65_20557 = (let _65_20556 = (mkInteger' id)
in (let _65_20555 = (let _65_20554 = (let _65_20553 = (constr_id_of_sort sort)
in (let _65_20552 = (let _65_20551 = (mkApp (tok_name, []))
in (_65_20551)::[])
in (_65_20553, _65_20552)))
in (mkApp _65_20554))
in (_65_20556, _65_20555)))
in (mkEq _65_20557))
in (_65_20558, Some ("fresh token")))
in Assume (_65_20559))
end))

let constructor_to_decl = (fun ( _47_523 ) -> (match (_47_523) with
| (name, projectors, sort, id) -> begin
(let id = (Support.Microsoft.FStar.Util.string_of_int id)
in (let cdecl = (let _65_20563 = (let _65_20562 = (Support.Prims.pipe_right projectors (Support.List.map Support.Prims.snd))
in (name, _65_20562, sort, Some ("Constructor")))
in DeclFun (_65_20563))
in (let n_bvars = (Support.List.length projectors)
in (let bvar_name = (fun ( i ) -> (let _65_20566 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.String.strcat "x_" _65_20566)))
in (let bvar_index = (fun ( i ) -> (n_bvars - (i + 1)))
in (let bvar = (fun ( i ) ( s ) -> (let _65_20574 = (let _65_20573 = (bvar_name i)
in (_65_20573, s))
in (mkFreeV _65_20574)))
in (let bvars = (Support.Prims.pipe_right projectors (Support.List.mapi (fun ( i ) ( _47_538 ) -> (match (_47_538) with
| (_, s) -> begin
(bvar i s)
end))))
in (let bvar_names = (Support.List.map fv_of_term bvars)
in (let capp = (mkApp (name, bvars))
in (let cid_app = (let _65_20578 = (let _65_20577 = (constr_id_of_sort sort)
in (_65_20577, (capp)::[]))
in (mkApp _65_20578))
in (let cid = (let _65_20584 = (let _65_20583 = (let _65_20582 = (let _65_20581 = (let _65_20580 = (let _65_20579 = (mkInteger id)
in (_65_20579, cid_app))
in (mkEq _65_20580))
in ([], bvar_names, _65_20581))
in (mkForall _65_20582))
in (_65_20583, Some ("Constructor distinct")))
in Assume (_65_20584))
in (let disc_name = (Support.String.strcat "is-" name)
in (let xfv = ("x", sort)
in (let xx = (mkFreeV xfv)
in (let disc_eq = (let _65_20589 = (let _65_20588 = (let _65_20586 = (let _65_20585 = (constr_id_of_sort sort)
in (_65_20585, (xx)::[]))
in (mkApp _65_20586))
in (let _65_20587 = (mkInteger id)
in (_65_20588, _65_20587)))
in (mkEq _65_20589))
in (let proj_terms = (Support.Prims.pipe_right projectors (Support.List.map (fun ( _47_550 ) -> (match (_47_550) with
| (proj, s) -> begin
(mkApp (proj, (xx)::[]))
end))))
in (let disc_inv_body = (let _65_20592 = (let _65_20591 = (mkApp (name, proj_terms))
in (xx, _65_20591))
in (mkEq _65_20592))
in (let disc_ax = (mkAnd (disc_eq, disc_inv_body))
in (let disc = (mkDefineFun (disc_name, (xfv)::[], Bool_sort, disc_ax, Some ("Discriminator definition")))
in (let projs = (let _65_20603 = (Support.Prims.pipe_right projectors (Support.List.mapi (fun ( i ) ( _47_558 ) -> (match (_47_558) with
| (name, s) -> begin
(let cproj_app = (mkApp (name, (capp)::[]))
in (let _65_20602 = (let _65_20601 = (let _65_20600 = (let _65_20599 = (let _65_20598 = (let _65_20597 = (let _65_20596 = (let _65_20595 = (bvar i s)
in (cproj_app, _65_20595))
in (mkEq _65_20596))
in ((capp)::[], bvar_names, _65_20597))
in (mkForall _65_20598))
in (_65_20599, Some ("Projection inverse")))
in Assume (_65_20600))
in (_65_20601)::[])
in (DeclFun ((name, (sort)::[], s, Some ("Projector"))))::_65_20602))
end))))
in (Support.Prims.pipe_right _65_20603 Support.List.flatten))
in (let _65_20610 = (let _65_20606 = (let _65_20605 = (let _65_20604 = (Support.Microsoft.FStar.Util.format1 "<start constructor %s>" name)
in Caption (_65_20604))
in (_65_20605)::(cdecl)::(cid)::projs)
in (Support.List.append _65_20606 ((disc)::[])))
in (let _65_20609 = (let _65_20608 = (let _65_20607 = (Support.Microsoft.FStar.Util.format1 "</end constructor %s>" name)
in Caption (_65_20607))
in (_65_20608)::[])
in (Support.List.append _65_20610 _65_20609)))))))))))))))))))))))
end))

let name_binders_inner = (fun ( outer_names ) ( start ) ( sorts ) -> (let _47_580 = (Support.Prims.pipe_right sorts (Support.List.fold_left (fun ( _47_567 ) ( s ) -> (match (_47_567) with
| (names, binders, n) -> begin
(let prefix = (match (s) with
| Type_sort -> begin
"@a"
end
| Term_sort -> begin
"@x"
end
| _ -> begin
"@u"
end)
in (let nm = (let _65_20619 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.String.strcat prefix _65_20619))
in (let names = ((nm, s))::names
in (let b = (let _65_20620 = (strSort s)
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" nm _65_20620))
in (names, (b)::binders, (n + 1))))))
end)) (outer_names, [], start)))
in (match (_47_580) with
| (names, binders, n) -> begin
(names, (Support.List.rev binders), n)
end)))

let name_binders = (fun ( sorts ) -> (let _47_585 = (name_binders_inner [] 0 sorts)
in (match (_47_585) with
| (names, binders, n) -> begin
((Support.List.rev names), binders)
end)))

let termToSmt = (fun ( t ) -> (let rec aux = (fun ( n ) ( names ) ( t ) -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _65_20631 = (Support.List.nth names i)
in (Support.Prims.pipe_right _65_20631 Support.Prims.fst))
end
| FreeV (x) -> begin
(Support.Prims.fst x)
end
| App ((op, [])) -> begin
(op_to_string op)
end
| App ((op, tms)) -> begin
(let _65_20633 = (let _65_20632 = (Support.List.map (aux n names) tms)
in (Support.Prims.pipe_right _65_20632 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" (op_to_string op) _65_20633))
end
| Quant ((qop, pats, wopt, sorts, body)) -> begin
(let _47_615 = (name_binders_inner names n sorts)
in (match (_47_615) with
| (names, binders, n) -> begin
(let binders = (Support.Prims.pipe_right binders (Support.String.concat " "))
in (let pats_str = (match (pats) with
| ([]::[]) | ([]) -> begin
""
end
| _ -> begin
(let _65_20639 = (Support.Prims.pipe_right pats (Support.List.map (fun ( pats ) -> (let _65_20638 = (let _65_20637 = (Support.List.map (fun ( p ) -> (let _65_20636 = (aux n names p)
in (Support.Microsoft.FStar.Util.format1 "%s" _65_20636))) pats)
in (Support.String.concat " " _65_20637))
in (Support.Microsoft.FStar.Util.format1 "\n:pattern (%s)" _65_20638)))))
in (Support.Prims.pipe_right _65_20639 (Support.String.concat "\n")))
end)
in (match ((pats, wopt)) with
| (([]::[], None)) | (([], None)) -> begin
(let _65_20640 = (aux n names body)
in (Support.Microsoft.FStar.Util.format3 "(%s (%s)\n %s)" (qop_to_string qop) binders _65_20640))
end
| _ -> begin
(let _65_20642 = (aux n names body)
in (let _65_20641 = (weightToSmt wopt)
in (Support.Microsoft.FStar.Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _65_20642 _65_20641 pats_str)))
end)))
end))
end))
in (aux 0 [] t)))

let caption_to_string = (fun ( _47_6 ) -> (match (_47_6) with
| None -> begin
""
end
| Some (c) -> begin
(let _47_640 = (Support.Microsoft.FStar.Util.splitlines c)
in (match (_47_640) with
| hd::tl -> begin
(let suffix = (match (tl) with
| [] -> begin
""
end
| _ -> begin
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
(let _65_20651 = (Support.Prims.pipe_right (Support.Microsoft.FStar.Util.splitlines c) (fun ( _47_7 ) -> (match (_47_7) with
| [] -> begin
""
end
| h::t -> begin
h
end)))
in (Support.Microsoft.FStar.Util.format1 "\n; %s" _65_20651))
end
| DeclFun ((f, argsorts, retsort, c)) -> begin
(let l = (Support.List.map strSort argsorts)
in (let _65_20653 = (caption_to_string c)
in (let _65_20652 = (strSort retsort)
in (Support.Microsoft.FStar.Util.format4 "%s(declare-fun %s (%s) %s)" _65_20653 f (Support.String.concat " " l) _65_20652))))
end
| DefineFun ((f, arg_sorts, retsort, body, c)) -> begin
(let _47_671 = (name_binders arg_sorts)
in (match (_47_671) with
| (names, binders) -> begin
(let body = (let _65_20654 = (Support.List.map mkFreeV names)
in (inst _65_20654 body))
in (let _65_20657 = (caption_to_string c)
in (let _65_20656 = (strSort retsort)
in (let _65_20655 = (termToSmt body)
in (Support.Microsoft.FStar.Util.format5 "%s(define-fun %s (%s) %s\n %s)" _65_20657 f (Support.String.concat " " binders) _65_20656 _65_20655)))))
end))
end
| Assume ((t, c)) -> begin
(let _65_20659 = (caption_to_string c)
in (let _65_20658 = (termToSmt t)
in (Support.Microsoft.FStar.Util.format2 "%s(assert %s)" _65_20659 _65_20658)))
end
| Eval (t) -> begin
(let _65_20660 = (termToSmt t)
in (Support.Microsoft.FStar.Util.format1 "(eval %s)" _65_20660))
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
and mkPrelude = (fun ( z3options ) -> (let basic = (Support.String.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort String)\n(declare-fun String_constr_id (String) Int)\n\n(declare-sort Kind)\n(declare-fun Kind_constr_id (Kind) Int)\n\n(declare-sort Type)\n(declare-fun Type_constr_id (Type) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreKind (Type) Kind)\n(declare-fun PreType (Term) Type)\n(declare-fun Valid (Type) Bool)\n(declare-fun HasKind (Type Kind) Bool)\n(declare-fun HasType (Term Type) Bool)\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Type)) (HasType x t)))\n(declare-fun HasTypeFuel (Fuel Term Type) Bool)\n(declare-fun ApplyEF (Term Fuel) Term)\n(declare-fun ApplyEE (Term Term) Term)\n(declare-fun ApplyET (Term Type) Term)\n(declare-fun ApplyTE (Type Term) Type)\n(declare-fun ApplyTT (Type Type) Type)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsType (Type Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Type)\n(assert (forall ((e Term) (t Type))\n(!  (= (HasType e t)\n(HasTypeFuel MaxIFuel e t))\n:pattern ((HasType e t)))))\n(assert (forall ((f Fuel) (e Term) (t Type)) \n(! (= (HasTypeFuel (SFuel f) e t)\n(HasTypeFuel f e t))\n:pattern ((HasTypeFuel (SFuel f) e t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.Precedes ((a Type) (b Type) (t1 Term) (t2 Term)) Type\n(Precedes t1 t2))\n")
in (let constrs = (("String_const", (("String_const_proj_0", Int_sort))::[], String_sort, 0))::(("Kind_type", [], Kind_sort, 0))::(("Kind_arrow", (("Kind_arrow_id", Int_sort))::[], Kind_sort, 1))::(("Kind_uvar", (("Kind_uvar_fst", Int_sort))::[], Kind_sort, 2))::(("Typ_fun", (("Typ_fun_id", Int_sort))::[], Type_sort, 1))::(("Typ_app", (("Typ_app_fst", Type_sort))::(("Typ_app_snd", Type_sort))::[], Type_sort, 2))::(("Typ_dep", (("Typ_dep_fst", Type_sort))::(("Typ_dep_snd", Term_sort))::[], Type_sort, 3))::(("Typ_uvar", (("Typ_uvar_fst", Int_sort))::[], Type_sort, 4))::(("Term_unit", [], Term_sort, 0))::(("BoxInt", (("BoxInt_proj_0", Int_sort))::[], Term_sort, 1))::(("BoxBool", (("BoxBool_proj_0", Bool_sort))::[], Term_sort, 2))::(("BoxString", (("BoxString_proj_0", String_sort))::[], Term_sort, 3))::(("BoxRef", (("BoxRef_proj_0", Ref_sort))::[], Term_sort, 4))::(("Exp_uvar", (("Exp_uvar_fst", Int_sort))::[], Term_sort, 5))::(("LexCons", (("LexCons_0", Term_sort))::(("LexCons_1", Term_sort))::[], Term_sort, 6))::[]
in (let bcons = (let _65_20663 = (let _65_20662 = (Support.Prims.pipe_right constrs (Support.List.collect constructor_to_decl))
in (Support.Prims.pipe_right _65_20662 (Support.List.map (declToSmt z3options))))
in (Support.Prims.pipe_right _65_20663 (Support.String.concat "\n")))
in (let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Support.String.strcat (Support.String.strcat basic bcons) lex_ordering))))))

let mk_Kind_type = (mkApp ("Kind_type", []))

let mk_Kind_uvar = (fun ( i ) -> (let _65_20668 = (let _65_20667 = (let _65_20666 = (mkInteger' i)
in (_65_20666)::[])
in ("Kind_uvar", _65_20667))
in (mkApp _65_20668)))

let mk_Typ_app = (fun ( t1 ) ( t2 ) -> (mkApp ("Typ_app", (t1)::(t2)::[])))

let mk_Typ_dep = (fun ( t1 ) ( t2 ) -> (mkApp ("Typ_dep", (t1)::(t2)::[])))

let mk_Typ_uvar = (fun ( i ) -> (let _65_20681 = (let _65_20680 = (let _65_20679 = (mkInteger' i)
in (_65_20679)::[])
in ("Typ_uvar", _65_20680))
in (mkApp _65_20681)))

let mk_Exp_uvar = (fun ( i ) -> (let _65_20686 = (let _65_20685 = (let _65_20684 = (mkInteger' i)
in (_65_20684)::[])
in ("Exp_uvar", _65_20685))
in (mkApp _65_20686)))

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
| _ -> begin
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
| _ -> begin
(raise (Support.Microsoft.FStar.Util.Impos))
end))

let mk_PreKind = (fun ( t ) -> (mkApp ("PreKind", (t)::[])))

let mk_PreType = (fun ( t ) -> (mkApp ("PreType", (t)::[])))

let mk_Valid = (fun ( t ) -> (mkApp ("Valid", (t)::[])))

let mk_HasType = (fun ( v ) ( t ) -> (mkApp ("HasType", (v)::(t)::[])))

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

let mk_String_const = (fun ( i ) -> (let _65_20771 = (let _65_20770 = (let _65_20769 = (mkInteger' i)
in (_65_20769)::[])
in ("String_const", _65_20770))
in (mkApp _65_20771)))

let mk_Precedes = (fun ( x1 ) ( x2 ) -> (let _65_20776 = (mkApp ("Precedes", (x1)::(x2)::[]))
in (Support.Prims.pipe_right _65_20776 mk_Valid)))

let mk_LexCons = (fun ( x1 ) ( x2 ) -> (mkApp ("LexCons", (x1)::(x2)::[])))

let rec n_fuel = (fun ( n ) -> (match ((n = 0)) with
| true -> begin
(mkApp ("ZFuel", []))
end
| false -> begin
(let _65_20785 = (let _65_20784 = (let _65_20783 = (n_fuel (n - 1))
in (_65_20783)::[])
in ("SFuel", _65_20784))
in (mkApp _65_20785))
end))

let fuel_2 = (n_fuel 2)

let fuel_100 = (n_fuel 100)

let mk_and_opt = (fun ( p1 ) ( p2 ) -> (match ((p1, p2)) with
| (Some (p1), Some (p2)) -> begin
(let _65_20790 = (mkAnd (p1, p2))
in Some (_65_20790))
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
(let _65_20807 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "BoundV %s" _65_20807))
end
| FreeV (fv) -> begin
(Support.Microsoft.FStar.Util.format1 "FreeV %s" (Support.Prims.fst fv))
end
| App ((op, l)) -> begin
(let _65_20808 = (print_smt_term_list l)
in (Support.Microsoft.FStar.Util.format2 "App %s [ %s ]" (op_to_string op) _65_20808))
end
| Quant ((qop, l, _, _, t)) -> begin
(let _65_20810 = (print_smt_term_list_list l)
in (let _65_20809 = (print_smt_term t)
in (Support.Microsoft.FStar.Util.format3 "Quant %s %s %s" (qop_to_string qop) _65_20810 _65_20809)))
end))
and print_smt_term_list = (fun ( l ) -> (Support.List.fold_left (fun ( s ) ( t ) -> (let _65_20814 = (print_smt_term t)
in (Support.String.strcat (Support.String.strcat s "; ") _65_20814))) "" l))
and print_smt_term_list_list = (fun ( l ) -> (Support.List.fold_left (fun ( s ) ( l ) -> (let _65_20819 = (let _65_20818 = (print_smt_term_list l)
in (Support.String.strcat (Support.String.strcat s "; [ ") _65_20818))
in (Support.String.strcat _65_20819 " ] "))) "" l))




