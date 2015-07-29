
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

let rec strSort = (fun ( x  :  sort ) -> (match (x) with
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
(let _52_17011 = (strSort s1)
in (let _52_17010 = (strSort s2)
in (Support.Microsoft.FStar.Util.format2 "(Array %s %s)" _52_17011 _52_17010)))
end
| Arrow ((s1, s2)) -> begin
(let _52_17013 = (strSort s1)
in (let _52_17012 = (strSort s2)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _52_17013 _52_17012)))
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

let is_Mkterm = (fun ( _  :  term ) -> (failwith ("Not yet implemented")))

let fv_eq = (fun ( x  :  fv ) ( y  :  fv ) -> ((Support.Prims.fst x) = (Support.Prims.fst y)))

let fv_sort = (fun ( x  :  ('u47u1173 * 'u47u1172) ) -> (Support.Prims.snd x))

let freevar_eq = (fun ( x  :  term ) ( y  :  term ) -> (match ((x.tm, y.tm)) with
| (FreeV (x), FreeV (y)) -> begin
(fv_eq x y)
end
| _ -> begin
false
end))

let freevar_sort = (fun ( _47_1  :  term ) -> (match (_47_1) with
| {tm = FreeV (x); hash = _; freevars = _} -> begin
(fv_sort x)
end
| _ -> begin
(failwith ("impossible"))
end))

let fv_of_term = (fun ( _47_2  :  term ) -> (match (_47_2) with
| {tm = FreeV (fv); hash = _; freevars = _} -> begin
fv
end
| _ -> begin
(failwith ("impossible"))
end))

let rec freevars = (fun ( t  :  term ) -> (match (t.tm) with
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

let free_variables = (fun ( t  :  term ) -> (match ((Support.ST.read t.freevars)) with
| Some (b) -> begin
b
end
| None -> begin
(let fvs = (let _52_17104 = (freevars t)
in (Support.Microsoft.FStar.Util.remove_dups fv_eq _52_17104))
in (let _47_111 = (Support.ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))

let qop_to_string = (fun ( _47_3  :  qop ) -> (match (_47_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))

let op_to_string = (fun ( _47_4  :  op ) -> (match (_47_4) with
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

let weightToSmt = (fun ( _47_5  :  int option ) -> (match (_47_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _52_17111 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format1 ":weight %s\n" _52_17111))
end))

let rec hash_of_term' = (fun ( t  :  term' ) -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _52_17114 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.String.strcat "@" _52_17114))
end
| FreeV (x) -> begin
(let _52_17115 = (strSort (Support.Prims.snd x))
in (Support.String.strcat (Support.String.strcat (Support.Prims.fst x) ":") _52_17115))
end
| App ((op, tms)) -> begin
(let _52_17119 = (let _52_17118 = (let _52_17117 = (Support.List.map (fun ( t  :  term ) -> t.hash) tms)
in (Support.Prims.pipe_right _52_17117 (Support.String.concat " ")))
in (Support.String.strcat (Support.String.strcat "(" (op_to_string op)) _52_17118))
in (Support.String.strcat _52_17119 ")"))
end
| Quant ((qop, pats, wopt, sorts, body)) -> begin
(let _52_17127 = (let _52_17120 = (Support.List.map strSort sorts)
in (Support.Prims.pipe_right _52_17120 (Support.String.concat " ")))
in (let _52_17126 = (weightToSmt wopt)
in (let _52_17125 = (let _52_17124 = (Support.Prims.pipe_right pats (Support.List.map (fun ( pats  :  term list ) -> (let _52_17123 = (Support.List.map (fun ( p  :  term ) -> p.hash) pats)
in (Support.Prims.pipe_right _52_17123 (Support.String.concat " "))))))
in (Support.Prims.pipe_right _52_17124 (Support.String.concat "; ")))
in (Support.Microsoft.FStar.Util.format5 "(%s (%s)(! %s %s %s))" (qop_to_string qop) _52_17127 body.hash _52_17126 _52_17125))))
end))

let all_terms_l = (let _52_17129 = (let _52_17128 = (Support.Microsoft.FStar.Util.smap_create 10000)
in (_52_17128)::[])
in (ref _52_17129))

let all_terms = (fun ( _47_163  :  unit ) -> (match (()) with
| () -> begin
(let _52_17132 = (Support.ST.read all_terms_l)
in (Support.List.hd _52_17132))
end))

let push = (fun ( _47_164  :  unit ) -> ())

let pop = (fun ( _47_165  :  unit ) -> ())

let commit_mark = (fun ( _47_166  :  unit ) -> ())

let mk = (fun ( t  :  term' ) -> (let key = (hash_of_term' t)
in (match ((let _52_17141 = (all_terms ())
in (Support.Microsoft.FStar.Util.smap_try_find _52_17141 key))) with
| Some (tm) -> begin
tm
end
| None -> begin
(let tm = (let _52_17142 = (Support.Microsoft.FStar.Util.mk_ref None)
in {tm = t; hash = key; freevars = _52_17142})
in (let _47_173 = (let _52_17143 = (all_terms ())
in (Support.Microsoft.FStar.Util.smap_add _52_17143 key tm))
in tm))
end)))

let mkTrue = (mk (App ((True, []))))

let mkFalse = (mk (App ((False, []))))

let mkInteger = (fun ( i  :  string ) -> (mk (Integer (i))))

let mkInteger' = (fun ( i  :  int ) -> (let _52_17148 = (Support.Microsoft.FStar.Util.string_of_int i)
in (mkInteger _52_17148)))

let mkBoundV = (fun ( i  :  int ) -> (mk (BoundV (i))))

let mkFreeV = (fun ( x  :  (string * sort) ) -> (mk (FreeV (x))))

let mkApp' = (fun ( f  :  (op * term list) ) -> (mk (App (f))))

let mkApp = (fun ( _47_182  :  (string * term list) ) -> (match (_47_182) with
| (s, args) -> begin
(mk (App ((Var (s), args))))
end))

let mkNot = (fun ( t  :  term ) -> (match (t.tm) with
| App ((True, _)) -> begin
mkFalse
end
| App ((False, _)) -> begin
mkTrue
end
| _ -> begin
(mkApp' (Not, (t)::[]))
end))

let mkAnd = (fun ( _47_198  :  (term * term) ) -> (match (_47_198) with
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

let mkOr = (fun ( _47_258  :  (term * term) ) -> (match (_47_258) with
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

let mkImp = (fun ( _47_318  :  (term * term) ) -> (match (_47_318) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (_, App ((True, _))) -> begin
mkTrue
end
| (App ((True, _)), _) -> begin
t2
end
| (_, App ((Imp, t1'::t2'::[]))) -> begin
(let _52_17167 = (let _52_17166 = (let _52_17165 = (mkAnd (t1, t1'))
in (_52_17165)::(t2')::[])
in (Imp, _52_17166))
in (mkApp' _52_17167))
end
| _ -> begin
(mkApp' (Imp, (t1)::(t2)::[]))
end)
end))

let mk_bin_op = (fun ( op  :  op ) ( _47_349  :  (term * term) ) -> (match (_47_349) with
| (t1, t2) -> begin
(mkApp' (op, (t1)::(t2)::[]))
end))

let mkMinus = (fun ( t  :  term ) -> (mkApp' (Minus, (t)::[])))

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

let mkITE = (fun ( _47_354  :  (term * term * term) ) -> (match (_47_354) with
| (t1, t2, t3) -> begin
(match ((t2.tm, t3.tm)) with
| (App ((True, _)), App ((True, _))) -> begin
mkTrue
end
| (App ((True, _)), _) -> begin
(let _52_17188 = (let _52_17187 = (mkNot t1)
in (_52_17187, t3))
in (mkImp _52_17188))
end
| (_, App ((True, _))) -> begin
(mkImp (t1, t2))
end
| (_, _) -> begin
(mkApp' (ITE, (t1)::(t2)::(t3)::[]))
end)
end))

let mkCases = (fun ( t  :  term list ) -> (match (t) with
| [] -> begin
(failwith ("Impos"))
end
| hd::tl -> begin
(Support.List.fold_left (fun ( out  :  term ) ( t  :  term ) -> (mkAnd (out, t))) hd tl)
end))

let mkQuant = (fun ( _47_399  :  (qop * pat list list * int option * sort list * term) ) -> (match (_47_399) with
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

let abstr = (fun ( fvs  :  fv list ) ( t  :  term ) -> (let nvars = (Support.List.length fvs)
in (let index_of = (fun ( fv  :  fv ) -> (match ((Support.Microsoft.FStar.Util.try_find_index (fv_eq fv) fvs)) with
| None -> begin
None
end
| Some (i) -> begin
Some ((nvars - (i + 1)))
end))
in (let rec aux = (fun ( ix  :  int ) ( t  :  term ) -> (match ((Support.ST.read t.freevars)) with
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
(let _52_17206 = (let _52_17205 = (Support.List.map (aux ix) tms)
in (op, _52_17205))
in (mkApp' _52_17206))
end
| Quant ((qop, pats, wopt, vars, body)) -> begin
(let n = (Support.List.length vars)
in (let _52_17209 = (let _52_17208 = (Support.Prims.pipe_right pats (Support.List.map (Support.List.map (aux (ix + n)))))
in (let _52_17207 = (aux (ix + n) body)
in (qop, _52_17208, wopt, vars, _52_17207)))
in (mkQuant _52_17209)))
end)
end))
in (aux 0 t)))))

let inst = (fun ( tms  :  term list ) ( t  :  term ) -> (let n = (Support.List.length tms)
in (let rec aux = (fun ( shift  :  int ) ( t  :  term ) -> (match (t.tm) with
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
(let _52_17219 = (let _52_17218 = (Support.List.map (aux shift) tms)
in (op, _52_17218))
in (mkApp' _52_17219))
end
| Quant ((qop, pats, wopt, vars, body)) -> begin
(let m = (Support.List.length vars)
in (let shift = (shift + m)
in (let _52_17222 = (let _52_17221 = (Support.Prims.pipe_right pats (Support.List.map (Support.List.map (aux shift))))
in (let _52_17220 = (aux shift body)
in (qop, _52_17221, wopt, vars, _52_17220)))
in (mkQuant _52_17222))))
end))
in (aux 0 t))))

let mkQuant' = (fun ( _47_477  :  (qop * term list list * int option * fv list * term) ) -> (match (_47_477) with
| (qop, pats, wopt, vars, body) -> begin
(let _52_17228 = (let _52_17227 = (Support.Prims.pipe_right pats (Support.List.map (Support.List.map (abstr vars))))
in (let _52_17226 = (Support.List.map fv_sort vars)
in (let _52_17225 = (abstr vars body)
in (qop, _52_17227, wopt, _52_17226, _52_17225))))
in (mkQuant _52_17228))
end))

let mkForall'' = (fun ( _47_482  :  (pat list list * int option * sort list * term) ) -> (match (_47_482) with
| (pats, wopt, sorts, body) -> begin
(mkQuant (Forall, pats, wopt, sorts, body))
end))

let mkForall' = (fun ( _47_487  :  (pat list list * int option * fvs * term) ) -> (match (_47_487) with
| (pats, wopt, vars, body) -> begin
(mkQuant' (Forall, pats, wopt, vars, body))
end))

let mkForall = (fun ( _47_491  :  (pat list * fvs * term) ) -> (match (_47_491) with
| (pats, vars, body) -> begin
(mkQuant' (Forall, (pats)::[], None, vars, body))
end))

let mkExists = (fun ( _47_495  :  (pat list * fvs * term) ) -> (match (_47_495) with
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

let mkDefineFun = (fun ( _47_513  :  (string * (string * sort) list * sort * term * caption) ) -> (match (_47_513) with
| (nm, vars, s, tm, c) -> begin
(let _52_17287 = (let _52_17286 = (Support.List.map fv_sort vars)
in (let _52_17285 = (abstr vars tm)
in (nm, _52_17286, s, _52_17285, c)))
in DefineFun (_52_17287))
end))

let constr_id_of_sort = (fun ( sort  :  sort ) -> (let _52_17290 = (strSort sort)
in (Support.Microsoft.FStar.Util.format1 "%s_constr_id" _52_17290)))

let fresh_token = (fun ( _47_517  :  (string * sort) ) ( id  :  int ) -> (match (_47_517) with
| (tok_name, sort) -> begin
(let _52_17303 = (let _52_17302 = (let _52_17301 = (let _52_17300 = (mkInteger' id)
in (let _52_17299 = (let _52_17298 = (let _52_17297 = (constr_id_of_sort sort)
in (let _52_17296 = (let _52_17295 = (mkApp (tok_name, []))
in (_52_17295)::[])
in (_52_17297, _52_17296)))
in (mkApp _52_17298))
in (_52_17300, _52_17299)))
in (mkEq _52_17301))
in (_52_17302, Some ("fresh token")))
in Assume (_52_17303))
end))

let constructor_to_decl = (fun ( _47_523  :  constructor_t ) -> (match (_47_523) with
| (name, projectors, sort, id) -> begin
(let id = (Support.Microsoft.FStar.Util.string_of_int id)
in (let cdecl = (let _52_17307 = (let _52_17306 = (Support.Prims.pipe_right projectors (Support.List.map Support.Prims.snd))
in (name, _52_17306, sort, Some ("Constructor")))
in DeclFun (_52_17307))
in (let n_bvars = (Support.List.length projectors)
in (let bvar_name = (fun ( i  :  int ) -> (let _52_17310 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.String.strcat "x_" _52_17310)))
in (let bvar_index = (fun ( i  :  int ) -> (n_bvars - (i + 1)))
in (let bvar = (fun ( i  :  int ) ( s  :  sort ) -> (let _52_17318 = (let _52_17317 = (bvar_name i)
in (_52_17317, s))
in (mkFreeV _52_17318)))
in (let bvars = (Support.Prims.pipe_right projectors (Support.List.mapi (fun ( i  :  int ) ( _47_538  :  (string * sort) ) -> (match (_47_538) with
| (_, s) -> begin
(bvar i s)
end))))
in (let bvar_names = (Support.List.map fv_of_term bvars)
in (let capp = (mkApp (name, bvars))
in (let cid_app = (let _52_17322 = (let _52_17321 = (constr_id_of_sort sort)
in (_52_17321, (capp)::[]))
in (mkApp _52_17322))
in (let cid = (let _52_17328 = (let _52_17327 = (let _52_17326 = (let _52_17325 = (let _52_17324 = (let _52_17323 = (mkInteger id)
in (_52_17323, cid_app))
in (mkEq _52_17324))
in ([], bvar_names, _52_17325))
in (mkForall _52_17326))
in (_52_17327, Some ("Constructor distinct")))
in Assume (_52_17328))
in (let disc_name = (Support.String.strcat "is-" name)
in (let xfv = ("x", sort)
in (let xx = (mkFreeV xfv)
in (let disc_eq = (let _52_17333 = (let _52_17332 = (let _52_17330 = (let _52_17329 = (constr_id_of_sort sort)
in (_52_17329, (xx)::[]))
in (mkApp _52_17330))
in (let _52_17331 = (mkInteger id)
in (_52_17332, _52_17331)))
in (mkEq _52_17333))
in (let proj_terms = (Support.Prims.pipe_right projectors (Support.List.map (fun ( _47_550  :  (string * sort) ) -> (match (_47_550) with
| (proj, s) -> begin
(mkApp (proj, (xx)::[]))
end))))
in (let disc_inv_body = (let _52_17336 = (let _52_17335 = (mkApp (name, proj_terms))
in (xx, _52_17335))
in (mkEq _52_17336))
in (let disc_ax = (mkAnd (disc_eq, disc_inv_body))
in (let disc = (mkDefineFun (disc_name, (xfv)::[], Bool_sort, disc_ax, Some ("Discriminator definition")))
in (let projs = (let _52_17347 = (Support.Prims.pipe_right projectors (Support.List.mapi (fun ( i  :  int ) ( _47_558  :  (string * sort) ) -> (match (_47_558) with
| (name, s) -> begin
(let cproj_app = (mkApp (name, (capp)::[]))
in (let _52_17346 = (let _52_17345 = (let _52_17344 = (let _52_17343 = (let _52_17342 = (let _52_17341 = (let _52_17340 = (let _52_17339 = (bvar i s)
in (cproj_app, _52_17339))
in (mkEq _52_17340))
in ((capp)::[], bvar_names, _52_17341))
in (mkForall _52_17342))
in (_52_17343, Some ("Projection inverse")))
in Assume (_52_17344))
in (_52_17345)::[])
in (DeclFun ((name, (sort)::[], s, Some ("Projector"))))::_52_17346))
end))))
in (Support.Prims.pipe_right _52_17347 Support.List.flatten))
in (let _52_17354 = (let _52_17350 = (let _52_17349 = (let _52_17348 = (Support.Microsoft.FStar.Util.format1 "<start constructor %s>" name)
in Caption (_52_17348))
in (_52_17349)::(cdecl)::(cid)::projs)
in (Support.List.append _52_17350 ((disc)::[])))
in (let _52_17353 = (let _52_17352 = (let _52_17351 = (Support.Microsoft.FStar.Util.format1 "</end constructor %s>" name)
in Caption (_52_17351))
in (_52_17352)::[])
in (Support.List.append _52_17354 _52_17353)))))))))))))))))))))))
end))

let name_binders_inner = (fun ( outer_names  :  (string * sort) list ) ( start  :  int ) ( sorts  :  sort list ) -> (let _47_580 = (Support.Prims.pipe_right sorts (Support.List.fold_left (fun ( _47_567  :  ((string * sort) list * string list * int) ) ( s  :  sort ) -> (match (_47_567) with
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
in (let nm = (let _52_17363 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.String.strcat prefix _52_17363))
in (let names = ((nm, s))::names
in (let b = (let _52_17364 = (strSort s)
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" nm _52_17364))
in (names, (b)::binders, (n + 1))))))
end)) (outer_names, [], start)))
in (match (_47_580) with
| (names, binders, n) -> begin
(names, (Support.List.rev binders), n)
end)))

let name_binders = (fun ( sorts  :  sort list ) -> (let _47_585 = (name_binders_inner [] 0 sorts)
in (match (_47_585) with
| (names, binders, n) -> begin
((Support.List.rev names), binders)
end)))

let termToSmt = (fun ( t  :  term ) -> (let rec aux = (fun ( n  :  int ) ( names  :  fv list ) ( t  :  term ) -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _52_17375 = (Support.List.nth names i)
in (Support.Prims.pipe_right _52_17375 Support.Prims.fst))
end
| FreeV (x) -> begin
(Support.Prims.fst x)
end
| App ((op, [])) -> begin
(op_to_string op)
end
| App ((op, tms)) -> begin
(let _52_17377 = (let _52_17376 = (Support.List.map (aux n names) tms)
in (Support.Prims.pipe_right _52_17376 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" (op_to_string op) _52_17377))
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
(let _52_17383 = (Support.Prims.pipe_right pats (Support.List.map (fun ( pats  :  term list ) -> (let _52_17382 = (let _52_17381 = (Support.List.map (fun ( p  :  term ) -> (let _52_17380 = (aux n names p)
in (Support.Microsoft.FStar.Util.format1 "%s" _52_17380))) pats)
in (Support.String.concat " " _52_17381))
in (Support.Microsoft.FStar.Util.format1 "\n:pattern (%s)" _52_17382)))))
in (Support.Prims.pipe_right _52_17383 (Support.String.concat "\n")))
end)
in (match ((pats, wopt)) with
| (([]::[], None)) | (([], None)) -> begin
(let _52_17384 = (aux n names body)
in (Support.Microsoft.FStar.Util.format3 "(%s (%s)\n %s)" (qop_to_string qop) binders _52_17384))
end
| _ -> begin
(let _52_17386 = (aux n names body)
in (let _52_17385 = (weightToSmt wopt)
in (Support.Microsoft.FStar.Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _52_17386 _52_17385 pats_str)))
end)))
end))
end))
in (aux 0 [] t)))

let caption_to_string = (fun ( _47_6  :  string option ) -> (match (_47_6) with
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

let rec declToSmt = (fun ( z3options  :  string ) ( decl  :  decl ) -> (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(let _52_17395 = (Support.Prims.pipe_right (Support.Microsoft.FStar.Util.splitlines c) (fun ( _47_7  :  string list ) -> (match (_47_7) with
| [] -> begin
""
end
| h::t -> begin
h
end)))
in (Support.Microsoft.FStar.Util.format1 "\n; %s" _52_17395))
end
| DeclFun ((f, argsorts, retsort, c)) -> begin
(let l = (Support.List.map strSort argsorts)
in (let _52_17397 = (caption_to_string c)
in (let _52_17396 = (strSort retsort)
in (Support.Microsoft.FStar.Util.format4 "%s(declare-fun %s (%s) %s)" _52_17397 f (Support.String.concat " " l) _52_17396))))
end
| DefineFun ((f, arg_sorts, retsort, body, c)) -> begin
(let _47_671 = (name_binders arg_sorts)
in (match (_47_671) with
| (names, binders) -> begin
(let body = (let _52_17398 = (Support.List.map mkFreeV names)
in (inst _52_17398 body))
in (let _52_17401 = (caption_to_string c)
in (let _52_17400 = (strSort retsort)
in (let _52_17399 = (termToSmt body)
in (Support.Microsoft.FStar.Util.format5 "%s(define-fun %s (%s) %s\n %s)" _52_17401 f (Support.String.concat " " binders) _52_17400 _52_17399)))))
end))
end
| Assume ((t, c)) -> begin
(let _52_17403 = (caption_to_string c)
in (let _52_17402 = (termToSmt t)
in (Support.Microsoft.FStar.Util.format2 "%s(assert %s)" _52_17403 _52_17402)))
end
| Eval (t) -> begin
(let _52_17404 = (termToSmt t)
in (Support.Microsoft.FStar.Util.format1 "(eval %s)" _52_17404))
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
and mkPrelude = (fun ( z3options  :  string ) -> (let basic = (Support.String.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort String)\n(declare-fun String_constr_id (String) Int)\n\n(declare-sort Kind)\n(declare-fun Kind_constr_id (Kind) Int)\n\n(declare-sort Type)\n(declare-fun Type_constr_id (Type) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreKind (Type) Kind)\n(declare-fun PreType (Term) Type)\n(declare-fun Valid (Type) Bool)\n(declare-fun HasKind (Type Kind) Bool)\n(declare-fun HasType (Term Type) Bool)\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Type)) (HasType x t)))\n(declare-fun HasTypeFuel (Fuel Term Type) Bool)\n(declare-fun ApplyEF (Term Fuel) Term)\n(declare-fun ApplyEE (Term Term) Term)\n(declare-fun ApplyET (Term Type) Term)\n(declare-fun ApplyTE (Type Term) Type)\n(declare-fun ApplyTT (Type Type) Type)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsType (Type Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Type)\n(assert (forall ((e Term) (t Type))\n(!  (= (HasType e t)\n(HasTypeFuel MaxIFuel e t))\n:pattern ((HasType e t)))))\n(assert (forall ((f Fuel) (e Term) (t Type)) \n(! (= (HasTypeFuel (SFuel f) e t)\n(HasTypeFuel f e t))\n:pattern ((HasTypeFuel (SFuel f) e t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.Precedes ((a Type) (b Type) (t1 Term) (t2 Term)) Type\n(Precedes t1 t2))\n")
in (let constrs = (("String_const", (("String_const_proj_0", Int_sort))::[], String_sort, 0))::(("Kind_type", [], Kind_sort, 0))::(("Kind_arrow", (("Kind_arrow_id", Int_sort))::[], Kind_sort, 1))::(("Kind_uvar", (("Kind_uvar_fst", Int_sort))::[], Kind_sort, 2))::(("Typ_fun", (("Typ_fun_id", Int_sort))::[], Type_sort, 1))::(("Typ_app", (("Typ_app_fst", Type_sort))::(("Typ_app_snd", Type_sort))::[], Type_sort, 2))::(("Typ_dep", (("Typ_dep_fst", Type_sort))::(("Typ_dep_snd", Term_sort))::[], Type_sort, 3))::(("Typ_uvar", (("Typ_uvar_fst", Int_sort))::[], Type_sort, 4))::(("Term_unit", [], Term_sort, 0))::(("BoxInt", (("BoxInt_proj_0", Int_sort))::[], Term_sort, 1))::(("BoxBool", (("BoxBool_proj_0", Bool_sort))::[], Term_sort, 2))::(("BoxString", (("BoxString_proj_0", String_sort))::[], Term_sort, 3))::(("BoxRef", (("BoxRef_proj_0", Ref_sort))::[], Term_sort, 4))::(("Exp_uvar", (("Exp_uvar_fst", Int_sort))::[], Term_sort, 5))::(("LexCons", (("LexCons_0", Term_sort))::(("LexCons_1", Term_sort))::[], Term_sort, 6))::[]
in (let bcons = (let _52_17407 = (let _52_17406 = (Support.Prims.pipe_right constrs (Support.List.collect constructor_to_decl))
in (Support.Prims.pipe_right _52_17406 (Support.List.map (declToSmt z3options))))
in (Support.Prims.pipe_right _52_17407 (Support.String.concat "\n")))
in (let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Support.String.strcat (Support.String.strcat basic bcons) lex_ordering))))))

let mk_Kind_type = (mkApp ("Kind_type", []))

let mk_Kind_uvar = (fun ( i  :  int ) -> (let _52_17412 = (let _52_17411 = (let _52_17410 = (mkInteger' i)
in (_52_17410)::[])
in ("Kind_uvar", _52_17411))
in (mkApp _52_17412)))

let mk_Typ_app = (fun ( t1  :  term ) ( t2  :  term ) -> (mkApp ("Typ_app", (t1)::(t2)::[])))

let mk_Typ_dep = (fun ( t1  :  term ) ( t2  :  term ) -> (mkApp ("Typ_dep", (t1)::(t2)::[])))

let mk_Typ_uvar = (fun ( i  :  int ) -> (let _52_17425 = (let _52_17424 = (let _52_17423 = (mkInteger' i)
in (_52_17423)::[])
in ("Typ_uvar", _52_17424))
in (mkApp _52_17425)))

let mk_Exp_uvar = (fun ( i  :  int ) -> (let _52_17430 = (let _52_17429 = (let _52_17428 = (mkInteger' i)
in (_52_17428)::[])
in ("Exp_uvar", _52_17429))
in (mkApp _52_17430)))

let mk_Term_unit = (mkApp ("Term_unit", []))

let boxInt = (fun ( t  :  term ) -> (mkApp ("BoxInt", (t)::[])))

let unboxInt = (fun ( t  :  term ) -> (mkApp ("BoxInt_proj_0", (t)::[])))

let boxBool = (fun ( t  :  term ) -> (mkApp ("BoxBool", (t)::[])))

let unboxBool = (fun ( t  :  term ) -> (mkApp ("BoxBool_proj_0", (t)::[])))

let boxString = (fun ( t  :  term ) -> (mkApp ("BoxString", (t)::[])))

let unboxString = (fun ( t  :  term ) -> (mkApp ("BoxString_proj_0", (t)::[])))

let boxRef = (fun ( t  :  term ) -> (mkApp ("BoxRef", (t)::[])))

let unboxRef = (fun ( t  :  term ) -> (mkApp ("BoxRef_proj_0", (t)::[])))

let boxTerm = (fun ( sort  :  sort ) ( t  :  term ) -> (match (sort) with
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

let unboxTerm = (fun ( sort  :  sort ) ( t  :  term ) -> (match (sort) with
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

let mk_PreKind = (fun ( t  :  term ) -> (mkApp ("PreKind", (t)::[])))

let mk_PreType = (fun ( t  :  term ) -> (mkApp ("PreType", (t)::[])))

let mk_Valid = (fun ( t  :  term ) -> (mkApp ("Valid", (t)::[])))

let mk_HasType = (fun ( v  :  term ) ( t  :  term ) -> (mkApp ("HasType", (v)::(t)::[])))

let mk_IsTyped = (fun ( v  :  term ) -> (mkApp ("IsTyped", (v)::[])))

let mk_HasTypeFuel = (fun ( f  :  term ) ( v  :  term ) ( t  :  term ) -> (match ((Support.ST.read Microsoft_FStar_Options.unthrottle_inductives)) with
| true -> begin
(mk_HasType v t)
end
| false -> begin
(mkApp ("HasTypeFuel", (f)::(v)::(t)::[]))
end))

let mk_HasTypeWithFuel = (fun ( f  :  term option ) ( v  :  term ) ( t  :  term ) -> (match (f) with
| None -> begin
(mk_HasType v t)
end
| Some (f) -> begin
(mk_HasTypeFuel f v t)
end))

let mk_Destruct = (fun ( v  :  term ) -> (mkApp ("Destruct", (v)::[])))

let mk_HasKind = (fun ( t  :  term ) ( k  :  term ) -> (mkApp ("HasKind", (t)::(k)::[])))

let mk_Rank = (fun ( x  :  term ) -> (mkApp ("Rank", (x)::[])))

let mk_tester = (fun ( n  :  string ) ( t  :  term ) -> (mkApp ((Support.String.strcat "is-" n), (t)::[])))

let mk_ApplyTE = (fun ( t  :  term ) ( e  :  term ) -> (mkApp ("ApplyTE", (t)::(e)::[])))

let mk_ApplyTT = (fun ( t  :  term ) ( t'  :  term ) -> (mkApp ("ApplyTT", (t)::(t')::[])))

let mk_ApplyET = (fun ( e  :  term ) ( t  :  term ) -> (mkApp ("ApplyET", (e)::(t)::[])))

let mk_ApplyEE = (fun ( e  :  term ) ( e'  :  term ) -> (mkApp ("ApplyEE", (e)::(e')::[])))

let mk_ApplyEF = (fun ( e  :  term ) ( f  :  term ) -> (mkApp ("ApplyEF", (e)::(f)::[])))

let mk_String_const = (fun ( i  :  int ) -> (let _52_17515 = (let _52_17514 = (let _52_17513 = (mkInteger' i)
in (_52_17513)::[])
in ("String_const", _52_17514))
in (mkApp _52_17515)))

let mk_Precedes = (fun ( x1  :  term ) ( x2  :  term ) -> (let _52_17520 = (mkApp ("Precedes", (x1)::(x2)::[]))
in (Support.Prims.pipe_right _52_17520 mk_Valid)))

let mk_LexCons = (fun ( x1  :  term ) ( x2  :  term ) -> (mkApp ("LexCons", (x1)::(x2)::[])))

let rec n_fuel = (fun ( n  :  int ) -> (match ((n = 0)) with
| true -> begin
(mkApp ("ZFuel", []))
end
| false -> begin
(let _52_17529 = (let _52_17528 = (let _52_17527 = (n_fuel (n - 1))
in (_52_17527)::[])
in ("SFuel", _52_17528))
in (mkApp _52_17529))
end))

let fuel_2 = (n_fuel 2)

let fuel_100 = (n_fuel 100)

let mk_and_opt = (fun ( p1  :  term option ) ( p2  :  term option ) -> (match ((p1, p2)) with
| (Some (p1), Some (p2)) -> begin
(let _52_17534 = (mkAnd (p1, p2))
in Some (_52_17534))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))

let mk_and_opt_l = (fun ( pl  :  term option list ) -> (Support.List.fold_left (fun ( out  :  term option ) ( p  :  term option ) -> (mk_and_opt p out)) None pl))

let mk_and_l = (fun ( l  :  term list ) -> (match (l) with
| [] -> begin
mkTrue
end
| hd::tl -> begin
(Support.List.fold_left (fun ( p1  :  term ) ( p2  :  term ) -> (mkAnd (p1, p2))) hd tl)
end))

let mk_or_l = (fun ( l  :  term list ) -> (match (l) with
| [] -> begin
mkFalse
end
| hd::tl -> begin
(Support.List.fold_left (fun ( p1  :  term ) ( p2  :  term ) -> (mkOr (p1, p2))) hd tl)
end))

let rec print_smt_term = (fun ( t  :  term ) -> (match (t.tm) with
| Integer (n) -> begin
(Support.Microsoft.FStar.Util.format1 "Integer %s" n)
end
| BoundV (n) -> begin
(let _52_17551 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "BoundV %s" _52_17551))
end
| FreeV (fv) -> begin
(Support.Microsoft.FStar.Util.format1 "FreeV %s" (Support.Prims.fst fv))
end
| App ((op, l)) -> begin
(let _52_17552 = (print_smt_term_list l)
in (Support.Microsoft.FStar.Util.format2 "App %s [ %s ]" (op_to_string op) _52_17552))
end
| Quant ((qop, l, _, _, t)) -> begin
(let _52_17554 = (print_smt_term_list_list l)
in (let _52_17553 = (print_smt_term t)
in (Support.Microsoft.FStar.Util.format3 "Quant %s %s %s" (qop_to_string qop) _52_17554 _52_17553)))
end))
and print_smt_term_list = (fun ( l  :  term list ) -> (Support.List.fold_left (fun ( s  :  string ) ( t  :  term ) -> (let _52_17558 = (print_smt_term t)
in (Support.String.strcat (Support.String.strcat s "; ") _52_17558))) "" l))
and print_smt_term_list_list = (fun ( l  :  term list list ) -> (Support.List.fold_left (fun ( s  :  string ) ( l  :  term list ) -> (let _52_17563 = (let _52_17562 = (print_smt_term_list l)
in (Support.String.strcat (Support.String.strcat s "; [ ") _52_17562))
in (Support.String.strcat _52_17563 " ] "))) "" l))




