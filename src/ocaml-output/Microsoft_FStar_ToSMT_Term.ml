
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

let rec strSort = (fun x -> (match (x) with
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
(Support.Microsoft.FStar.Util.format2 "\x28Array %s %s\x29" (strSort s1) (strSort s2))
end
| Arrow ((s1, s2)) -> begin
(Support.Microsoft.FStar.Util.format2 "\x28%s -> %s\x29" (strSort s1) (strSort s2))
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

type qop =
| Forall
| Exists

type term' =
| Integer of string
| BoundV of int
| FreeV of fv
| App of (op * term list)
| Quant of (qop * pat list list * int option * sort list * term) and term =
{tm : term'; hash : string; freevars : fvs Microsoft_FStar_Absyn_Syntax.memo} and pat =
term and fv =
(string * sort) and fvs =
fv list

let fv_eq = (fun x y -> ((Support.Prims.fst x) = (Support.Prims.fst y)))

let fv_sort = (fun x -> (Support.Prims.snd x))

let freevar_eq = (fun x y -> (match ((x.tm, y.tm)) with
| (FreeV (x), FreeV (y)) -> begin
(fv_eq x y)
end
| _ -> begin
false
end))

let freevar_sort = (fun _42_1 -> (match (_42_1) with
| {tm = FreeV (x); hash = _; freevars = _} -> begin
(fv_sort x)
end
| _ -> begin
(failwith "impossible")
end))

let fv_of_term = (fun _42_2 -> (match (_42_2) with
| {tm = FreeV (fv); hash = _; freevars = _} -> begin
fv
end
| _ -> begin
(failwith "impossible")
end))

let rec freevars = (fun t -> (match (t.tm) with
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

let free_variables = (fun t -> (match ((! (t.freevars))) with
| Some (b) -> begin
b
end
| None -> begin
(let fvs = (Support.Microsoft.FStar.Util.remove_dups fv_eq (freevars t))
in (let _42_111 = (Support.ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))

let qop_to_string = (fun _42_3 -> (match (_42_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))

let op_to_string = (fun _42_4 -> (match (_42_4) with
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

let weightToSmt = (fun _42_5 -> (match (_42_5) with
| None -> begin
""
end
| Some (i) -> begin
(Support.Microsoft.FStar.Util.format1 ":weight %s\n" (Support.Microsoft.FStar.Util.string_of_int i))
end))

let rec hash_of_term' = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(Support.String.strcat "@" (Support.Microsoft.FStar.Util.string_of_int i))
end
| FreeV (x) -> begin
(Support.String.strcat (Support.String.strcat (Support.Prims.fst x) ":") (strSort (Support.Prims.snd x)))
end
| App ((op, tms)) -> begin
(Support.String.strcat (Support.String.strcat (Support.String.strcat "\x28" (op_to_string op)) ((Support.String.concat " ") (Support.List.map (fun t -> t.hash) tms))) "\x29")
end
| Quant ((qop, pats, wopt, sorts, body)) -> begin
(Support.Microsoft.FStar.Util.format5 "\x28%s \x28%s\x29\x28! %s %s %s\x29\x29" (qop_to_string qop) ((Support.String.concat " ") (Support.List.map strSort sorts)) body.hash (weightToSmt wopt) ((Support.String.concat "; ") ((Support.List.map (fun pats -> ((Support.String.concat " ") (Support.List.map (fun p -> p.hash) pats)))) pats)))
end))

let all_terms_l = (ref (((Support.Microsoft.FStar.Util.smap_create 10000))::[]))

let all_terms = (fun _42_163 -> (match (_42_163) with
| () -> begin
(Support.List.hd (! (all_terms_l)))
end))

let push = (fun _42_164 -> (match (_42_164) with
| () -> begin
()
end))

let pop = (fun _42_165 -> (match (_42_165) with
| () -> begin
()
end))

let commit_mark = (fun _42_166 -> (match (_42_166) with
| () -> begin
()
end))

let mk = (fun t -> (let key = (hash_of_term' t)
in (match ((Support.Microsoft.FStar.Util.smap_try_find (all_terms ()) key)) with
| Some (tm) -> begin
tm
end
| None -> begin
(let tm = {tm = t; hash = key; freevars = (Support.Microsoft.FStar.Util.mk_ref None)}
in (let _42_173 = (Support.Microsoft.FStar.Util.smap_add (all_terms ()) key tm)
in tm))
end)))

let mkTrue = (mk (App ((True, []))))

let mkFalse = (mk (App ((False, []))))

let mkInteger = (fun i -> (mk (Integer (i))))

let mkInteger' = (fun i -> (mkInteger (Support.Microsoft.FStar.Util.string_of_int i)))

let mkBoundV = (fun i -> (mk (BoundV (i))))

let mkFreeV = (fun x -> (mk (FreeV (x))))

let mkApp' = (fun f -> (mk (App (f))))

let mkApp = (fun _42_182 -> (match (_42_182) with
| (s, args) -> begin
(mk (App ((Var (s), args))))
end))

let mkNot = (fun t -> (match (t.tm) with
| App ((True, _)) -> begin
mkFalse
end
| App ((False, _)) -> begin
mkTrue
end
| _ -> begin
(mkApp' (Not, (t)::[]))
end))

let mkAnd = (fun _42_198 -> (match (_42_198) with
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

let mkOr = (fun _42_258 -> (match (_42_258) with
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

let mkImp = (fun _42_318 -> (match (_42_318) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (_, App ((True, _))) -> begin
mkTrue
end
| (App ((True, _)), _) -> begin
t2
end
| (_, App ((Imp, t1'::t2'::[]))) -> begin
(mkApp' (Imp, ((mkAnd (t1, t1')))::(t2')::[]))
end
| _ -> begin
(mkApp' (Imp, (t1)::(t2)::[]))
end)
end))

let mk_bin_op = (fun op _42_349 -> (match (_42_349) with
| (t1, t2) -> begin
(mkApp' (op, (t1)::(t2)::[]))
end))

let mkMinus = (fun t -> (mkApp' (Minus, (t)::[])))

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

let mkITE = (fun _42_354 -> (match (_42_354) with
| (t1, t2, t3) -> begin
(match ((t2.tm, t3.tm)) with
| (App ((True, _)), App ((True, _))) -> begin
mkTrue
end
| (App ((True, _)), _) -> begin
(mkImp ((mkNot t1), t3))
end
| (_, App ((True, _))) -> begin
(mkImp (t1, t2))
end
| (_, _) -> begin
(mkApp' (ITE, (t1)::(t2)::(t3)::[]))
end)
end))

let mkCases = (fun t -> (match (t) with
| [] -> begin
(failwith "Impos")
end
| hd::tl -> begin
(Support.List.fold_left (fun out t -> (mkAnd (out, t))) hd tl)
end))

let mkQuant = (fun _42_399 -> (match (_42_399) with
| (qop, pats, wopt, vars, body) -> begin
if ((Support.List.length vars) = 0) then begin
body
end else begin
(match (body.tm) with
| App ((True, _)) -> begin
body
end
| _ -> begin
(mk (Quant ((qop, pats, wopt, vars, body))))
end)
end
end))

let abstr = (fun fvs t -> (let nvars = (Support.List.length fvs)
in (let index_of = (fun fv -> (match ((Support.Microsoft.FStar.Util.try_find_index (fv_eq fv) fvs)) with
| None -> begin
None
end
| Some (i) -> begin
Some ((nvars - (i + 1)))
end))
in (let rec aux = (fun ix t -> (match ((! (t.freevars))) with
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
(mkApp' (op, (Support.List.map (aux ix) tms)))
end
| Quant ((qop, pats, wopt, vars, body)) -> begin
(let n = (Support.List.length vars)
in (mkQuant (qop, ((Support.List.map (Support.List.map (aux (ix + n)))) pats), wopt, vars, (aux (ix + n) body))))
end)
end))
in (aux 0 t)))))

let inst = (fun tms t -> (let n = (Support.List.length tms)
in (let rec aux = (fun shift t -> (match (t.tm) with
| (Integer (_)) | (FreeV (_)) -> begin
t
end
| BoundV (i) -> begin
if ((0 <= (i - shift)) && ((i - shift) < n)) then begin
(Support.List.nth tms (i - shift))
end else begin
t
end
end
| App ((op, tms)) -> begin
(mkApp' (op, (Support.List.map (aux shift) tms)))
end
| Quant ((qop, pats, wopt, vars, body)) -> begin
(let m = (Support.List.length vars)
in (let shift = (shift + m)
in (mkQuant (qop, ((Support.List.map (Support.List.map (aux shift))) pats), wopt, vars, (aux shift body)))))
end))
in (aux 0 t))))

let mkQuant' = (fun _42_477 -> (match (_42_477) with
| (qop, pats, wopt, vars, body) -> begin
(mkQuant (qop, ((Support.List.map (Support.List.map (abstr vars))) pats), wopt, (Support.List.map (fv_sort) vars), (abstr vars body)))
end))

let mkForall'' = (fun _42_482 -> (match (_42_482) with
| (pats, wopt, sorts, body) -> begin
(mkQuant (Forall, pats, wopt, sorts, body))
end))

let mkForall' = (fun _42_487 -> (match (_42_487) with
| (pats, wopt, vars, body) -> begin
(mkQuant' (Forall, pats, wopt, vars, body))
end))

let mkForall = (fun _42_491 -> (match (_42_491) with
| (pats, vars, body) -> begin
(mkQuant' (Forall, (pats)::[], None, vars, body))
end))

let mkExists = (fun _42_495 -> (match (_42_495) with
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

type decls_t =
decl list

let mkDefineFun = (fun _42_513 -> (match (_42_513) with
| (nm, vars, s, tm, c) -> begin
DefineFun ((nm, (Support.List.map (fv_sort) vars), s, (abstr vars tm), c))
end))

let constr_id_of_sort = (fun sort -> (Support.Microsoft.FStar.Util.format1 "%s\x5fconstr\x5fid" (strSort sort)))

let fresh_token = (fun _42_517 id -> (match (_42_517) with
| (tok_name, sort) -> begin
Assume (((mkEq ((mkInteger' id), (mkApp ((constr_id_of_sort sort), ((mkApp (tok_name, [])))::[])))), Some ("fresh token")))
end))

let constructor_to_decl = (fun _42_523 -> (match (_42_523) with
| (name, projectors, sort, id) -> begin
(let id = (Support.Microsoft.FStar.Util.string_of_int id)
in (let cdecl = DeclFun ((name, ((Support.List.map (Support.Prims.snd)) projectors), sort, Some ("Constructor")))
in (let n_bvars = (Support.List.length projectors)
in (let bvar_name = (fun i -> (Support.String.strcat "x\x5f" (Support.Microsoft.FStar.Util.string_of_int i)))
in (let bvar_index = (fun i -> (n_bvars - (i + 1)))
in (let bvar = (fun i s -> (mkFreeV ((bvar_name i), s)))
in (let bvars = ((Support.List.mapi (fun i _42_538 -> (match (_42_538) with
| (_, s) -> begin
(bvar i s)
end))) projectors)
in (let bvar_names = (Support.List.map fv_of_term bvars)
in (let capp = (mkApp (name, bvars))
in (let cid_app = (mkApp ((constr_id_of_sort sort), (capp)::[]))
in (let cid = Assume (((mkForall ([], bvar_names, (mkEq ((mkInteger id), cid_app)))), Some ("Constructor distinct")))
in (let disc_name = (Support.String.strcat "is-" name)
in (let xfv = ("x", sort)
in (let xx = (mkFreeV xfv)
in (let disc_eq = (mkEq ((mkApp ((constr_id_of_sort sort), (xx)::[])), (mkInteger id)))
in (let proj_terms = ((Support.List.map (fun _42_550 -> (match (_42_550) with
| (proj, s) -> begin
(mkApp (proj, (xx)::[]))
end))) projectors)
in (let disc_inv_body = (mkEq (xx, (mkApp (name, proj_terms))))
in (let disc_ax = (mkAnd (disc_eq, disc_inv_body))
in (let disc = (mkDefineFun (disc_name, (xfv)::[], Bool_sort, disc_ax, Some ("Discriminator definition")))
in (let projs = ((Support.List.flatten) ((Support.List.mapi (fun i _42_558 -> (match (_42_558) with
| (name, s) -> begin
(let cproj_app = (mkApp (name, (capp)::[]))
in (DeclFun ((name, (sort)::[], s, Some ("Projector"))))::(Assume (((mkForall ((capp)::[], bvar_names, (mkEq (cproj_app, (bvar i s))))), Some ("Projection inverse"))))::[])
end))) projectors))
in (Support.List.append (Support.List.append ((Caption ((Support.Microsoft.FStar.Util.format1 "<start constructor %s>" name)))::(cdecl)::(cid)::projs) ((disc)::[])) ((Caption ((Support.Microsoft.FStar.Util.format1 "</end constructor %s>" name)))::[]))))))))))))))))))))))
end))

let name_binders_inner = (fun outer_names start sorts -> (let _42_580 = ((Support.List.fold_left (fun _42_567 s -> (match (_42_567) with
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
in (let nm = (Support.String.strcat prefix (Support.Microsoft.FStar.Util.string_of_int n))
in (let names = ((nm, s))::names
in (let b = (Support.Microsoft.FStar.Util.format2 "\x28%s %s\x29" nm (strSort s))
in (names, (b)::binders, (n + 1))))))
end)) (outer_names, [], start)) sorts)
in (match (_42_580) with
| (names, binders, n) -> begin
(names, (Support.List.rev binders), n)
end)))

let name_binders = (fun sorts -> (let _42_585 = (name_binders_inner [] 0 sorts)
in (match (_42_585) with
| (names, binders, n) -> begin
((Support.List.rev names), binders)
end)))

let termToSmt = (fun t -> (let rec aux = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
((Support.Prims.fst) (Support.List.nth names i))
end
| FreeV (x) -> begin
(Support.Prims.fst x)
end
| App ((op, [])) -> begin
(op_to_string op)
end
| App ((op, tms)) -> begin
(Support.Microsoft.FStar.Util.format2 "\x28%s %s\x29" (op_to_string op) ((Support.String.concat "\n") (Support.List.map (aux n names) tms)))
end
| Quant ((qop, pats, wopt, sorts, body)) -> begin
(let _42_615 = (name_binders_inner names n sorts)
in (match (_42_615) with
| (names, binders, n) -> begin
(let binders = ((Support.String.concat " ") binders)
in (let pats_str = (match (pats) with
| ([]::[]) | ([]) -> begin
""
end
| _ -> begin
((Support.String.concat "\n") ((Support.List.map (fun pats -> (Support.Microsoft.FStar.Util.format1 "\n:pattern \x28%s\x29" (Support.String.concat " " (Support.List.map (fun p -> (Support.Microsoft.FStar.Util.format1 "%s" (aux n names p))) pats))))) pats))
end)
in (match ((pats, wopt)) with
| (([]::[], None)) | (([], None)) -> begin
(Support.Microsoft.FStar.Util.format3 "\x28%s \x28%s\x29\n %s\x29" (qop_to_string qop) binders (aux n names body))
end
| _ -> begin
(Support.Microsoft.FStar.Util.format5 "\x28%s \x28%s\x29\n \x28! %s\n %s %s\x29\x29" (qop_to_string qop) binders (aux n names body) (weightToSmt wopt) pats_str)
end)))
end))
end))
in (aux 0 [] t)))

let caption_to_string = (fun _42_6 -> (match (_42_6) with
| None -> begin
""
end
| Some (c) -> begin
(let _42_640 = (Support.Microsoft.FStar.Util.splitlines c)
in (match (_42_640) with
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

let rec declToSmt = (fun z3options decl -> (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(Support.Microsoft.FStar.Util.format1 "\n; %s" ((fun _42_7 -> (match (_42_7) with
| [] -> begin
""
end
| h::t -> begin
h
end)) (Support.Microsoft.FStar.Util.splitlines c)))
end
| DeclFun ((f, argsorts, retsort, c)) -> begin
(let l = (Support.List.map strSort argsorts)
in (Support.Microsoft.FStar.Util.format4 "%s\x28declare-fun %s \x28%s\x29 %s\x29" (caption_to_string c) f (Support.String.concat " " l) (strSort retsort)))
end
| DefineFun ((f, arg_sorts, retsort, body, c)) -> begin
(let _42_671 = (name_binders arg_sorts)
in (match (_42_671) with
| (names, binders) -> begin
(let body = (inst (Support.List.map mkFreeV names) body)
in (Support.Microsoft.FStar.Util.format5 "%s\x28define-fun %s \x28%s\x29 %s\n %s\x29" (caption_to_string c) f (Support.String.concat " " binders) (strSort retsort) (termToSmt body)))
end))
end
| Assume ((t, c)) -> begin
(Support.Microsoft.FStar.Util.format2 "%s\x28assert %s\x29" (caption_to_string c) (termToSmt t))
end
| Eval (t) -> begin
(Support.Microsoft.FStar.Util.format1 "\x28eval %s\x29" (termToSmt t))
end
| Echo (s) -> begin
(Support.Microsoft.FStar.Util.format1 "\x28echo \"%s\"\x29" s)
end
| CheckSat -> begin
"\x28check-sat\x29"
end
| Push -> begin
"\x28push\x29"
end
| Pop -> begin
"\x28pop\x29"
end))
and mkPrelude = (fun z3options -> (let basic = (Support.String.strcat z3options "\x28declare-sort Ref\x29\n\n\x28declare-fun Ref\x5fconstr\x5fid \x28Ref\x29 Int\x29\n\n\n\n\x28declare-sort String\x29\n\n\x28declare-fun String\x5fconstr\x5fid \x28String\x29 Int\x29\n\n\n\n\x28declare-sort Kind\x29\n\n\x28declare-fun Kind\x5fconstr\x5fid \x28Kind\x29 Int\x29\n\n\n\n\x28declare-sort Type\x29\n\n\x28declare-fun Type\x5fconstr\x5fid \x28Type\x29 Int\x29\n\n\n\n\x28declare-sort Term\x29\n\n\x28declare-fun Term\x5fconstr\x5fid \x28Term\x29 Int\x29\n\n\x28declare-datatypes \x28\x29 \x28\x28Fuel \n\n\x28ZFuel\x29 \n\n\x28SFuel \x28prec Fuel\x29\x29\x29\x29\x29\n\n\x28declare-fun MaxIFuel \x28\x29 Fuel\x29\n\n\x28declare-fun MaxFuel \x28\x29 Fuel\x29\n\n\x28declare-fun PreKind \x28Type\x29 Kind\x29\n\n\x28declare-fun PreType \x28Term\x29 Type\x29\n\n\x28declare-fun Valid \x28Type\x29 Bool\x29\n\n\x28declare-fun HasKind \x28Type Kind\x29 Bool\x29\n\n\x28declare-fun HasType \x28Term Type\x29 Bool\x29\n\n\x28define-fun  IsTyped \x28\x28x Term\x29\x29 Bool\n\n\x28exists \x28\x28t Type\x29\x29 \x28HasType x t\x29\x29\x29\n\n\x28declare-fun HasTypeFuel \x28Fuel Term Type\x29 Bool\x29\n\n\x28declare-fun ApplyEF \x28Term Fuel\x29 Term\x29\n\n\x28declare-fun ApplyEE \x28Term Term\x29 Term\x29\n\n\x28declare-fun ApplyET \x28Term Type\x29 Term\x29\n\n\x28declare-fun ApplyTE \x28Type Term\x29 Type\x29\n\n\x28declare-fun ApplyTT \x28Type Type\x29 Type\x29\n\n\x28declare-fun Rank \x28Term\x29 Int\x29\n\n\x28declare-fun Closure \x28Term\x29 Term\x29\n\n\x28declare-fun ConsTerm \x28Term Term\x29 Term\x29\n\n\x28declare-fun ConsType \x28Type Term\x29 Term\x29\n\n\x28declare-fun ConsFuel \x28Fuel Term\x29 Term\x29\n\n\x28declare-fun Precedes \x28Term Term\x29 Type\x29\n\n\x28assert \x28forall \x28\x28e Term\x29 \x28t Type\x29\x29\n\n\x28!  \x28= \x28HasType e t\x29\n\n\x28HasTypeFuel MaxIFuel e t\x29\x29\n\n:pattern \x28\x28HasType e t\x29\x29\x29\x29\x29\n\n\x28assert \x28forall \x28\x28f Fuel\x29 \x28e Term\x29 \x28t Type\x29\x29 \n\n\x28! \x28= \x28HasTypeFuel \x28SFuel f\x29 e t\x29\n\n\x28HasTypeFuel f e t\x29\x29\n\n:pattern \x28\x28HasTypeFuel \x28SFuel f\x29 e t\x29\x29\x29\x29\x29\n\n\x28assert \x28forall \x28\x28t1 Term\x29 \x28t2 Term\x29\x29\n\n\x28! \x28iff \x28Valid \x28Precedes t1 t2\x29\x29 \n\n\x28< \x28Rank t1\x29 \x28Rank t2\x29\x29\x29\n\n:pattern \x28\x28Precedes t1 t2\x29\x29\x29\x29\x29\n\n\x28define-fun Prims.Precedes \x28\x28a Type\x29 \x28b Type\x29 \x28t1 Term\x29 \x28t2 Term\x29\x29 Type\n\n\x28Precedes t1 t2\x29\x29\n")
in (let constrs = (("String\x5fconst", (("String\x5fconst\x5fproj\x5f0", Int_sort))::[], String_sort, 0))::(("Kind\x5ftype", [], Kind_sort, 0))::(("Kind\x5farrow", (("Kind\x5farrow\x5fid", Int_sort))::[], Kind_sort, 1))::(("Typ\x5ffun", (("Typ\x5ffun\x5fid", Int_sort))::[], Type_sort, 1))::(("Typ\x5fapp", (("Typ\x5fapp\x5ffst", Type_sort))::(("Typ\x5fapp\x5fsnd", Type_sort))::[], Type_sort, 2))::(("Typ\x5fdep", (("Typ\x5fdep\x5ffst", Type_sort))::(("Typ\x5fdep\x5fsnd", Term_sort))::[], Type_sort, 3))::(("Typ\x5fuvar", (("Typ\x5fuvar\x5ffst", Int_sort))::[], Type_sort, 4))::(("Term\x5funit", [], Term_sort, 0))::(("BoxInt", (("BoxInt\x5fproj\x5f0", Int_sort))::[], Term_sort, 1))::(("BoxBool", (("BoxBool\x5fproj\x5f0", Bool_sort))::[], Term_sort, 2))::(("BoxString", (("BoxString\x5fproj\x5f0", String_sort))::[], Term_sort, 3))::(("BoxRef", (("BoxRef\x5fproj\x5f0", Ref_sort))::[], Term_sort, 4))::(("Exp\x5fuvar", (("Exp\x5fuvar\x5ffst", Int_sort))::[], Term_sort, 5))::(("LexCons", (("LexCons\x5f0", Term_sort))::(("LexCons\x5f1", Term_sort))::[], Term_sort, 6))::[]
in (let bcons = ((Support.String.concat "\n") ((Support.List.map (declToSmt z3options)) ((Support.List.collect constructor_to_decl) constrs)))
in (let lex_ordering = "\n\x28define-fun is-Prims.LexCons \x28\x28t Term\x29\x29 Bool \n\n\x28is-LexCons t\x29\x29\n\n\x28assert \x28forall \x28\x28x1 Term\x29 \x28x2 Term\x29 \x28y1 Term\x29 \x28y2 Term\x29\x29\n\n\x28iff \x28Valid \x28Precedes \x28LexCons x1 x2\x29 \x28LexCons y1 y2\x29\x29\x29\n\n\x28or \x28Valid \x28Precedes x1 y1\x29\x29\n\n\x28and \x28= x1 y1\x29\n\n\x28Valid \x28Precedes x2 y2\x29\x29\x29\x29\x29\x29\x29\n"
in (Support.String.strcat (Support.String.strcat basic bcons) lex_ordering))))))

let mk_Kind_type = (mkApp ("Kind\x5ftype", []))

let mk_Typ_app = (fun t1 t2 -> (mkApp ("Typ\x5fapp", (t1)::(t2)::[])))

let mk_Typ_dep = (fun t1 t2 -> (mkApp ("Typ\x5fdep", (t1)::(t2)::[])))

let mk_Typ_uvar = (fun i -> (mkApp ("Typ\x5fuvar", ((mkInteger' i))::[])))

let mk_Exp_uvar = (fun i -> (mkApp ("Exp\x5fuvar", ((mkInteger' i))::[])))

let mk_Term_unit = (mkApp ("Term\x5funit", []))

let boxInt = (fun t -> (mkApp ("BoxInt", (t)::[])))

let unboxInt = (fun t -> (mkApp ("BoxInt\x5fproj\x5f0", (t)::[])))

let boxBool = (fun t -> (mkApp ("BoxBool", (t)::[])))

let unboxBool = (fun t -> (mkApp ("BoxBool\x5fproj\x5f0", (t)::[])))

let boxString = (fun t -> (mkApp ("BoxString", (t)::[])))

let unboxString = (fun t -> (mkApp ("BoxString\x5fproj\x5f0", (t)::[])))

let boxRef = (fun t -> (mkApp ("BoxRef", (t)::[])))

let unboxRef = (fun t -> (mkApp ("BoxRef\x5fproj\x5f0", (t)::[])))

let boxTerm = (fun sort t -> (match (sort) with
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

let unboxTerm = (fun sort t -> (match (sort) with
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

let mk_PreKind = (fun t -> (mkApp ("PreKind", (t)::[])))

let mk_PreType = (fun t -> (mkApp ("PreType", (t)::[])))

let mk_Valid = (fun t -> (mkApp ("Valid", (t)::[])))

let mk_HasType = (fun v t -> (mkApp ("HasType", (v)::(t)::[])))

let mk_IsTyped = (fun v -> (mkApp ("IsTyped", (v)::[])))

let mk_HasTypeFuel = (fun f v t -> if (! (Microsoft_FStar_Options.unthrottle_inductives)) then begin
(mk_HasType v t)
end else begin
(mkApp ("HasTypeFuel", (f)::(v)::(t)::[]))
end)

let mk_HasTypeWithFuel = (fun f v t -> (match (f) with
| None -> begin
(mk_HasType v t)
end
| Some (f) -> begin
(mk_HasTypeFuel f v t)
end))

let mk_Destruct = (fun v -> (mkApp ("Destruct", (v)::[])))

let mk_HasKind = (fun t k -> (mkApp ("HasKind", (t)::(k)::[])))

let mk_Rank = (fun x -> (mkApp ("Rank", (x)::[])))

let mk_tester = (fun n t -> (mkApp ((Support.String.strcat "is-" n), (t)::[])))

let mk_ApplyTE = (fun t e -> (mkApp ("ApplyTE", (t)::(e)::[])))

let mk_ApplyTT = (fun t t' -> (mkApp ("ApplyTT", (t)::(t')::[])))

let mk_ApplyET = (fun e t -> (mkApp ("ApplyET", (e)::(t)::[])))

let mk_ApplyEE = (fun e e' -> (mkApp ("ApplyEE", (e)::(e')::[])))

let mk_ApplyEF = (fun e f -> (mkApp ("ApplyEF", (e)::(f)::[])))

let mk_String_const = (fun i -> (mkApp ("String\x5fconst", ((mkInteger' i))::[])))

let mk_Precedes = (fun x1 x2 -> (mk_Valid (mkApp ("Precedes", (x1)::(x2)::[]))))

let mk_LexCons = (fun x1 x2 -> (mkApp ("LexCons", (x1)::(x2)::[])))

let rec n_fuel = (fun n -> if (n = 0) then begin
(mkApp ("ZFuel", []))
end else begin
(mkApp ("SFuel", ((n_fuel (n - 1)))::[]))
end)

let fuel_2 = (n_fuel 2)

let fuel_100 = (n_fuel 100)

let mk_and_opt = (fun p1 p2 -> (match ((p1, p2)) with
| (Some (p1), Some (p2)) -> begin
Some ((mkAnd (p1, p2)))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))

let mk_and_opt_l = (fun pl -> (Support.List.fold_left (fun out p -> (mk_and_opt p out)) None pl))

let mk_and_l = (fun l -> (match (l) with
| [] -> begin
mkTrue
end
| hd::tl -> begin
(Support.List.fold_left (fun p1 p2 -> (mkAnd (p1, p2))) hd tl)
end))

let mk_or_l = (fun l -> (match (l) with
| [] -> begin
mkFalse
end
| hd::tl -> begin
(Support.List.fold_left (fun p1 p2 -> (mkOr (p1, p2))) hd tl)
end))

let rec print_smt_term = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(Support.Microsoft.FStar.Util.format1 "Integer %s" n)
end
| BoundV (n) -> begin
(Support.Microsoft.FStar.Util.format1 "BoundV %s" (Support.Microsoft.FStar.Util.string_of_int n))
end
| FreeV (fv) -> begin
(Support.Microsoft.FStar.Util.format1 "FreeV %s" (Support.Prims.fst fv))
end
| App ((op, l)) -> begin
(Support.Microsoft.FStar.Util.format2 "App %s \x5b %s \x5d" (op_to_string op) (print_smt_term_list l))
end
| Quant ((qop, l, _, _, t)) -> begin
(Support.Microsoft.FStar.Util.format3 "Quant %s %s %s" (qop_to_string qop) (print_smt_term_list_list l) (print_smt_term t))
end))
and print_smt_term_list = (fun l -> (Support.List.fold_left (fun s t -> (Support.String.strcat (Support.String.strcat s "; ") (print_smt_term t))) "" l))
and print_smt_term_list_list = (fun l -> (Support.List.fold_left (fun s l -> (Support.String.strcat (Support.String.strcat (Support.String.strcat s "; \x5b ") (print_smt_term_list l)) " \x5d ")) "" l))




