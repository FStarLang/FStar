
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
(Support.Microsoft.FStar.Util.format2 "(Array %s %s)" (strSort s1) (strSort s2))
end
| Arrow ((s1, s2)) -> begin
(Support.Microsoft.FStar.Util.format2 "(%s -> %s)" (strSort s1) (strSort s2))
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
| Integer of int
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

let freevar_sort = (fun _415905 -> (match (_415905) with
| {tm = FreeV (x); hash = _; freevars = _} -> begin
(fv_sort x)
end
| _ -> begin
(failwith "impossible")
end))

let fv_of_term = (fun _415906 -> (match (_415906) with
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
in (let _416015 = (t.freevars := Some (fvs))
in fvs))
end))

let qop_to_string = (fun _415907 -> (match (_415907) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))

let op_to_string = (fun _415908 -> (match (_415908) with
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

let weightToSmt = (fun _415909 -> (match (_415909) with
| None -> begin
""
end
| Some (i) -> begin
(Support.Microsoft.FStar.Util.format1 ":weight %s\n" (Support.Microsoft.FStar.Util.string_of_int i))
end))

let rec hash_of_term' = (fun t -> (match (t) with
| Integer (i) -> begin
(Support.Microsoft.FStar.Util.string_of_int i)
end
| BoundV (i) -> begin
(Support.String.strcat "@" (Support.Microsoft.FStar.Util.string_of_int i))
end
| FreeV (x) -> begin
(Support.String.strcat (Support.String.strcat (Support.Prims.fst x) ":") (strSort (Support.Prims.snd x)))
end
| App ((op, tms)) -> begin
(Support.String.strcat (Support.String.strcat (Support.String.strcat "(" (op_to_string op)) ((Support.String.concat " ") (Support.List.map (fun t -> t.hash) tms))) ")")
end
| Quant ((qop, pats, wopt, sorts, body)) -> begin
(Support.Microsoft.FStar.Util.format5 "(%s (%s)(! %s %s %s))" (qop_to_string qop) ((Support.String.concat " ") (Support.List.map strSort sorts)) body.hash (weightToSmt wopt) ((Support.String.concat "; ") ((Support.List.map (fun pats -> ((Support.String.concat " ") (Support.List.map (fun p -> p.hash) pats)))) pats)))
end))

let all_terms_l = (ref (((Support.Microsoft.FStar.Util.smap_create 10000))::[]))

let all_terms = (fun _416067 -> (match (_416067) with
| () -> begin
(Support.List.hd (! (all_terms_l)))
end))

let push = (fun _416068 -> (match (_416068) with
| () -> begin
()
end))

let pop = (fun _416069 -> (match (_416069) with
| () -> begin
()
end))

let commit_mark = (fun _416070 -> (match (_416070) with
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
in (let _416077 = (Support.Microsoft.FStar.Util.smap_add (all_terms ()) key tm)
in tm))
end)))

let mkTrue = (mk (App ((True, []))))

let mkFalse = (mk (App ((False, []))))

let mkInteger = (fun i -> (mk (Integer (i))))

let mkBoundV = (fun i -> (mk (BoundV (i))))

let mkFreeV = (fun x -> (mk (FreeV (x))))

let mkApp' = (fun f -> (mk (App (f))))

let mkApp = (fun _416085 -> (match (_416085) with
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

let mkAnd = (fun _416101 -> (match (_416101) with
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

let mkOr = (fun _416161 -> (match (_416161) with
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

let mkImp = (fun _416221 -> (match (_416221) with
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

let mk_bin_op = (fun op _416252 -> (match (_416252) with
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

let mkITE = (fun _416257 -> (match (_416257) with
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

let mkQuant = (fun _416302 -> (match (_416302) with
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

let mkQuant' = (fun _416380 -> (match (_416380) with
| (qop, pats, wopt, vars, body) -> begin
(mkQuant (qop, ((Support.List.map (Support.List.map (abstr vars))) pats), wopt, (Support.List.map (fv_sort) vars), (abstr vars body)))
end))

let mkForall' = (fun _416385 -> (match (_416385) with
| (pats, wopt, vars, body) -> begin
(mkQuant' (Forall, pats, wopt, vars, body))
end))

let mkForall = (fun _416389 -> (match (_416389) with
| (pats, vars, body) -> begin
(mkQuant' (Forall, (pats)::[], None, vars, body))
end))

let mkExists = (fun _416393 -> (match (_416393) with
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

let mkDefineFun = (fun _416411 -> (match (_416411) with
| (nm, vars, s, tm, c) -> begin
DefineFun ((nm, (Support.List.map (fv_sort) vars), s, (abstr vars tm), c))
end))

let constr_id_of_sort = (fun sort -> (Support.Microsoft.FStar.Util.format1 "%s_constr_id" (strSort sort)))

let fresh_token = (fun _416415 id -> (match (_416415) with
| (tok_name, sort) -> begin
Assume (((mkEq ((mkInteger id), (mkApp ((constr_id_of_sort sort), ((mkApp (tok_name, [])))::[])))), Some ("fresh token")))
end))

let constructor_to_decl = (fun _416421 -> (match (_416421) with
| (name, projectors, sort, id) -> begin
(let cdecl = DeclFun ((name, ((Support.List.map (Support.Prims.snd)) projectors), sort, Some ("Constructor")))
in (let n_bvars = (Support.List.length projectors)
in (let bvar_name = (fun i -> (Support.String.strcat "x_" (Support.Microsoft.FStar.Util.string_of_int i)))
in (let bvar_index = (fun i -> (n_bvars - (i + 1)))
in (let bvar = (fun i s -> (mkFreeV ((bvar_name i), s)))
in (let bvars = ((Support.List.mapi (fun i _416435 -> (match (_416435) with
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
in (let proj_terms = ((Support.List.map (fun _416447 -> (match (_416447) with
| (proj, s) -> begin
(mkApp (proj, (xx)::[]))
end))) projectors)
in (let disc_inv_body = (mkEq (xx, (mkApp (name, proj_terms))))
in (let disc_ax = (mkAnd (disc_eq, disc_inv_body))
in (let disc = (mkDefineFun (disc_name, (xfv)::[], Bool_sort, disc_ax, Some ("Discriminator definition")))
in (let projs = ((Support.List.flatten) ((Support.List.mapi (fun i _416455 -> (match (_416455) with
| (name, s) -> begin
(let cproj_app = (mkApp (name, (capp)::[]))
in (DeclFun ((name, (sort)::[], s, Some ("Projector"))))::(Assume (((mkForall ((capp)::[], bvar_names, (mkEq (cproj_app, (bvar i s))))), Some ("Projection inverse"))))::[])
end))) projectors))
in (Support.List.append (Support.List.append ((Caption ((Support.Microsoft.FStar.Util.format1 "<start constructor %s>" name)))::(cdecl)::(cid)::projs) ((disc)::[])) ((Caption ((Support.Microsoft.FStar.Util.format1 "</end constructor %s>" name)))::[])))))))))))))))))))))
end))

let name_binders_inner = (fun outer_names start sorts -> (let _416477 = ((Support.List.fold_left (fun _416464 s -> (match (_416464) with
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
in (let b = (Support.Microsoft.FStar.Util.format2 "(%s %s)" nm (strSort s))
in (names, (b)::binders, (n + 1))))))
end)) (outer_names, [], start)) sorts)
in (match (_416477) with
| (names, binders, n) -> begin
(names, (Support.List.rev binders), n)
end)))

let name_binders = (fun sorts -> (let _416482 = (name_binders_inner [] 0 sorts)
in (match (_416482) with
| (names, binders, n) -> begin
((Support.List.rev names), binders)
end)))

let termToSmt = (fun t -> (let rec aux = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
if (i < 0) then begin
(Support.Microsoft.FStar.Util.format1 "(- %s)" (Support.Microsoft.FStar.Util.string_of_int (- (i))))
end else begin
(Support.Microsoft.FStar.Util.string_of_int i)
end
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
(Support.Microsoft.FStar.Util.format2 "(%s %s)" (op_to_string op) ((Support.String.concat "\n") (Support.List.map (aux n names) tms)))
end
| Quant ((qop, pats, wopt, sorts, body)) -> begin
(let _416512 = (name_binders_inner names n sorts)
in (match (_416512) with
| (names, binders, n) -> begin
(let binders = ((Support.String.concat " ") binders)
in (let pats_str = (match (pats) with
| ([]::[]) | ([]) -> begin
""
end
| _ -> begin
((Support.String.concat "\n") ((Support.List.map (fun pats -> (Support.Microsoft.FStar.Util.format1 "\n:pattern (%s)" (Support.String.concat " " (Support.List.map (fun p -> (Support.Microsoft.FStar.Util.format1 "%s" (aux n names p))) pats))))) pats))
end)
in (match ((pats, wopt)) with
| (([]::[], None)) | (([], None)) -> begin
(Support.Microsoft.FStar.Util.format3 "(%s (%s)\n %s)" (qop_to_string qop) binders (aux n names body))
end
| _ -> begin
(Support.Microsoft.FStar.Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders (aux n names body) (weightToSmt wopt) pats_str)
end)))
end))
end))
in (aux 0 [] t)))

let caption_to_string = (fun _415910 -> (match (_415910) with
| None -> begin
""
end
| Some (c) -> begin
(let _416537 = (Support.Microsoft.FStar.Util.splitlines c)
in (match (_416537) with
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
(Support.Microsoft.FStar.Util.format1 "\n; %s" ((fun _415911 -> (match (_415911) with
| [] -> begin
""
end
| h::t -> begin
h
end)) (Support.Microsoft.FStar.Util.splitlines c)))
end
| DeclFun ((f, argsorts, retsort, c)) -> begin
(let l = (Support.List.map strSort argsorts)
in (Support.Microsoft.FStar.Util.format4 "%s(declare-fun %s (%s) %s)" (caption_to_string c) f (Support.String.concat " " l) (strSort retsort)))
end
| DefineFun ((f, arg_sorts, retsort, body, c)) -> begin
(let _416568 = (name_binders arg_sorts)
in (match (_416568) with
| (names, binders) -> begin
(let body = (inst (Support.List.map mkFreeV names) body)
in (Support.Microsoft.FStar.Util.format5 "%s(define-fun %s (%s) %s\n %s)" (caption_to_string c) f (Support.String.concat " " binders) (strSort retsort) (termToSmt body)))
end))
end
| Assume ((t, c)) -> begin
(Support.Microsoft.FStar.Util.format2 "%s(assert %s)" (caption_to_string c) (termToSmt t))
end
| Eval (t) -> begin
(Support.Microsoft.FStar.Util.format1 "(eval %s)" (termToSmt t))
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
and mkPrelude = (fun z3options -> (let basic = (Support.String.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort String)\n(declare-fun String_constr_id (String) Int)\n\n(declare-sort Kind)\n(declare-fun Kind_constr_id (Kind) Int)\n\n(declare-sort Type)\n(declare-fun Type_constr_id (Type) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreKind (Type) Kind)\n(declare-fun PreType (Term) Type)\n(declare-fun Valid (Type) Bool)\n(declare-fun HasKind (Type Kind) Bool)\n(declare-fun HasType (Term Type) Bool)\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Type)) (HasType x t)))\n(declare-fun HasTypeFuel (Fuel Term Type) Bool)\n(declare-fun ApplyEF (Term Fuel) Term)\n(declare-fun ApplyEE (Term Term) Term)\n(declare-fun ApplyET (Term Type) Term)\n(declare-fun ApplyTE (Type Term) Type)\n(declare-fun ApplyTT (Type Type) Type)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsType (Type Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Type)\n(assert (forall ((e Term) (t Type))\n(!  (= (HasType e t)\n(HasTypeFuel MaxIFuel e t))\n:pattern ((HasType e t)))))\n(assert (forall ((f Fuel) (e Term) (t Type)) \n(! (= (HasTypeFuel (SFuel f) e t)\n(HasTypeFuel f e t))\n:pattern ((HasTypeFuel (SFuel f) e t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.Precedes ((a Type) (b Type) (t1 Term) (t2 Term)) Type\n(Precedes t1 t2))\n")
in (let constrs = (("String_const", (("String_const_proj_0", Int_sort))::[], String_sort, 0))::(("Kind_type", [], Kind_sort, 0))::(("Kind_arrow", (("Kind_arrow_id", Int_sort))::[], Kind_sort, 1))::(("Typ_fun", (("Typ_fun_id", Int_sort))::[], Type_sort, 1))::(("Typ_app", (("Typ_app_fst", Type_sort))::(("Typ_app_snd", Type_sort))::[], Type_sort, 2))::(("Typ_dep", (("Typ_dep_fst", Type_sort))::(("Typ_dep_snd", Term_sort))::[], Type_sort, 3))::(("Typ_uvar", (("Typ_uvar_fst", Int_sort))::[], Type_sort, 4))::(("Term_unit", [], Term_sort, 0))::(("BoxInt", (("BoxInt_proj_0", Int_sort))::[], Term_sort, 1))::(("BoxBool", (("BoxBool_proj_0", Bool_sort))::[], Term_sort, 2))::(("BoxString", (("BoxString_proj_0", String_sort))::[], Term_sort, 3))::(("BoxRef", (("BoxRef_proj_0", Ref_sort))::[], Term_sort, 4))::(("Exp_uvar", (("Exp_uvar_fst", Int_sort))::[], Term_sort, 5))::(("LexCons", (("LexCons_0", Term_sort))::(("LexCons_1", Term_sort))::[], Term_sort, 6))::[]
in (let bcons = ((Support.String.concat "\n") ((Support.List.map (declToSmt z3options)) ((Support.List.collect constructor_to_decl) constrs)))
in (let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Support.String.strcat (Support.String.strcat basic bcons) lex_ordering))))))

let mk_Kind_type = (mkApp ("Kind_type", []))

let mk_Typ_app = (fun t1 t2 -> (mkApp ("Typ_app", (t1)::(t2)::[])))

let mk_Typ_dep = (fun t1 t2 -> (mkApp ("Typ_dep", (t1)::(t2)::[])))

let mk_Typ_uvar = (fun i -> (mkApp ("Typ_uvar", ((mkInteger i))::[])))

let mk_Exp_uvar = (fun i -> (mkApp ("Exp_uvar", ((mkInteger i))::[])))

let mk_Term_unit = (mkApp ("Term_unit", []))

let boxInt = (fun t -> (mkApp ("BoxInt", (t)::[])))

let unboxInt = (fun t -> (mkApp ("BoxInt_proj_0", (t)::[])))

let boxBool = (fun t -> (mkApp ("BoxBool", (t)::[])))

let unboxBool = (fun t -> (mkApp ("BoxBool_proj_0", (t)::[])))

let boxString = (fun t -> (mkApp ("BoxString", (t)::[])))

let unboxString = (fun t -> (mkApp ("BoxString_proj_0", (t)::[])))

let boxRef = (fun t -> (mkApp ("BoxRef", (t)::[])))

let unboxRef = (fun t -> (mkApp ("BoxRef_proj_0", (t)::[])))

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

let mk_String_const = (fun i -> (mkApp ("String_const", ((mkInteger i))::[])))

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




