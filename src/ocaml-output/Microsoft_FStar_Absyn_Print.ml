
let infix_prim_ops = ((Microsoft_FStar_Absyn_Const.op_Addition, "+"))::((Microsoft_FStar_Absyn_Const.op_Subtraction, "-"))::((Microsoft_FStar_Absyn_Const.op_Multiply, "*"))::((Microsoft_FStar_Absyn_Const.op_Division, "/"))::((Microsoft_FStar_Absyn_Const.op_Eq, "="))::((Microsoft_FStar_Absyn_Const.op_ColonEq, ":="))::((Microsoft_FStar_Absyn_Const.op_notEq, "<>"))::((Microsoft_FStar_Absyn_Const.op_And, "&&"))::((Microsoft_FStar_Absyn_Const.op_Or, "||"))::((Microsoft_FStar_Absyn_Const.op_LTE, "<="))::((Microsoft_FStar_Absyn_Const.op_GTE, ">="))::((Microsoft_FStar_Absyn_Const.op_LT, "<"))::((Microsoft_FStar_Absyn_Const.op_GT, ">"))::((Microsoft_FStar_Absyn_Const.op_Modulus, "mod"))::[]

let unary_prim_ops = ((Microsoft_FStar_Absyn_Const.op_Negation, "not"))::((Microsoft_FStar_Absyn_Const.op_Minus, "-"))::[]

let infix_type_ops = ((Microsoft_FStar_Absyn_Const.and_lid, "/\\"))::((Microsoft_FStar_Absyn_Const.or_lid, "\\/"))::((Microsoft_FStar_Absyn_Const.imp_lid, "==>"))::((Microsoft_FStar_Absyn_Const.iff_lid, "<==>"))::((Microsoft_FStar_Absyn_Const.precedes_lid, "<<"))::((Microsoft_FStar_Absyn_Const.eq2_lid, "=="))::((Microsoft_FStar_Absyn_Const.eqT_lid, "=="))::[]

let unary_type_ops = ((Microsoft_FStar_Absyn_Const.not_lid, "~"))::[]

let is_prim_op = (fun ps f -> (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)) -> begin
((Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v)) ps)
end
| _ -> begin
false
end))

let is_type_op = (fun ps t -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (ftv) -> begin
((Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals ftv.Microsoft_FStar_Absyn_Syntax.v)) ps)
end
| _ -> begin
false
end))

let get_lid = (fun f -> (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)) -> begin
fv.Microsoft_FStar_Absyn_Syntax.v
end
| _ -> begin
(failwith "get_lid")
end))

let get_type_lid = (fun t -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (ftv) -> begin
ftv.Microsoft_FStar_Absyn_Syntax.v
end
| _ -> begin
(failwith "get_type_lid")
end))

let is_infix_prim_op = (fun e -> (is_prim_op (Support.Prims.fst (Support.List.split infix_prim_ops)) e))

let is_unary_prim_op = (fun e -> (is_prim_op (Support.Prims.fst (Support.List.split unary_prim_ops)) e))

let is_infix_type_op = (fun t -> (is_type_op (Support.Prims.fst (Support.List.split infix_type_ops)) t))

let is_unary_type_op = (fun t -> (is_type_op (Support.Prims.fst (Support.List.split unary_type_ops)) t))

let quants = ((Microsoft_FStar_Absyn_Const.forall_lid, "forall"))::((Microsoft_FStar_Absyn_Const.exists_lid, "exists"))::((Microsoft_FStar_Absyn_Const.allTyp_lid, "forall"))::((Microsoft_FStar_Absyn_Const.exTyp_lid, "exists"))::[]

let is_b2t = (fun t -> (is_type_op ((Microsoft_FStar_Absyn_Const.b2t_lid)::[]) t))

let is_quant = (fun t -> (is_type_op (Support.Prims.fst (Support.List.split quants)) t))

let is_ite = (fun t -> (is_type_op ((Microsoft_FStar_Absyn_Const.ite_lid)::[]) t))

let is_lex_cons = (fun f -> (is_prim_op ((Microsoft_FStar_Absyn_Const.lexcons_lid)::[]) f))

let is_lex_top = (fun f -> (is_prim_op ((Microsoft_FStar_Absyn_Const.lextop_lid)::[]) f))

let is_inr = (fun _96241 -> (match (_96241) with
| Support.Microsoft.FStar.Util.Inl (_) -> begin
false
end
| Support.Microsoft.FStar.Util.Inr (_) -> begin
true
end))

let rec reconstruct_lex = (fun e -> (match ((Microsoft_FStar_Absyn_Util.compress_exp e).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((f, args)) -> begin
(let args = (Support.List.filter (fun a -> (((Support.Prims.snd a) <> Some (Microsoft_FStar_Absyn_Syntax.Implicit)) && (is_inr (Support.Prims.fst a)))) args)
in (let exps = (Support.List.map (fun _96242 -> (match (_96242) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
(failwith "impossible")
end
| (Support.Microsoft.FStar.Util.Inr (x), _) -> begin
x
end)) args)
in if ((is_lex_cons f) && ((Support.List.length exps) = 2)) then begin
(match ((reconstruct_lex (Support.List.nth exps 1))) with
| Some (xs) -> begin
Some (((Support.List.nth exps 0))::xs)
end
| None -> begin
None
end)
end else begin
None
end))
end
| _ -> begin
if (is_lex_top e) then begin
Some ([])
end else begin
None
end
end))

let rec find = (fun f l -> (match (l) with
| [] -> begin
(failwith "blah")
end
| hd::tl -> begin
if (f hd) then begin
hd
end else begin
(find f tl)
end
end))

let find_lid = (fun x xs -> (Support.Prims.snd (find (fun p -> (Microsoft_FStar_Absyn_Syntax.lid_equals x (Support.Prims.fst p))) xs)))

let infix_prim_op_to_string = (fun e -> (find_lid (get_lid e) infix_prim_ops))

let unary_prim_op_to_string = (fun e -> (find_lid (get_lid e) unary_prim_ops))

let infix_type_op_to_string = (fun t -> (find_lid (get_type_lid t) infix_type_ops))

let unary_type_op_to_string = (fun t -> (find_lid (get_type_lid t) unary_type_ops))

let quant_to_string = (fun t -> (find_lid (get_type_lid t) quants))

let rec sli = (fun l -> (match (l.Microsoft_FStar_Absyn_Syntax.ns) with
| hd::tl when (hd.Microsoft_FStar_Absyn_Syntax.idText = "Prims") -> begin
(match (tl) with
| [] -> begin
l.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText
end
| _ -> begin
(Support.String.strcat (Support.String.strcat ((Support.String.concat ".") (Support.List.map (fun i -> i.Microsoft_FStar_Absyn_Syntax.idText) tl)) ".") l.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)
end)
end
| _ -> begin
if (! (Microsoft_FStar_Options.print_real_names)) then begin
l.Microsoft_FStar_Absyn_Syntax.str
end else begin
l.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText
end
end))

let strBvd = (fun bvd -> if (! (Microsoft_FStar_Options.print_real_names)) then begin
(Support.String.strcat bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText bvd.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText)
end else begin
if ((! (Microsoft_FStar_Options.hide_genident_nums)) && (Support.Microsoft.FStar.Util.starts_with bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText "_")) then begin
(Support.Prims.try_with (fun _96354 -> (match (_96354) with
| () -> begin
(let _96360 = (Support.Microsoft.FStar.Util.int_of_string (Support.Microsoft.FStar.Util.substring_from bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText 1))
in "_?")
end)) (fun _96353 -> bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText))
end else begin
bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText
end
end)

let filter_imp = (fun a -> ((Support.List.filter (fun _96243 -> (match (_96243) with
| (_, Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _ -> begin
true
end))) a))

let const_to_string = (fun x -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Const_unit -> begin
"()"
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (b) -> begin
if b then begin
"true"
end else begin
"false"
end
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (x) -> begin
(Support.Microsoft.FStar.Util.string_of_int32 x)
end
| Microsoft_FStar_Absyn_Syntax.Const_float (x) -> begin
(Support.Microsoft.FStar.Util.string_of_float x)
end
| Microsoft_FStar_Absyn_Syntax.Const_char (x) -> begin
(Support.String.strcat (Support.String.strcat "\'" (Support.Microsoft.FStar.Util.string_of_char x)) "\'")
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((bytes, _)) -> begin
(Support.Microsoft.FStar.Util.format1 "\"%s\"" (Support.Microsoft.FStar.Util.string_of_bytes bytes))
end
| Microsoft_FStar_Absyn_Syntax.Const_bytearray (_) -> begin
"<bytearray>"
end
| Microsoft_FStar_Absyn_Syntax.Const_int (x) -> begin
(Support.Microsoft.FStar.Util.string_of_int x)
end
| Microsoft_FStar_Absyn_Syntax.Const_int64 (_) -> begin
"<int64>"
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (_) -> begin
"<uint8>"
end))

let rec tag_of_typ = (fun t -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (_) -> begin
"Typ_btvar"
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (v) -> begin
(Support.String.strcat "Typ_const " v.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_) -> begin
"Typ_fun"
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_) -> begin
"Typ_refine"
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(Support.Microsoft.FStar.Util.format2 "Typ_app(%s, [%s args])" (tag_of_typ head) (Support.Microsoft.FStar.Util.string_of_int (Support.List.length args)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam (_) -> begin
"Typ_lam"
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_) -> begin
"Typ_ascribed"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern (_)) -> begin
"Typ_meta_pattern"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named (_)) -> begin
"Typ_meta_named"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled (_)) -> begin
"Typ_meta_labeled"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (_)) -> begin
"Typ_meta_refresh_label"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula (_)) -> begin
"Typ_meta_slack_formula"
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar (_) -> begin
"Typ_uvar"
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_) -> begin
"Typ_delayed"
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
"Typ_unknown"
end))
and tag_of_exp = (fun e -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (_) -> begin
"Exp_bvar"
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar (_) -> begin
"Exp_fvar"
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (_) -> begin
"Exp_constant"
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (_) -> begin
"Exp_abs"
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (_) -> begin
"Exp_app"
end
| Microsoft_FStar_Absyn_Syntax.Exp_match (_) -> begin
"Exp_match"
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed (_) -> begin
"Exp_ascribed"
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (_) -> begin
"Exp_let"
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar (_) -> begin
"Exp_uvar"
end
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_) -> begin
"Exp_delayed"
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((_, m))) -> begin
(Support.String.strcat "Exp_meta_desugared " (meta_e_to_string m))
end))
and meta_e_to_string = (fun _96244 -> (match (_96244) with
| Microsoft_FStar_Absyn_Syntax.Data_app -> begin
"Data_app"
end
| Microsoft_FStar_Absyn_Syntax.Sequence -> begin
"Sequence"
end
| Microsoft_FStar_Absyn_Syntax.Primop -> begin
"Primop"
end
| Microsoft_FStar_Absyn_Syntax.MaskedEffect -> begin
"MaskedEffect"
end))
and typ_to_string = (fun x -> (let x = (Microsoft_FStar_Absyn_Util.compress_typ x)
in (match (x.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_) -> begin
(failwith "impossible")
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((_, l))) -> begin
(sli l)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (meta) -> begin
(Support.Microsoft.FStar.Util.format1 "(Meta %s)" (meta_to_string meta))
end
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(strBvd btv.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (v) -> begin
(sli v.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, c)) -> begin
(Support.Microsoft.FStar.Util.format2 "(%s -> %s)" (binders_to_string " -> " binders) (comp_typ_to_string c))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((xt, f)) -> begin
(Support.Microsoft.FStar.Util.format3 "%s:%s{%s}" (strBvd xt.Microsoft_FStar_Absyn_Syntax.v) (typ_to_string xt.Microsoft_FStar_Absyn_Syntax.sort) (formula_to_string f))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, args)) -> begin
(let q_to_string = (fun k a -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t)) -> begin
(k (b, t))
end
| _ -> begin
(Support.Microsoft.FStar.Util.format2 "<Expected a type-lambda! got %s>%s" (tag_of_typ t) (typ_to_string t))
end))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(Support.Microsoft.FStar.Util.format1 "(<Expected a type!>%s)" (exp_to_string e))
end))
in (let qbinder_to_string = (q_to_string (fun x -> (binder_to_string (Support.Prims.fst x))))
in (let qbody_to_string = (q_to_string (fun x -> (typ_to_string (Support.Prims.snd x))))
in (let args' = if ((! (Microsoft_FStar_Options.print_implicits)) && (not ((is_quant t)))) then begin
args
end else begin
(Support.List.filter (fun _96245 -> (match (_96245) with
| (_, Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _ -> begin
true
end)) args)
end
in if ((is_ite t) && ((Support.List.length args) = 3)) then begin
(Support.Microsoft.FStar.Util.format3 "if %s then %s else %s" (arg_to_string (Support.List.nth args 0)) (arg_to_string (Support.List.nth args 1)) (arg_to_string (Support.List.nth args 2)))
end else begin
if ((is_b2t t) && ((Support.List.length args) = 1)) then begin
(arg_to_string (Support.List.nth args 0))
end else begin
if ((is_quant t) && ((Support.List.length args) <= 2)) then begin
(Support.Microsoft.FStar.Util.format3 "(%s (%s). %s)" (quant_to_string t) (qbinder_to_string (Support.List.nth args' 0)) (qbody_to_string (Support.List.nth args' 0)))
end else begin
if ((is_infix_type_op t) && ((Support.List.length args') = 2)) then begin
(Support.Microsoft.FStar.Util.format3 "(%s %s %s)" (arg_to_string (Support.List.nth args' 0)) ((infix_type_op_to_string) t) (arg_to_string (Support.List.nth args' 1)))
end else begin
if ((is_unary_type_op t) && ((Support.List.length args') = 1)) then begin
(Support.Microsoft.FStar.Util.format2 "(%s %s)" ((unary_type_op_to_string) t) (arg_to_string (Support.List.nth args' 0)))
end else begin
(Support.Microsoft.FStar.Util.format2 "(%s %s)" (typ_to_string t) (args_to_string args))
end
end
end
end
end))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((binders, t2)) -> begin
(Support.Microsoft.FStar.Util.format2 "(fun %s -> %s)" (binders_to_string " " binders) (typ_to_string t2))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, k)) -> begin
if (! (Microsoft_FStar_Options.print_real_names)) then begin
(Support.Microsoft.FStar.Util.format2 "(%s <: %s)" (typ_to_string t) (kind_to_string k))
end else begin
(typ_to_string t)
end
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
"<UNKNOWN>"
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(match ((Microsoft_FStar_Absyn_Visit.compress_typ_aux false x)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
(uvar_t_to_string (uv, k))
end
| t -> begin
(typ_to_string t)
end)
end)))
and uvar_t_to_string = (fun _96573 -> (match (_96573) with
| (uv, k) -> begin
if (false && (! (Microsoft_FStar_Options.print_real_names))) then begin
(Support.Microsoft.FStar.Util.format2 "(U%s : %s)" (if (! (Microsoft_FStar_Options.hide_uvar_nums)) then begin
"?"
end else begin
(Support.Microsoft.FStar.Util.string_of_int (Support.Microsoft.FStar.Unionfind.uvar_id uv))
end) (kind_to_string k))
end else begin
(Support.Microsoft.FStar.Util.format1 "U%s" (if (! (Microsoft_FStar_Options.hide_uvar_nums)) then begin
"?"
end else begin
(Support.Microsoft.FStar.Util.string_of_int (Support.Microsoft.FStar.Unionfind.uvar_id uv))
end))
end
end))
and imp_to_string = (fun s _96246 -> (match (_96246) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
(Support.String.strcat "#" s)
end
| Some (Microsoft_FStar_Absyn_Syntax.Equality) -> begin
(Support.String.strcat "=" s)
end
| _ -> begin
s
end))
and binder_to_string' = (fun is_arrow b -> (match (b) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
if ((Microsoft_FStar_Absyn_Syntax.is_null_binder b) || ((not ((! (Microsoft_FStar_Options.print_real_names)))) && (Microsoft_FStar_Absyn_Syntax.is_null_pp a.Microsoft_FStar_Absyn_Syntax.v))) then begin
(kind_to_string a.Microsoft_FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((! (Microsoft_FStar_Options.print_implicits))))) then begin
(imp_to_string (strBvd a.Microsoft_FStar_Absyn_Syntax.v) imp)
end else begin
(imp_to_string (Support.String.strcat (Support.String.strcat (strBvd a.Microsoft_FStar_Absyn_Syntax.v) ":") (kind_to_string a.Microsoft_FStar_Absyn_Syntax.sort)) imp)
end
end
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
if ((Microsoft_FStar_Absyn_Syntax.is_null_binder b) || ((not ((! (Microsoft_FStar_Options.print_real_names)))) && (Microsoft_FStar_Absyn_Syntax.is_null_pp x.Microsoft_FStar_Absyn_Syntax.v))) then begin
(typ_to_string x.Microsoft_FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((! (Microsoft_FStar_Options.print_implicits))))) then begin
(imp_to_string (strBvd x.Microsoft_FStar_Absyn_Syntax.v) imp)
end else begin
(imp_to_string (Support.String.strcat (Support.String.strcat (strBvd x.Microsoft_FStar_Absyn_Syntax.v) ":") (typ_to_string x.Microsoft_FStar_Absyn_Syntax.sort)) imp)
end
end
end))
and binder_to_string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string = (fun b -> (binder_to_string' true b))
and binders_to_string = (fun sep bs -> (let bs = if (! (Microsoft_FStar_Options.print_implicits)) then begin
bs
end else begin
(filter_imp bs)
end
in if (sep = " -> ") then begin
((Support.String.concat sep) ((Support.List.map arrow_binder_to_string) bs))
end else begin
((Support.String.concat sep) ((Support.List.map binder_to_string) bs))
end))
and arg_to_string = (fun _96247 -> (match (_96247) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(imp_to_string (typ_to_string a) imp)
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(imp_to_string (exp_to_string x) imp)
end))
and args_to_string = (fun args -> (let args = if (! (Microsoft_FStar_Options.print_implicits)) then begin
args
end else begin
(filter_imp args)
end
in ((Support.String.concat " ") ((Support.List.map arg_to_string) args))))
and lcomp_typ_to_string = (fun lc -> (Support.Microsoft.FStar.Util.format2 "%s %s" (sli lc.Microsoft_FStar_Absyn_Syntax.eff_name) (typ_to_string lc.Microsoft_FStar_Absyn_Syntax.res_typ)))
and comp_typ_to_string = (fun c -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(Support.Microsoft.FStar.Util.format1 "Tot %s" (typ_to_string t))
end
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
(let basic = if (((Support.Microsoft.FStar.Util.for_some (fun _96248 -> (match (_96248) with
| Microsoft_FStar_Absyn_Syntax.TOTAL -> begin
true
end
| _ -> begin
false
end))) c.Microsoft_FStar_Absyn_Syntax.flags) && (not ((! (Microsoft_FStar_Options.print_effect_args))))) then begin
(Support.Microsoft.FStar.Util.format1 "Tot %s" (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ))
end else begin
if ((not ((! (Microsoft_FStar_Options.print_effect_args)))) && (Microsoft_FStar_Absyn_Syntax.lid_equals c.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.ml_effect_lid)) then begin
(typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
end else begin
if ((not ((! (Microsoft_FStar_Options.print_effect_args)))) && ((Support.Microsoft.FStar.Util.for_some (fun _96249 -> (match (_96249) with
| Microsoft_FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _ -> begin
false
end))) c.Microsoft_FStar_Absyn_Syntax.flags)) then begin
(Support.Microsoft.FStar.Util.format1 "ALL %s" (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ))
end else begin
if (! (Microsoft_FStar_Options.print_effect_args)) then begin
(Support.Microsoft.FStar.Util.format3 "%s (%s) %s" (sli c.Microsoft_FStar_Absyn_Syntax.effect_name) (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ) ((Support.String.concat ", ") ((Support.List.map effect_arg_to_string) c.Microsoft_FStar_Absyn_Syntax.effect_args)))
end else begin
(Support.Microsoft.FStar.Util.format2 "%s (%s)" (sli c.Microsoft_FStar_Absyn_Syntax.effect_name) (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ))
end
end
end
end
in (let dec = ((Support.String.concat " ") ((Support.List.collect (fun _96250 -> (match (_96250) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
((Support.Microsoft.FStar.Util.format1 " (decreases %s)" (exp_to_string e)))::[]
end
| _ -> begin
[]
end))) c.Microsoft_FStar_Absyn_Syntax.flags))
in (Support.Microsoft.FStar.Util.format2 "%s%s" basic dec)))
end))
and effect_arg_to_string = (fun e -> (match (e) with
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(exp_to_string e)
end
| (Support.Microsoft.FStar.Util.Inl (wp), _) -> begin
(formula_to_string wp)
end))
and formula_to_string = (fun phi -> (typ_to_string phi))
and formula_to_string_old_now_unused = (fun phi -> (let const_op = (fun f _96644 -> f)
in (let un_op = (fun f _96251 -> (match (_96251) with
| (Support.Microsoft.FStar.Util.Inl (t), _)::[] -> begin
(Support.Microsoft.FStar.Util.format2 "%s %s" f (formula_to_string t))
end
| _ -> begin
(failwith "impos")
end))
in (let bin_top = (fun f _96252 -> (match (_96252) with
| (Support.Microsoft.FStar.Util.Inl (t1), _)::(Support.Microsoft.FStar.Util.Inl (t2), _)::[] -> begin
(Support.Microsoft.FStar.Util.format3 "%s %s %s" (formula_to_string t1) f (formula_to_string t2))
end
| _ -> begin
(failwith "Impos")
end))
in (let bin_eop = (fun f _96253 -> (match (_96253) with
| (Support.Microsoft.FStar.Util.Inr (e1), _)::(Support.Microsoft.FStar.Util.Inr (e2), _)::[] -> begin
(Support.Microsoft.FStar.Util.format3 "%s %s %s" (exp_to_string e1) f (exp_to_string e2))
end
| _ -> begin
(failwith "impos")
end))
in (let ite = (fun _96254 -> (match (_96254) with
| (Support.Microsoft.FStar.Util.Inl (t1), _)::(Support.Microsoft.FStar.Util.Inl (t2), _)::(Support.Microsoft.FStar.Util.Inl (t3), _)::[] -> begin
(Support.Microsoft.FStar.Util.format3 "if %s then %s else %s" (formula_to_string t1) (formula_to_string t2) (formula_to_string t3))
end
| _ -> begin
(failwith "impos")
end))
in (let eq_op = (fun _96255 -> (match (_96255) with
| (Support.Microsoft.FStar.Util.Inl (t1), _)::(Support.Microsoft.FStar.Util.Inl (t2), _)::(Support.Microsoft.FStar.Util.Inr (e1), _)::(Support.Microsoft.FStar.Util.Inr (e2), _)::[] -> begin
if (! (Microsoft_FStar_Options.print_implicits)) then begin
(Support.Microsoft.FStar.Util.format4 "Eq2 %s %s %s %s" (typ_to_string t1) (typ_to_string t2) (exp_to_string e1) (exp_to_string e2))
end else begin
(Support.Microsoft.FStar.Util.format2 "%s == %s" (exp_to_string e1) (exp_to_string e2))
end
end
| (Support.Microsoft.FStar.Util.Inr (e1), _)::(Support.Microsoft.FStar.Util.Inr (e2), _)::[] -> begin
(Support.Microsoft.FStar.Util.format2 "%s == %s" (exp_to_string e1) (exp_to_string e2))
end
| _ -> begin
(failwith "Impossible")
end))
in (let connectives = ((Microsoft_FStar_Absyn_Const.and_lid, (bin_top "/\\")))::((Microsoft_FStar_Absyn_Const.or_lid, (bin_top "\\/")))::((Microsoft_FStar_Absyn_Const.imp_lid, (bin_top "==>")))::((Microsoft_FStar_Absyn_Const.iff_lid, (bin_top "<==>")))::((Microsoft_FStar_Absyn_Const.ite_lid, ite))::((Microsoft_FStar_Absyn_Const.not_lid, (un_op "~")))::((Microsoft_FStar_Absyn_Const.eqT_lid, (bin_top "==")))::((Microsoft_FStar_Absyn_Const.eq2_lid, eq_op))::((Microsoft_FStar_Absyn_Const.true_lid, (const_op "True")))::((Microsoft_FStar_Absyn_Const.false_lid, (const_op "False")))::[]
in (let fallback = (fun phi -> (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((binders, phi)) -> begin
(Support.Microsoft.FStar.Util.format2 "(fun %s => %s)" (binders_to_string " " binders) (formula_to_string phi))
end
| _ -> begin
(typ_to_string phi)
end))
in (match ((Microsoft_FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (Microsoft_FStar_Absyn_Util.BaseConn ((op, arms))) -> begin
(match (((Support.List.tryFind (fun _96763 -> (match (_96763) with
| (l, _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals op l)
end))) connectives)) with
| None -> begin
(fallback phi)
end
| Some ((_, f)) -> begin
(f arms)
end)
end
| Some (Microsoft_FStar_Absyn_Util.QAll ((vars, _, body))) -> begin
(Support.Microsoft.FStar.Util.format2 "(forall %s. %s)" (binders_to_string " " vars) (formula_to_string body))
end
| Some (Microsoft_FStar_Absyn_Util.QEx ((vars, _, body))) -> begin
(Support.Microsoft.FStar.Util.format2 "(exists %s. %s)" (binders_to_string " " vars) (formula_to_string body))
end))))))))))
and exp_to_string = (fun x -> (match ((Microsoft_FStar_Absyn_Util.compress_exp x).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_) -> begin
(failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _))) -> begin
(exp_to_string e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, t)) -> begin
(uvar_e_to_string (uv, t))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (bvv) -> begin
(strBvd bvv.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)) -> begin
(sli fv.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(const_to_string c)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((binders, e)) -> begin
(Support.Microsoft.FStar.Util.format2 "(fun %s -> %s)" (binders_to_string " " binders) (exp_to_string e))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((e, args)) -> begin
(let lex = if (! (Microsoft_FStar_Options.print_implicits)) then begin
None
end else begin
(reconstruct_lex x)
end
in (match (lex) with
| Some (es) -> begin
(Support.String.strcat (Support.String.strcat "%[" (Support.String.concat "; " (Support.List.map exp_to_string es))) "]")
end
| None -> begin
(let args' = ((Support.List.filter (fun _96256 -> (match (_96256) with
| (Support.Microsoft.FStar.Util.Inr (_), _) -> begin
true
end
| _ -> begin
false
end))) (filter_imp args))
in if ((is_infix_prim_op e) && ((Support.List.length args') = 2)) then begin
(Support.Microsoft.FStar.Util.format3 "(%s %s %s)" (arg_to_string (Support.List.nth args' 0)) ((infix_prim_op_to_string) e) (arg_to_string (Support.List.nth args' 1)))
end else begin
if ((is_unary_prim_op e) && ((Support.List.length args') = 1)) then begin
(Support.Microsoft.FStar.Util.format2 "(%s %s)" ((unary_prim_op_to_string) e) (arg_to_string (Support.List.nth args' 0)))
end else begin
(Support.Microsoft.FStar.Util.format2 "(%s %s)" (exp_to_string e) (args_to_string args))
end
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, pats)) -> begin
(Support.Microsoft.FStar.Util.format2 "(match %s with %s)" (exp_to_string e) (Support.Microsoft.FStar.Util.concat_l "\n\t" ((Support.List.map (fun _96836 -> (match (_96836) with
| (p, wopt, e) -> begin
(Support.Microsoft.FStar.Util.format3 "%s %s -> %s" (pat_to_string p) (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(Support.Microsoft.FStar.Util.format1 "when %s" (exp_to_string w))
end) (exp_to_string e))
end))) pats)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t)) -> begin
(Support.Microsoft.FStar.Util.format2 "(%s:%s)" (exp_to_string e) (typ_to_string t))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, e)) -> begin
(Support.Microsoft.FStar.Util.format2 "%s in %s" (lbs_to_string lbs) (exp_to_string e))
end))
and uvar_e_to_string = (fun _96851 -> (match (_96851) with
| (uv, _) -> begin
(Support.String.strcat "\'e" (if (! (Microsoft_FStar_Options.hide_uvar_nums)) then begin
"?"
end else begin
(Support.Microsoft.FStar.Util.string_of_int (Support.Microsoft.FStar.Unionfind.uvar_id uv))
end))
end))
and lbs_to_string = (fun lbs -> (Support.Microsoft.FStar.Util.format2 "let %s %s" (if (Support.Prims.fst lbs) then begin
"rec"
end else begin
""
end) (Support.Microsoft.FStar.Util.concat_l "\n and " ((Support.List.map (fun _96856 -> (match (_96856) with
| (x, t, e) -> begin
(Support.Microsoft.FStar.Util.format3 "%s:%s = %s" (lbname_to_string x) (typ_to_string t) (exp_to_string e))
end))) (Support.Prims.snd lbs)))))
and lbname_to_string = (fun x -> (match (x) with
| Support.Microsoft.FStar.Util.Inl (bvd) -> begin
(strBvd bvd)
end
| Support.Microsoft.FStar.Util.Inr (lid) -> begin
(sli lid)
end))
and either_to_string = (fun x -> (match (x) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(typ_to_string t)
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(exp_to_string e)
end))
and either_l_to_string = (fun delim l -> ((Support.Microsoft.FStar.Util.concat_l delim) ((Support.List.map either_to_string) l)))
and meta_to_string = (fun x -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _, _)) -> begin
(Support.Microsoft.FStar.Util.format1 "(refresh) %s" (typ_to_string t))
end
| Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, _, _)) -> begin
(Support.Microsoft.FStar.Util.format2 "(labeled \"%s\") %s" l (typ_to_string t))
end
| Microsoft_FStar_Absyn_Syntax.Meta_named ((_, l)) -> begin
(sli l)
end
| Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, ps)) -> begin
(Support.Microsoft.FStar.Util.format2 "{:pattern %s} %s" (args_to_string ps) (typ_to_string t))
end
| Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, _)) -> begin
(Support.Microsoft.FStar.Util.format2 "%s /\\ %s" (formula_to_string t1) (formula_to_string t2))
end))
and kind_to_string = (fun x -> (match ((Microsoft_FStar_Absyn_Util.compress_kind x).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam (_) -> begin
(failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed (_) -> begin
(failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, args)) -> begin
(uvar_k_to_string' (uv, args))
end
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
"Type"
end
| Microsoft_FStar_Absyn_Syntax.Kind_effect -> begin
"Effect"
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev (((n, args), k)) -> begin
if (! (Microsoft_FStar_Options.print_real_names)) then begin
(kind_to_string k)
end else begin
(Support.Microsoft.FStar.Util.format2 "%s %s" (sli n) (args_to_string args))
end
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((binders, k)) -> begin
(Support.Microsoft.FStar.Util.format2 "(%s -> %s)" (binders_to_string " -> " binders) (kind_to_string k))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun uv -> (Support.String.strcat "\'k_" (if (! (Microsoft_FStar_Options.hide_uvar_nums)) then begin
"?"
end else begin
(Support.Microsoft.FStar.Util.string_of_int (Support.Microsoft.FStar.Unionfind.uvar_id uv))
end)))
and uvar_k_to_string' = (fun _96927 -> (match (_96927) with
| (uv, args) -> begin
(let str = if (! (Microsoft_FStar_Options.hide_uvar_nums)) then begin
"?"
end else begin
(Support.Microsoft.FStar.Util.string_of_int (Support.Microsoft.FStar.Unionfind.uvar_id uv))
end
in (Support.Microsoft.FStar.Util.format2 "(\'k_%s %s)" str (args_to_string args)))
end))
and pat_to_string = (fun x -> (match (x.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, pats)) -> begin
(Support.Microsoft.FStar.Util.format2 "(%s %s)" (sli l.Microsoft_FStar_Absyn_Syntax.v) ((Support.String.concat " ") (Support.List.map pat_to_string pats)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _)) -> begin
(Support.Microsoft.FStar.Util.format1 ".%s" (strBvd x.Microsoft_FStar_Absyn_Syntax.v))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((x, _)) -> begin
(Support.Microsoft.FStar.Util.format1 ".\'%s" (strBvd x.Microsoft_FStar_Absyn_Syntax.v))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, true)) -> begin
(Support.Microsoft.FStar.Util.format1 "#%s" (strBvd x.Microsoft_FStar_Absyn_Syntax.v))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, false)) -> begin
(strBvd x.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(strBvd a.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (_) -> begin
"_"
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (_) -> begin
"\'_"
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(Support.Microsoft.FStar.Util.concat_l " | " (Support.List.map pat_to_string ps))
end))

let subst_to_string = (fun subst -> ((Support.Microsoft.FStar.Util.format1 "{%s}") ((Support.String.concat ", ") (Support.List.map (fun _96257 -> (match (_96257) with
| Support.Microsoft.FStar.Util.Inl ((a, t)) -> begin
(Support.Microsoft.FStar.Util.format2 "(%s -> %s)" (strBvd a) (typ_to_string t))
end
| Support.Microsoft.FStar.Util.Inr ((x, e)) -> begin
(Support.Microsoft.FStar.Util.format2 "(%s -> %s)" (strBvd x) (exp_to_string e))
end)) subst))))

let freevars_to_string = (fun fvs -> (let f = (fun l -> ((Support.String.concat ", ") ((Support.List.map (fun t -> (strBvd t.Microsoft_FStar_Absyn_Syntax.v))) ((Support.Microsoft.FStar.Util.set_elements) l))))
in (Support.Microsoft.FStar.Util.format2 "ftvs={%s}, fxvs={%s}" (f fvs.Microsoft_FStar_Absyn_Syntax.ftvs) (f fvs.Microsoft_FStar_Absyn_Syntax.fxvs))))

let qual_to_string = (fun _96258 -> (match (_96258) with
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
"logic"
end
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
"opaque"
end
| Microsoft_FStar_Absyn_Syntax.Discriminator (_) -> begin
"discriminator"
end
| Microsoft_FStar_Absyn_Syntax.Projector (_) -> begin
"projector"
end
| Microsoft_FStar_Absyn_Syntax.RecordType (ids) -> begin
(Support.Microsoft.FStar.Util.format1 "record(%s)" ((Support.String.concat ", ") ((Support.List.map (fun id -> id.Microsoft_FStar_Absyn_Syntax.idText)) ids)))
end
| _ -> begin
"other"
end))

let quals_to_string = (fun quals -> ((Support.String.concat " ") ((Support.List.map qual_to_string) quals)))

let rec sigelt_to_string = (fun x -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Sig_pragma ((Microsoft_FStar_Absyn_Syntax.ResetOptions, _)) -> begin
"#reset-options"
end
| Microsoft_FStar_Absyn_Syntax.Sig_pragma ((Microsoft_FStar_Absyn_Syntax.SetOptions (s), _)) -> begin
(Support.Microsoft.FStar.Util.format1 "#set-options \"%s\"" s)
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _, _, quals, _)) -> begin
(Support.Microsoft.FStar.Util.format4 "%s type %s %s : %s" (quals_to_string quals) lid.Microsoft_FStar_Absyn_Syntax.str (binders_to_string " " tps) (kind_to_string k))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k, t, _, _)) -> begin
(Support.Microsoft.FStar.Util.format4 "type %s %s : %s = %s" lid.Microsoft_FStar_Absyn_Syntax.str (binders_to_string " " tps) (kind_to_string k) (typ_to_string t))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, t, _, _, _, _)) -> begin
(Support.Microsoft.FStar.Util.format2 "datacon %s : %s" lid.Microsoft_FStar_Absyn_Syntax.str (typ_to_string t))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, _)) -> begin
(Support.Microsoft.FStar.Util.format3 "%s val %s : %s" (quals_to_string quals) lid.Microsoft_FStar_Absyn_Syntax.str (typ_to_string t))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((lid, f, _, _)) -> begin
(Support.Microsoft.FStar.Util.format2 "val %s : %s" lid.Microsoft_FStar_Absyn_Syntax.str (typ_to_string f))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, _, _, b)) -> begin
(lbs_to_string lbs)
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, _)) -> begin
(Support.Microsoft.FStar.Util.format1 "let _ = %s" (exp_to_string e))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _, _, _)) -> begin
((Support.String.concat "\n") (Support.List.map sigelt_to_string ses))
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_) -> begin
"new_effect { ... }"
end
| Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_) -> begin
"sub_effect ..."
end
| Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_) -> begin
"kind ..."
end
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((l, tps, c, _, _)) -> begin
(Support.Microsoft.FStar.Util.format3 "effect %s %s = %s" (sli l) (binders_to_string " " tps) (comp_typ_to_string c))
end))

let format_error = (fun r msg -> (Support.Microsoft.FStar.Util.format2 "%s: %s\n" (Support.Microsoft.FStar.Range.string_of_range r) msg))

let rec sigelt_to_string_short = (fun x -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Sig_let (((_, (Support.Microsoft.FStar.Util.Inr (l), t, _)::[]), _, _, _)) -> begin
(Support.Microsoft.FStar.Util.format2 "let %s : %s" l.Microsoft_FStar_Absyn_Syntax.str (typ_to_string t))
end
| _ -> begin
((Support.String.concat ", ") ((Support.List.map (fun l -> l.Microsoft_FStar_Absyn_Syntax.str)) (Microsoft_FStar_Absyn_Util.lids_of_sigelt x)))
end))

let rec modul_to_string = (fun m -> (Support.Microsoft.FStar.Util.format2 "module %s\n%s" (sli m.Microsoft_FStar_Absyn_Syntax.name) ((Support.String.concat "\n") (Support.List.map sigelt_to_string m.Microsoft_FStar_Absyn_Syntax.declarations))))




