
let infix_prim_ops = ((Microsoft_FStar_Absyn_Const.op_Addition, "+"))::((Microsoft_FStar_Absyn_Const.op_Subtraction, "-"))::((Microsoft_FStar_Absyn_Const.op_Multiply, "*"))::((Microsoft_FStar_Absyn_Const.op_Division, "/"))::((Microsoft_FStar_Absyn_Const.op_Eq, "="))::((Microsoft_FStar_Absyn_Const.op_ColonEq, ":="))::((Microsoft_FStar_Absyn_Const.op_notEq, "<>"))::((Microsoft_FStar_Absyn_Const.op_And, "&&"))::((Microsoft_FStar_Absyn_Const.op_Or, "||"))::((Microsoft_FStar_Absyn_Const.op_LTE, "<="))::((Microsoft_FStar_Absyn_Const.op_GTE, ">="))::((Microsoft_FStar_Absyn_Const.op_LT, "<"))::((Microsoft_FStar_Absyn_Const.op_GT, ">"))::((Microsoft_FStar_Absyn_Const.op_Modulus, "mod"))::[]

let unary_prim_ops = ((Microsoft_FStar_Absyn_Const.op_Negation, "not"))::((Microsoft_FStar_Absyn_Const.op_Minus, "-"))::[]

let infix_type_ops = ((Microsoft_FStar_Absyn_Const.and_lid, "/\\"))::((Microsoft_FStar_Absyn_Const.or_lid, "\\/"))::((Microsoft_FStar_Absyn_Const.imp_lid, "==>"))::((Microsoft_FStar_Absyn_Const.iff_lid, "<==>"))::((Microsoft_FStar_Absyn_Const.precedes_lid, "<<"))::((Microsoft_FStar_Absyn_Const.eq2_lid, "=="))::((Microsoft_FStar_Absyn_Const.eqT_lid, "=="))::[]

let unary_type_ops = ((Microsoft_FStar_Absyn_Const.not_lid, "~"))::[]

let is_prim_op = (fun ( ps  :  Microsoft_FStar_Absyn_Syntax.lident list ) ( f  :  (Microsoft_FStar_Absyn_Syntax.exp', 'u24u1048) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)) -> begin
(Support.Prims.pipe_right ps (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v)))
end
| _ -> begin
false
end))

let is_type_op = (fun ( ps  :  Microsoft_FStar_Absyn_Syntax.lident list ) ( t  :  (Microsoft_FStar_Absyn_Syntax.typ', 'u24u1113) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(Support.Prims.pipe_right ps (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals ftv.Microsoft_FStar_Absyn_Syntax.v)))
end
| _ -> begin
false
end))

let get_lid = (fun ( f  :  (Microsoft_FStar_Absyn_Syntax.exp', 'u24u1182) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)) -> begin
fv.Microsoft_FStar_Absyn_Syntax.v
end
| _ -> begin
(failwith ("get_lid"))
end))

let get_type_lid = (fun ( t  :  (Microsoft_FStar_Absyn_Syntax.typ', 'u24u1243) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (ftv) -> begin
ftv.Microsoft_FStar_Absyn_Syntax.v
end
| _ -> begin
(failwith ("get_type_lid"))
end))

let is_infix_prim_op = (fun ( e  :  Microsoft_FStar_Absyn_Syntax.exp ) -> (is_prim_op (Support.Prims.fst (Support.List.split infix_prim_ops)) e))

let is_unary_prim_op = (fun ( e  :  Microsoft_FStar_Absyn_Syntax.exp ) -> (is_prim_op (Support.Prims.fst (Support.List.split unary_prim_ops)) e))

let is_infix_type_op = (fun ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (is_type_op (Support.Prims.fst (Support.List.split infix_type_ops)) t))

let is_unary_type_op = (fun ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (is_type_op (Support.Prims.fst (Support.List.split unary_type_ops)) t))

let quants = ((Microsoft_FStar_Absyn_Const.forall_lid, "forall"))::((Microsoft_FStar_Absyn_Const.exists_lid, "exists"))::((Microsoft_FStar_Absyn_Const.allTyp_lid, "forall"))::((Microsoft_FStar_Absyn_Const.exTyp_lid, "exists"))::[]

let is_b2t = (fun ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (is_type_op ((Microsoft_FStar_Absyn_Const.b2t_lid)::[]) t))

let is_quant = (fun ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (is_type_op (Support.Prims.fst (Support.List.split quants)) t))

let is_ite = (fun ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (is_type_op ((Microsoft_FStar_Absyn_Const.ite_lid)::[]) t))

let is_lex_cons = (fun ( f  :  Microsoft_FStar_Absyn_Syntax.exp ) -> (is_prim_op ((Microsoft_FStar_Absyn_Const.lexcons_lid)::[]) f))

let is_lex_top = (fun ( f  :  Microsoft_FStar_Absyn_Syntax.exp ) -> (is_prim_op ((Microsoft_FStar_Absyn_Const.lextop_lid)::[]) f))

let is_inr = (fun ( _24_1  :  ('u24u1357, 'u24u1356) Support.Microsoft.FStar.Util.either ) -> (match (_24_1) with
| Support.Microsoft.FStar.Util.Inl (_) -> begin
false
end
| Support.Microsoft.FStar.Util.Inr (_) -> begin
true
end))

let rec reconstruct_lex = (fun ( e  :  Microsoft_FStar_Absyn_Syntax.exp ) -> (match ((let _52_6610 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _52_6610.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((f, args)) -> begin
(let args = (Support.List.filter (fun ( a  :  Microsoft_FStar_Absyn_Syntax.arg ) -> (((Support.Prims.snd a) <> Some (Microsoft_FStar_Absyn_Syntax.Implicit)) && (is_inr (Support.Prims.fst a)))) args)
in (let exps = (Support.List.map (fun ( _24_2  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_24_2) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
(failwith ("impossible"))
end
| (Support.Microsoft.FStar.Util.Inr (x), _) -> begin
x
end)) args)
in (match ((let _52_6613 = (is_lex_cons f)
in (_52_6613 && ((Support.List.length exps) = 2)))) with
| true -> begin
(match ((let _52_6614 = (Support.List.nth exps 1)
in (reconstruct_lex _52_6614))) with
| Some (xs) -> begin
(let _52_6616 = (let _52_6615 = (Support.List.nth exps 0)
in (_52_6615)::xs)
in Some (_52_6616))
end
| None -> begin
None
end)
end
| false -> begin
None
end)))
end
| _ -> begin
(match ((is_lex_top e)) with
| true -> begin
Some ([])
end
| false -> begin
None
end)
end))

let rec find = (fun ( f  :  'u24u1717  ->  bool ) ( l  :  'u24u1717 list ) -> (match (l) with
| [] -> begin
(failwith ("blah"))
end
| hd::tl -> begin
(match ((f hd)) with
| true -> begin
hd
end
| false -> begin
(Obj.magic (find (Obj.magic tl)))
end)
end))

let find_lid = (fun ( x  :  Microsoft_FStar_Absyn_Syntax.lident ) ( xs  :  (Microsoft_FStar_Absyn_Syntax.lident * string) list ) -> (let _52_6627 = (find (fun ( p  :  (Microsoft_FStar_Absyn_Syntax.lident * string) ) -> (Microsoft_FStar_Absyn_Syntax.lid_equals x (Support.Prims.fst p))) xs)
in (Support.Prims.snd _52_6627)))

let infix_prim_op_to_string = (fun ( e  :  (Microsoft_FStar_Absyn_Syntax.exp', 'u24u1744) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _52_6629 = (get_lid e)
in (find_lid _52_6629 infix_prim_ops)))

let unary_prim_op_to_string = (fun ( e  :  (Microsoft_FStar_Absyn_Syntax.exp', 'u24u1750) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _52_6631 = (get_lid e)
in (find_lid _52_6631 unary_prim_ops)))

let infix_type_op_to_string = (fun ( t  :  (Microsoft_FStar_Absyn_Syntax.typ', 'u24u1756) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _52_6633 = (get_type_lid t)
in (find_lid _52_6633 infix_type_ops)))

let unary_type_op_to_string = (fun ( t  :  (Microsoft_FStar_Absyn_Syntax.typ', 'u24u1762) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _52_6635 = (get_type_lid t)
in (find_lid _52_6635 unary_type_ops)))

let quant_to_string = (fun ( t  :  (Microsoft_FStar_Absyn_Syntax.typ', 'u24u1768) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _52_6637 = (get_type_lid t)
in (find_lid _52_6637 quants)))

let rec sli = (fun ( l  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (match ((Support.ST.read Microsoft_FStar_Options.print_real_names)) with
| true -> begin
l.Microsoft_FStar_Absyn_Syntax.str
end
| false -> begin
l.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText
end))

let strBvd = (fun ( bvd  :  'u24u1890 Microsoft_FStar_Absyn_Syntax.bvdef ) -> (match ((Support.ST.read Microsoft_FStar_Options.print_real_names)) with
| true -> begin
(Support.String.strcat bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText bvd.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText)
end
| false -> begin
(match ((let _52_6641 = (Support.ST.read Microsoft_FStar_Options.hide_genident_nums)
in (_52_6641 && (Support.Microsoft.FStar.Util.starts_with bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText "_")))) with
| true -> begin
(Support.Prims.try_with (fun ( _24_105  :  unit ) -> (match (()) with
| () -> begin
(let _24_111 = (let _52_6643 = (Support.Microsoft.FStar.Util.substring_from bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText 1)
in (Support.Microsoft.FStar.Util.int_of_string _52_6643))
in "_?")
end)) (fun ( _24_104  :  Support.Prims.exn ) -> (match (_24_104) with
| _ -> begin
bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText
end)))
end
| false -> begin
bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText
end)
end))

let filter_imp = (fun ( a  :  ('u24u1954 * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) -> (Support.Prims.pipe_right a (Support.List.filter (fun ( _24_3  :  ('u24u1954 * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_24_3) with
| (_, Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _ -> begin
true
end)))))

let const_to_string = (fun ( x  :  Microsoft_FStar_Absyn_Syntax.sconst ) -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Const_unit -> begin
"()"
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (b) -> begin
(match (b) with
| true -> begin
"true"
end
| false -> begin
"false"
end)
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
x
end
| Microsoft_FStar_Absyn_Syntax.Const_int64 (_) -> begin
"<int64>"
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (_) -> begin
"<uint8>"
end))

let rec tag_of_typ = (fun ( t  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
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
(let _52_6683 = (tag_of_typ head)
in (let _52_6682 = (Support.Prims.pipe_left Support.Microsoft.FStar.Util.string_of_int (Support.List.length args))
in (Support.Microsoft.FStar.Util.format2 "Typ_app(%s, [%s args])" _52_6683 _52_6682)))
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
and tag_of_exp = (fun ( e  :  (Microsoft_FStar_Absyn_Syntax.exp', 'u24u8618) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
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
(let _52_6684 = (meta_e_to_string m)
in (Support.String.strcat "Exp_meta_desugared " _52_6684))
end))
and meta_e_to_string = (fun ( _24_4  :  Microsoft_FStar_Absyn_Syntax.meta_source_info ) -> (match (_24_4) with
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
and typ_to_string = (fun ( x  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let x = (Microsoft_FStar_Absyn_Util.compress_typ x)
in (match (x.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_) -> begin
(failwith ("impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((_, l))) -> begin
(sli l)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (meta) -> begin
(let _52_6687 = (Support.Prims.pipe_right meta meta_to_string)
in (Support.Microsoft.FStar.Util.format1 "(Meta %s)" _52_6687))
end
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(strBvd btv.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (v) -> begin
(sli v.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, c)) -> begin
(let _52_6689 = (binders_to_string " -> " binders)
in (let _52_6688 = (comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _52_6689 _52_6688)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((xt, f)) -> begin
(let _52_6692 = (strBvd xt.Microsoft_FStar_Absyn_Syntax.v)
in (let _52_6691 = (Support.Prims.pipe_right xt.Microsoft_FStar_Absyn_Syntax.sort typ_to_string)
in (let _52_6690 = (Support.Prims.pipe_right f formula_to_string)
in (Support.Microsoft.FStar.Util.format3 "%s:%s{%s}" _52_6692 _52_6691 _52_6690))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, args)) -> begin
(let q_to_string = (fun ( k  :  (((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) * Microsoft_FStar_Absyn_Syntax.typ)  ->  string ) ( a  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t)) -> begin
(k (b, t))
end
| _ -> begin
(let _52_6703 = (tag_of_typ t)
in (let _52_6702 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "<Expected a type-lambda! got %s>%s" _52_6703 _52_6702)))
end))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _52_6704 = (exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 "(<Expected a type!>%s)" _52_6704))
end))
in (let qbinder_to_string = (q_to_string (fun ( x  :  (((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) * Microsoft_FStar_Absyn_Syntax.typ) ) -> (binder_to_string (Support.Prims.fst x))))
in (let qbody_to_string = (q_to_string (fun ( x  :  (((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) * Microsoft_FStar_Absyn_Syntax.typ) ) -> (typ_to_string (Support.Prims.snd x))))
in (let args' = (match ((let _52_6711 = (Support.ST.read Microsoft_FStar_Options.print_implicits)
in (let _52_6710 = (let _52_6709 = (is_quant t)
in (not (_52_6709)))
in (_52_6711 && _52_6710)))) with
| true -> begin
args
end
| false -> begin
(Support.List.filter (fun ( _24_5  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_24_5) with
| (_, Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _ -> begin
true
end)) args)
end)
in (match ((let _52_6713 = (is_ite t)
in (_52_6713 && ((Support.List.length args) = 3)))) with
| true -> begin
(let _52_6719 = (let _52_6714 = (Support.List.nth args 0)
in (arg_to_string _52_6714))
in (let _52_6718 = (let _52_6715 = (Support.List.nth args 1)
in (arg_to_string _52_6715))
in (let _52_6717 = (let _52_6716 = (Support.List.nth args 2)
in (arg_to_string _52_6716))
in (Support.Microsoft.FStar.Util.format3 "if %s then %s else %s" _52_6719 _52_6718 _52_6717))))
end
| false -> begin
(match ((let _52_6720 = (is_b2t t)
in (_52_6720 && ((Support.List.length args) = 1)))) with
| true -> begin
(let _52_6721 = (Support.List.nth args 0)
in (Support.Prims.pipe_right _52_6721 arg_to_string))
end
| false -> begin
(match ((let _52_6722 = (is_quant t)
in (_52_6722 && ((Support.List.length args) <= 2)))) with
| true -> begin
(let _52_6727 = (quant_to_string t)
in (let _52_6726 = (let _52_6723 = (Support.List.nth args' 0)
in (qbinder_to_string _52_6723))
in (let _52_6725 = (let _52_6724 = (Support.List.nth args' 0)
in (qbody_to_string _52_6724))
in (Support.Microsoft.FStar.Util.format3 "(%s (%s). %s)" _52_6727 _52_6726 _52_6725))))
end
| false -> begin
(match ((let _52_6728 = (is_infix_type_op t)
in (_52_6728 && ((Support.List.length args') = 2)))) with
| true -> begin
(let _52_6733 = (let _52_6729 = (Support.List.nth args' 0)
in (Support.Prims.pipe_right _52_6729 arg_to_string))
in (let _52_6732 = (Support.Prims.pipe_right t infix_type_op_to_string)
in (let _52_6731 = (let _52_6730 = (Support.List.nth args' 1)
in (Support.Prims.pipe_right _52_6730 arg_to_string))
in (Support.Microsoft.FStar.Util.format3 "(%s %s %s)" _52_6733 _52_6732 _52_6731))))
end
| false -> begin
(match ((let _52_6734 = (is_unary_type_op t)
in (_52_6734 && ((Support.List.length args') = 1)))) with
| true -> begin
(let _52_6737 = (Support.Prims.pipe_right t unary_type_op_to_string)
in (let _52_6736 = (let _52_6735 = (Support.List.nth args' 0)
in (Support.Prims.pipe_right _52_6735 arg_to_string))
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _52_6737 _52_6736)))
end
| false -> begin
(let _52_6739 = (Support.Prims.pipe_right t typ_to_string)
in (let _52_6738 = (Support.Prims.pipe_right args args_to_string)
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _52_6739 _52_6738)))
end)
end)
end)
end)
end)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((binders, t2)) -> begin
(let _52_6741 = (binders_to_string " " binders)
in (let _52_6740 = (Support.Prims.pipe_right t2 typ_to_string)
in (Support.Microsoft.FStar.Util.format2 "(fun %s -> %s)" _52_6741 _52_6740)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, k)) -> begin
(match ((Support.ST.read Microsoft_FStar_Options.print_real_names)) with
| true -> begin
(let _52_6743 = (typ_to_string t)
in (let _52_6742 = (kind_to_string k)
in (Support.Microsoft.FStar.Util.format2 "(%s <: %s)" _52_6743 _52_6742)))
end
| false -> begin
(Support.Prims.pipe_right t typ_to_string)
end)
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
(Support.Prims.pipe_right t typ_to_string)
end)
end)))
and uvar_t_to_string = (fun ( _24_324  :  (Microsoft_FStar_Absyn_Syntax.uvar_t * Microsoft_FStar_Absyn_Syntax.knd) ) -> (match (_24_324) with
| (uv, k) -> begin
(match ((let _52_6745 = (Support.ST.read Microsoft_FStar_Options.print_real_names)
in (false && _52_6745))) with
| true -> begin
(let _52_6748 = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _52_6746 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _52_6746))
end)
in (let _52_6747 = (kind_to_string k)
in (Support.Microsoft.FStar.Util.format2 "(U%s : %s)" _52_6748 _52_6747)))
end
| false -> begin
(let _52_6750 = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _52_6749 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _52_6749))
end)
in (Support.Microsoft.FStar.Util.format1 "U%s" _52_6750))
end)
end))
and imp_to_string = (fun ( s  :  string ) ( _24_6  :  Microsoft_FStar_Absyn_Syntax.arg_qualifier option ) -> (match (_24_6) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
(Support.String.strcat "#" s)
end
| Some (Microsoft_FStar_Absyn_Syntax.Equality) -> begin
(Support.String.strcat "=" s)
end
| _ -> begin
s
end))
and binder_to_string' = (fun ( is_arrow  :  bool ) ( b  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (b) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(match ((let _52_6759 = (Microsoft_FStar_Absyn_Syntax.is_null_binder b)
in (let _52_6758 = (let _52_6757 = (let _52_6755 = (Support.ST.read Microsoft_FStar_Options.print_real_names)
in (Support.Prims.pipe_right _52_6755 Support.Prims.op_Negation))
in (let _52_6756 = (Microsoft_FStar_Absyn_Syntax.is_null_pp a.Microsoft_FStar_Absyn_Syntax.v)
in (_52_6757 && _52_6756)))
in (_52_6759 || _52_6758)))) with
| true -> begin
(kind_to_string a.Microsoft_FStar_Absyn_Syntax.sort)
end
| false -> begin
(match ((let _52_6761 = (let _52_6760 = (Support.ST.read Microsoft_FStar_Options.print_implicits)
in (not (_52_6760)))
in ((not (is_arrow)) && _52_6761))) with
| true -> begin
(let _52_6762 = (strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (imp_to_string _52_6762 imp))
end
| false -> begin
(let _52_6766 = (let _52_6765 = (let _52_6763 = (strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.String.strcat _52_6763 ":"))
in (let _52_6764 = (kind_to_string a.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.String.strcat _52_6765 _52_6764)))
in (imp_to_string _52_6766 imp))
end)
end)
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(match ((let _52_6771 = (Microsoft_FStar_Absyn_Syntax.is_null_binder b)
in (let _52_6770 = (let _52_6769 = (let _52_6767 = (Support.ST.read Microsoft_FStar_Options.print_real_names)
in (Support.Prims.pipe_right _52_6767 Support.Prims.op_Negation))
in (let _52_6768 = (Microsoft_FStar_Absyn_Syntax.is_null_pp x.Microsoft_FStar_Absyn_Syntax.v)
in (_52_6769 && _52_6768)))
in (_52_6771 || _52_6770)))) with
| true -> begin
(typ_to_string x.Microsoft_FStar_Absyn_Syntax.sort)
end
| false -> begin
(match ((let _52_6773 = (let _52_6772 = (Support.ST.read Microsoft_FStar_Options.print_implicits)
in (not (_52_6772)))
in ((not (is_arrow)) && _52_6773))) with
| true -> begin
(let _52_6774 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (imp_to_string _52_6774 imp))
end
| false -> begin
(let _52_6778 = (let _52_6777 = (let _52_6775 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Support.String.strcat _52_6775 ":"))
in (let _52_6776 = (typ_to_string x.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.String.strcat _52_6777 _52_6776)))
in (imp_to_string _52_6778 imp))
end)
end)
end))
and binder_to_string = (fun ( b  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (binder_to_string' false b))
and arrow_binder_to_string = (fun ( b  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (binder_to_string' true b))
and binders_to_string = (fun ( sep  :  string ) ( bs  :  Microsoft_FStar_Absyn_Syntax.binders ) -> (let bs = (match ((Support.ST.read Microsoft_FStar_Options.print_implicits)) with
| true -> begin
bs
end
| false -> begin
(filter_imp bs)
end)
in (match ((sep = " -> ")) with
| true -> begin
(let _52_6783 = (Support.Prims.pipe_right bs (Support.List.map arrow_binder_to_string))
in (Support.Prims.pipe_right _52_6783 (Support.String.concat sep)))
end
| false -> begin
(let _52_6784 = (Support.Prims.pipe_right bs (Support.List.map binder_to_string))
in (Support.Prims.pipe_right _52_6784 (Support.String.concat sep)))
end)))
and arg_to_string = (fun ( _24_7  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_24_7) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _52_6786 = (typ_to_string a)
in (imp_to_string _52_6786 imp))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _52_6787 = (exp_to_string x)
in (imp_to_string _52_6787 imp))
end))
and args_to_string = (fun ( args  :  Microsoft_FStar_Absyn_Syntax.args ) -> (let args = (match ((Support.ST.read Microsoft_FStar_Options.print_implicits)) with
| true -> begin
args
end
| false -> begin
(filter_imp args)
end)
in (let _52_6789 = (Support.Prims.pipe_right args (Support.List.map arg_to_string))
in (Support.Prims.pipe_right _52_6789 (Support.String.concat " ")))))
and lcomp_typ_to_string = (fun ( lc  :  Microsoft_FStar_Absyn_Syntax.lcomp ) -> (let _52_6792 = (sli lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in (let _52_6791 = (typ_to_string lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in (Support.Microsoft.FStar.Util.format2 "%s %s" _52_6792 _52_6791))))
and comp_typ_to_string = (fun ( c  :  Microsoft_FStar_Absyn_Syntax.comp ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _52_6794 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "Tot %s" _52_6794))
end
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
(let basic = (match ((let _52_6798 = (Support.Prims.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.for_some (fun ( _24_8  :  Microsoft_FStar_Absyn_Syntax.cflags ) -> (match (_24_8) with
| Microsoft_FStar_Absyn_Syntax.TOTAL -> begin
true
end
| _ -> begin
false
end))))
in (let _52_6797 = (let _52_6796 = (Support.ST.read Microsoft_FStar_Options.print_effect_args)
in (not (_52_6796)))
in (_52_6798 && _52_6797)))) with
| true -> begin
(let _52_6799 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (Support.Microsoft.FStar.Util.format1 "Tot %s" _52_6799))
end
| false -> begin
(match ((let _52_6801 = (let _52_6800 = (Support.ST.read Microsoft_FStar_Options.print_effect_args)
in (not (_52_6800)))
in (_52_6801 && (Microsoft_FStar_Absyn_Syntax.lid_equals c.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_ML_lid)))) with
| true -> begin
(typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
end
| false -> begin
(match ((let _52_6805 = (let _52_6802 = (Support.ST.read Microsoft_FStar_Options.print_effect_args)
in (not (_52_6802)))
in (let _52_6804 = (Support.Prims.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.for_some (fun ( _24_9  :  Microsoft_FStar_Absyn_Syntax.cflags ) -> (match (_24_9) with
| Microsoft_FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _ -> begin
false
end))))
in (_52_6805 && _52_6804)))) with
| true -> begin
(let _52_6806 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (Support.Microsoft.FStar.Util.format1 "ALL %s" _52_6806))
end
| false -> begin
(match ((Support.ST.read Microsoft_FStar_Options.print_effect_args)) with
| true -> begin
(let _52_6810 = (sli c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _52_6809 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _52_6808 = (let _52_6807 = (Support.Prims.pipe_right c.Microsoft_FStar_Absyn_Syntax.effect_args (Support.List.map effect_arg_to_string))
in (Support.Prims.pipe_right _52_6807 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format3 "%s (%s) %s" _52_6810 _52_6809 _52_6808))))
end
| false -> begin
(let _52_6812 = (sli c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _52_6811 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (Support.Microsoft.FStar.Util.format2 "%s (%s)" _52_6812 _52_6811)))
end)
end)
end)
end)
in (let dec = (let _52_6816 = (Support.Prims.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Support.List.collect (fun ( _24_10  :  Microsoft_FStar_Absyn_Syntax.cflags ) -> (match (_24_10) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _52_6815 = (let _52_6814 = (exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 " (decreases %s)" _52_6814))
in (_52_6815)::[])
end
| _ -> begin
[]
end))))
in (Support.Prims.pipe_right _52_6816 (Support.String.concat " ")))
in (Support.Microsoft.FStar.Util.format2 "%s%s" basic dec)))
end))
and effect_arg_to_string = (fun ( e  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (e) with
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(exp_to_string e)
end
| (Support.Microsoft.FStar.Util.Inl (wp), _) -> begin
(formula_to_string wp)
end))
and formula_to_string = (fun ( phi  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (typ_to_string phi))
and formula_to_string_old_now_unused = (fun ( phi  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let const_op = (fun ( f  :  string ) ( _24_395  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) -> f)
in (let un_op = (fun ( f  :  string ) ( _24_11  :  ((Microsoft_FStar_Absyn_Syntax.typ, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) -> (match (_24_11) with
| (Support.Microsoft.FStar.Util.Inl (t), _)::[] -> begin
(let _52_6828 = (formula_to_string t)
in (Support.Microsoft.FStar.Util.format2 "%s %s" f _52_6828))
end
| _ -> begin
(failwith ("impos"))
end))
in (let bin_top = (fun ( f  :  string ) ( _24_12  :  ((Microsoft_FStar_Absyn_Syntax.typ, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) -> (match (_24_12) with
| (Support.Microsoft.FStar.Util.Inl (t1), _)::(Support.Microsoft.FStar.Util.Inl (t2), _)::[] -> begin
(let _52_6834 = (formula_to_string t1)
in (let _52_6833 = (formula_to_string t2)
in (Support.Microsoft.FStar.Util.format3 "%s %s %s" _52_6834 f _52_6833)))
end
| _ -> begin
(failwith ("Impos"))
end))
in (let bin_eop = (fun ( f  :  string ) ( _24_13  :  ((Obj.t, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Obj.t) list ) -> (match (_24_13) with
| (Support.Microsoft.FStar.Util.Inr (e1), _)::(Support.Microsoft.FStar.Util.Inr (e2), _)::[] -> begin
(let _52_6840 = (exp_to_string e1)
in (let _52_6839 = (exp_to_string e2)
in (Support.Microsoft.FStar.Util.format3 "%s %s %s" _52_6840 f _52_6839)))
end
| _ -> begin
(failwith ("impos"))
end))
in (let ite = (fun ( _24_14  :  ((Microsoft_FStar_Absyn_Syntax.typ, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) -> (match (_24_14) with
| (Support.Microsoft.FStar.Util.Inl (t1), _)::(Support.Microsoft.FStar.Util.Inl (t2), _)::(Support.Microsoft.FStar.Util.Inl (t3), _)::[] -> begin
(let _52_6845 = (formula_to_string t1)
in (let _52_6844 = (formula_to_string t2)
in (let _52_6843 = (formula_to_string t3)
in (Support.Microsoft.FStar.Util.format3 "if %s then %s else %s" _52_6845 _52_6844 _52_6843))))
end
| _ -> begin
(failwith ("impos"))
end))
in (let eq_op = (fun ( _24_15  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) -> (match (_24_15) with
| (Support.Microsoft.FStar.Util.Inl (t1), _)::(Support.Microsoft.FStar.Util.Inl (t2), _)::(Support.Microsoft.FStar.Util.Inr (e1), _)::(Support.Microsoft.FStar.Util.Inr (e2), _)::[] -> begin
(match ((Support.ST.read Microsoft_FStar_Options.print_implicits)) with
| true -> begin
(let _52_6851 = (typ_to_string t1)
in (let _52_6850 = (typ_to_string t2)
in (let _52_6849 = (exp_to_string e1)
in (let _52_6848 = (exp_to_string e2)
in (Support.Microsoft.FStar.Util.format4 "Eq2 %s %s %s %s" _52_6851 _52_6850 _52_6849 _52_6848)))))
end
| false -> begin
(let _52_6853 = (exp_to_string e1)
in (let _52_6852 = (exp_to_string e2)
in (Support.Microsoft.FStar.Util.format2 "%s == %s" _52_6853 _52_6852)))
end)
end
| (Support.Microsoft.FStar.Util.Inr (e1), _)::(Support.Microsoft.FStar.Util.Inr (e2), _)::[] -> begin
(let _52_6855 = (exp_to_string e1)
in (let _52_6854 = (exp_to_string e2)
in (Support.Microsoft.FStar.Util.format2 "%s == %s" _52_6855 _52_6854)))
end
| _ -> begin
(failwith ("Impossible"))
end))
in (let connectives = ((Microsoft_FStar_Absyn_Const.and_lid, (bin_top "/\\")))::((Microsoft_FStar_Absyn_Const.or_lid, (bin_top "\\/")))::((Microsoft_FStar_Absyn_Const.imp_lid, (bin_top "==>")))::((Microsoft_FStar_Absyn_Const.iff_lid, (bin_top "<==>")))::((Microsoft_FStar_Absyn_Const.ite_lid, ite))::((Microsoft_FStar_Absyn_Const.not_lid, (un_op "~")))::((Microsoft_FStar_Absyn_Const.eqT_lid, (bin_top "==")))::((Microsoft_FStar_Absyn_Const.eq2_lid, eq_op))::((Microsoft_FStar_Absyn_Const.true_lid, (const_op "True")))::((Microsoft_FStar_Absyn_Const.false_lid, (const_op "False")))::[]
in (let fallback = (fun ( phi  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((binders, phi)) -> begin
(let _52_6894 = (binders_to_string " " binders)
in (let _52_6893 = (formula_to_string phi)
in (Support.Microsoft.FStar.Util.format2 "(fun %s => %s)" _52_6894 _52_6893)))
end
| _ -> begin
(typ_to_string phi)
end))
in (match ((Microsoft_FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (Microsoft_FStar_Absyn_Util.BaseConn ((op, arms))) -> begin
(match ((Support.Prims.pipe_right connectives (Support.List.tryFind (fun ( _24_514  :  (Microsoft_FStar_Absyn_Syntax.lident * (((Microsoft_FStar_Absyn_Syntax.typ, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list  ->  string)) ) -> (match (_24_514) with
| (l, _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some ((_, f)) -> begin
(f arms)
end)
end
| Some (Microsoft_FStar_Absyn_Util.QAll ((vars, _, body))) -> begin
(let _52_6911 = (binders_to_string " " vars)
in (let _52_6910 = (formula_to_string body)
in (Support.Microsoft.FStar.Util.format2 "(forall %s. %s)" _52_6911 _52_6910)))
end
| Some (Microsoft_FStar_Absyn_Util.QEx ((vars, _, body))) -> begin
(let _52_6913 = (binders_to_string " " vars)
in (let _52_6912 = (formula_to_string body)
in (Support.Microsoft.FStar.Util.format2 "(exists %s. %s)" _52_6913 _52_6912)))
end))))))))))
and exp_to_string = (fun ( x  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match ((let _52_6915 = (Microsoft_FStar_Absyn_Util.compress_exp x)
in _52_6915.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_) -> begin
(failwith ("Impossible"))
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
(Support.Prims.pipe_right c const_to_string)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((binders, e)) -> begin
(let _52_6917 = (binders_to_string " " binders)
in (let _52_6916 = (Support.Prims.pipe_right e exp_to_string)
in (Support.Microsoft.FStar.Util.format2 "(fun %s -> %s)" _52_6917 _52_6916)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((e, args)) -> begin
(let lex = (match ((Support.ST.read Microsoft_FStar_Options.print_implicits)) with
| true -> begin
None
end
| false -> begin
(reconstruct_lex x)
end)
in (match (lex) with
| Some (es) -> begin
(let _52_6920 = (let _52_6919 = (let _52_6918 = (Support.List.map exp_to_string es)
in (Support.String.concat "; " _52_6918))
in (Support.String.strcat "%[" _52_6919))
in (Support.String.strcat _52_6920 "]"))
end
| None -> begin
(let args' = (let _52_6922 = (filter_imp args)
in (Support.Prims.pipe_right _52_6922 (Support.List.filter (fun ( _24_16  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_24_16) with
| (Support.Microsoft.FStar.Util.Inr (_), _) -> begin
true
end
| _ -> begin
false
end)))))
in (match ((let _52_6923 = (is_infix_prim_op e)
in (_52_6923 && ((Support.List.length args') = 2)))) with
| true -> begin
(let _52_6928 = (let _52_6924 = (Support.List.nth args' 0)
in (Support.Prims.pipe_right _52_6924 arg_to_string))
in (let _52_6927 = (Support.Prims.pipe_right e infix_prim_op_to_string)
in (let _52_6926 = (let _52_6925 = (Support.List.nth args' 1)
in (Support.Prims.pipe_right _52_6925 arg_to_string))
in (Support.Microsoft.FStar.Util.format3 "(%s %s %s)" _52_6928 _52_6927 _52_6926))))
end
| false -> begin
(match ((let _52_6929 = (is_unary_prim_op e)
in (_52_6929 && ((Support.List.length args') = 1)))) with
| true -> begin
(let _52_6932 = (Support.Prims.pipe_right e unary_prim_op_to_string)
in (let _52_6931 = (let _52_6930 = (Support.List.nth args' 0)
in (Support.Prims.pipe_right _52_6930 arg_to_string))
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _52_6932 _52_6931)))
end
| false -> begin
(let _52_6934 = (Support.Prims.pipe_right e exp_to_string)
in (let _52_6933 = (args_to_string args)
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _52_6934 _52_6933)))
end)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, pats)) -> begin
(let _52_6942 = (Support.Prims.pipe_right e exp_to_string)
in (let _52_6941 = (let _52_6940 = (Support.Prims.pipe_right pats (Support.List.map (fun ( _24_587  :  (Microsoft_FStar_Absyn_Syntax.pat * (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax option * (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) ) -> (match (_24_587) with
| (p, wopt, e) -> begin
(let _52_6939 = (Support.Prims.pipe_right p pat_to_string)
in (let _52_6938 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _52_6936 = (Support.Prims.pipe_right w exp_to_string)
in (Support.Microsoft.FStar.Util.format1 "when %s" _52_6936))
end)
in (let _52_6937 = (Support.Prims.pipe_right e exp_to_string)
in (Support.Microsoft.FStar.Util.format3 "%s %s -> %s" _52_6939 _52_6938 _52_6937))))
end))))
in (Support.Microsoft.FStar.Util.concat_l "\n\t" _52_6940))
in (Support.Microsoft.FStar.Util.format2 "(match %s with %s)" _52_6942 _52_6941)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _)) -> begin
(let _52_6944 = (Support.Prims.pipe_right e exp_to_string)
in (let _52_6943 = (Support.Prims.pipe_right t typ_to_string)
in (Support.Microsoft.FStar.Util.format2 "(%s:%s)" _52_6944 _52_6943)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, e)) -> begin
(let _52_6946 = (lbs_to_string lbs)
in (let _52_6945 = (Support.Prims.pipe_right e exp_to_string)
in (Support.Microsoft.FStar.Util.format2 "%s in %s" _52_6946 _52_6945)))
end))
and uvar_e_to_string = (fun ( _24_604  :  (Microsoft_FStar_Absyn_Syntax.uvar_e * Microsoft_FStar_Absyn_Syntax.typ) ) -> (match (_24_604) with
| (uv, _) -> begin
(let _52_6949 = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _52_6948 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _52_6948))
end)
in (Support.String.strcat "\'e" _52_6949))
end))
and lbs_to_string = (fun ( lbs  :  Microsoft_FStar_Absyn_Syntax.letbindings ) -> (let _52_6956 = (let _52_6955 = (Support.Prims.pipe_right (Support.Prims.snd lbs) (Support.List.map (fun ( lb  :  Microsoft_FStar_Absyn_Syntax.letbinding ) -> (let _52_6954 = (lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (let _52_6953 = (Support.Prims.pipe_right lb.Microsoft_FStar_Absyn_Syntax.lbtyp typ_to_string)
in (let _52_6952 = (Support.Prims.pipe_right lb.Microsoft_FStar_Absyn_Syntax.lbdef exp_to_string)
in (Support.Microsoft.FStar.Util.format3 "%s:%s = %s" _52_6954 _52_6953 _52_6952)))))))
in (Support.Microsoft.FStar.Util.concat_l "\n and " _52_6955))
in (Support.Microsoft.FStar.Util.format2 "let %s %s" (match ((Support.Prims.fst lbs)) with
| true -> begin
"rec"
end
| false -> begin
""
end) _52_6956)))
and lbname_to_string = (fun ( x  :  Microsoft_FStar_Absyn_Syntax.lbname ) -> (match (x) with
| Support.Microsoft.FStar.Util.Inl (bvd) -> begin
(strBvd bvd)
end
| Support.Microsoft.FStar.Util.Inr (lid) -> begin
(sli lid)
end))
and either_to_string = (fun ( x  :  ((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either ) -> (match (x) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(typ_to_string t)
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(exp_to_string e)
end))
and either_l_to_string = (fun ( delim  :  string ) ( l  :  ((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either list ) -> (let _52_6961 = (Support.Prims.pipe_right l (Support.List.map either_to_string))
in (Support.Prims.pipe_right _52_6961 (Support.Microsoft.FStar.Util.concat_l delim))))
and meta_to_string = (fun ( x  :  Microsoft_FStar_Absyn_Syntax.meta_t ) -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _, _)) -> begin
(let _52_6963 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "(refresh) %s" _52_6963))
end
| Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, _, _)) -> begin
(let _52_6964 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "(labeled \"%s\") %s" l _52_6964))
end
| Microsoft_FStar_Absyn_Syntax.Meta_named ((_, l)) -> begin
(sli l)
end
| Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, ps)) -> begin
(let _52_6966 = (args_to_string ps)
in (let _52_6965 = (Support.Prims.pipe_right t typ_to_string)
in (Support.Microsoft.FStar.Util.format2 "{:pattern %s} %s" _52_6966 _52_6965)))
end
| Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, _)) -> begin
(let _52_6968 = (formula_to_string t1)
in (let _52_6967 = (formula_to_string t2)
in (Support.Microsoft.FStar.Util.format2 "%s /\\ %s" _52_6968 _52_6967)))
end))
and kind_to_string = (fun ( x  :  Microsoft_FStar_Absyn_Syntax.knd ) -> (match ((let _52_6970 = (Microsoft_FStar_Absyn_Util.compress_kind x)
in _52_6970.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam (_) -> begin
(failwith ("Impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed (_) -> begin
(failwith ("Impossible"))
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
(match ((Support.ST.read Microsoft_FStar_Options.print_real_names)) with
| true -> begin
(kind_to_string k)
end
| false -> begin
(let _52_6972 = (sli n)
in (let _52_6971 = (args_to_string args)
in (Support.Microsoft.FStar.Util.format2 "%s %s" _52_6972 _52_6971)))
end)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((binders, k)) -> begin
(let _52_6974 = (binders_to_string " -> " binders)
in (let _52_6973 = (Support.Prims.pipe_right k kind_to_string)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _52_6974 _52_6973)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun ( uv  :  'u24u8619 Support.Microsoft.FStar.Unionfind.uvar ) -> (let _52_6976 = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _52_6975 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _52_6975))
end)
in (Support.String.strcat "\'k_" _52_6976)))
and uvar_k_to_string' = (fun ( _24_677  :  ((Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.uvar_basis Support.Microsoft.FStar.Unionfind.uvar * (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list) ) -> (match (_24_677) with
| (uv, args) -> begin
(let str = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _52_6978 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _52_6978))
end)
in (let _52_6979 = (args_to_string args)
in (Support.Microsoft.FStar.Util.format2 "(\'k_%s %s)" str _52_6979)))
end))
and pat_to_string = (fun ( x  :  Microsoft_FStar_Absyn_Syntax.pat ) -> (match (x.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, _, pats)) -> begin
(let _52_6983 = (sli l.Microsoft_FStar_Absyn_Syntax.v)
in (let _52_6982 = (let _52_6981 = (Support.List.map pat_to_string pats)
in (Support.Prims.pipe_right _52_6981 (Support.String.concat " ")))
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _52_6983 _52_6982)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _)) -> begin
(let _52_6984 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 ".%s" _52_6984))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((x, _)) -> begin
(let _52_6985 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 ".\'%s" _52_6985))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, true)) -> begin
(let _52_6986 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "#%s" _52_6986))
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
(let _52_6987 = (Support.List.map pat_to_string ps)
in (Support.Microsoft.FStar.Util.concat_l " | " _52_6987))
end))

let subst_to_string = (fun ( subst  :  (('u24u8752 Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax), ('u24u8751 Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax)) Support.Microsoft.FStar.Util.either list ) -> (let _52_6995 = (let _52_6994 = (Support.List.map (fun ( _24_17  :  (('u24u8752 Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax), ('u24u8751 Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax)) Support.Microsoft.FStar.Util.either ) -> (match (_24_17) with
| Support.Microsoft.FStar.Util.Inl ((a, t)) -> begin
(let _52_6991 = (strBvd a)
in (let _52_6990 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _52_6991 _52_6990)))
end
| Support.Microsoft.FStar.Util.Inr ((x, e)) -> begin
(let _52_6993 = (strBvd x)
in (let _52_6992 = (exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _52_6993 _52_6992)))
end)) subst)
in (Support.Prims.pipe_right _52_6994 (Support.String.concat ", ")))
in (Support.Prims.pipe_left (Support.Microsoft.FStar.Util.format1 "{%s}") _52_6995)))

let freevars_to_string = (fun ( fvs  :  Microsoft_FStar_Absyn_Syntax.freevars ) -> (let f = (fun ( l  :  ('a, 'b) Microsoft_FStar_Absyn_Syntax.bvar Support.Microsoft.FStar.Util.set ) -> (let _52_7001 = (let _52_7000 = (Support.Prims.pipe_right l Support.Microsoft.FStar.Util.set_elements)
in (Support.Prims.pipe_right _52_7000 (Support.List.map (fun ( t  :  ('a Microsoft_FStar_Absyn_Syntax.bvdef, 'b) Microsoft_FStar_Absyn_Syntax.withinfo_t ) -> (strBvd t.Microsoft_FStar_Absyn_Syntax.v)))))
in (Support.Prims.pipe_right _52_7001 (Support.String.concat ", "))))
in (let _52_7003 = (f fvs.Microsoft_FStar_Absyn_Syntax.ftvs)
in (let _52_7002 = (f fvs.Microsoft_FStar_Absyn_Syntax.fxvs)
in (Support.Microsoft.FStar.Util.format2 "ftvs={%s}, fxvs={%s}" _52_7003 _52_7002)))))

let qual_to_string = (fun ( _24_18  :  Microsoft_FStar_Absyn_Syntax.qualifier ) -> (match (_24_18) with
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
(let _52_7008 = (let _52_7007 = (Support.Prims.pipe_right ids (Support.List.map (fun ( lid  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) -> lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)))
in (Support.Prims.pipe_right _52_7007 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format1 "record(%s)" _52_7008))
end
| _ -> begin
"other"
end))

let quals_to_string = (fun ( quals  :  Microsoft_FStar_Absyn_Syntax.qualifier list ) -> (let _52_7011 = (Support.Prims.pipe_right quals (Support.List.map qual_to_string))
in (Support.Prims.pipe_right _52_7011 (Support.String.concat " "))))

let rec sigelt_to_string = (fun ( x  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Sig_pragma ((Microsoft_FStar_Absyn_Syntax.ResetOptions, _)) -> begin
"#reset-options"
end
| Microsoft_FStar_Absyn_Syntax.Sig_pragma ((Microsoft_FStar_Absyn_Syntax.SetOptions (s), _)) -> begin
(Support.Microsoft.FStar.Util.format1 "#set-options \"%s\"" s)
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _, _, quals, _)) -> begin
(let _52_7016 = (quals_to_string quals)
in (let _52_7015 = (binders_to_string " " tps)
in (let _52_7014 = (kind_to_string k)
in (Support.Microsoft.FStar.Util.format4 "%s type %s %s : %s" _52_7016 lid.Microsoft_FStar_Absyn_Syntax.str _52_7015 _52_7014))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k, t, _, _)) -> begin
(let _52_7019 = (binders_to_string " " tps)
in (let _52_7018 = (kind_to_string k)
in (let _52_7017 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format4 "type %s %s : %s = %s" lid.Microsoft_FStar_Absyn_Syntax.str _52_7019 _52_7018 _52_7017))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, t, _, _, _, _)) -> begin
(let _52_7020 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "datacon %s : %s" lid.Microsoft_FStar_Absyn_Syntax.str _52_7020))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, _)) -> begin
(let _52_7022 = (quals_to_string quals)
in (let _52_7021 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format3 "%s val %s : %s" _52_7022 lid.Microsoft_FStar_Absyn_Syntax.str _52_7021)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((lid, f, _, _)) -> begin
(let _52_7023 = (typ_to_string f)
in (Support.Microsoft.FStar.Util.format2 "val %s : %s" lid.Microsoft_FStar_Absyn_Syntax.str _52_7023))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, _, _, b)) -> begin
(lbs_to_string lbs)
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, _)) -> begin
(let _52_7024 = (exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 "let _ = %s" _52_7024))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _, _, _)) -> begin
(let _52_7025 = (Support.List.map sigelt_to_string ses)
in (Support.Prims.pipe_right _52_7025 (Support.String.concat "\n")))
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
(let _52_7028 = (sli l)
in (let _52_7027 = (binders_to_string " " tps)
in (let _52_7026 = (comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.format3 "effect %s %s = %s" _52_7028 _52_7027 _52_7026))))
end))

let format_error = (fun ( r  :  Support.Microsoft.FStar.Range.range ) ( msg  :  string ) -> (let _52_7033 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "%s: %s\n" _52_7033 msg)))

let rec sigelt_to_string_short = (fun ( x  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Sig_let (((_, {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = _}::[]), _, _, _)) -> begin
(let _52_7036 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "let %s : %s" l.Microsoft_FStar_Absyn_Syntax.str _52_7036))
end
| _ -> begin
(let _52_7039 = (let _52_7038 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt x)
in (Support.Prims.pipe_right _52_7038 (Support.List.map (fun ( l  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) -> l.Microsoft_FStar_Absyn_Syntax.str))))
in (Support.Prims.pipe_right _52_7039 (Support.String.concat ", ")))
end))

let rec modul_to_string = (fun ( m  :  Microsoft_FStar_Absyn_Syntax.modul ) -> (let _52_7044 = (sli m.Microsoft_FStar_Absyn_Syntax.name)
in (let _52_7043 = (let _52_7042 = (Support.List.map sigelt_to_string m.Microsoft_FStar_Absyn_Syntax.declarations)
in (Support.Prims.pipe_right _52_7042 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.format2 "module %s\n%s" _52_7044 _52_7043))))




