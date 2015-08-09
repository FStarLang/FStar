
let infix_prim_ops = ((Microsoft_FStar_Absyn_Const.op_Addition, "+"))::((Microsoft_FStar_Absyn_Const.op_Subtraction, "-"))::((Microsoft_FStar_Absyn_Const.op_Multiply, "*"))::((Microsoft_FStar_Absyn_Const.op_Division, "/"))::((Microsoft_FStar_Absyn_Const.op_Eq, "="))::((Microsoft_FStar_Absyn_Const.op_ColonEq, ":="))::((Microsoft_FStar_Absyn_Const.op_notEq, "<>"))::((Microsoft_FStar_Absyn_Const.op_And, "&&"))::((Microsoft_FStar_Absyn_Const.op_Or, "||"))::((Microsoft_FStar_Absyn_Const.op_LTE, "<="))::((Microsoft_FStar_Absyn_Const.op_GTE, ">="))::((Microsoft_FStar_Absyn_Const.op_LT, "<"))::((Microsoft_FStar_Absyn_Const.op_GT, ">"))::((Microsoft_FStar_Absyn_Const.op_Modulus, "mod"))::[]

let unary_prim_ops = ((Microsoft_FStar_Absyn_Const.op_Negation, "not"))::((Microsoft_FStar_Absyn_Const.op_Minus, "-"))::[]

let infix_type_ops = ((Microsoft_FStar_Absyn_Const.and_lid, "/\\"))::((Microsoft_FStar_Absyn_Const.or_lid, "\\/"))::((Microsoft_FStar_Absyn_Const.imp_lid, "==>"))::((Microsoft_FStar_Absyn_Const.iff_lid, "<==>"))::((Microsoft_FStar_Absyn_Const.precedes_lid, "<<"))::((Microsoft_FStar_Absyn_Const.eq2_lid, "=="))::((Microsoft_FStar_Absyn_Const.eqT_lid, "=="))::[]

let unary_type_ops = ((Microsoft_FStar_Absyn_Const.not_lid, "~"))::[]

let is_prim_op = (fun ( ps ) ( f ) -> (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _26_23)) -> begin
(Support.All.pipe_right ps (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v)))
end
| _26_27 -> begin
false
end))

let is_type_op = (fun ( ps ) ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(Support.All.pipe_right ps (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals ftv.Microsoft_FStar_Absyn_Syntax.v)))
end
| _26_33 -> begin
false
end))

let get_lid = (fun ( f ) -> (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _26_37)) -> begin
fv.Microsoft_FStar_Absyn_Syntax.v
end
| _26_41 -> begin
(Support.All.failwith "get_lid")
end))

let get_type_lid = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (ftv) -> begin
ftv.Microsoft_FStar_Absyn_Syntax.v
end
| _26_46 -> begin
(Support.All.failwith "get_type_lid")
end))

let is_infix_prim_op = (fun ( e ) -> (is_prim_op (Support.Prims.fst (Support.List.split infix_prim_ops)) e))

let is_unary_prim_op = (fun ( e ) -> (is_prim_op (Support.Prims.fst (Support.List.split unary_prim_ops)) e))

let is_infix_type_op = (fun ( t ) -> (is_type_op (Support.Prims.fst (Support.List.split infix_type_ops)) t))

let is_unary_type_op = (fun ( t ) -> (is_type_op (Support.Prims.fst (Support.List.split unary_type_ops)) t))

let quants = ((Microsoft_FStar_Absyn_Const.forall_lid, "forall"))::((Microsoft_FStar_Absyn_Const.exists_lid, "exists"))::((Microsoft_FStar_Absyn_Const.allTyp_lid, "forall"))::((Microsoft_FStar_Absyn_Const.exTyp_lid, "exists"))::[]

let is_b2t = (fun ( t ) -> (is_type_op ((Microsoft_FStar_Absyn_Const.b2t_lid)::[]) t))

let is_quant = (fun ( t ) -> (is_type_op (Support.Prims.fst (Support.List.split quants)) t))

let is_ite = (fun ( t ) -> (is_type_op ((Microsoft_FStar_Absyn_Const.ite_lid)::[]) t))

let is_lex_cons = (fun ( f ) -> (is_prim_op ((Microsoft_FStar_Absyn_Const.lexcons_lid)::[]) f))

let is_lex_top = (fun ( f ) -> (is_prim_op ((Microsoft_FStar_Absyn_Const.lextop_lid)::[]) f))

let is_inr = (fun ( _26_1 ) -> (match (_26_1) with
| Support.Microsoft.FStar.Util.Inl (_26_58) -> begin
false
end
| Support.Microsoft.FStar.Util.Inr (_26_61) -> begin
true
end))

let rec reconstruct_lex = (fun ( e ) -> (match ((let _70_11541 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _70_11541.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((f, args)) -> begin
(let args = (Support.List.filter (fun ( a ) -> (((Support.Prims.snd a) <> Some (Microsoft_FStar_Absyn_Syntax.Implicit)) && (is_inr (Support.Prims.fst a)))) args)
in (let exps = (Support.List.map (fun ( _26_2 ) -> (match (_26_2) with
| (Support.Microsoft.FStar.Util.Inl (_26_72), _26_75) -> begin
(Support.All.failwith "impossible")
end
| (Support.Microsoft.FStar.Util.Inr (x), _26_80) -> begin
x
end)) args)
in (match (((is_lex_cons f) && ((Support.List.length exps) = 2))) with
| true -> begin
(match ((let _70_11544 = (Support.List.nth exps 1)
in (reconstruct_lex _70_11544))) with
| Some (xs) -> begin
(let _70_11546 = (let _70_11545 = (Support.List.nth exps 0)
in (_70_11545)::xs)
in Some (_70_11546))
end
| None -> begin
None
end)
end
| false -> begin
None
end)))
end
| _26_87 -> begin
(match ((is_lex_top e)) with
| true -> begin
Some ([])
end
| false -> begin
None
end)
end))

let rec find = (fun ( f ) ( l ) -> (match (l) with
| [] -> begin
(Support.All.failwith "blah")
end
| hd::tl -> begin
(match ((f hd)) with
| true -> begin
hd
end
| false -> begin
(find f tl)
end)
end))

let find_lid = (fun ( x ) ( xs ) -> (let _70_11560 = (find (fun ( p ) -> (Microsoft_FStar_Absyn_Syntax.lid_equals x (Support.Prims.fst p))) xs)
in (Support.Prims.snd _70_11560)))

let infix_prim_op_to_string = (fun ( e ) -> (let _70_11562 = (get_lid e)
in (find_lid _70_11562 infix_prim_ops)))

let unary_prim_op_to_string = (fun ( e ) -> (let _70_11564 = (get_lid e)
in (find_lid _70_11564 unary_prim_ops)))

let infix_type_op_to_string = (fun ( t ) -> (let _70_11566 = (get_type_lid t)
in (find_lid _70_11566 infix_type_ops)))

let unary_type_op_to_string = (fun ( t ) -> (let _70_11568 = (get_type_lid t)
in (find_lid _70_11568 unary_type_ops)))

let quant_to_string = (fun ( t ) -> (let _70_11570 = (get_type_lid t)
in (find_lid _70_11570 quants)))

let rec sli = (fun ( l ) -> (match ((Support.ST.read Microsoft_FStar_Options.print_real_names)) with
| true -> begin
l.Microsoft_FStar_Absyn_Syntax.str
end
| false -> begin
l.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText
end))

let strBvd = (fun ( bvd ) -> (match ((Support.ST.read Microsoft_FStar_Options.print_real_names)) with
| true -> begin
(Support.String.strcat bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText bvd.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText)
end
| false -> begin
(match (((Support.ST.read Microsoft_FStar_Options.hide_genident_nums) && (Support.Microsoft.FStar.Util.starts_with bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText "_"))) with
| true -> begin
(Support.All.try_with (fun ( _26_106 ) -> (match (()) with
| () -> begin
(let _26_112 = (let _70_11575 = (Support.Microsoft.FStar.Util.substring_from bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText 1)
in (Support.Microsoft.FStar.Util.int_of_string _70_11575))
in "_?")
end)) (fun ( _26_105 ) -> (match (_26_105) with
| _26_109 -> begin
bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText
end)))
end
| false -> begin
bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText
end)
end))

let filter_imp = (fun ( a ) -> (Support.All.pipe_right a (Support.List.filter (fun ( _26_3 ) -> (match (_26_3) with
| (_26_117, Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _26_122 -> begin
true
end)))))

let const_to_string = (fun ( x ) -> (match (x) with
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
| Microsoft_FStar_Absyn_Syntax.Const_string ((bytes, _26_135)) -> begin
(Support.Microsoft.FStar.Util.format1 "\"%s\"" (Support.Microsoft.FStar.Util.string_of_bytes bytes))
end
| Microsoft_FStar_Absyn_Syntax.Const_bytearray (_26_139) -> begin
"<bytearray>"
end
| Microsoft_FStar_Absyn_Syntax.Const_int (x) -> begin
x
end
| Microsoft_FStar_Absyn_Syntax.Const_int64 (_26_144) -> begin
"<int64>"
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (_26_147) -> begin
"<uint8>"
end))

let rec tag_of_typ = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (_26_151) -> begin
"Typ_btvar"
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (v) -> begin
(Support.String.strcat "Typ_const " v.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_26_156) -> begin
"Typ_fun"
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_26_159) -> begin
"Typ_refine"
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(let _70_11615 = (tag_of_typ head)
in (let _70_11614 = (Support.All.pipe_left Support.Microsoft.FStar.Util.string_of_int (Support.List.length args))
in (Support.Microsoft.FStar.Util.format2 "Typ_app(%s, [%s args])" _70_11615 _70_11614)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam (_26_166) -> begin
"Typ_lam"
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_26_169) -> begin
"Typ_ascribed"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern (_26_172)) -> begin
"Typ_meta_pattern"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named (_26_176)) -> begin
"Typ_meta_named"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled (_26_180)) -> begin
"Typ_meta_labeled"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (_26_184)) -> begin
"Typ_meta_refresh_label"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula (_26_188)) -> begin
"Typ_meta_slack_formula"
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar (_26_192) -> begin
"Typ_uvar"
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_26_195) -> begin
"Typ_delayed"
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
"Typ_unknown"
end))
and tag_of_exp = (fun ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (_26_200) -> begin
"Exp_bvar"
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar (_26_203) -> begin
"Exp_fvar"
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (_26_206) -> begin
"Exp_constant"
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (_26_209) -> begin
"Exp_abs"
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (_26_212) -> begin
"Exp_app"
end
| Microsoft_FStar_Absyn_Syntax.Exp_match (_26_215) -> begin
"Exp_match"
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed (_26_218) -> begin
"Exp_ascribed"
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (_26_221) -> begin
"Exp_let"
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar (_26_224) -> begin
"Exp_uvar"
end
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_26_227) -> begin
"Exp_delayed"
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((_26_230, m))) -> begin
(let _70_11619 = (meta_e_to_string m)
in (Support.String.strcat "Exp_meta_desugared " _70_11619))
end))
and meta_e_to_string = (fun ( _26_4 ) -> (match (_26_4) with
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
and typ_to_string = (fun ( x ) -> (let x = (Microsoft_FStar_Absyn_Util.compress_typ x)
in (match (x.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_26_243) -> begin
(Support.All.failwith "impossible")
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((_26_246, l))) -> begin
(sli l)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (meta) -> begin
(let _70_11625 = (Support.All.pipe_right meta meta_to_string)
in (Support.Microsoft.FStar.Util.format1 "(Meta %s)" _70_11625))
end
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(strBvd btv.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (v) -> begin
(sli v.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, c)) -> begin
(let _70_11627 = (binders_to_string " -> " binders)
in (let _70_11626 = (comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _70_11627 _70_11626)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((xt, f)) -> begin
(let _70_11630 = (strBvd xt.Microsoft_FStar_Absyn_Syntax.v)
in (let _70_11629 = (Support.All.pipe_right xt.Microsoft_FStar_Absyn_Syntax.sort typ_to_string)
in (let _70_11628 = (Support.All.pipe_right f formula_to_string)
in (Support.Microsoft.FStar.Util.format3 "%s:%s{%s}" _70_11630 _70_11629 _70_11628))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, args)) -> begin
(let q_to_string = (fun ( k ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t)) -> begin
(k (b, t))
end
| _26_281 -> begin
(let _70_11641 = (tag_of_typ t)
in (let _70_11640 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "<Expected a type-lambda! got %s>%s" _70_11641 _70_11640)))
end))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _70_11642 = (exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 "(<Expected a type!>%s)" _70_11642))
end))
in (let qbinder_to_string = (q_to_string (fun ( x ) -> (binder_to_string (Support.Prims.fst x))))
in (let qbody_to_string = (q_to_string (fun ( x ) -> (typ_to_string (Support.Prims.snd x))))
in (let args' = (match (((Support.ST.read Microsoft_FStar_Options.print_implicits) && (not ((is_quant t))))) with
| true -> begin
args
end
| false -> begin
(Support.List.filter (fun ( _26_5 ) -> (match (_26_5) with
| (_26_290, Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _26_295 -> begin
true
end)) args)
end)
in (match (((is_ite t) && ((Support.List.length args) = 3))) with
| true -> begin
(let _70_11653 = (let _70_11648 = (Support.List.nth args 0)
in (arg_to_string _70_11648))
in (let _70_11652 = (let _70_11649 = (Support.List.nth args 1)
in (arg_to_string _70_11649))
in (let _70_11651 = (let _70_11650 = (Support.List.nth args 2)
in (arg_to_string _70_11650))
in (Support.Microsoft.FStar.Util.format3 "if %s then %s else %s" _70_11653 _70_11652 _70_11651))))
end
| false -> begin
(match (((is_b2t t) && ((Support.List.length args) = 1))) with
| true -> begin
(let _70_11654 = (Support.List.nth args 0)
in (Support.All.pipe_right _70_11654 arg_to_string))
end
| false -> begin
(match (((is_quant t) && ((Support.List.length args) <= 2))) with
| true -> begin
(let _70_11659 = (quant_to_string t)
in (let _70_11658 = (let _70_11655 = (Support.List.nth args' 0)
in (qbinder_to_string _70_11655))
in (let _70_11657 = (let _70_11656 = (Support.List.nth args' 0)
in (qbody_to_string _70_11656))
in (Support.Microsoft.FStar.Util.format3 "(%s (%s). %s)" _70_11659 _70_11658 _70_11657))))
end
| false -> begin
(match (((is_infix_type_op t) && ((Support.List.length args') = 2))) with
| true -> begin
(let _70_11664 = (let _70_11660 = (Support.List.nth args' 0)
in (Support.All.pipe_right _70_11660 arg_to_string))
in (let _70_11663 = (Support.All.pipe_right t infix_type_op_to_string)
in (let _70_11662 = (let _70_11661 = (Support.List.nth args' 1)
in (Support.All.pipe_right _70_11661 arg_to_string))
in (Support.Microsoft.FStar.Util.format3 "(%s %s %s)" _70_11664 _70_11663 _70_11662))))
end
| false -> begin
(match (((is_unary_type_op t) && ((Support.List.length args') = 1))) with
| true -> begin
(let _70_11667 = (Support.All.pipe_right t unary_type_op_to_string)
in (let _70_11666 = (let _70_11665 = (Support.List.nth args' 0)
in (Support.All.pipe_right _70_11665 arg_to_string))
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _70_11667 _70_11666)))
end
| false -> begin
(let _70_11669 = (Support.All.pipe_right t typ_to_string)
in (let _70_11668 = (Support.All.pipe_right args args_to_string)
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _70_11669 _70_11668)))
end)
end)
end)
end)
end)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((binders, t2)) -> begin
(let _70_11671 = (binders_to_string " " binders)
in (let _70_11670 = (Support.All.pipe_right t2 typ_to_string)
in (Support.Microsoft.FStar.Util.format2 "(fun %s -> %s)" _70_11671 _70_11670)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, k)) -> begin
(match ((Support.ST.read Microsoft_FStar_Options.print_real_names)) with
| true -> begin
(let _70_11673 = (typ_to_string t)
in (let _70_11672 = (kind_to_string k)
in (Support.Microsoft.FStar.Util.format2 "(%s <: %s)" _70_11673 _70_11672)))
end
| false -> begin
(Support.All.pipe_right t typ_to_string)
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
"<UNKNOWN>"
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(match ((Microsoft_FStar_Absyn_Visit.compress_typ_aux false x)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_26_319); Microsoft_FStar_Absyn_Syntax.tk = _26_317; Microsoft_FStar_Absyn_Syntax.pos = _26_315; Microsoft_FStar_Absyn_Syntax.fvs = _26_313; Microsoft_FStar_Absyn_Syntax.uvs = _26_311} -> begin
(uvar_t_to_string (uv, k))
end
| t -> begin
(Support.All.pipe_right t typ_to_string)
end)
end)))
and uvar_t_to_string = (fun ( _26_325 ) -> (match (_26_325) with
| (uv, k) -> begin
(match ((false && (Support.ST.read Microsoft_FStar_Options.print_real_names))) with
| true -> begin
(let _70_11677 = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _70_11675 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _70_11675))
end)
in (let _70_11676 = (kind_to_string k)
in (Support.Microsoft.FStar.Util.format2 "(U%s : %s)" _70_11677 _70_11676)))
end
| false -> begin
(let _70_11679 = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _70_11678 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _70_11678))
end)
in (Support.Microsoft.FStar.Util.format1 "U%s" _70_11679))
end)
end))
and imp_to_string = (fun ( s ) ( _26_6 ) -> (match (_26_6) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
(Support.String.strcat "#" s)
end
| Some (Microsoft_FStar_Absyn_Syntax.Equality) -> begin
(Support.String.strcat "=" s)
end
| _26_333 -> begin
s
end))
and binder_to_string' = (fun ( is_arrow ) ( b ) -> (match (b) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(match (((Microsoft_FStar_Absyn_Syntax.is_null_binder b) || ((let _70_11684 = (Support.ST.read Microsoft_FStar_Options.print_real_names)
in (Support.All.pipe_right _70_11684 Support.Prims.op_Negation)) && (Microsoft_FStar_Absyn_Syntax.is_null_pp a.Microsoft_FStar_Absyn_Syntax.v)))) with
| true -> begin
(kind_to_string a.Microsoft_FStar_Absyn_Syntax.sort)
end
| false -> begin
(match (((not (is_arrow)) && (not ((Support.ST.read Microsoft_FStar_Options.print_implicits))))) with
| true -> begin
(let _70_11685 = (strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (imp_to_string _70_11685 imp))
end
| false -> begin
(let _70_11689 = (let _70_11688 = (let _70_11686 = (strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.String.strcat _70_11686 ":"))
in (let _70_11687 = (kind_to_string a.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.String.strcat _70_11688 _70_11687)))
in (imp_to_string _70_11689 imp))
end)
end)
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(match (((Microsoft_FStar_Absyn_Syntax.is_null_binder b) || ((let _70_11690 = (Support.ST.read Microsoft_FStar_Options.print_real_names)
in (Support.All.pipe_right _70_11690 Support.Prims.op_Negation)) && (Microsoft_FStar_Absyn_Syntax.is_null_pp x.Microsoft_FStar_Absyn_Syntax.v)))) with
| true -> begin
(typ_to_string x.Microsoft_FStar_Absyn_Syntax.sort)
end
| false -> begin
(match (((not (is_arrow)) && (not ((Support.ST.read Microsoft_FStar_Options.print_implicits))))) with
| true -> begin
(let _70_11691 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (imp_to_string _70_11691 imp))
end
| false -> begin
(let _70_11695 = (let _70_11694 = (let _70_11692 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Support.String.strcat _70_11692 ":"))
in (let _70_11693 = (typ_to_string x.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.String.strcat _70_11694 _70_11693)))
in (imp_to_string _70_11695 imp))
end)
end)
end))
and binder_to_string = (fun ( b ) -> (binder_to_string' false b))
and arrow_binder_to_string = (fun ( b ) -> (binder_to_string' true b))
and binders_to_string = (fun ( sep ) ( bs ) -> (let bs = (match ((Support.ST.read Microsoft_FStar_Options.print_implicits)) with
| true -> begin
bs
end
| false -> begin
(filter_imp bs)
end)
in (match ((sep = " -> ")) with
| true -> begin
(let _70_11700 = (Support.All.pipe_right bs (Support.List.map arrow_binder_to_string))
in (Support.All.pipe_right _70_11700 (Support.String.concat sep)))
end
| false -> begin
(let _70_11701 = (Support.All.pipe_right bs (Support.List.map binder_to_string))
in (Support.All.pipe_right _70_11701 (Support.String.concat sep)))
end)))
and arg_to_string = (fun ( _26_7 ) -> (match (_26_7) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _70_11703 = (typ_to_string a)
in (imp_to_string _70_11703 imp))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _70_11704 = (exp_to_string x)
in (imp_to_string _70_11704 imp))
end))
and args_to_string = (fun ( args ) -> (let args = (match ((Support.ST.read Microsoft_FStar_Options.print_implicits)) with
| true -> begin
args
end
| false -> begin
(filter_imp args)
end)
in (let _70_11706 = (Support.All.pipe_right args (Support.List.map arg_to_string))
in (Support.All.pipe_right _70_11706 (Support.String.concat " ")))))
and lcomp_typ_to_string = (fun ( lc ) -> (let _70_11709 = (sli lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in (let _70_11708 = (typ_to_string lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in (Support.Microsoft.FStar.Util.format2 "%s %s" _70_11709 _70_11708))))
and comp_typ_to_string = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _70_11711 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "Tot %s" _70_11711))
end
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
(let basic = (match (((Support.All.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.for_some (fun ( _26_8 ) -> (match (_26_8) with
| Microsoft_FStar_Absyn_Syntax.TOTAL -> begin
true
end
| _26_369 -> begin
false
end)))) && (not ((Support.ST.read Microsoft_FStar_Options.print_effect_args))))) with
| true -> begin
(let _70_11713 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (Support.Microsoft.FStar.Util.format1 "Tot %s" _70_11713))
end
| false -> begin
(match (((not ((Support.ST.read Microsoft_FStar_Options.print_effect_args))) && (Microsoft_FStar_Absyn_Syntax.lid_equals c.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_ML_lid))) with
| true -> begin
(typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
end
| false -> begin
(match (((not ((Support.ST.read Microsoft_FStar_Options.print_effect_args))) && (Support.All.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.for_some (fun ( _26_9 ) -> (match (_26_9) with
| Microsoft_FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _26_373 -> begin
false
end)))))) with
| true -> begin
(let _70_11715 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (Support.Microsoft.FStar.Util.format1 "ALL %s" _70_11715))
end
| false -> begin
(match ((Support.ST.read Microsoft_FStar_Options.print_effect_args)) with
| true -> begin
(let _70_11719 = (sli c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _70_11718 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _70_11717 = (let _70_11716 = (Support.All.pipe_right c.Microsoft_FStar_Absyn_Syntax.effect_args (Support.List.map effect_arg_to_string))
in (Support.All.pipe_right _70_11716 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format3 "%s (%s) %s" _70_11719 _70_11718 _70_11717))))
end
| false -> begin
(let _70_11721 = (sli c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _70_11720 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (Support.Microsoft.FStar.Util.format2 "%s (%s)" _70_11721 _70_11720)))
end)
end)
end)
end)
in (let dec = (let _70_11725 = (Support.All.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Support.List.collect (fun ( _26_10 ) -> (match (_26_10) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _70_11724 = (let _70_11723 = (exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 " (decreases %s)" _70_11723))
in (_70_11724)::[])
end
| _26_379 -> begin
[]
end))))
in (Support.All.pipe_right _70_11725 (Support.String.concat " ")))
in (Support.Microsoft.FStar.Util.format2 "%s%s" basic dec)))
end))
and effect_arg_to_string = (fun ( e ) -> (match (e) with
| (Support.Microsoft.FStar.Util.Inr (e), _26_385) -> begin
(exp_to_string e)
end
| (Support.Microsoft.FStar.Util.Inl (wp), _26_390) -> begin
(formula_to_string wp)
end))
and formula_to_string = (fun ( phi ) -> (typ_to_string phi))
and formula_to_string_old_now_unused = (fun ( phi ) -> (let const_op = (fun ( f ) ( _26_396 ) -> f)
in (let un_op = (fun ( f ) ( _26_11 ) -> (match (_26_11) with
| (Support.Microsoft.FStar.Util.Inl (t), _26_404)::[] -> begin
(let _70_11737 = (formula_to_string t)
in (Support.Microsoft.FStar.Util.format2 "%s %s" f _70_11737))
end
| _26_408 -> begin
(Support.All.failwith "impos")
end))
in (let bin_top = (fun ( f ) ( _26_12 ) -> (match (_26_12) with
| (Support.Microsoft.FStar.Util.Inl (t1), _26_420)::(Support.Microsoft.FStar.Util.Inl (t2), _26_415)::[] -> begin
(let _70_11743 = (formula_to_string t1)
in (let _70_11742 = (formula_to_string t2)
in (Support.Microsoft.FStar.Util.format3 "%s %s %s" _70_11743 f _70_11742)))
end
| _26_424 -> begin
(Support.All.failwith "Impos")
end))
in (let bin_eop = (fun ( f ) ( _26_13 ) -> (match (_26_13) with
| (Support.Microsoft.FStar.Util.Inr (e1), _26_436)::(Support.Microsoft.FStar.Util.Inr (e2), _26_431)::[] -> begin
(let _70_11749 = (exp_to_string e1)
in (let _70_11748 = (exp_to_string e2)
in (Support.Microsoft.FStar.Util.format3 "%s %s %s" _70_11749 f _70_11748)))
end
| _26_440 -> begin
(Support.All.failwith "impos")
end))
in (let ite = (fun ( _26_14 ) -> (match (_26_14) with
| (Support.Microsoft.FStar.Util.Inl (t1), _26_455)::(Support.Microsoft.FStar.Util.Inl (t2), _26_450)::(Support.Microsoft.FStar.Util.Inl (t3), _26_445)::[] -> begin
(let _70_11754 = (formula_to_string t1)
in (let _70_11753 = (formula_to_string t2)
in (let _70_11752 = (formula_to_string t3)
in (Support.Microsoft.FStar.Util.format3 "if %s then %s else %s" _70_11754 _70_11753 _70_11752))))
end
| _26_459 -> begin
(Support.All.failwith "impos")
end))
in (let eq_op = (fun ( _26_15 ) -> (match (_26_15) with
| (Support.Microsoft.FStar.Util.Inl (t1), _26_480)::(Support.Microsoft.FStar.Util.Inl (t2), _26_475)::(Support.Microsoft.FStar.Util.Inr (e1), _26_470)::(Support.Microsoft.FStar.Util.Inr (e2), _26_465)::[] -> begin
(match ((Support.ST.read Microsoft_FStar_Options.print_implicits)) with
| true -> begin
(let _70_11760 = (typ_to_string t1)
in (let _70_11759 = (typ_to_string t2)
in (let _70_11758 = (exp_to_string e1)
in (let _70_11757 = (exp_to_string e2)
in (Support.Microsoft.FStar.Util.format4 "Eq2 %s %s %s %s" _70_11760 _70_11759 _70_11758 _70_11757)))))
end
| false -> begin
(let _70_11762 = (exp_to_string e1)
in (let _70_11761 = (exp_to_string e2)
in (Support.Microsoft.FStar.Util.format2 "%s == %s" _70_11762 _70_11761)))
end)
end
| (Support.Microsoft.FStar.Util.Inr (e1), _26_491)::(Support.Microsoft.FStar.Util.Inr (e2), _26_486)::[] -> begin
(let _70_11764 = (exp_to_string e1)
in (let _70_11763 = (exp_to_string e2)
in (Support.Microsoft.FStar.Util.format2 "%s == %s" _70_11764 _70_11763)))
end
| _26_495 -> begin
(Support.All.failwith "Impossible")
end))
in (let connectives = ((Microsoft_FStar_Absyn_Const.and_lid, (bin_top "/\\")))::((Microsoft_FStar_Absyn_Const.or_lid, (bin_top "\\/")))::((Microsoft_FStar_Absyn_Const.imp_lid, (bin_top "==>")))::((Microsoft_FStar_Absyn_Const.iff_lid, (bin_top "<==>")))::((Microsoft_FStar_Absyn_Const.ite_lid, ite))::((Microsoft_FStar_Absyn_Const.not_lid, (un_op "~")))::((Microsoft_FStar_Absyn_Const.eqT_lid, (bin_top "==")))::((Microsoft_FStar_Absyn_Const.eq2_lid, eq_op))::((Microsoft_FStar_Absyn_Const.true_lid, (const_op "True")))::((Microsoft_FStar_Absyn_Const.false_lid, (const_op "False")))::[]
in (let fallback = (fun ( phi ) -> (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((binders, phi)) -> begin
(let _70_11803 = (binders_to_string " " binders)
in (let _70_11802 = (formula_to_string phi)
in (Support.Microsoft.FStar.Util.format2 "(fun %s => %s)" _70_11803 _70_11802)))
end
| _26_505 -> begin
(typ_to_string phi)
end))
in (match ((Microsoft_FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (Microsoft_FStar_Absyn_Util.BaseConn ((op, arms))) -> begin
(match ((Support.All.pipe_right connectives (Support.List.tryFind (fun ( _26_515 ) -> (match (_26_515) with
| (l, _26_514) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some ((_26_518, f)) -> begin
(f arms)
end)
end
| Some (Microsoft_FStar_Absyn_Util.QAll ((vars, _26_524, body))) -> begin
(let _70_11821 = (binders_to_string " " vars)
in (let _70_11820 = (formula_to_string body)
in (Support.Microsoft.FStar.Util.format2 "(forall %s. %s)" _70_11821 _70_11820)))
end
| Some (Microsoft_FStar_Absyn_Util.QEx ((vars, _26_531, body))) -> begin
(let _70_11823 = (binders_to_string " " vars)
in (let _70_11822 = (formula_to_string body)
in (Support.Microsoft.FStar.Util.format2 "(exists %s. %s)" _70_11823 _70_11822)))
end))))))))))
and exp_to_string = (fun ( x ) -> (match ((let _70_11825 = (Microsoft_FStar_Absyn_Util.compress_exp x)
in _70_11825.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_26_538) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _26_542))) -> begin
(exp_to_string e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, t)) -> begin
(uvar_e_to_string (uv, t))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (bvv) -> begin
(strBvd bvv.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _26_554)) -> begin
(sli fv.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(Support.All.pipe_right c const_to_string)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((binders, e)) -> begin
(let _70_11827 = (binders_to_string " " binders)
in (let _70_11826 = (Support.All.pipe_right e exp_to_string)
in (Support.Microsoft.FStar.Util.format2 "(fun %s -> %s)" _70_11827 _70_11826)))
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
(let _70_11830 = (let _70_11829 = (let _70_11828 = (Support.List.map exp_to_string es)
in (Support.String.concat "; " _70_11828))
in (Support.String.strcat "%[" _70_11829))
in (Support.String.strcat _70_11830 "]"))
end
| None -> begin
(let args' = (let _70_11832 = (filter_imp args)
in (Support.All.pipe_right _70_11832 (Support.List.filter (fun ( _26_16 ) -> (match (_26_16) with
| (Support.Microsoft.FStar.Util.Inr (_26_573), _26_576) -> begin
true
end
| _26_579 -> begin
false
end)))))
in (match (((is_infix_prim_op e) && ((Support.List.length args') = 2))) with
| true -> begin
(let _70_11837 = (let _70_11833 = (Support.List.nth args' 0)
in (Support.All.pipe_right _70_11833 arg_to_string))
in (let _70_11836 = (Support.All.pipe_right e infix_prim_op_to_string)
in (let _70_11835 = (let _70_11834 = (Support.List.nth args' 1)
in (Support.All.pipe_right _70_11834 arg_to_string))
in (Support.Microsoft.FStar.Util.format3 "(%s %s %s)" _70_11837 _70_11836 _70_11835))))
end
| false -> begin
(match (((is_unary_prim_op e) && ((Support.List.length args') = 1))) with
| true -> begin
(let _70_11840 = (Support.All.pipe_right e unary_prim_op_to_string)
in (let _70_11839 = (let _70_11838 = (Support.List.nth args' 0)
in (Support.All.pipe_right _70_11838 arg_to_string))
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _70_11840 _70_11839)))
end
| false -> begin
(let _70_11842 = (Support.All.pipe_right e exp_to_string)
in (let _70_11841 = (args_to_string args)
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _70_11842 _70_11841)))
end)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, pats)) -> begin
(let _70_11850 = (Support.All.pipe_right e exp_to_string)
in (let _70_11849 = (let _70_11848 = (Support.All.pipe_right pats (Support.List.map (fun ( _26_588 ) -> (match (_26_588) with
| (p, wopt, e) -> begin
(let _70_11847 = (Support.All.pipe_right p pat_to_string)
in (let _70_11846 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _70_11844 = (Support.All.pipe_right w exp_to_string)
in (Support.Microsoft.FStar.Util.format1 "when %s" _70_11844))
end)
in (let _70_11845 = (Support.All.pipe_right e exp_to_string)
in (Support.Microsoft.FStar.Util.format3 "%s %s -> %s" _70_11847 _70_11846 _70_11845))))
end))))
in (Support.Microsoft.FStar.Util.concat_l "\n\t" _70_11848))
in (Support.Microsoft.FStar.Util.format2 "(match %s with %s)" _70_11850 _70_11849)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _26_595)) -> begin
(let _70_11852 = (Support.All.pipe_right e exp_to_string)
in (let _70_11851 = (Support.All.pipe_right t typ_to_string)
in (Support.Microsoft.FStar.Util.format2 "(%s:%s)" _70_11852 _70_11851)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, e)) -> begin
(let _70_11854 = (lbs_to_string lbs)
in (let _70_11853 = (Support.All.pipe_right e exp_to_string)
in (Support.Microsoft.FStar.Util.format2 "%s in %s" _70_11854 _70_11853)))
end))
and uvar_e_to_string = (fun ( _26_605 ) -> (match (_26_605) with
| (uv, _26_604) -> begin
(let _70_11857 = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _70_11856 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _70_11856))
end)
in (Support.String.strcat "\'e" _70_11857))
end))
and lbs_to_string = (fun ( lbs ) -> (let _70_11864 = (let _70_11863 = (Support.All.pipe_right (Support.Prims.snd lbs) (Support.List.map (fun ( lb ) -> (let _70_11862 = (lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (let _70_11861 = (Support.All.pipe_right lb.Microsoft_FStar_Absyn_Syntax.lbtyp typ_to_string)
in (let _70_11860 = (Support.All.pipe_right lb.Microsoft_FStar_Absyn_Syntax.lbdef exp_to_string)
in (Support.Microsoft.FStar.Util.format3 "%s:%s = %s" _70_11862 _70_11861 _70_11860)))))))
in (Support.Microsoft.FStar.Util.concat_l "\n and " _70_11863))
in (Support.Microsoft.FStar.Util.format2 "let %s %s" (match ((Support.Prims.fst lbs)) with
| true -> begin
"rec"
end
| false -> begin
""
end) _70_11864)))
and lbname_to_string = (fun ( x ) -> (match (x) with
| Support.Microsoft.FStar.Util.Inl (bvd) -> begin
(strBvd bvd)
end
| Support.Microsoft.FStar.Util.Inr (lid) -> begin
(sli lid)
end))
and either_to_string = (fun ( x ) -> (match (x) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(typ_to_string t)
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(exp_to_string e)
end))
and either_l_to_string = (fun ( delim ) ( l ) -> (let _70_11869 = (Support.All.pipe_right l (Support.List.map either_to_string))
in (Support.All.pipe_right _70_11869 (Support.Microsoft.FStar.Util.concat_l delim))))
and meta_to_string = (fun ( x ) -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _26_623, _26_625)) -> begin
(let _70_11871 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "(refresh) %s" _70_11871))
end
| Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, _26_631, _26_633)) -> begin
(let _70_11872 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "(labeled \"%s\") %s" l _70_11872))
end
| Microsoft_FStar_Absyn_Syntax.Meta_named ((_26_637, l)) -> begin
(sli l)
end
| Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, ps)) -> begin
(let _70_11874 = (args_to_string ps)
in (let _70_11873 = (Support.All.pipe_right t typ_to_string)
in (Support.Microsoft.FStar.Util.format2 "{:pattern %s} %s" _70_11874 _70_11873)))
end
| Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, _26_648)) -> begin
(let _70_11876 = (formula_to_string t1)
in (let _70_11875 = (formula_to_string t2)
in (Support.Microsoft.FStar.Util.format2 "%s /\\ %s" _70_11876 _70_11875)))
end))
and kind_to_string = (fun ( x ) -> (match ((let _70_11878 = (Microsoft_FStar_Absyn_Util.compress_kind x)
in _70_11878.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam (_26_653) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed (_26_656) -> begin
(Support.All.failwith "Impossible")
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
(let _70_11880 = (sli n)
in (let _70_11879 = (args_to_string args)
in (Support.Microsoft.FStar.Util.format2 "%s %s" _70_11880 _70_11879)))
end)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((binders, k)) -> begin
(let _70_11882 = (binders_to_string " -> " binders)
in (let _70_11881 = (Support.All.pipe_right k kind_to_string)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _70_11882 _70_11881)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun ( uv ) -> (let _70_11884 = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _70_11883 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _70_11883))
end)
in (Support.String.strcat "\'k_" _70_11884)))
and uvar_k_to_string' = (fun ( _26_678 ) -> (match (_26_678) with
| (uv, args) -> begin
(let str = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _70_11886 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _70_11886))
end)
in (let _70_11887 = (args_to_string args)
in (Support.Microsoft.FStar.Util.format2 "(\'k_%s %s)" str _70_11887)))
end))
and pat_to_string = (fun ( x ) -> (match (x.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, _26_683, pats)) -> begin
(let _70_11892 = (sli l.Microsoft_FStar_Absyn_Syntax.v)
in (let _70_11891 = (let _70_11890 = (Support.List.map (fun ( _26_689 ) -> (match (_26_689) with
| (x, b) -> begin
(let p = (pat_to_string x)
in (match (b) with
| true -> begin
(Support.String.strcat "#" p)
end
| false -> begin
p
end))
end)) pats)
in (Support.All.pipe_right _70_11890 (Support.String.concat " ")))
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _70_11892 _70_11891)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _26_693)) -> begin
(let _70_11893 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 ".%s" _70_11893))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((x, _26_698)) -> begin
(let _70_11894 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 ".\'%s" _70_11894))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var (x) -> begin
(strBvd x.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(strBvd a.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (_26_708) -> begin
"_"
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (_26_711) -> begin
"\'_"
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(let _70_11895 = (Support.List.map pat_to_string ps)
in (Support.Microsoft.FStar.Util.concat_l " | " _70_11895))
end))

let subst_to_string = (fun ( subst ) -> (let _70_11903 = (let _70_11902 = (Support.List.map (fun ( _26_17 ) -> (match (_26_17) with
| Support.Microsoft.FStar.Util.Inl ((a, t)) -> begin
(let _70_11899 = (strBvd a)
in (let _70_11898 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _70_11899 _70_11898)))
end
| Support.Microsoft.FStar.Util.Inr ((x, e)) -> begin
(let _70_11901 = (strBvd x)
in (let _70_11900 = (exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _70_11901 _70_11900)))
end)) subst)
in (Support.All.pipe_right _70_11902 (Support.String.concat ", ")))
in (Support.All.pipe_left (Support.Microsoft.FStar.Util.format1 "{%s}") _70_11903)))

let freevars_to_string = (fun ( fvs ) -> (let f = (fun ( l ) -> (let _70_11909 = (let _70_11908 = (Support.All.pipe_right l Support.Microsoft.FStar.Util.set_elements)
in (Support.All.pipe_right _70_11908 (Support.List.map (fun ( t ) -> (strBvd t.Microsoft_FStar_Absyn_Syntax.v)))))
in (Support.All.pipe_right _70_11909 (Support.String.concat ", "))))
in (let _70_11911 = (f fvs.Microsoft_FStar_Absyn_Syntax.ftvs)
in (let _70_11910 = (f fvs.Microsoft_FStar_Absyn_Syntax.fxvs)
in (Support.Microsoft.FStar.Util.format2 "ftvs={%s}, fxvs={%s}" _70_11911 _70_11910)))))

let qual_to_string = (fun ( _26_18 ) -> (match (_26_18) with
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
"logic"
end
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
"opaque"
end
| Microsoft_FStar_Absyn_Syntax.Discriminator (_26_735) -> begin
"discriminator"
end
| Microsoft_FStar_Absyn_Syntax.Projector (_26_738) -> begin
"projector"
end
| Microsoft_FStar_Absyn_Syntax.RecordType (ids) -> begin
(let _70_11916 = (let _70_11915 = (Support.All.pipe_right ids (Support.List.map (fun ( lid ) -> lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)))
in (Support.All.pipe_right _70_11915 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format1 "record(%s)" _70_11916))
end
| _26_744 -> begin
"other"
end))

let quals_to_string = (fun ( quals ) -> (let _70_11919 = (Support.All.pipe_right quals (Support.List.map qual_to_string))
in (Support.All.pipe_right _70_11919 (Support.String.concat " "))))

let rec sigelt_to_string = (fun ( x ) -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Sig_pragma ((Microsoft_FStar_Absyn_Syntax.ResetOptions, _26_749)) -> begin
"#reset-options"
end
| Microsoft_FStar_Absyn_Syntax.Sig_pragma ((Microsoft_FStar_Absyn_Syntax.SetOptions (s), _26_755)) -> begin
(Support.Microsoft.FStar.Util.format1 "#set-options \"%s\"" s)
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _26_762, _26_764, quals, _26_767)) -> begin
(let _70_11924 = (quals_to_string quals)
in (let _70_11923 = (binders_to_string " " tps)
in (let _70_11922 = (kind_to_string k)
in (Support.Microsoft.FStar.Util.format4 "%s type %s %s : %s" _70_11924 lid.Microsoft_FStar_Absyn_Syntax.str _70_11923 _70_11922))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k, t, _26_775, _26_777)) -> begin
(let _70_11927 = (binders_to_string " " tps)
in (let _70_11926 = (kind_to_string k)
in (let _70_11925 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format4 "type %s %s : %s = %s" lid.Microsoft_FStar_Absyn_Syntax.str _70_11927 _70_11926 _70_11925))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, t, _26_783, _26_785, _26_787, _26_789)) -> begin
(let _70_11928 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "datacon %s : %s" lid.Microsoft_FStar_Absyn_Syntax.str _70_11928))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, _26_796)) -> begin
(let _70_11930 = (quals_to_string quals)
in (let _70_11929 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format3 "%s val %s : %s" _70_11930 lid.Microsoft_FStar_Absyn_Syntax.str _70_11929)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((lid, f, _26_802, _26_804)) -> begin
(let _70_11931 = (typ_to_string f)
in (Support.Microsoft.FStar.Util.format2 "val %s : %s" lid.Microsoft_FStar_Absyn_Syntax.str _70_11931))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, _26_809, _26_811, b)) -> begin
(lbs_to_string lbs)
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, _26_817)) -> begin
(let _70_11932 = (exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 "let _ = %s" _70_11932))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _26_822, _26_824, _26_826)) -> begin
(let _70_11933 = (Support.List.map sigelt_to_string ses)
in (Support.All.pipe_right _70_11933 (Support.String.concat "\n")))
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_26_830) -> begin
"new_effect { ... }"
end
| Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_26_833) -> begin
"sub_effect ..."
end
| Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_26_836) -> begin
"kind ..."
end
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((l, tps, c, _26_842, _26_844)) -> begin
(let _70_11936 = (sli l)
in (let _70_11935 = (binders_to_string " " tps)
in (let _70_11934 = (comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.format3 "effect %s %s = %s" _70_11936 _70_11935 _70_11934))))
end))

let format_error = (fun ( r ) ( msg ) -> (let _70_11941 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "%s: %s\n" _70_11941 msg)))

let rec sigelt_to_string_short = (fun ( x ) -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Sig_let (((_26_851, {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _26_855; Microsoft_FStar_Absyn_Syntax.lbdef = _26_853}::[]), _26_863, _26_865, _26_867)) -> begin
(let _70_11944 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "let %s : %s" l.Microsoft_FStar_Absyn_Syntax.str _70_11944))
end
| _26_871 -> begin
(let _70_11947 = (let _70_11946 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt x)
in (Support.All.pipe_right _70_11946 (Support.List.map (fun ( l ) -> l.Microsoft_FStar_Absyn_Syntax.str))))
in (Support.All.pipe_right _70_11947 (Support.String.concat ", ")))
end))

let rec modul_to_string = (fun ( m ) -> (let _70_11952 = (sli m.Microsoft_FStar_Absyn_Syntax.name)
in (let _70_11951 = (let _70_11950 = (Support.List.map sigelt_to_string m.Microsoft_FStar_Absyn_Syntax.declarations)
in (Support.All.pipe_right _70_11950 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.format2 "module %s\n%s" _70_11952 _70_11951))))




