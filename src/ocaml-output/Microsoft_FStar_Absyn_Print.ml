
let infix_prim_ops = ((Microsoft_FStar_Absyn_Const.op_Addition, "+"))::((Microsoft_FStar_Absyn_Const.op_Subtraction, "-"))::((Microsoft_FStar_Absyn_Const.op_Multiply, "*"))::((Microsoft_FStar_Absyn_Const.op_Division, "/"))::((Microsoft_FStar_Absyn_Const.op_Eq, "="))::((Microsoft_FStar_Absyn_Const.op_ColonEq, ":="))::((Microsoft_FStar_Absyn_Const.op_notEq, "<>"))::((Microsoft_FStar_Absyn_Const.op_And, "&&"))::((Microsoft_FStar_Absyn_Const.op_Or, "||"))::((Microsoft_FStar_Absyn_Const.op_LTE, "<="))::((Microsoft_FStar_Absyn_Const.op_GTE, ">="))::((Microsoft_FStar_Absyn_Const.op_LT, "<"))::((Microsoft_FStar_Absyn_Const.op_GT, ">"))::((Microsoft_FStar_Absyn_Const.op_Modulus, "mod"))::[]

let unary_prim_ops = ((Microsoft_FStar_Absyn_Const.op_Negation, "not"))::((Microsoft_FStar_Absyn_Const.op_Minus, "-"))::[]

let infix_type_ops = ((Microsoft_FStar_Absyn_Const.and_lid, "/\\"))::((Microsoft_FStar_Absyn_Const.or_lid, "\\/"))::((Microsoft_FStar_Absyn_Const.imp_lid, "==>"))::((Microsoft_FStar_Absyn_Const.iff_lid, "<==>"))::((Microsoft_FStar_Absyn_Const.precedes_lid, "<<"))::((Microsoft_FStar_Absyn_Const.eq2_lid, "=="))::((Microsoft_FStar_Absyn_Const.eqT_lid, "=="))::[]

let unary_type_ops = ((Microsoft_FStar_Absyn_Const.not_lid, "~"))::[]

let is_prim_op = (fun ps f -> (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar (fv, _26_23) -> begin
(All.pipe_right ps (Microsoft_FStar_Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v)))
end
| _26_27 -> begin
false
end))

let is_type_op = (fun ps t -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(All.pipe_right ps (Microsoft_FStar_Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals ftv.Microsoft_FStar_Absyn_Syntax.v)))
end
| _26_33 -> begin
false
end))

let get_lid = (fun f -> (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar (fv, _26_37) -> begin
fv.Microsoft_FStar_Absyn_Syntax.v
end
| _26_41 -> begin
(All.failwith "get_lid")
end))

let get_type_lid = (fun t -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (ftv) -> begin
ftv.Microsoft_FStar_Absyn_Syntax.v
end
| _26_46 -> begin
(All.failwith "get_type_lid")
end))

let is_infix_prim_op = (fun e -> (is_prim_op (Prims.fst (Microsoft_FStar_List.split infix_prim_ops)) e))

let is_unary_prim_op = (fun e -> (is_prim_op (Prims.fst (Microsoft_FStar_List.split unary_prim_ops)) e))

let is_infix_type_op = (fun t -> (is_type_op (Prims.fst (Microsoft_FStar_List.split infix_type_ops)) t))

let is_unary_type_op = (fun t -> (is_type_op (Prims.fst (Microsoft_FStar_List.split unary_type_ops)) t))

let quants = ((Microsoft_FStar_Absyn_Const.forall_lid, "forall"))::((Microsoft_FStar_Absyn_Const.exists_lid, "exists"))::((Microsoft_FStar_Absyn_Const.allTyp_lid, "forall"))::((Microsoft_FStar_Absyn_Const.exTyp_lid, "exists"))::[]

let is_b2t = (fun t -> (is_type_op ((Microsoft_FStar_Absyn_Const.b2t_lid)::[]) t))

let is_quant = (fun t -> (is_type_op (Prims.fst (Microsoft_FStar_List.split quants)) t))

let is_ite = (fun t -> (is_type_op ((Microsoft_FStar_Absyn_Const.ite_lid)::[]) t))

let is_lex_cons = (fun f -> (is_prim_op ((Microsoft_FStar_Absyn_Const.lexcons_lid)::[]) f))

let is_lex_top = (fun f -> (is_prim_op ((Microsoft_FStar_Absyn_Const.lextop_lid)::[]) f))

let is_inr = (fun _26_1 -> (match (_26_1) with
| Microsoft_FStar_Util.Inl (_26_58) -> begin
false
end
| Microsoft_FStar_Util.Inr (_26_61) -> begin
true
end))

let rec reconstruct_lex = (fun e -> (match ((let _92_28 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _92_28.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app (f, args) -> begin
(let args = (Microsoft_FStar_List.filter (fun a -> (((Prims.snd a) <> Some (Microsoft_FStar_Absyn_Syntax.Implicit)) && (is_inr (Prims.fst a)))) args)
in (let exps = (Microsoft_FStar_List.map (fun _26_2 -> (match (_26_2) with
| (Microsoft_FStar_Util.Inl (_26_72), _26_75) -> begin
(All.failwith "impossible")
end
| (Microsoft_FStar_Util.Inr (x), _26_80) -> begin
x
end)) args)
in (match (((is_lex_cons f) && ((Microsoft_FStar_List.length exps) = 2))) with
| true -> begin
(match ((let _92_31 = (Microsoft_FStar_List.nth exps 1)
in (reconstruct_lex _92_31))) with
| Some (xs) -> begin
(let _92_33 = (let _92_32 = (Microsoft_FStar_List.nth exps 0)
in (_92_32)::xs)
in Some (_92_33))
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

let rec find = (fun f l -> (match (l) with
| [] -> begin
(All.failwith "blah")
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

let find_lid = (fun x xs -> (let _92_47 = (find (fun p -> (Microsoft_FStar_Absyn_Syntax.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _92_47)))

let infix_prim_op_to_string = (fun e -> (let _92_49 = (get_lid e)
in (find_lid _92_49 infix_prim_ops)))

let unary_prim_op_to_string = (fun e -> (let _92_51 = (get_lid e)
in (find_lid _92_51 unary_prim_ops)))

let infix_type_op_to_string = (fun t -> (let _92_53 = (get_type_lid t)
in (find_lid _92_53 infix_type_ops)))

let unary_type_op_to_string = (fun t -> (let _92_55 = (get_type_lid t)
in (find_lid _92_55 unary_type_ops)))

let quant_to_string = (fun t -> (let _92_57 = (get_type_lid t)
in (find_lid _92_57 quants)))

let rec sli = (fun l -> (match ((ST.read Microsoft_FStar_Options.print_real_names)) with
| true -> begin
l.Microsoft_FStar_Absyn_Syntax.str
end
| false -> begin
l.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText
end))

let strBvd = (fun bvd -> (match ((ST.read Microsoft_FStar_Options.print_real_names)) with
| true -> begin
(Prims.strcat bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText bvd.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText)
end
| false -> begin
(match (((ST.read Microsoft_FStar_Options.hide_genident_nums) && (Microsoft_FStar_Util.starts_with bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText "_"))) with
| true -> begin
(All.try_with (fun _26_106 -> (match (()) with
| () -> begin
(let _26_112 = (let _92_62 = (Microsoft_FStar_Util.substring_from bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText 1)
in (Microsoft_FStar_Util.int_of_string _92_62))
in "_?")
end)) (fun _26_105 -> (match (_26_105) with
| _26_109 -> begin
bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText
end)))
end
| false -> begin
bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText
end)
end))

let filter_imp = (fun a -> (All.pipe_right a (Microsoft_FStar_List.filter (fun _26_3 -> (match (_26_3) with
| (_26_117, Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _26_122 -> begin
true
end)))))

let const_to_string = (fun x -> (match (x) with
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
(Microsoft_FStar_Util.string_of_int32 x)
end
| Microsoft_FStar_Absyn_Syntax.Const_float (x) -> begin
(Microsoft_FStar_Util.string_of_float x)
end
| Microsoft_FStar_Absyn_Syntax.Const_char (x) -> begin
(Prims.strcat (Prims.strcat "\'" (Microsoft_FStar_Util.string_of_char x)) "\'")
end
| Microsoft_FStar_Absyn_Syntax.Const_string (bytes, _26_135) -> begin
(Microsoft_FStar_Util.format1 "\"%s\"" (Microsoft_FStar_Util.string_of_bytes bytes))
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

let rec tag_of_typ = (fun t -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (_26_151) -> begin
"Typ_btvar"
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (v) -> begin
(Prims.strcat "Typ_const " v.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_26_156) -> begin
"Typ_fun"
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_26_159) -> begin
"Typ_refine"
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let _92_102 = (tag_of_typ head)
in (let _92_101 = (All.pipe_left Microsoft_FStar_Util.string_of_int (Microsoft_FStar_List.length args))
in (Microsoft_FStar_Util.format2 "Typ_app(%s, [%s args])" _92_102 _92_101)))
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
and tag_of_exp = (fun e -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
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
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared (_26_230, m)) -> begin
(let _92_106 = (meta_e_to_string m)
in (Prims.strcat "Exp_meta_desugared " _92_106))
end))
and meta_e_to_string = (fun _26_4 -> (match (_26_4) with
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
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_26_243) -> begin
(All.failwith "impossible")
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named (_26_246, l)) -> begin
(sli l)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (meta) -> begin
(let _92_112 = (All.pipe_right meta meta_to_string)
in (Microsoft_FStar_Util.format1 "(Meta %s)" _92_112))
end
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(strBvd btv.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (v) -> begin
(sli v.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun (binders, c) -> begin
(let _92_114 = (binders_to_string " -> " binders)
in (let _92_113 = (comp_typ_to_string c)
in (Microsoft_FStar_Util.format2 "(%s -> %s)" _92_114 _92_113)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (xt, f) -> begin
(let _92_117 = (strBvd xt.Microsoft_FStar_Absyn_Syntax.v)
in (let _92_116 = (All.pipe_right xt.Microsoft_FStar_Absyn_Syntax.sort typ_to_string)
in (let _92_115 = (All.pipe_right f formula_to_string)
in (Microsoft_FStar_Util.format3 "%s:%s{%s}" _92_117 _92_116 _92_115))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(let q_to_string = (fun k a -> (match ((Prims.fst a)) with
| Microsoft_FStar_Util.Inl (t) -> begin
(let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam (b::[], t) -> begin
(k (b, t))
end
| _26_281 -> begin
(let _92_128 = (tag_of_typ t)
in (let _92_127 = (typ_to_string t)
in (Microsoft_FStar_Util.format2 "<Expected a type-lambda! got %s>%s" _92_128 _92_127)))
end))
end
| Microsoft_FStar_Util.Inr (e) -> begin
(let _92_129 = (exp_to_string e)
in (Microsoft_FStar_Util.format1 "(<Expected a type!>%s)" _92_129))
end))
in (let qbinder_to_string = (q_to_string (fun x -> (binder_to_string (Prims.fst x))))
in (let qbody_to_string = (q_to_string (fun x -> (typ_to_string (Prims.snd x))))
in (let args' = (match (((ST.read Microsoft_FStar_Options.print_implicits) && (not ((is_quant t))))) with
| true -> begin
args
end
| false -> begin
(Microsoft_FStar_List.filter (fun _26_5 -> (match (_26_5) with
| (_26_290, Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _26_295 -> begin
true
end)) args)
end)
in (match (((is_ite t) && ((Microsoft_FStar_List.length args) = 3))) with
| true -> begin
(let _92_140 = (let _92_135 = (Microsoft_FStar_List.nth args 0)
in (arg_to_string _92_135))
in (let _92_139 = (let _92_136 = (Microsoft_FStar_List.nth args 1)
in (arg_to_string _92_136))
in (let _92_138 = (let _92_137 = (Microsoft_FStar_List.nth args 2)
in (arg_to_string _92_137))
in (Microsoft_FStar_Util.format3 "if %s then %s else %s" _92_140 _92_139 _92_138))))
end
| false -> begin
(match (((is_b2t t) && ((Microsoft_FStar_List.length args) = 1))) with
| true -> begin
(let _92_141 = (Microsoft_FStar_List.nth args 0)
in (All.pipe_right _92_141 arg_to_string))
end
| false -> begin
(match (((is_quant t) && ((Microsoft_FStar_List.length args) <= 2))) with
| true -> begin
(let _92_146 = (quant_to_string t)
in (let _92_145 = (let _92_142 = (Microsoft_FStar_List.nth args' 0)
in (qbinder_to_string _92_142))
in (let _92_144 = (let _92_143 = (Microsoft_FStar_List.nth args' 0)
in (qbody_to_string _92_143))
in (Microsoft_FStar_Util.format3 "(%s (%s). %s)" _92_146 _92_145 _92_144))))
end
| false -> begin
(match (((is_infix_type_op t) && ((Microsoft_FStar_List.length args') = 2))) with
| true -> begin
(let _92_151 = (let _92_147 = (Microsoft_FStar_List.nth args' 0)
in (All.pipe_right _92_147 arg_to_string))
in (let _92_150 = (All.pipe_right t infix_type_op_to_string)
in (let _92_149 = (let _92_148 = (Microsoft_FStar_List.nth args' 1)
in (All.pipe_right _92_148 arg_to_string))
in (Microsoft_FStar_Util.format3 "(%s %s %s)" _92_151 _92_150 _92_149))))
end
| false -> begin
(match (((is_unary_type_op t) && ((Microsoft_FStar_List.length args') = 1))) with
| true -> begin
(let _92_154 = (All.pipe_right t unary_type_op_to_string)
in (let _92_153 = (let _92_152 = (Microsoft_FStar_List.nth args' 0)
in (All.pipe_right _92_152 arg_to_string))
in (Microsoft_FStar_Util.format2 "(%s %s)" _92_154 _92_153)))
end
| false -> begin
(let _92_156 = (All.pipe_right t typ_to_string)
in (let _92_155 = (All.pipe_right args args_to_string)
in (Microsoft_FStar_Util.format2 "(%s %s)" _92_156 _92_155)))
end)
end)
end)
end)
end)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(let _92_158 = (binders_to_string " " binders)
in (let _92_157 = (All.pipe_right t2 typ_to_string)
in (Microsoft_FStar_Util.format2 "(fun %s -> %s)" _92_158 _92_157)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
(match ((ST.read Microsoft_FStar_Options.print_real_names)) with
| true -> begin
(let _92_160 = (typ_to_string t)
in (let _92_159 = (kind_to_string k)
in (Microsoft_FStar_Util.format2 "(%s <: %s)" _92_160 _92_159)))
end
| false -> begin
(All.pipe_right t typ_to_string)
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
"<UNKNOWN>"
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(match ((Microsoft_FStar_Absyn_Visit.compress_typ_aux false x)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_26_319); Microsoft_FStar_Absyn_Syntax.tk = _26_317; Microsoft_FStar_Absyn_Syntax.pos = _26_315; Microsoft_FStar_Absyn_Syntax.fvs = _26_313; Microsoft_FStar_Absyn_Syntax.uvs = _26_311} -> begin
(uvar_t_to_string (uv, k))
end
| t -> begin
(All.pipe_right t typ_to_string)
end)
end)))
and uvar_t_to_string = (fun _26_325 -> (match (_26_325) with
| (uv, k) -> begin
(match ((false && (ST.read Microsoft_FStar_Options.print_real_names))) with
| true -> begin
(let _92_164 = (match ((ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _92_162 = (Microsoft_FStar_Unionfind.uvar_id uv)
in (Microsoft_FStar_Util.string_of_int _92_162))
end)
in (let _92_163 = (kind_to_string k)
in (Microsoft_FStar_Util.format2 "(U%s : %s)" _92_164 _92_163)))
end
| false -> begin
(let _92_166 = (match ((ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _92_165 = (Microsoft_FStar_Unionfind.uvar_id uv)
in (Microsoft_FStar_Util.string_of_int _92_165))
end)
in (Microsoft_FStar_Util.format1 "U%s" _92_166))
end)
end))
and imp_to_string = (fun s _26_6 -> (match (_26_6) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
(Prims.strcat "#" s)
end
| Some (Microsoft_FStar_Absyn_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _26_333 -> begin
s
end))
and binder_to_string' = (fun is_arrow b -> (match (b) with
| (Microsoft_FStar_Util.Inl (a), imp) -> begin
(match (((Microsoft_FStar_Absyn_Syntax.is_null_binder b) || ((let _92_171 = (ST.read Microsoft_FStar_Options.print_real_names)
in (All.pipe_right _92_171 Prims.op_Negation)) && (Microsoft_FStar_Absyn_Syntax.is_null_pp a.Microsoft_FStar_Absyn_Syntax.v)))) with
| true -> begin
(kind_to_string a.Microsoft_FStar_Absyn_Syntax.sort)
end
| false -> begin
(match (((not (is_arrow)) && (not ((ST.read Microsoft_FStar_Options.print_implicits))))) with
| true -> begin
(let _92_172 = (strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (imp_to_string _92_172 imp))
end
| false -> begin
(let _92_176 = (let _92_175 = (let _92_173 = (strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Prims.strcat _92_173 ":"))
in (let _92_174 = (kind_to_string a.Microsoft_FStar_Absyn_Syntax.sort)
in (Prims.strcat _92_175 _92_174)))
in (imp_to_string _92_176 imp))
end)
end)
end
| (Microsoft_FStar_Util.Inr (x), imp) -> begin
(match (((Microsoft_FStar_Absyn_Syntax.is_null_binder b) || ((let _92_177 = (ST.read Microsoft_FStar_Options.print_real_names)
in (All.pipe_right _92_177 Prims.op_Negation)) && (Microsoft_FStar_Absyn_Syntax.is_null_pp x.Microsoft_FStar_Absyn_Syntax.v)))) with
| true -> begin
(typ_to_string x.Microsoft_FStar_Absyn_Syntax.sort)
end
| false -> begin
(match (((not (is_arrow)) && (not ((ST.read Microsoft_FStar_Options.print_implicits))))) with
| true -> begin
(let _92_178 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (imp_to_string _92_178 imp))
end
| false -> begin
(let _92_182 = (let _92_181 = (let _92_179 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Prims.strcat _92_179 ":"))
in (let _92_180 = (typ_to_string x.Microsoft_FStar_Absyn_Syntax.sort)
in (Prims.strcat _92_181 _92_180)))
in (imp_to_string _92_182 imp))
end)
end)
end))
and binder_to_string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string = (fun b -> (binder_to_string' true b))
and binders_to_string = (fun sep bs -> (let bs = (match ((ST.read Microsoft_FStar_Options.print_implicits)) with
| true -> begin
bs
end
| false -> begin
(filter_imp bs)
end)
in (match ((sep = " -> ")) with
| true -> begin
(let _92_187 = (All.pipe_right bs (Microsoft_FStar_List.map arrow_binder_to_string))
in (All.pipe_right _92_187 (Microsoft_FStar_String.concat sep)))
end
| false -> begin
(let _92_188 = (All.pipe_right bs (Microsoft_FStar_List.map binder_to_string))
in (All.pipe_right _92_188 (Microsoft_FStar_String.concat sep)))
end)))
and arg_to_string = (fun _26_7 -> (match (_26_7) with
| (Microsoft_FStar_Util.Inl (a), imp) -> begin
(let _92_190 = (typ_to_string a)
in (imp_to_string _92_190 imp))
end
| (Microsoft_FStar_Util.Inr (x), imp) -> begin
(let _92_191 = (exp_to_string x)
in (imp_to_string _92_191 imp))
end))
and args_to_string = (fun args -> (let args = (match ((ST.read Microsoft_FStar_Options.print_implicits)) with
| true -> begin
args
end
| false -> begin
(filter_imp args)
end)
in (let _92_193 = (All.pipe_right args (Microsoft_FStar_List.map arg_to_string))
in (All.pipe_right _92_193 (Microsoft_FStar_String.concat " ")))))
and lcomp_typ_to_string = (fun lc -> (let _92_196 = (sli lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in (let _92_195 = (typ_to_string lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in (Microsoft_FStar_Util.format2 "%s %s" _92_196 _92_195))))
and comp_typ_to_string = (fun c -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _92_198 = (typ_to_string t)
in (Microsoft_FStar_Util.format1 "Tot %s" _92_198))
end
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
(let basic = (match (((All.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Microsoft_FStar_Util.for_some (fun _26_8 -> (match (_26_8) with
| Microsoft_FStar_Absyn_Syntax.TOTAL -> begin
true
end
| _26_369 -> begin
false
end)))) && (not ((ST.read Microsoft_FStar_Options.print_effect_args))))) with
| true -> begin
(let _92_200 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (Microsoft_FStar_Util.format1 "Tot %s" _92_200))
end
| false -> begin
(match (((not ((ST.read Microsoft_FStar_Options.print_effect_args))) && (Microsoft_FStar_Absyn_Syntax.lid_equals c.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_ML_lid))) with
| true -> begin
(typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
end
| false -> begin
(match (((not ((ST.read Microsoft_FStar_Options.print_effect_args))) && (All.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Microsoft_FStar_Util.for_some (fun _26_9 -> (match (_26_9) with
| Microsoft_FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _26_373 -> begin
false
end)))))) with
| true -> begin
(let _92_202 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (Microsoft_FStar_Util.format1 "ALL %s" _92_202))
end
| false -> begin
(match ((ST.read Microsoft_FStar_Options.print_effect_args)) with
| true -> begin
(let _92_206 = (sli c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _92_205 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _92_204 = (let _92_203 = (All.pipe_right c.Microsoft_FStar_Absyn_Syntax.effect_args (Microsoft_FStar_List.map effect_arg_to_string))
in (All.pipe_right _92_203 (Microsoft_FStar_String.concat ", ")))
in (Microsoft_FStar_Util.format3 "%s (%s) %s" _92_206 _92_205 _92_204))))
end
| false -> begin
(let _92_208 = (sli c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _92_207 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (Microsoft_FStar_Util.format2 "%s (%s)" _92_208 _92_207)))
end)
end)
end)
end)
in (let dec = (let _92_212 = (All.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Microsoft_FStar_List.collect (fun _26_10 -> (match (_26_10) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _92_211 = (let _92_210 = (exp_to_string e)
in (Microsoft_FStar_Util.format1 " (decreases %s)" _92_210))
in (_92_211)::[])
end
| _26_379 -> begin
[]
end))))
in (All.pipe_right _92_212 (Microsoft_FStar_String.concat " ")))
in (Microsoft_FStar_Util.format2 "%s%s" basic dec)))
end))
and effect_arg_to_string = (fun e -> (match (e) with
| (Microsoft_FStar_Util.Inr (e), _26_385) -> begin
(exp_to_string e)
end
| (Microsoft_FStar_Util.Inl (wp), _26_390) -> begin
(formula_to_string wp)
end))
and formula_to_string = (fun phi -> (typ_to_string phi))
and formula_to_string_old_now_unused = (fun phi -> (let const_op = (fun f _26_396 -> f)
in (let un_op = (fun f _26_11 -> (match (_26_11) with
| (Microsoft_FStar_Util.Inl (t), _26_404)::[] -> begin
(let _92_224 = (formula_to_string t)
in (Microsoft_FStar_Util.format2 "%s %s" f _92_224))
end
| _26_408 -> begin
(All.failwith "impos")
end))
in (let bin_top = (fun f _26_12 -> (match (_26_12) with
| (Microsoft_FStar_Util.Inl (t1), _26_420)::(Microsoft_FStar_Util.Inl (t2), _26_415)::[] -> begin
(let _92_230 = (formula_to_string t1)
in (let _92_229 = (formula_to_string t2)
in (Microsoft_FStar_Util.format3 "%s %s %s" _92_230 f _92_229)))
end
| _26_424 -> begin
(All.failwith "Impos")
end))
in (let bin_eop = (fun f _26_13 -> (match (_26_13) with
| (Microsoft_FStar_Util.Inr (e1), _26_436)::(Microsoft_FStar_Util.Inr (e2), _26_431)::[] -> begin
(let _92_236 = (exp_to_string e1)
in (let _92_235 = (exp_to_string e2)
in (Microsoft_FStar_Util.format3 "%s %s %s" _92_236 f _92_235)))
end
| _26_440 -> begin
(All.failwith "impos")
end))
in (let ite = (fun _26_14 -> (match (_26_14) with
| (Microsoft_FStar_Util.Inl (t1), _26_455)::(Microsoft_FStar_Util.Inl (t2), _26_450)::(Microsoft_FStar_Util.Inl (t3), _26_445)::[] -> begin
(let _92_241 = (formula_to_string t1)
in (let _92_240 = (formula_to_string t2)
in (let _92_239 = (formula_to_string t3)
in (Microsoft_FStar_Util.format3 "if %s then %s else %s" _92_241 _92_240 _92_239))))
end
| _26_459 -> begin
(All.failwith "impos")
end))
in (let eq_op = (fun _26_15 -> (match (_26_15) with
| (Microsoft_FStar_Util.Inl (t1), _26_480)::(Microsoft_FStar_Util.Inl (t2), _26_475)::(Microsoft_FStar_Util.Inr (e1), _26_470)::(Microsoft_FStar_Util.Inr (e2), _26_465)::[] -> begin
(match ((ST.read Microsoft_FStar_Options.print_implicits)) with
| true -> begin
(let _92_247 = (typ_to_string t1)
in (let _92_246 = (typ_to_string t2)
in (let _92_245 = (exp_to_string e1)
in (let _92_244 = (exp_to_string e2)
in (Microsoft_FStar_Util.format4 "Eq2 %s %s %s %s" _92_247 _92_246 _92_245 _92_244)))))
end
| false -> begin
(let _92_249 = (exp_to_string e1)
in (let _92_248 = (exp_to_string e2)
in (Microsoft_FStar_Util.format2 "%s == %s" _92_249 _92_248)))
end)
end
| (Microsoft_FStar_Util.Inr (e1), _26_491)::(Microsoft_FStar_Util.Inr (e2), _26_486)::[] -> begin
(let _92_251 = (exp_to_string e1)
in (let _92_250 = (exp_to_string e2)
in (Microsoft_FStar_Util.format2 "%s == %s" _92_251 _92_250)))
end
| _26_495 -> begin
(All.failwith "Impossible")
end))
in (let connectives = ((Microsoft_FStar_Absyn_Const.and_lid, (bin_top "/\\")))::((Microsoft_FStar_Absyn_Const.or_lid, (bin_top "\\/")))::((Microsoft_FStar_Absyn_Const.imp_lid, (bin_top "==>")))::((Microsoft_FStar_Absyn_Const.iff_lid, (bin_top "<==>")))::((Microsoft_FStar_Absyn_Const.ite_lid, ite))::((Microsoft_FStar_Absyn_Const.not_lid, (un_op "~")))::((Microsoft_FStar_Absyn_Const.eqT_lid, (bin_top "==")))::((Microsoft_FStar_Absyn_Const.eq2_lid, eq_op))::((Microsoft_FStar_Absyn_Const.true_lid, (const_op "True")))::((Microsoft_FStar_Absyn_Const.false_lid, (const_op "False")))::[]
in (let fallback = (fun phi -> (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam (binders, phi) -> begin
(let _92_290 = (binders_to_string " " binders)
in (let _92_289 = (formula_to_string phi)
in (Microsoft_FStar_Util.format2 "(fun %s => %s)" _92_290 _92_289)))
end
| _26_505 -> begin
(typ_to_string phi)
end))
in (match ((Microsoft_FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (Microsoft_FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((All.pipe_right connectives (Microsoft_FStar_List.tryFind (fun _26_515 -> (match (_26_515) with
| (l, _26_514) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_26_518, f) -> begin
(f arms)
end)
end
| Some (Microsoft_FStar_Absyn_Util.QAll (vars, _26_524, body)) -> begin
(let _92_308 = (binders_to_string " " vars)
in (let _92_307 = (formula_to_string body)
in (Microsoft_FStar_Util.format2 "(forall %s. %s)" _92_308 _92_307)))
end
| Some (Microsoft_FStar_Absyn_Util.QEx (vars, _26_531, body)) -> begin
(let _92_310 = (binders_to_string " " vars)
in (let _92_309 = (formula_to_string body)
in (Microsoft_FStar_Util.format2 "(exists %s. %s)" _92_310 _92_309)))
end))))))))))
and exp_to_string = (fun x -> (match ((let _92_312 = (Microsoft_FStar_Absyn_Util.compress_exp x)
in _92_312.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_26_538) -> begin
(All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared (e, _26_542)) -> begin
(exp_to_string e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(uvar_e_to_string (uv, t))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (bvv) -> begin
(strBvd bvv.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar (fv, _26_554) -> begin
(sli fv.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(All.pipe_right c const_to_string)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (binders, e) -> begin
(let _92_314 = (binders_to_string " " binders)
in (let _92_313 = (All.pipe_right e exp_to_string)
in (Microsoft_FStar_Util.format2 "(fun %s -> %s)" _92_314 _92_313)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(let lex = (match ((ST.read Microsoft_FStar_Options.print_implicits)) with
| true -> begin
None
end
| false -> begin
(reconstruct_lex x)
end)
in (match (lex) with
| Some (es) -> begin
(let _92_317 = (let _92_316 = (let _92_315 = (Microsoft_FStar_List.map exp_to_string es)
in (Microsoft_FStar_String.concat "; " _92_315))
in (Prims.strcat "%[" _92_316))
in (Prims.strcat _92_317 "]"))
end
| None -> begin
(let args' = (let _92_319 = (filter_imp args)
in (All.pipe_right _92_319 (Microsoft_FStar_List.filter (fun _26_16 -> (match (_26_16) with
| (Microsoft_FStar_Util.Inr (_26_573), _26_576) -> begin
true
end
| _26_579 -> begin
false
end)))))
in (match (((is_infix_prim_op e) && ((Microsoft_FStar_List.length args') = 2))) with
| true -> begin
(let _92_324 = (let _92_320 = (Microsoft_FStar_List.nth args' 0)
in (All.pipe_right _92_320 arg_to_string))
in (let _92_323 = (All.pipe_right e infix_prim_op_to_string)
in (let _92_322 = (let _92_321 = (Microsoft_FStar_List.nth args' 1)
in (All.pipe_right _92_321 arg_to_string))
in (Microsoft_FStar_Util.format3 "(%s %s %s)" _92_324 _92_323 _92_322))))
end
| false -> begin
(match (((is_unary_prim_op e) && ((Microsoft_FStar_List.length args') = 1))) with
| true -> begin
(let _92_327 = (All.pipe_right e unary_prim_op_to_string)
in (let _92_326 = (let _92_325 = (Microsoft_FStar_List.nth args' 0)
in (All.pipe_right _92_325 arg_to_string))
in (Microsoft_FStar_Util.format2 "(%s %s)" _92_327 _92_326)))
end
| false -> begin
(let _92_329 = (All.pipe_right e exp_to_string)
in (let _92_328 = (args_to_string args)
in (Microsoft_FStar_Util.format2 "(%s %s)" _92_329 _92_328)))
end)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _92_337 = (All.pipe_right e exp_to_string)
in (let _92_336 = (let _92_335 = (All.pipe_right pats (Microsoft_FStar_List.map (fun _26_588 -> (match (_26_588) with
| (p, wopt, e) -> begin
(let _92_334 = (All.pipe_right p pat_to_string)
in (let _92_333 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _92_331 = (All.pipe_right w exp_to_string)
in (Microsoft_FStar_Util.format1 "when %s" _92_331))
end)
in (let _92_332 = (All.pipe_right e exp_to_string)
in (Microsoft_FStar_Util.format3 "%s %s -> %s" _92_334 _92_333 _92_332))))
end))))
in (Microsoft_FStar_Util.concat_l "\n\t" _92_335))
in (Microsoft_FStar_Util.format2 "(match %s with %s)" _92_337 _92_336)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed (e, t, _26_595) -> begin
(let _92_339 = (All.pipe_right e exp_to_string)
in (let _92_338 = (All.pipe_right t typ_to_string)
in (Microsoft_FStar_Util.format2 "(%s:%s)" _92_339 _92_338)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(let _92_341 = (lbs_to_string lbs)
in (let _92_340 = (All.pipe_right e exp_to_string)
in (Microsoft_FStar_Util.format2 "%s in %s" _92_341 _92_340)))
end))
and uvar_e_to_string = (fun _26_605 -> (match (_26_605) with
| (uv, _26_604) -> begin
(let _92_344 = (match ((ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _92_343 = (Microsoft_FStar_Unionfind.uvar_id uv)
in (Microsoft_FStar_Util.string_of_int _92_343))
end)
in (Prims.strcat "\'e" _92_344))
end))
and lbs_to_string = (fun lbs -> (let _92_351 = (let _92_350 = (All.pipe_right (Prims.snd lbs) (Microsoft_FStar_List.map (fun lb -> (let _92_349 = (lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (let _92_348 = (All.pipe_right lb.Microsoft_FStar_Absyn_Syntax.lbtyp typ_to_string)
in (let _92_347 = (All.pipe_right lb.Microsoft_FStar_Absyn_Syntax.lbdef exp_to_string)
in (Microsoft_FStar_Util.format3 "%s:%s = %s" _92_349 _92_348 _92_347)))))))
in (Microsoft_FStar_Util.concat_l "\n and " _92_350))
in (Microsoft_FStar_Util.format2 "let %s %s" (match ((Prims.fst lbs)) with
| true -> begin
"rec"
end
| false -> begin
""
end) _92_351)))
and lbname_to_string = (fun x -> (match (x) with
| Microsoft_FStar_Util.Inl (bvd) -> begin
(strBvd bvd)
end
| Microsoft_FStar_Util.Inr (lid) -> begin
(sli lid)
end))
and either_to_string = (fun x -> (match (x) with
| Microsoft_FStar_Util.Inl (t) -> begin
(typ_to_string t)
end
| Microsoft_FStar_Util.Inr (e) -> begin
(exp_to_string e)
end))
and either_l_to_string = (fun delim l -> (let _92_356 = (All.pipe_right l (Microsoft_FStar_List.map either_to_string))
in (All.pipe_right _92_356 (Microsoft_FStar_Util.concat_l delim))))
and meta_to_string = (fun x -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (t, _26_623, _26_625) -> begin
(let _92_358 = (typ_to_string t)
in (Microsoft_FStar_Util.format1 "(refresh) %s" _92_358))
end
| Microsoft_FStar_Absyn_Syntax.Meta_labeled (t, l, _26_631, _26_633) -> begin
(let _92_359 = (typ_to_string t)
in (Microsoft_FStar_Util.format2 "(labeled \"%s\") %s" l _92_359))
end
| Microsoft_FStar_Absyn_Syntax.Meta_named (_26_637, l) -> begin
(sli l)
end
| Microsoft_FStar_Absyn_Syntax.Meta_pattern (t, ps) -> begin
(let _92_361 = (args_to_string ps)
in (let _92_360 = (All.pipe_right t typ_to_string)
in (Microsoft_FStar_Util.format2 "{:pattern %s} %s" _92_361 _92_360)))
end
| Microsoft_FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _26_648) -> begin
(let _92_363 = (formula_to_string t1)
in (let _92_362 = (formula_to_string t2)
in (Microsoft_FStar_Util.format2 "%s /\\ %s" _92_363 _92_362)))
end))
and kind_to_string = (fun x -> (match ((let _92_365 = (Microsoft_FStar_Absyn_Util.compress_kind x)
in _92_365.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam (_26_653) -> begin
(All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed (_26_656) -> begin
(All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(uvar_k_to_string' (uv, args))
end
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
"Type"
end
| Microsoft_FStar_Absyn_Syntax.Kind_effect -> begin
"Effect"
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((n, args), k) -> begin
(match ((ST.read Microsoft_FStar_Options.print_real_names)) with
| true -> begin
(kind_to_string k)
end
| false -> begin
(let _92_367 = (sli n)
in (let _92_366 = (args_to_string args)
in (Microsoft_FStar_Util.format2 "%s %s" _92_367 _92_366)))
end)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(let _92_369 = (binders_to_string " -> " binders)
in (let _92_368 = (All.pipe_right k kind_to_string)
in (Microsoft_FStar_Util.format2 "(%s -> %s)" _92_369 _92_368)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun uv -> (let _92_371 = (match ((ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _92_370 = (Microsoft_FStar_Unionfind.uvar_id uv)
in (Microsoft_FStar_Util.string_of_int _92_370))
end)
in (Prims.strcat "\'k_" _92_371)))
and uvar_k_to_string' = (fun _26_678 -> (match (_26_678) with
| (uv, args) -> begin
(let str = (match ((ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _92_373 = (Microsoft_FStar_Unionfind.uvar_id uv)
in (Microsoft_FStar_Util.string_of_int _92_373))
end)
in (let _92_374 = (args_to_string args)
in (Microsoft_FStar_Util.format2 "(\'k_%s %s)" str _92_374)))
end))
and pat_to_string = (fun x -> (match (x.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons (l, _26_683, pats) -> begin
(let _92_379 = (sli l.Microsoft_FStar_Absyn_Syntax.v)
in (let _92_378 = (let _92_377 = (Microsoft_FStar_List.map (fun _26_689 -> (match (_26_689) with
| (x, b) -> begin
(let p = (pat_to_string x)
in (match (b) with
| true -> begin
(Prims.strcat "#" p)
end
| false -> begin
p
end))
end)) pats)
in (All.pipe_right _92_377 (Microsoft_FStar_String.concat " ")))
in (Microsoft_FStar_Util.format2 "(%s %s)" _92_379 _92_378)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term (x, _26_693) -> begin
(let _92_380 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Util.format1 ".%s" _92_380))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (x, _26_698) -> begin
(let _92_381 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Util.format1 ".\'%s" _92_381))
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
(let _92_382 = (Microsoft_FStar_List.map pat_to_string ps)
in (Microsoft_FStar_Util.concat_l " | " _92_382))
end))

let subst_to_string = (fun subst -> (let _92_390 = (let _92_389 = (Microsoft_FStar_List.map (fun _26_17 -> (match (_26_17) with
| Microsoft_FStar_Util.Inl (a, t) -> begin
(let _92_386 = (strBvd a)
in (let _92_385 = (typ_to_string t)
in (Microsoft_FStar_Util.format2 "(%s -> %s)" _92_386 _92_385)))
end
| Microsoft_FStar_Util.Inr (x, e) -> begin
(let _92_388 = (strBvd x)
in (let _92_387 = (exp_to_string e)
in (Microsoft_FStar_Util.format2 "(%s -> %s)" _92_388 _92_387)))
end)) subst)
in (All.pipe_right _92_389 (Microsoft_FStar_String.concat ", ")))
in (All.pipe_left (Microsoft_FStar_Util.format1 "{%s}") _92_390)))

let freevars_to_string = (fun fvs -> (let f = (fun l -> (let _92_396 = (let _92_395 = (All.pipe_right l Microsoft_FStar_Util.set_elements)
in (All.pipe_right _92_395 (Microsoft_FStar_List.map (fun t -> (strBvd t.Microsoft_FStar_Absyn_Syntax.v)))))
in (All.pipe_right _92_396 (Microsoft_FStar_String.concat ", "))))
in (let _92_398 = (f fvs.Microsoft_FStar_Absyn_Syntax.ftvs)
in (let _92_397 = (f fvs.Microsoft_FStar_Absyn_Syntax.fxvs)
in (Microsoft_FStar_Util.format2 "ftvs={%s}, fxvs={%s}" _92_398 _92_397)))))

let qual_to_string = (fun _26_18 -> (match (_26_18) with
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
(let _92_403 = (let _92_402 = (All.pipe_right ids (Microsoft_FStar_List.map (fun lid -> lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)))
in (All.pipe_right _92_402 (Microsoft_FStar_String.concat ", ")))
in (Microsoft_FStar_Util.format1 "record(%s)" _92_403))
end
| _26_744 -> begin
"other"
end))

let quals_to_string = (fun quals -> (let _92_406 = (All.pipe_right quals (Microsoft_FStar_List.map qual_to_string))
in (All.pipe_right _92_406 (Microsoft_FStar_String.concat " "))))

let rec sigelt_to_string = (fun x -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Sig_pragma (Microsoft_FStar_Absyn_Syntax.ResetOptions, _26_749) -> begin
"#reset-options"
end
| Microsoft_FStar_Absyn_Syntax.Sig_pragma (Microsoft_FStar_Absyn_Syntax.SetOptions (s), _26_755) -> begin
(Microsoft_FStar_Util.format1 "#set-options \"%s\"" s)
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _26_762, _26_764, quals, _26_767) -> begin
(let _92_411 = (quals_to_string quals)
in (let _92_410 = (binders_to_string " " tps)
in (let _92_409 = (kind_to_string k)
in (Microsoft_FStar_Util.format4 "%s type %s %s : %s" _92_411 lid.Microsoft_FStar_Absyn_Syntax.str _92_410 _92_409))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, _26_775, _26_777) -> begin
(let _92_414 = (binders_to_string " " tps)
in (let _92_413 = (kind_to_string k)
in (let _92_412 = (typ_to_string t)
in (Microsoft_FStar_Util.format4 "type %s %s : %s = %s" lid.Microsoft_FStar_Absyn_Syntax.str _92_414 _92_413 _92_412))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon (lid, t, _26_783, _26_785, _26_787, _26_789) -> begin
(let _92_415 = (typ_to_string t)
in (Microsoft_FStar_Util.format2 "datacon %s : %s" lid.Microsoft_FStar_Absyn_Syntax.str _92_415))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _26_796) -> begin
(let _92_417 = (quals_to_string quals)
in (let _92_416 = (typ_to_string t)
in (Microsoft_FStar_Util.format3 "%s val %s : %s" _92_417 lid.Microsoft_FStar_Absyn_Syntax.str _92_416)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume (lid, f, _26_802, _26_804) -> begin
(let _92_418 = (typ_to_string f)
in (Microsoft_FStar_Util.format2 "val %s : %s" lid.Microsoft_FStar_Absyn_Syntax.str _92_418))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (lbs, _26_809, _26_811, b) -> begin
(lbs_to_string lbs)
end
| Microsoft_FStar_Absyn_Syntax.Sig_main (e, _26_817) -> begin
(let _92_419 = (exp_to_string e)
in (Microsoft_FStar_Util.format1 "let _ = %s" _92_419))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle (ses, _26_822, _26_824, _26_826) -> begin
(let _92_420 = (Microsoft_FStar_List.map sigelt_to_string ses)
in (All.pipe_right _92_420 (Microsoft_FStar_String.concat "\n")))
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
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (l, tps, c, _26_842, _26_844) -> begin
(let _92_423 = (sli l)
in (let _92_422 = (binders_to_string " " tps)
in (let _92_421 = (comp_typ_to_string c)
in (Microsoft_FStar_Util.format3 "effect %s %s = %s" _92_423 _92_422 _92_421))))
end))

let format_error = (fun r msg -> (let _92_428 = (Microsoft_FStar_Range.string_of_range r)
in (Microsoft_FStar_Util.format2 "%s: %s\n" _92_428 msg)))

let rec sigelt_to_string_short = (fun x -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Sig_let ((_26_851, {Microsoft_FStar_Absyn_Syntax.lbname = Microsoft_FStar_Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _26_855; Microsoft_FStar_Absyn_Syntax.lbdef = _26_853}::[]), _26_863, _26_865, _26_867) -> begin
(let _92_431 = (typ_to_string t)
in (Microsoft_FStar_Util.format2 "let %s : %s" l.Microsoft_FStar_Absyn_Syntax.str _92_431))
end
| _26_871 -> begin
(let _92_434 = (let _92_433 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt x)
in (All.pipe_right _92_433 (Microsoft_FStar_List.map (fun l -> l.Microsoft_FStar_Absyn_Syntax.str))))
in (All.pipe_right _92_434 (Microsoft_FStar_String.concat ", ")))
end))

let rec modul_to_string = (fun m -> (let _92_439 = (sli m.Microsoft_FStar_Absyn_Syntax.name)
in (let _92_438 = (let _92_437 = (Microsoft_FStar_List.map sigelt_to_string m.Microsoft_FStar_Absyn_Syntax.declarations)
in (All.pipe_right _92_437 (Microsoft_FStar_String.concat "\n")))
in (Microsoft_FStar_Util.format2 "module %s\n%s" _92_439 _92_438))))




