
let indent = (FStar_ST.alloc 0)

let skip_let = (FStar_ST.alloc false)

let current_mod = (FStar_ST.alloc "")

let comp_arg_counter = (FStar_ST.alloc 0)

let space = (fun n -> (FStar_Projection_Util.string_make n " "))

let get_ind = (fun _65_20 -> (match (()) with
| () -> begin
(let _134_5 = (FStar_ST.read indent)
in (space _134_5))
end))

let infix_prim_ops = ((FStar_Absyn_Const.op_Addition, "+"))::((FStar_Absyn_Const.op_Subtraction, "-"))::((FStar_Absyn_Const.op_Multiply, "*"))::((FStar_Absyn_Const.op_Division, "/"))::((FStar_Absyn_Const.op_Eq, "="))::((FStar_Absyn_Const.op_ColonEq, ":="))::((FStar_Absyn_Const.op_notEq, "<>"))::((FStar_Absyn_Const.op_And, "&&"))::((FStar_Absyn_Const.op_Or, "||"))::((FStar_Absyn_Const.op_LTE, "<="))::((FStar_Absyn_Const.op_GTE, ">="))::((FStar_Absyn_Const.op_LT, "<"))::((FStar_Absyn_Const.op_GT, ">"))::((FStar_Absyn_Const.op_Modulus, "mod"))::[]

let unary_prim_ops = ((FStar_Absyn_Const.op_Negation, "not"))::((FStar_Absyn_Const.op_Minus, "-"))::[]

let infix_type_ops = ((FStar_Absyn_Const.and_lid, "/\\"))::((FStar_Absyn_Const.or_lid, "\\/"))::((FStar_Absyn_Const.imp_lid, "==>"))::((FStar_Absyn_Const.iff_lid, "<==>"))::((FStar_Absyn_Const.precedes_lid, "<<"))::((FStar_Absyn_Const.eq2_lid, "=="))::((FStar_Absyn_Const.eqT_lid, "=="))::[]

let unary_type_ops = ((FStar_Absyn_Const.not_lid, "~"))::[]

let is_prim_op = (fun ps f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _65_25) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _65_29 -> begin
false
end))

let is_type_op = (fun ps t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Absyn_Syntax.lid_equals ftv.FStar_Absyn_Syntax.v)))
end
| _65_35 -> begin
false
end))

let get_lid = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _65_39) -> begin
fv.FStar_Absyn_Syntax.v
end
| _65_43 -> begin
(FStar_All.failwith "get_lid")
end))

let get_type_lid = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
ftv.FStar_Absyn_Syntax.v
end
| _65_48 -> begin
(FStar_All.failwith "get_type_lid")
end))

let is_infix_prim_op = (fun e -> (is_prim_op (Prims.fst (FStar_List.split infix_prim_ops)) e))

let is_unary_prim_op = (fun e -> (is_prim_op (Prims.fst (FStar_List.split unary_prim_ops)) e))

let is_infix_type_op = (fun t -> (is_type_op (Prims.fst (FStar_List.split infix_type_ops)) t))

let is_unary_type_op = (fun t -> (is_type_op (Prims.fst (FStar_List.split unary_type_ops)) t))

let quants = ((FStar_Absyn_Const.forall_lid, "forall"))::((FStar_Absyn_Const.exists_lid, "exists"))::((FStar_Absyn_Const.allTyp_lid, "forall"))::((FStar_Absyn_Const.exTyp_lid, "exists"))::[]

let is_b2t = (fun t -> (is_type_op ((FStar_Absyn_Const.b2t_lid)::[]) t))

let is_quant = (fun t -> (is_type_op (Prims.fst (FStar_List.split quants)) t))

let is_ite = (fun t -> (is_type_op ((FStar_Absyn_Const.ite_lid)::[]) t))

let is_lex_cons = (fun f -> (is_prim_op ((FStar_Absyn_Const.lexcons_lid)::[]) f))

let is_lex_top = (fun f -> (is_prim_op ((FStar_Absyn_Const.lextop_lid)::[]) f))

let is_inr = (fun _65_1 -> (match (_65_1) with
| FStar_Util.Inl (_65_60) -> begin
false
end
| FStar_Util.Inr (_65_63) -> begin
true
end))

let rec reconstruct_lex = (fun e -> (match ((let _134_33 = (FStar_Absyn_Util.compress_exp e)
in _134_33.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (f, args) -> begin
(let args = (FStar_List.filter (fun a -> (((Prims.snd a) <> Some (FStar_Absyn_Syntax.Implicit)) && (is_inr (Prims.fst a)))) args)
in (let exps = (FStar_List.map (fun _65_2 -> (match (_65_2) with
| (FStar_Util.Inl (_65_74), _65_77) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Util.Inr (x), _65_82) -> begin
x
end)) args)
in (match (((is_lex_cons f) && ((FStar_List.length exps) = 2))) with
| true -> begin
(match ((let _134_36 = (FStar_List.nth exps 1)
in (reconstruct_lex _134_36))) with
| Some (xs) -> begin
(let _134_38 = (let _134_37 = (FStar_List.nth exps 0)
in (_134_37)::xs)
in Some (_134_38))
end
| None -> begin
None
end)
end
| false -> begin
None
end)))
end
| _65_89 -> begin
(match ((is_lex_top e)) with
| true -> begin
Some ([])
end
| false -> begin
None
end)
end))

let arg_is_abs = (fun a -> (match ((not ((is_inr (Prims.fst a))))) with
| true -> begin
false
end
| false -> begin
(match ((let _134_41 = (let _134_40 = (FStar_Util.right (Prims.fst a))
in (FStar_Absyn_Util.compress_exp _134_40))
in _134_41.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_fvar (_65_92) -> begin
false
end
| _65_95 -> begin
true
end)
end))

let rec find = (fun f l -> (match (l) with
| [] -> begin
(FStar_All.failwith "blah")
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

let find_lid = (fun x xs -> (let _134_55 = (find (fun p -> (FStar_Absyn_Syntax.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _134_55)))

let infix_prim_op_to_string = (fun e -> (let _134_57 = (get_lid e)
in (find_lid _134_57 infix_prim_ops)))

let unary_prim_op_to_string = (fun e -> (let _134_59 = (get_lid e)
in (find_lid _134_59 unary_prim_ops)))

let infix_type_op_to_string = (fun t -> (let _134_61 = (get_type_lid t)
in (find_lid _134_61 infix_type_ops)))

let unary_type_op_to_string = (fun t -> (let _134_63 = (get_type_lid t)
in (find_lid _134_63 unary_type_ops)))

let quant_to_string = (fun t -> (let _134_65 = (get_type_lid t)
in (find_lid _134_65 quants)))

let rec sli = (fun l -> (match (((l.FStar_Absyn_Syntax.nsstr = (FStar_ST.read current_mod)) || (l.FStar_Absyn_Syntax.nsstr = "Prims"))) with
| true -> begin
l.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText
end
| false -> begin
l.FStar_Absyn_Syntax.str
end))

let strBvd = (fun bvd -> (match ((FStar_ST.read FStar_Options.print_real_names)) with
| true -> begin
(Prims.strcat bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText bvd.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText)
end
| false -> begin
(match (((FStar_ST.read FStar_Options.hide_genident_nums) && (FStar_Util.starts_with bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText "_"))) with
| true -> begin
(FStar_All.try_with (fun _65_114 -> (match (()) with
| () -> begin
(let _65_120 = (let _134_70 = (FStar_Util.substring_from bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText 1)
in (FStar_Util.int_of_string _134_70))
in "_?")
end)) (fun _65_113 -> (match (_65_113) with
| _65_117 -> begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText
end)))
end
| false -> begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText
end)
end))

let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _65_3 -> (match (_65_3) with
| (_65_125, Some (FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _65_130 -> begin
true
end)))))

let const_to_string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Const_unit -> begin
"()"
end
| FStar_Absyn_Syntax.Const_bool (b) -> begin
(match (b) with
| true -> begin
"true"
end
| false -> begin
"false"
end)
end
| FStar_Absyn_Syntax.Const_int32 (x) -> begin
(FStar_Util.string_of_int32 x)
end
| FStar_Absyn_Syntax.Const_float (x) -> begin
(FStar_Util.string_of_float x)
end
| FStar_Absyn_Syntax.Const_char (x) -> begin
(Prims.strcat (Prims.strcat "\'" (FStar_Util.string_of_char x)) "\'")
end
| FStar_Absyn_Syntax.Const_string (bytes, _65_143) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Absyn_Syntax.Const_bytearray (_65_147) -> begin
"<bytearray>"
end
| FStar_Absyn_Syntax.Const_int (x) -> begin
x
end
| FStar_Absyn_Syntax.Const_int64 (_65_152) -> begin
"<int64>"
end
| FStar_Absyn_Syntax.Const_uint8 (_65_155) -> begin
"<uint8>"
end))

let rec tag_of_typ = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_65_159) -> begin
"Typ_btvar"
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(Prims.strcat "Typ_const " v.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str)
end
| FStar_Absyn_Syntax.Typ_fun (_65_164) -> begin
"Typ_fun"
end
| FStar_Absyn_Syntax.Typ_refine (_65_167) -> begin
"Typ_refine"
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let _134_111 = (tag_of_typ head)
in (let _134_110 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.format2 "Typ_app(%s, [%s args])" _134_111 _134_110)))
end
| FStar_Absyn_Syntax.Typ_lam (_65_174) -> begin
"Typ_lam"
end
| FStar_Absyn_Syntax.Typ_ascribed (_65_177) -> begin
"Typ_ascribed"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_65_180)) -> begin
"Typ_meta_pattern"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_65_184)) -> begin
"Typ_meta_named"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_65_188)) -> begin
"Typ_meta_labeled"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_65_192)) -> begin
"Typ_meta_refresh_label"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_65_196)) -> begin
"Typ_meta_slack_formula"
end
| FStar_Absyn_Syntax.Typ_uvar (_65_200) -> begin
"Typ_uvar"
end
| FStar_Absyn_Syntax.Typ_delayed (_65_203) -> begin
"Typ_delayed"
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"Typ_unknown"
end))
and tag_of_exp = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_65_208) -> begin
"Exp_bvar"
end
| FStar_Absyn_Syntax.Exp_fvar (_65_211) -> begin
"Exp_fvar"
end
| FStar_Absyn_Syntax.Exp_constant (_65_214) -> begin
"Exp_constant"
end
| FStar_Absyn_Syntax.Exp_abs (_65_217) -> begin
"Exp_abs"
end
| FStar_Absyn_Syntax.Exp_app (_65_220) -> begin
"Exp_app"
end
| FStar_Absyn_Syntax.Exp_match (_65_223) -> begin
"Exp_match"
end
| FStar_Absyn_Syntax.Exp_ascribed (_65_226) -> begin
"Exp_ascribed"
end
| FStar_Absyn_Syntax.Exp_let (_65_229) -> begin
"Exp_let"
end
| FStar_Absyn_Syntax.Exp_uvar (_65_232) -> begin
"Exp_uvar"
end
| FStar_Absyn_Syntax.Exp_delayed (_65_235) -> begin
"Exp_delayed"
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_65_238, m)) -> begin
(let _134_115 = (meta_e_to_string m)
in (Prims.strcat "Exp_meta_desugared " _134_115))
end))
and meta_e_to_string = (fun _65_4 -> (match (_65_4) with
| FStar_Absyn_Syntax.Data_app -> begin
"Data_app"
end
| FStar_Absyn_Syntax.Sequence -> begin
"Sequence"
end
| FStar_Absyn_Syntax.Primop -> begin
"Primop"
end
| FStar_Absyn_Syntax.MaskedEffect -> begin
"MaskedEffect"
end))
and typ_to_string = (fun x -> (let x = (FStar_Absyn_Util.compress_typ x)
in (match (x.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_65_251) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_65_254, l)) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Typ_meta (meta) -> begin
(FStar_All.pipe_right meta meta_to_string)
end
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(strBvd btv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(sli v.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_fun (binders, c) -> begin
(let _134_122 = (binders_to_string " -> " binders)
in (let _134_121 = (comp_typ_to_string c)
in (FStar_Util.format2 "%s -> %s" _134_122 _134_121)))
end
| FStar_Absyn_Syntax.Typ_refine (xt, f) -> begin
(let _134_125 = (strBvd xt.FStar_Absyn_Syntax.v)
in (let _134_124 = (FStar_All.pipe_right xt.FStar_Absyn_Syntax.sort typ_to_string)
in (let _134_123 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _134_125 _134_124 _134_123))))
end
| FStar_Absyn_Syntax.Typ_app (_65_274, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(let q_to_string = (fun k a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (b::[], t) -> begin
(k (b, t))
end
| _65_294 -> begin
(let _134_136 = (tag_of_typ t)
in (let _134_135 = (typ_to_string t)
in (FStar_Util.format2 "<Expected a type-lambda! got %s>%s" _134_136 _134_135)))
end))
end
| FStar_Util.Inr (e) -> begin
(let _134_137 = (exp_to_string e)
in (FStar_Util.format1 "(<Expected a type!>%s)" _134_137))
end))
in (let qbinder_to_string = (q_to_string (fun x -> (binder_to_string (Prims.fst x))))
in (let qbody_to_string = (q_to_string (fun x -> (typ_to_string (Prims.snd x))))
in (let args' = (match (((FStar_ST.read FStar_Options.print_implicits) && (not ((is_quant t))))) with
| true -> begin
args
end
| false -> begin
(FStar_List.filter (fun _65_5 -> (match (_65_5) with
| (_65_303, Some (FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _65_308 -> begin
true
end)) args)
end)
in (match (((is_ite t) && ((FStar_List.length args) = 3))) with
| true -> begin
(let _134_148 = (let _134_143 = (FStar_List.nth args 0)
in (arg_to_string _134_143))
in (let _134_147 = (let _134_144 = (FStar_List.nth args 1)
in (arg_to_string _134_144))
in (let _134_146 = (let _134_145 = (FStar_List.nth args 2)
in (arg_to_string _134_145))
in (FStar_Util.format3 "if %s then %s else %s" _134_148 _134_147 _134_146))))
end
| false -> begin
(match (((is_b2t t) && ((FStar_List.length args) = 1))) with
| true -> begin
(let _134_149 = (FStar_List.nth args 0)
in (FStar_All.pipe_right _134_149 arg_to_string))
end
| false -> begin
(match (((is_quant t) && ((FStar_List.length args) <= 2))) with
| true -> begin
(let _134_154 = (quant_to_string t)
in (let _134_153 = (let _134_150 = (FStar_List.nth args' 0)
in (qbinder_to_string _134_150))
in (let _134_152 = (let _134_151 = (FStar_List.nth args' 0)
in (qbody_to_string _134_151))
in (FStar_Util.format3 "(%s (%s). %s)" _134_154 _134_153 _134_152))))
end
| false -> begin
(match (((is_infix_type_op t) && ((FStar_List.length args') = 2))) with
| true -> begin
(let _134_159 = (let _134_155 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _134_155 arg_to_string))
in (let _134_158 = (FStar_All.pipe_right t infix_type_op_to_string)
in (let _134_157 = (let _134_156 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _134_156 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _134_159 _134_158 _134_157))))
end
| false -> begin
(match (((is_unary_type_op t) && ((FStar_List.length args') = 1))) with
| true -> begin
(let _134_162 = (FStar_All.pipe_right t unary_type_op_to_string)
in (let _134_161 = (let _134_160 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _134_160 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _134_162 _134_161)))
end
| false -> begin
(let _134_164 = (FStar_All.pipe_right t typ_to_string)
in (let _134_163 = (FStar_All.pipe_right args args_to_string)
in (FStar_Util.format2 "(%s %s)" _134_164 _134_163)))
end)
end)
end)
end)
end)))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(let _134_166 = (binders_to_string " " binders)
in (let _134_165 = (FStar_All.pipe_right t2 typ_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _134_166 _134_165)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
(match ((FStar_ST.read FStar_Options.print_real_names)) with
| true -> begin
(let _134_168 = (typ_to_string t)
in (let _134_167 = (kind_to_string k)
in (FStar_Util.format2 "(%s <: %s)" _134_168 _134_167)))
end
| false -> begin
(FStar_All.pipe_right t typ_to_string)
end)
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"<UNKNOWN>"
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(match ((FStar_Absyn_Visit.compress_typ_aux false x)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_65_332); FStar_Absyn_Syntax.tk = _65_330; FStar_Absyn_Syntax.pos = _65_328; FStar_Absyn_Syntax.fvs = _65_326; FStar_Absyn_Syntax.uvs = _65_324} -> begin
(uvar_t_to_string (uv, k))
end
| t -> begin
(FStar_All.pipe_right t typ_to_string)
end)
end)))
and uvar_t_to_string = (fun _65_338 -> (match (_65_338) with
| (uv, k) -> begin
(match ((false && (FStar_ST.read FStar_Options.print_real_names))) with
| true -> begin
(let _134_172 = (match ((FStar_ST.read FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _134_170 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _134_170))
end)
in (let _134_171 = (kind_to_string k)
in (FStar_Util.format2 "(U%s : %s)" _134_172 _134_171)))
end
| false -> begin
(let _134_174 = (match ((FStar_ST.read FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _134_173 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _134_173))
end)
in (FStar_Util.format1 "U%s" _134_174))
end)
end))
and imp_to_string = (fun s _65_6 -> (match (_65_6) with
| Some (FStar_Absyn_Syntax.Implicit) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Absyn_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _65_346 -> begin
s
end))
and binder_to_string' = (fun is_arrow b -> (match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(match (((FStar_Absyn_Syntax.is_null_binder b) || ((let _134_179 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _134_179 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp a.FStar_Absyn_Syntax.v)))) with
| true -> begin
(kind_to_string a.FStar_Absyn_Syntax.sort)
end
| false -> begin
(match (((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits))))) with
| true -> begin
(let _134_180 = (strBvd a.FStar_Absyn_Syntax.v)
in (imp_to_string _134_180 imp))
end
| false -> begin
(let _134_184 = (let _134_183 = (let _134_181 = (strBvd a.FStar_Absyn_Syntax.v)
in (Prims.strcat _134_181 ":"))
in (let _134_182 = (kind_to_string a.FStar_Absyn_Syntax.sort)
in (Prims.strcat _134_183 _134_182)))
in (imp_to_string _134_184 imp))
end)
end)
end
| (FStar_Util.Inr (x), imp) -> begin
(match (((FStar_Absyn_Syntax.is_null_binder b) || ((let _134_185 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _134_185 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp x.FStar_Absyn_Syntax.v)))) with
| true -> begin
(typ_to_string x.FStar_Absyn_Syntax.sort)
end
| false -> begin
(match (((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits))))) with
| true -> begin
(let _134_186 = (strBvd x.FStar_Absyn_Syntax.v)
in (imp_to_string _134_186 imp))
end
| false -> begin
(let _134_190 = (let _134_189 = (let _134_187 = (strBvd x.FStar_Absyn_Syntax.v)
in (Prims.strcat _134_187 ":"))
in (let _134_188 = (typ_to_string x.FStar_Absyn_Syntax.sort)
in (Prims.strcat _134_189 _134_188)))
in (imp_to_string _134_190 imp))
end)
end)
end))
and binder_to_string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string = (fun b -> (binder_to_string' true b))
and binders_to_string = (fun sep bs -> (let bs = (match ((FStar_ST.read FStar_Options.print_implicits)) with
| true -> begin
bs
end
| false -> begin
(filter_imp bs)
end)
in (match ((sep = " -> ")) with
| true -> begin
(let _134_195 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _134_195 (FStar_String.concat sep)))
end
| false -> begin
(let _134_196 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _134_196 (FStar_String.concat sep)))
end)))
and arg_to_string = (fun _65_7 -> (match (_65_7) with
| (FStar_Util.Inl (a), imp) -> begin
(let _134_198 = (typ_to_string a)
in (imp_to_string _134_198 imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _134_199 = (exp_to_string x)
in (imp_to_string _134_199 imp))
end))
and args_to_string = (fun args -> (let args = (match ((FStar_ST.read FStar_Options.print_implicits)) with
| true -> begin
args
end
| false -> begin
(filter_imp args)
end)
in (let _134_201 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _134_201 (FStar_String.concat " ")))))
and lcomp_typ_to_string = (fun lc -> (let _134_204 = (sli lc.FStar_Absyn_Syntax.eff_name)
in (let _134_203 = (typ_to_string lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _134_204 _134_203))))
and comp_typ_to_string = (fun c -> (let _65_375 = (FStar_ST.op_Colon_Equals comp_arg_counter 0)
in (let ind = (get_ind ())
in (let _65_378 = (let _134_206 = ((FStar_ST.read indent) + 2)
in (FStar_ST.op_Colon_Equals indent _134_206))
in (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _134_207 = (typ_to_string t)
in (FStar_Util.format1 "Tot (%s)" _134_207))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(let basic = (match (((FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _65_8 -> (match (_65_8) with
| FStar_Absyn_Syntax.TOTAL -> begin
true
end
| _65_387 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args))))) with
| true -> begin
(let _134_209 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _134_209))
end
| false -> begin
(let _134_217 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _134_216 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (let _134_215 = (get_ind ())
in (let _134_214 = (let _134_213 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.effect_args (FStar_List.map effect_arg_to_string))
in (let _134_212 = (let _134_211 = (let _134_210 = (get_ind ())
in (Prims.strcat "\n" _134_210))
in (FStar_String.concat _134_211))
in (FStar_All.pipe_right _134_213 _134_212)))
in (FStar_Util.format4 "%s (%s)\n%s%s" _134_217 _134_216 _134_215 _134_214)))))
end)
in (let dec = (let _134_221 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.collect (fun _65_9 -> (match (_65_9) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _134_220 = (let _134_219 = (exp_to_string e)
in (FStar_Util.format1 " (decreases %s)" _134_219))
in (_134_220)::[])
end
| _65_393 -> begin
[]
end))))
in (FStar_All.pipe_right _134_221 (FStar_String.concat " ")))
in (let _65_395 = (FStar_ST.op_Colon_Equals indent (FStar_String.length ind))
in (FStar_Util.format2 "%s%s" basic dec))))
end)))))
and effect_arg_to_string = (fun e -> (match (e) with
| (FStar_Util.Inr (e), _65_401) -> begin
(exp_to_string e)
end
| (FStar_Util.Inl (wp), _65_406) -> begin
(let r = (let _134_224 = (match ((FStar_ST.read comp_arg_counter)) with
| 0 -> begin
"requires"
end
| 1 -> begin
"ensures "
end
| _65_411 -> begin
"unexpected"
end)
in (let _134_223 = (formula_to_string wp)
in (FStar_Util.format2 "(%s %s)" _134_224 _134_223)))
in (let _65_413 = (let _134_225 = ((FStar_ST.read comp_arg_counter) + 1)
in (FStar_ST.op_Colon_Equals comp_arg_counter _134_225))
in r))
end))
and formula_to_string = (fun phi -> (typ_to_string phi))
and formula_to_string_old_now_unused = (fun phi -> (let const_op = (fun f _65_419 -> f)
in (let un_op = (fun f _65_10 -> (match (_65_10) with
| (FStar_Util.Inl (t), _65_427)::[] -> begin
(let _134_236 = (formula_to_string t)
in (FStar_Util.format2 "%s %s" f _134_236))
end
| _65_431 -> begin
(FStar_All.failwith "impos")
end))
in (let bin_top = (fun f _65_11 -> (match (_65_11) with
| (FStar_Util.Inl (t1), _65_443)::(FStar_Util.Inl (t2), _65_438)::[] -> begin
(let _134_242 = (formula_to_string t1)
in (let _134_241 = (formula_to_string t2)
in (FStar_Util.format3 "%s %s %s" _134_242 f _134_241)))
end
| _65_447 -> begin
(FStar_All.failwith "Impos")
end))
in (let bin_eop = (fun f _65_12 -> (match (_65_12) with
| (FStar_Util.Inr (e1), _65_459)::(FStar_Util.Inr (e2), _65_454)::[] -> begin
(let _134_248 = (exp_to_string e1)
in (let _134_247 = (exp_to_string e2)
in (FStar_Util.format3 "%s %s %s" _134_248 f _134_247)))
end
| _65_463 -> begin
(FStar_All.failwith "impos")
end))
in (let ite = (fun _65_13 -> (match (_65_13) with
| (FStar_Util.Inl (t1), _65_478)::(FStar_Util.Inl (t2), _65_473)::(FStar_Util.Inl (t3), _65_468)::[] -> begin
(let _134_253 = (formula_to_string t1)
in (let _134_252 = (formula_to_string t2)
in (let _134_251 = (formula_to_string t3)
in (FStar_Util.format3 "if %s then %s else %s" _134_253 _134_252 _134_251))))
end
| _65_482 -> begin
(FStar_All.failwith "impos")
end))
in (let eq_op = (fun _65_14 -> (match (_65_14) with
| (FStar_Util.Inl (t1), _65_503)::(FStar_Util.Inl (t2), _65_498)::(FStar_Util.Inr (e1), _65_493)::(FStar_Util.Inr (e2), _65_488)::[] -> begin
(match ((FStar_ST.read FStar_Options.print_implicits)) with
| true -> begin
(let _134_259 = (typ_to_string t1)
in (let _134_258 = (typ_to_string t2)
in (let _134_257 = (exp_to_string e1)
in (let _134_256 = (exp_to_string e2)
in (FStar_Util.format4 "Eq2 %s %s %s %s" _134_259 _134_258 _134_257 _134_256)))))
end
| false -> begin
(let _134_261 = (exp_to_string e1)
in (let _134_260 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _134_261 _134_260)))
end)
end
| (FStar_Util.Inr (e1), _65_514)::(FStar_Util.Inr (e2), _65_509)::[] -> begin
(let _134_263 = (exp_to_string e1)
in (let _134_262 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _134_263 _134_262)))
end
| _65_518 -> begin
(FStar_All.failwith "Impossible")
end))
in (let connectives = ((FStar_Absyn_Const.and_lid, (bin_top "/\\")))::((FStar_Absyn_Const.or_lid, (bin_top "\\/")))::((FStar_Absyn_Const.imp_lid, (bin_top "==>")))::((FStar_Absyn_Const.iff_lid, (bin_top "<==>")))::((FStar_Absyn_Const.ite_lid, ite))::((FStar_Absyn_Const.not_lid, (un_op "~")))::((FStar_Absyn_Const.eqT_lid, (bin_top "==")))::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op "True")))::((FStar_Absyn_Const.false_lid, (const_op "False")))::[]
in (let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (binders, phi) -> begin
(let _134_302 = (binders_to_string " " binders)
in (let _134_301 = (formula_to_string phi)
in (FStar_Util.format2 "(fun %s => %s)" _134_302 _134_301)))
end
| _65_528 -> begin
(typ_to_string phi)
end))
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _65_538 -> (match (_65_538) with
| (l, _65_537) -> begin
(FStar_Absyn_Syntax.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_65_541, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, _65_547, body)) -> begin
(let _134_320 = (binders_to_string " " vars)
in (let _134_319 = (formula_to_string body)
in (FStar_Util.format2 "(forall %s. %s)" _134_320 _134_319)))
end
| Some (FStar_Absyn_Util.QEx (vars, _65_554, body)) -> begin
(let _134_322 = (binders_to_string " " vars)
in (let _134_321 = (formula_to_string body)
in (FStar_Util.format2 "(exists %s. %s)" _134_322 _134_321)))
end))))))))))
and exp_to_string = (fun x -> (let ind = (get_ind ())
in (let res = (match ((let _134_324 = (FStar_Absyn_Util.compress_exp x)
in _134_324.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_delayed (_65_562) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _65_566)) -> begin
(exp_to_string e)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(uvar_e_to_string (uv, t))
end
| FStar_Absyn_Syntax.Exp_bvar (bvv) -> begin
(strBvd bvv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_fvar (fv, _65_578) -> begin
(sli fv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(FStar_All.pipe_right c const_to_string)
end
| FStar_Absyn_Syntax.Exp_abs (binders, e) -> begin
(let _65_587 = (let _134_325 = ((FStar_ST.read indent) + 2)
in (FStar_ST.op_Colon_Equals indent _134_325))
in (match ((filter_imp binders)) with
| [] -> begin
(exp_to_string e)
end
| _65_591 -> begin
(let _134_330 = (let _134_327 = (let _134_326 = (get_ind ())
in (Prims.strcat "(fun %s ->\n" _134_326))
in (Prims.strcat _134_327 "%s)"))
in (let _134_329 = (binders_to_string " " binders)
in (let _134_328 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 _134_330 _134_329 _134_328))))
end))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(let lex = (match ((FStar_ST.read FStar_Options.print_implicits)) with
| true -> begin
None
end
| false -> begin
(reconstruct_lex x)
end)
in (match (lex) with
| Some (es) -> begin
(let _134_333 = (let _134_332 = (let _134_331 = (FStar_List.map exp_to_string es)
in (FStar_String.concat "; " _134_331))
in (Prims.strcat "%[" _134_332))
in (Prims.strcat _134_333 "]"))
end
| None -> begin
(let args' = (let _134_335 = (filter_imp args)
in (FStar_All.pipe_right _134_335 (FStar_List.filter (fun _65_15 -> (match (_65_15) with
| (FStar_Util.Inr (_65_602), _65_605) -> begin
true
end
| _65_608 -> begin
false
end)))))
in (match (((is_infix_prim_op e) && ((FStar_List.length args') = 2))) with
| true -> begin
(let _134_340 = (let _134_336 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _134_336 arg_to_string))
in (let _134_339 = (FStar_All.pipe_right e infix_prim_op_to_string)
in (let _134_338 = (let _134_337 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _134_337 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _134_340 _134_339 _134_338))))
end
| false -> begin
(match (((is_unary_prim_op e) && ((FStar_List.length args') = 1))) with
| true -> begin
(let _134_343 = (FStar_All.pipe_right e unary_prim_op_to_string)
in (let _134_342 = (let _134_341 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _134_341 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _134_343 _134_342)))
end
| false -> begin
(let _65_610 = (let _134_344 = ((FStar_ST.read indent) + 2)
in (FStar_ST.op_Colon_Equals indent _134_344))
in (let _134_349 = (FStar_All.pipe_right e exp_to_string)
in (let _134_348 = (match ((let _134_345 = (FStar_List.hd args)
in (arg_is_abs _134_345))) with
| true -> begin
(let _134_346 = (get_ind ())
in (Prims.strcat "\n" _134_346))
end
| false -> begin
" "
end)
in (let _134_347 = (args_to_string args)
in (FStar_Util.format3 "(%s%s%s)" _134_349 _134_348 _134_347)))))
end)
end))
end))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _65_616 = (let _134_350 = ((FStar_ST.read indent) + 2)
in (FStar_ST.op_Colon_Equals indent _134_350))
in (let _134_363 = (FStar_All.pipe_right e exp_to_string)
in (let _134_362 = (let _134_361 = (let _134_351 = (get_ind ())
in (Prims.strcat "\n" _134_351))
in (let _134_360 = (let _134_359 = (let _134_352 = (get_ind ())
in (Prims.strcat "\n" _134_352))
in (let _134_358 = (FStar_All.pipe_right pats (FStar_List.map (fun _65_621 -> (match (_65_621) with
| (p, wopt, e) -> begin
(let _134_357 = (FStar_All.pipe_right p pat_to_string)
in (let _134_356 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _134_354 = (FStar_All.pipe_right w exp_to_string)
in (FStar_Util.format1 "when %s" _134_354))
end)
in (let _134_355 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format3 "| %s %s -> %s" _134_357 _134_356 _134_355))))
end))))
in (FStar_Util.concat_l _134_359 _134_358)))
in (Prims.strcat _134_361 _134_360)))
in (FStar_Util.format2 "(match %s with %s)" _134_363 _134_362))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _65_628) -> begin
(exp_to_string e)
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(let _134_366 = (let ind' = (FStar_ST.read indent)
in (let _65_636 = (let _134_364 = ((FStar_ST.read indent) + 2)
in (FStar_ST.op_Colon_Equals indent _134_364))
in (let r = (lbs_to_string lbs)
in (let _65_639 = (FStar_ST.op_Colon_Equals indent ind')
in r))))
in (let _134_365 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 (Prims.strcat (Prims.strcat "%s in\n" ind) "%s") _134_366 _134_365)))
end)
in (let _65_642 = (FStar_ST.op_Colon_Equals indent (FStar_String.length ind))
in res))))
and uvar_e_to_string = (fun _65_647 -> (match (_65_647) with
| (uv, _65_646) -> begin
(let _134_369 = (match ((FStar_ST.read FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _134_368 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _134_368))
end)
in (Prims.strcat "\'e" _134_369))
end))
and lbs_to_string = (fun lbs -> (let _134_375 = (let _134_374 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _134_373 = (lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _134_372 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbdef exp_to_string)
in (FStar_Util.format2 "%s = %s" _134_373 _134_372))))))
in (FStar_Util.concat_l "\nand " _134_374))
in (FStar_Util.format2 "let %s%s" (match ((Prims.fst lbs)) with
| true -> begin
"rec "
end
| false -> begin
""
end) _134_375)))
and lbs_to_string_tl = (fun lbs -> (let _65_651 = (let _134_377 = ((FStar_ST.read indent) + 2)
in (FStar_ST.op_Colon_Equals indent _134_377))
in (let _134_382 = (let _134_381 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _134_380 = (lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _134_379 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbdef exp_to_string)
in (FStar_Util.format2 "%s =\n  %s" _134_380 _134_379))))))
in (FStar_Util.concat_l "\nand " _134_381))
in (FStar_Util.format2 "let %s%s" (match ((Prims.fst lbs)) with
| true -> begin
"rec "
end
| false -> begin
""
end) _134_382))))
and lbname_to_string = (fun x -> (match (x) with
| FStar_Util.Inl (bvd) -> begin
(strBvd bvd)
end
| FStar_Util.Inr (lid) -> begin
(sli lid)
end))
and either_to_string = (fun x -> (match (x) with
| FStar_Util.Inl (t) -> begin
(typ_to_string t)
end
| FStar_Util.Inr (e) -> begin
(exp_to_string e)
end))
and either_l_to_string = (fun delim l -> (let _134_387 = (FStar_All.pipe_right l (FStar_List.map either_to_string))
in (FStar_All.pipe_right _134_387 (FStar_Util.concat_l delim))))
and meta_to_string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Meta_refresh_label (t, _65_669, _65_671) -> begin
(let _134_389 = (typ_to_string t)
in (FStar_Util.format1 "(refresh) %s" _134_389))
end
| FStar_Absyn_Syntax.Meta_labeled (t, l, _65_677, _65_679) -> begin
(typ_to_string t)
end
| FStar_Absyn_Syntax.Meta_named (_65_683, l) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Meta_pattern (t, ps) -> begin
(let _134_391 = (args_to_string ps)
in (let _134_390 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "{:pattern %s} %s" _134_391 _134_390)))
end
| FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _65_694) -> begin
(let _134_393 = (formula_to_string t1)
in (let _134_392 = (formula_to_string t2)
in (FStar_Util.format2 "%s /\\ %s" _134_393 _134_392)))
end))
and kind_to_string = (fun x -> (match ((let _134_395 = (FStar_Absyn_Util.compress_kind x)
in _134_395.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_lam (_65_699) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Kind_delayed (_65_702) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(uvar_k_to_string' (uv, args))
end
| FStar_Absyn_Syntax.Kind_type -> begin
"Type"
end
| FStar_Absyn_Syntax.Kind_effect -> begin
"Effect"
end
| FStar_Absyn_Syntax.Kind_abbrev ((n, args), k) -> begin
(match ((FStar_ST.read FStar_Options.print_real_names)) with
| true -> begin
(kind_to_string k)
end
| false -> begin
(let _134_397 = (sli n)
in (let _134_396 = (args_to_string args)
in (FStar_Util.format2 "%s %s" _134_397 _134_396)))
end)
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(let _134_399 = (binders_to_string " -> " binders)
in (let _134_398 = (FStar_All.pipe_right k kind_to_string)
in (FStar_Util.format2 "(%s -> %s)" _134_399 _134_398)))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun uv -> (let _134_401 = (match ((FStar_ST.read FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _134_400 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _134_400))
end)
in (Prims.strcat "\'k_" _134_401)))
and uvar_k_to_string' = (fun _65_724 -> (match (_65_724) with
| (uv, args) -> begin
(let str = (match ((FStar_ST.read FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _134_403 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _134_403))
end)
in (let _134_404 = (args_to_string args)
in (FStar_Util.format2 "(\'k_%s %s)" str _134_404)))
end))
and pat_to_string = (fun x -> (match (x.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (l, _65_729, pats) -> begin
(let _134_409 = (sli l.FStar_Absyn_Syntax.v)
in (let _134_408 = (let _134_407 = (FStar_List.map (fun _65_735 -> (match (_65_735) with
| (x, b) -> begin
(let p = (pat_to_string x)
in (match (b) with
| true -> begin
""
end
| false -> begin
p
end))
end)) pats)
in (FStar_All.pipe_right _134_407 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _134_409 _134_408)))
end
| FStar_Absyn_Syntax.Pat_dot_term (x, _65_739) -> begin
(let _134_410 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".%s" _134_410))
end
| FStar_Absyn_Syntax.Pat_dot_typ (x, _65_744) -> begin
(let _134_411 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".\'%s" _134_411))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(strBvd x.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(strBvd a.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Absyn_Syntax.Pat_wild (_65_754) -> begin
"_"
end
| FStar_Absyn_Syntax.Pat_twild (_65_757) -> begin
"\'_"
end
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(let _134_412 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _134_412))
end))

let subst_to_string = (fun subst -> (let _134_420 = (let _134_419 = (FStar_List.map (fun _65_16 -> (match (_65_16) with
| FStar_Util.Inl (a, t) -> begin
(let _134_416 = (strBvd a)
in (let _134_415 = (typ_to_string t)
in (FStar_Util.format2 "(%s -> %s)" _134_416 _134_415)))
end
| FStar_Util.Inr (x, e) -> begin
(let _134_418 = (strBvd x)
in (let _134_417 = (exp_to_string e)
in (FStar_Util.format2 "(%s -> %s)" _134_418 _134_417)))
end)) subst)
in (FStar_All.pipe_right _134_419 (FStar_String.concat ", ")))
in (FStar_All.pipe_left (FStar_Util.format1 "{%s}") _134_420)))

let freevars_to_string = (fun fvs -> (let f = (fun l -> (let _134_426 = (let _134_425 = (FStar_All.pipe_right l FStar_Util.set_elements)
in (FStar_All.pipe_right _134_425 (FStar_List.map (fun t -> (strBvd t.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _134_426 (FStar_String.concat ", "))))
in (let _134_428 = (f fvs.FStar_Absyn_Syntax.ftvs)
in (let _134_427 = (f fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_Util.format2 "ftvs={%s}, fxvs={%s}" _134_428 _134_427)))))

let is_discriminator_projector = (fun qs -> (FStar_Projection_Util.list_exists (fun _65_17 -> (match (_65_17) with
| FStar_Absyn_Syntax.Discriminator (_65_780) -> begin
true
end
| FStar_Absyn_Syntax.Projector (_65_783) -> begin
(let _65_785 = (FStar_ST.op_Colon_Equals skip_let true)
in true)
end
| _65_788 -> begin
false
end)) qs))

let qual_to_string = (fun _65_18 -> (match (_65_18) with
| FStar_Absyn_Syntax.Logic -> begin
"logic"
end
| FStar_Absyn_Syntax.Assumption -> begin
"assume"
end
| FStar_Absyn_Syntax.Opaque -> begin
"opaque"
end
| FStar_Absyn_Syntax.Discriminator (_65_794) -> begin
"discriminator"
end
| FStar_Absyn_Syntax.Projector (_65_797) -> begin
"projector"
end
| FStar_Absyn_Syntax.RecordType (ids) -> begin
(let _134_436 = (let _134_435 = (FStar_All.pipe_right ids (FStar_List.map (fun lid -> lid.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText)))
in (FStar_All.pipe_right _134_435 (FStar_String.concat ", ")))
in (FStar_Util.format1 "record(%s)" _134_436))
end
| _65_803 -> begin
"other"
end))

let quals_to_string = (fun quals -> (let res = (let _134_439 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _134_439 (FStar_String.concat " ")))
in (match ((res = "")) with
| true -> begin
res
end
| false -> begin
(Prims.strcat res " ")
end)))

let rec sigelt_to_string = (fun x -> (let _65_807 = (FStar_ST.op_Colon_Equals indent 0)
in (match (x) with
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.ResetOptions, _65_811) -> begin
"#reset-options"
end
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.SetOptions (s), _65_817) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _65_824, _65_826, quals, _65_829) -> begin
(let _134_445 = (quals_to_string quals)
in (let _134_444 = (sli lid)
in (let _134_443 = (binders_to_string " " tps)
in (let _134_442 = (kind_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s =" _134_445 _134_444 _134_443 _134_442)))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, _65_837, _65_839) -> begin
(let _134_449 = (sli lid)
in (let _134_448 = (binders_to_string " " tps)
in (let _134_447 = (kind_to_string k)
in (let _134_446 = (typ_to_string t)
in (FStar_Util.format4 "type %s %s : %s = %s" _134_449 _134_448 _134_447 _134_446)))))
end
| FStar_Absyn_Syntax.Sig_datacon (lid, t, _65_845, _65_847, _65_849, _65_851) -> begin
(let _134_451 = (sli lid)
in (let _134_450 = (typ_to_string t)
in (FStar_Util.format2 "| %s : %s" _134_451 _134_450)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _65_858) -> begin
(match ((not ((is_discriminator_projector quals)))) with
| true -> begin
(let _134_454 = (quals_to_string quals)
in (let _134_453 = (sli lid)
in (let _134_452 = (typ_to_string t)
in (FStar_Util.format3 "%sval %s : %s" _134_454 _134_453 _134_452))))
end
| false -> begin
""
end)
end
| FStar_Absyn_Syntax.Sig_assume (lid, f, _65_864, _65_866) -> begin
(let _134_455 = (typ_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Absyn_Syntax.str _134_455))
end
| FStar_Absyn_Syntax.Sig_let (lbs, _65_871, _65_873, b) -> begin
(match ((FStar_ST.read skip_let)) with
| true -> begin
(let _65_877 = (FStar_ST.op_Colon_Equals skip_let false)
in "")
end
| false -> begin
(let _134_456 = (lbs_to_string_tl lbs)
in (FStar_Util.format1 "%s\n" _134_456))
end)
end
| FStar_Absyn_Syntax.Sig_main (e, _65_881) -> begin
(let _134_457 = (exp_to_string e)
in (FStar_Util.format1 "let _ = %s\n" _134_457))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _65_886, _65_888, _65_890) -> begin
(let _134_458 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _134_458 (FStar_String.concat "\n")))
end
| FStar_Absyn_Syntax.Sig_new_effect (_65_894) -> begin
"new_effect { ... }"
end
| FStar_Absyn_Syntax.Sig_sub_effect (_65_897) -> begin
"sub_effect ..."
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_65_900) -> begin
"kind ..."
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, tps, c, _65_906, _65_908) -> begin
(let _134_461 = (sli l)
in (let _134_460 = (binders_to_string " " tps)
in (let _134_459 = (comp_typ_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _134_461 _134_460 _134_459))))
end)))

let format_error = (fun r msg -> (let _134_466 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _134_466 msg)))

let rec sigelt_to_string_short = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_let ((_65_915, {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _65_919; FStar_Absyn_Syntax.lbdef = _65_917}::[]), _65_927, _65_929, _65_931) -> begin
(let _134_469 = (typ_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Absyn_Syntax.str _134_469))
end
| _65_935 -> begin
(let _134_472 = (let _134_471 = (FStar_Absyn_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _134_471 (FStar_List.map (fun l -> l.FStar_Absyn_Syntax.str))))
in (FStar_All.pipe_right _134_472 (FStar_String.concat ", ")))
end))

let rec modul_to_string = (fun m -> (let _65_938 = (FStar_ST.op_Colon_Equals current_mod m.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str)
in (let _134_477 = (sli m.FStar_Absyn_Syntax.name)
in (let _134_476 = (let _134_475 = (FStar_List.map sigelt_to_string m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _134_475 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n\n%s" _134_477 _134_476)))))




