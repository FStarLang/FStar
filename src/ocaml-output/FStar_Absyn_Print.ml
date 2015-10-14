
open Prims
let infix_prim_ops = ((FStar_Absyn_Const.op_Addition, "+"))::((FStar_Absyn_Const.op_Subtraction, "-"))::((FStar_Absyn_Const.op_Multiply, "*"))::((FStar_Absyn_Const.op_Division, "/"))::((FStar_Absyn_Const.op_Eq, "="))::((FStar_Absyn_Const.op_ColonEq, ":="))::((FStar_Absyn_Const.op_notEq, "<>"))::((FStar_Absyn_Const.op_And, "&&"))::((FStar_Absyn_Const.op_Or, "||"))::((FStar_Absyn_Const.op_LTE, "<="))::((FStar_Absyn_Const.op_GTE, ">="))::((FStar_Absyn_Const.op_LT, "<"))::((FStar_Absyn_Const.op_GT, ">"))::((FStar_Absyn_Const.op_Modulus, "mod"))::[]

let unary_prim_ops = ((FStar_Absyn_Const.op_Negation, "not"))::((FStar_Absyn_Const.op_Minus, "-"))::[]

let infix_type_ops = ((FStar_Absyn_Const.and_lid, "/\\"))::((FStar_Absyn_Const.or_lid, "\\/"))::((FStar_Absyn_Const.imp_lid, "==>"))::((FStar_Absyn_Const.iff_lid, "<==>"))::((FStar_Absyn_Const.precedes_lid, "<<"))::((FStar_Absyn_Const.eq2_lid, "=="))::((FStar_Absyn_Const.eqT_lid, "=="))::[]

let unary_type_ops = ((FStar_Absyn_Const.not_lid, "~"))::[]

let is_prim_op = (fun ps f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _27_23) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _27_27 -> begin
false
end))

let is_type_op = (fun ps t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Absyn_Syntax.lid_equals ftv.FStar_Absyn_Syntax.v)))
end
| _27_33 -> begin
false
end))

let get_lid = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _27_37) -> begin
fv.FStar_Absyn_Syntax.v
end
| _27_41 -> begin
(FStar_All.failwith "get_lid")
end))

let get_type_lid = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
ftv.FStar_Absyn_Syntax.v
end
| _27_46 -> begin
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

let is_inr = (fun _27_1 -> (match (_27_1) with
| FStar_Util.Inl (_27_58) -> begin
false
end
| FStar_Util.Inr (_27_61) -> begin
true
end))

let rec reconstruct_lex = (fun e -> (match ((let _92_28 = (FStar_Absyn_Util.compress_exp e)
in _92_28.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (f, args) -> begin
(let args = (FStar_List.filter (fun a -> (((Prims.snd a) <> Some (FStar_Absyn_Syntax.Implicit)) && (is_inr (Prims.fst a)))) args)
in (let exps = (FStar_List.map (fun _27_2 -> (match (_27_2) with
| (FStar_Util.Inl (_27_72), _27_75) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Util.Inr (x), _27_80) -> begin
x
end)) args)
in (match (((is_lex_cons f) && ((FStar_List.length exps) = 2))) with
| true -> begin
(match ((let _92_31 = (FStar_List.nth exps 1)
in (reconstruct_lex _92_31))) with
| Some (xs) -> begin
(let _92_33 = (let _92_32 = (FStar_List.nth exps 0)
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
| _27_87 -> begin
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

let find_lid = (fun x xs -> (let _92_47 = (find (fun p -> (FStar_Absyn_Syntax.lid_equals x (Prims.fst p))) xs)
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

let rec sli = (fun l -> (match ((FStar_ST.read FStar_Options.print_real_names)) with
| true -> begin
l.FStar_Absyn_Syntax.str
end
| false -> begin
l.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText
end))

let strBvd = (fun bvd -> (match ((FStar_ST.read FStar_Options.print_real_names)) with
| true -> begin
(Prims.strcat bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText bvd.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText)
end
| false -> begin
(match (((FStar_ST.read FStar_Options.hide_genident_nums) && (FStar_Util.starts_with bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText "_"))) with
| true -> begin
(FStar_All.try_with (fun _27_106 -> (match (()) with
| () -> begin
(let _27_112 = (let _92_62 = (FStar_Util.substring_from bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText 1)
in (FStar_Util.int_of_string _92_62))
in "_?")
end)) (fun _27_105 -> (match (_27_105) with
| _27_109 -> begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText
end)))
end
| false -> begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText
end)
end))

let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _27_3 -> (match (_27_3) with
| (_27_117, Some (FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _27_122 -> begin
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
| FStar_Absyn_Syntax.Const_string (bytes, _27_135) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Absyn_Syntax.Const_bytearray (_27_139) -> begin
"<bytearray>"
end
| FStar_Absyn_Syntax.Const_int (x) -> begin
x
end
| FStar_Absyn_Syntax.Const_int64 (_27_144) -> begin
"<int64>"
end
| FStar_Absyn_Syntax.Const_uint8 (_27_147) -> begin
"<uint8>"
end))

let rec tag_of_typ = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_27_151) -> begin
"Typ_btvar"
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(Prims.strcat "Typ_const " v.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str)
end
| FStar_Absyn_Syntax.Typ_fun (_27_156) -> begin
"Typ_fun"
end
| FStar_Absyn_Syntax.Typ_refine (_27_159) -> begin
"Typ_refine"
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let _92_102 = (tag_of_typ head)
in (let _92_101 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.format2 "Typ_app(%s, [%s args])" _92_102 _92_101)))
end
| FStar_Absyn_Syntax.Typ_lam (_27_166) -> begin
"Typ_lam"
end
| FStar_Absyn_Syntax.Typ_ascribed (_27_169) -> begin
"Typ_ascribed"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_27_172)) -> begin
"Typ_meta_pattern"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_27_176)) -> begin
"Typ_meta_named"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_27_180)) -> begin
"Typ_meta_labeled"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_27_184)) -> begin
"Typ_meta_refresh_label"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_27_188)) -> begin
"Typ_meta_slack_formula"
end
| FStar_Absyn_Syntax.Typ_uvar (_27_192) -> begin
"Typ_uvar"
end
| FStar_Absyn_Syntax.Typ_delayed (_27_195) -> begin
"Typ_delayed"
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"Typ_unknown"
end))
and tag_of_exp = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_27_200) -> begin
"Exp_bvar"
end
| FStar_Absyn_Syntax.Exp_fvar (_27_203) -> begin
"Exp_fvar"
end
| FStar_Absyn_Syntax.Exp_constant (_27_206) -> begin
"Exp_constant"
end
| FStar_Absyn_Syntax.Exp_abs (_27_209) -> begin
"Exp_abs"
end
| FStar_Absyn_Syntax.Exp_app (_27_212) -> begin
"Exp_app"
end
| FStar_Absyn_Syntax.Exp_match (_27_215) -> begin
"Exp_match"
end
| FStar_Absyn_Syntax.Exp_ascribed (_27_218) -> begin
"Exp_ascribed"
end
| FStar_Absyn_Syntax.Exp_let (_27_221) -> begin
"Exp_let"
end
| FStar_Absyn_Syntax.Exp_uvar (_27_224) -> begin
"Exp_uvar"
end
| FStar_Absyn_Syntax.Exp_delayed (_27_227) -> begin
"Exp_delayed"
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_27_230, m)) -> begin
(let _92_106 = (meta_e_to_string m)
in (Prims.strcat "Exp_meta_desugared " _92_106))
end))
and meta_e_to_string = (fun _27_4 -> (match (_27_4) with
| FStar_Absyn_Syntax.Data_app -> begin
"Data_app"
end
| FStar_Absyn_Syntax.Sequence -> begin
"Sequence"
end
| FStar_Absyn_Syntax.Primop -> begin
"Primop"
end
| FStar_Absyn_Syntax.Masked_effect -> begin
"Masked_effect"
end
| FStar_Absyn_Syntax.Meta_smt_pat -> begin
"Meta_smt_pat"
end))
and typ_to_string = (fun x -> (let x = (FStar_Absyn_Util.compress_typ x)
in (match (x.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_27_244) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_27_247, l)) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Typ_meta (meta) -> begin
(let _92_112 = (FStar_All.pipe_right meta meta_to_string)
in (FStar_Util.format1 "(Meta %s)" _92_112))
end
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(strBvd btv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(sli v.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_fun (binders, c) -> begin
(let _92_114 = (binders_to_string " -> " binders)
in (let _92_113 = (comp_typ_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _92_114 _92_113)))
end
| FStar_Absyn_Syntax.Typ_refine (xt, f) -> begin
(let _92_117 = (strBvd xt.FStar_Absyn_Syntax.v)
in (let _92_116 = (FStar_All.pipe_right xt.FStar_Absyn_Syntax.sort typ_to_string)
in (let _92_115 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "%s:%s{%s}" _92_117 _92_116 _92_115))))
end
| FStar_Absyn_Syntax.Typ_app (_27_267, []) -> begin
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
| _27_287 -> begin
(let _92_128 = (tag_of_typ t)
in (let _92_127 = (typ_to_string t)
in (FStar_Util.format2 "<Expected a type-lambda! got %s>%s" _92_128 _92_127)))
end))
end
| FStar_Util.Inr (e) -> begin
(let _92_129 = (exp_to_string e)
in (FStar_Util.format1 "(<Expected a type!>%s)" _92_129))
end))
in (let qbinder_to_string = (q_to_string (fun x -> (binder_to_string (Prims.fst x))))
in (let qbody_to_string = (q_to_string (fun x -> (typ_to_string (Prims.snd x))))
in (let args' = (match (((FStar_ST.read FStar_Options.print_implicits) && (not ((is_quant t))))) with
| true -> begin
args
end
| false -> begin
(FStar_List.filter (fun _27_5 -> (match (_27_5) with
| (_27_296, Some (FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _27_301 -> begin
true
end)) args)
end)
in (match (((is_ite t) && ((FStar_List.length args) = 3))) with
| true -> begin
(let _92_140 = (let _92_135 = (FStar_List.nth args 0)
in (arg_to_string _92_135))
in (let _92_139 = (let _92_136 = (FStar_List.nth args 1)
in (arg_to_string _92_136))
in (let _92_138 = (let _92_137 = (FStar_List.nth args 2)
in (arg_to_string _92_137))
in (FStar_Util.format3 "if %s then %s else %s" _92_140 _92_139 _92_138))))
end
| false -> begin
(match (((is_b2t t) && ((FStar_List.length args) = 1))) with
| true -> begin
(let _92_141 = (FStar_List.nth args 0)
in (FStar_All.pipe_right _92_141 arg_to_string))
end
| false -> begin
(match (((is_quant t) && ((FStar_List.length args) <= 2))) with
| true -> begin
(let _92_146 = (quant_to_string t)
in (let _92_145 = (let _92_142 = (FStar_List.nth args' 0)
in (qbinder_to_string _92_142))
in (let _92_144 = (let _92_143 = (FStar_List.nth args' 0)
in (qbody_to_string _92_143))
in (FStar_Util.format3 "(%s (%s). %s)" _92_146 _92_145 _92_144))))
end
| false -> begin
(match (((is_infix_type_op t) && ((FStar_List.length args') = 2))) with
| true -> begin
(let _92_151 = (let _92_147 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _92_147 arg_to_string))
in (let _92_150 = (FStar_All.pipe_right t infix_type_op_to_string)
in (let _92_149 = (let _92_148 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _92_148 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _92_151 _92_150 _92_149))))
end
| false -> begin
(match (((is_unary_type_op t) && ((FStar_List.length args') = 1))) with
| true -> begin
(let _92_154 = (FStar_All.pipe_right t unary_type_op_to_string)
in (let _92_153 = (let _92_152 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _92_152 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _92_154 _92_153)))
end
| false -> begin
(let _92_156 = (FStar_All.pipe_right t typ_to_string)
in (let _92_155 = (FStar_All.pipe_right args args_to_string)
in (FStar_Util.format2 "(%s %s)" _92_156 _92_155)))
end)
end)
end)
end)
end)))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(let _92_158 = (binders_to_string " " binders)
in (let _92_157 = (FStar_All.pipe_right t2 typ_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _92_158 _92_157)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
(match ((FStar_ST.read FStar_Options.print_real_names)) with
| true -> begin
(let _92_160 = (typ_to_string t)
in (let _92_159 = (kind_to_string k)
in (FStar_Util.format2 "(%s <: %s)" _92_160 _92_159)))
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
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_27_325); FStar_Absyn_Syntax.tk = _27_323; FStar_Absyn_Syntax.pos = _27_321; FStar_Absyn_Syntax.fvs = _27_319; FStar_Absyn_Syntax.uvs = _27_317} -> begin
(uvar_t_to_string (uv, k))
end
| t -> begin
(FStar_All.pipe_right t typ_to_string)
end)
end)))
and uvar_t_to_string = (fun _27_331 -> (match (_27_331) with
| (uv, k) -> begin
(match ((false && (FStar_ST.read FStar_Options.print_real_names))) with
| true -> begin
(let _92_164 = (match ((FStar_ST.read FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _92_162 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _92_162))
end)
in (let _92_163 = (kind_to_string k)
in (FStar_Util.format2 "(U%s : %s)" _92_164 _92_163)))
end
| false -> begin
(let _92_166 = (match ((FStar_ST.read FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _92_165 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _92_165))
end)
in (FStar_Util.format1 "U%s" _92_166))
end)
end))
and imp_to_string = (fun s _27_6 -> (match (_27_6) with
| Some (FStar_Absyn_Syntax.Implicit) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Absyn_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _27_339 -> begin
s
end))
and binder_to_string' = (fun is_arrow b -> (match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(match (((FStar_Absyn_Syntax.is_null_binder b) || ((let _92_171 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _92_171 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp a.FStar_Absyn_Syntax.v)))) with
| true -> begin
(kind_to_string a.FStar_Absyn_Syntax.sort)
end
| false -> begin
(match (((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits))))) with
| true -> begin
(let _92_172 = (strBvd a.FStar_Absyn_Syntax.v)
in (imp_to_string _92_172 imp))
end
| false -> begin
(let _92_176 = (let _92_175 = (let _92_173 = (strBvd a.FStar_Absyn_Syntax.v)
in (Prims.strcat _92_173 ":"))
in (let _92_174 = (kind_to_string a.FStar_Absyn_Syntax.sort)
in (Prims.strcat _92_175 _92_174)))
in (imp_to_string _92_176 imp))
end)
end)
end
| (FStar_Util.Inr (x), imp) -> begin
(match (((FStar_Absyn_Syntax.is_null_binder b) || ((let _92_177 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _92_177 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp x.FStar_Absyn_Syntax.v)))) with
| true -> begin
(typ_to_string x.FStar_Absyn_Syntax.sort)
end
| false -> begin
(match (((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits))))) with
| true -> begin
(let _92_178 = (strBvd x.FStar_Absyn_Syntax.v)
in (imp_to_string _92_178 imp))
end
| false -> begin
(let _92_182 = (let _92_181 = (let _92_179 = (strBvd x.FStar_Absyn_Syntax.v)
in (Prims.strcat _92_179 ":"))
in (let _92_180 = (typ_to_string x.FStar_Absyn_Syntax.sort)
in (Prims.strcat _92_181 _92_180)))
in (imp_to_string _92_182 imp))
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
(let _92_187 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _92_187 (FStar_String.concat sep)))
end
| false -> begin
(let _92_188 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _92_188 (FStar_String.concat sep)))
end)))
and arg_to_string = (fun _27_7 -> (match (_27_7) with
| (FStar_Util.Inl (a), imp) -> begin
(let _92_190 = (typ_to_string a)
in (imp_to_string _92_190 imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _92_191 = (exp_to_string x)
in (imp_to_string _92_191 imp))
end))
and args_to_string = (fun args -> (let args = (match ((FStar_ST.read FStar_Options.print_implicits)) with
| true -> begin
args
end
| false -> begin
(filter_imp args)
end)
in (let _92_193 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _92_193 (FStar_String.concat " ")))))
and lcomp_typ_to_string = (fun lc -> (let _92_196 = (sli lc.FStar_Absyn_Syntax.eff_name)
in (let _92_195 = (typ_to_string lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _92_196 _92_195))))
and comp_typ_to_string = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _92_198 = (typ_to_string t)
in (FStar_Util.format1 "Tot %s" _92_198))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(let basic = (match (((FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _27_8 -> (match (_27_8) with
| FStar_Absyn_Syntax.TOTAL -> begin
true
end
| _27_375 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args))))) with
| true -> begin
(let _92_200 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _92_200))
end
| false -> begin
(match (((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_Absyn_Syntax.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid))) with
| true -> begin
(typ_to_string c.FStar_Absyn_Syntax.result_typ)
end
| false -> begin
(match (((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _27_9 -> (match (_27_9) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _27_379 -> begin
false
end)))))) with
| true -> begin
(let _92_202 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _92_202))
end
| false -> begin
(match ((FStar_ST.read FStar_Options.print_effect_args)) with
| true -> begin
(let _92_206 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _92_205 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (let _92_204 = (let _92_203 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.effect_args (FStar_List.map effect_arg_to_string))
in (FStar_All.pipe_right _92_203 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _92_206 _92_205 _92_204))))
end
| false -> begin
(let _92_208 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _92_207 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _92_208 _92_207)))
end)
end)
end)
end)
in (let dec = (let _92_212 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.collect (fun _27_10 -> (match (_27_10) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _92_211 = (let _92_210 = (exp_to_string e)
in (FStar_Util.format1 " (decreases %s)" _92_210))
in (_92_211)::[])
end
| _27_385 -> begin
[]
end))))
in (FStar_All.pipe_right _92_212 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and effect_arg_to_string = (fun e -> (match (e) with
| (FStar_Util.Inr (e), _27_391) -> begin
(exp_to_string e)
end
| (FStar_Util.Inl (wp), _27_396) -> begin
(formula_to_string wp)
end))
and formula_to_string = (fun phi -> (typ_to_string phi))
and formula_to_string_old_now_unused = (fun phi -> (let const_op = (fun f _27_402 -> f)
in (let un_op = (fun f _27_11 -> (match (_27_11) with
| (FStar_Util.Inl (t), _27_410)::[] -> begin
(let _92_224 = (formula_to_string t)
in (FStar_Util.format2 "%s %s" f _92_224))
end
| _27_414 -> begin
(FStar_All.failwith "impos")
end))
in (let bin_top = (fun f _27_12 -> (match (_27_12) with
| (FStar_Util.Inl (t1), _27_426)::(FStar_Util.Inl (t2), _27_421)::[] -> begin
(let _92_230 = (formula_to_string t1)
in (let _92_229 = (formula_to_string t2)
in (FStar_Util.format3 "%s %s %s" _92_230 f _92_229)))
end
| _27_430 -> begin
(FStar_All.failwith "Impos")
end))
in (let bin_eop = (fun f _27_13 -> (match (_27_13) with
| (FStar_Util.Inr (e1), _27_442)::(FStar_Util.Inr (e2), _27_437)::[] -> begin
(let _92_236 = (exp_to_string e1)
in (let _92_235 = (exp_to_string e2)
in (FStar_Util.format3 "%s %s %s" _92_236 f _92_235)))
end
| _27_446 -> begin
(FStar_All.failwith "impos")
end))
in (let ite = (fun _27_14 -> (match (_27_14) with
| (FStar_Util.Inl (t1), _27_461)::(FStar_Util.Inl (t2), _27_456)::(FStar_Util.Inl (t3), _27_451)::[] -> begin
(let _92_241 = (formula_to_string t1)
in (let _92_240 = (formula_to_string t2)
in (let _92_239 = (formula_to_string t3)
in (FStar_Util.format3 "if %s then %s else %s" _92_241 _92_240 _92_239))))
end
| _27_465 -> begin
(FStar_All.failwith "impos")
end))
in (let eq_op = (fun _27_15 -> (match (_27_15) with
| (FStar_Util.Inl (t1), _27_486)::(FStar_Util.Inl (t2), _27_481)::(FStar_Util.Inr (e1), _27_476)::(FStar_Util.Inr (e2), _27_471)::[] -> begin
(match ((FStar_ST.read FStar_Options.print_implicits)) with
| true -> begin
(let _92_247 = (typ_to_string t1)
in (let _92_246 = (typ_to_string t2)
in (let _92_245 = (exp_to_string e1)
in (let _92_244 = (exp_to_string e2)
in (FStar_Util.format4 "Eq2 %s %s %s %s" _92_247 _92_246 _92_245 _92_244)))))
end
| false -> begin
(let _92_249 = (exp_to_string e1)
in (let _92_248 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _92_249 _92_248)))
end)
end
| (FStar_Util.Inr (e1), _27_497)::(FStar_Util.Inr (e2), _27_492)::[] -> begin
(let _92_251 = (exp_to_string e1)
in (let _92_250 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _92_251 _92_250)))
end
| _27_501 -> begin
(FStar_All.failwith "Impossible")
end))
in (let connectives = ((FStar_Absyn_Const.and_lid, (bin_top "/\\")))::((FStar_Absyn_Const.or_lid, (bin_top "\\/")))::((FStar_Absyn_Const.imp_lid, (bin_top "==>")))::((FStar_Absyn_Const.iff_lid, (bin_top "<==>")))::((FStar_Absyn_Const.ite_lid, ite))::((FStar_Absyn_Const.not_lid, (un_op "~")))::((FStar_Absyn_Const.eqT_lid, (bin_top "==")))::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op "True")))::((FStar_Absyn_Const.false_lid, (const_op "False")))::[]
in (let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (binders, phi) -> begin
(let _92_290 = (binders_to_string " " binders)
in (let _92_289 = (formula_to_string phi)
in (FStar_Util.format2 "(fun %s => %s)" _92_290 _92_289)))
end
| _27_511 -> begin
(typ_to_string phi)
end))
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _27_521 -> (match (_27_521) with
| (l, _27_520) -> begin
(FStar_Absyn_Syntax.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_27_524, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, _27_530, body)) -> begin
(let _92_308 = (binders_to_string " " vars)
in (let _92_307 = (formula_to_string body)
in (FStar_Util.format2 "(forall %s. %s)" _92_308 _92_307)))
end
| Some (FStar_Absyn_Util.QEx (vars, _27_537, body)) -> begin
(let _92_310 = (binders_to_string " " vars)
in (let _92_309 = (formula_to_string body)
in (FStar_Util.format2 "(exists %s. %s)" _92_310 _92_309)))
end))))))))))
and exp_to_string = (fun x -> (match ((let _92_312 = (FStar_Absyn_Util.compress_exp x)
in _92_312.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_delayed (_27_544) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _27_548)) -> begin
(exp_to_string e)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(uvar_e_to_string (uv, t))
end
| FStar_Absyn_Syntax.Exp_bvar (bvv) -> begin
(strBvd bvv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_fvar (fv, _27_560) -> begin
(sli fv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(FStar_All.pipe_right c const_to_string)
end
| FStar_Absyn_Syntax.Exp_abs (binders, e) -> begin
(let _92_314 = (binders_to_string " " binders)
in (let _92_313 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _92_314 _92_313)))
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
(let _92_317 = (let _92_316 = (let _92_315 = (FStar_List.map exp_to_string es)
in (FStar_String.concat "; " _92_315))
in (Prims.strcat "%[" _92_316))
in (Prims.strcat _92_317 "]"))
end
| None -> begin
(let args' = (let _92_319 = (filter_imp args)
in (FStar_All.pipe_right _92_319 (FStar_List.filter (fun _27_16 -> (match (_27_16) with
| (FStar_Util.Inr (_27_579), _27_582) -> begin
true
end
| _27_585 -> begin
false
end)))))
in (match (((is_infix_prim_op e) && ((FStar_List.length args') = 2))) with
| true -> begin
(let _92_324 = (let _92_320 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _92_320 arg_to_string))
in (let _92_323 = (FStar_All.pipe_right e infix_prim_op_to_string)
in (let _92_322 = (let _92_321 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _92_321 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _92_324 _92_323 _92_322))))
end
| false -> begin
(match (((is_unary_prim_op e) && ((FStar_List.length args') = 1))) with
| true -> begin
(let _92_327 = (FStar_All.pipe_right e unary_prim_op_to_string)
in (let _92_326 = (let _92_325 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _92_325 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _92_327 _92_326)))
end
| false -> begin
(let _92_329 = (FStar_All.pipe_right e exp_to_string)
in (let _92_328 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _92_329 _92_328)))
end)
end))
end))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _92_337 = (FStar_All.pipe_right e exp_to_string)
in (let _92_336 = (let _92_335 = (FStar_All.pipe_right pats (FStar_List.map (fun _27_594 -> (match (_27_594) with
| (p, wopt, e) -> begin
(let _92_334 = (FStar_All.pipe_right p pat_to_string)
in (let _92_333 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _92_331 = (FStar_All.pipe_right w exp_to_string)
in (FStar_Util.format1 "when %s" _92_331))
end)
in (let _92_332 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format3 "%s %s -> %s" _92_334 _92_333 _92_332))))
end))))
in (FStar_Util.concat_l "\n\t" _92_335))
in (FStar_Util.format2 "(match %s with %s)" _92_337 _92_336)))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _27_601) -> begin
(let _92_339 = (FStar_All.pipe_right e exp_to_string)
in (let _92_338 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "(%s:%s)" _92_339 _92_338)))
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(let _92_341 = (lbs_to_string lbs)
in (let _92_340 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "%s in %s" _92_341 _92_340)))
end))
and uvar_e_to_string = (fun _27_611 -> (match (_27_611) with
| (uv, _27_610) -> begin
(let _92_344 = (match ((FStar_ST.read FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _92_343 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _92_343))
end)
in (Prims.strcat "\'e" _92_344))
end))
and lbs_to_string = (fun lbs -> (let _92_351 = (let _92_350 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _92_349 = (lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _92_348 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbtyp typ_to_string)
in (let _92_347 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbdef exp_to_string)
in (FStar_Util.format3 "%s:%s = %s" _92_349 _92_348 _92_347)))))))
in (FStar_Util.concat_l "\n and " _92_350))
in (FStar_Util.format2 "let %s %s" (match ((Prims.fst lbs)) with
| true -> begin
"rec"
end
| false -> begin
""
end) _92_351)))
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
and either_l_to_string = (fun delim l -> (let _92_356 = (FStar_All.pipe_right l (FStar_List.map either_to_string))
in (FStar_All.pipe_right _92_356 (FStar_Util.concat_l delim))))
and meta_to_string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Meta_refresh_label (t, _27_629, _27_631) -> begin
(let _92_358 = (typ_to_string t)
in (FStar_Util.format1 "(refresh) %s" _92_358))
end
| FStar_Absyn_Syntax.Meta_labeled (t, l, _27_637, _27_639) -> begin
(let _92_359 = (typ_to_string t)
in (FStar_Util.format2 "(labeled \"%s\") %s" l _92_359))
end
| FStar_Absyn_Syntax.Meta_named (_27_643, l) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Meta_pattern (t, ps) -> begin
(let _92_361 = (args_to_string ps)
in (let _92_360 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "{:pattern %s} %s" _92_361 _92_360)))
end
| FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _27_654) -> begin
(let _92_363 = (formula_to_string t1)
in (let _92_362 = (formula_to_string t2)
in (FStar_Util.format2 "%s /\\ %s" _92_363 _92_362)))
end))
and kind_to_string = (fun x -> (match ((let _92_365 = (FStar_Absyn_Util.compress_kind x)
in _92_365.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_lam (_27_659) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Kind_delayed (_27_662) -> begin
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
(let _92_367 = (sli n)
in (let _92_366 = (args_to_string args)
in (FStar_Util.format2 "%s %s" _92_367 _92_366)))
end)
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(let _92_369 = (binders_to_string " -> " binders)
in (let _92_368 = (FStar_All.pipe_right k kind_to_string)
in (FStar_Util.format2 "(%s -> %s)" _92_369 _92_368)))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun uv -> (let _92_371 = (match ((FStar_ST.read FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _92_370 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _92_370))
end)
in (Prims.strcat "\'k_" _92_371)))
and uvar_k_to_string' = (fun _27_684 -> (match (_27_684) with
| (uv, args) -> begin
(let str = (match ((FStar_ST.read FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _92_373 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _92_373))
end)
in (let _92_374 = (args_to_string args)
in (FStar_Util.format2 "(\'k_%s %s)" str _92_374)))
end))
and pat_to_string = (fun x -> (match (x.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (l, _27_689, pats) -> begin
(let _92_379 = (sli l.FStar_Absyn_Syntax.v)
in (let _92_378 = (let _92_377 = (FStar_List.map (fun _27_695 -> (match (_27_695) with
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
in (FStar_All.pipe_right _92_377 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _92_379 _92_378)))
end
| FStar_Absyn_Syntax.Pat_dot_term (x, _27_699) -> begin
(let _92_380 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".%s" _92_380))
end
| FStar_Absyn_Syntax.Pat_dot_typ (x, _27_704) -> begin
(let _92_381 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".\'%s" _92_381))
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
| FStar_Absyn_Syntax.Pat_wild (_27_714) -> begin
"_"
end
| FStar_Absyn_Syntax.Pat_twild (_27_717) -> begin
"\'_"
end
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(let _92_382 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _92_382))
end))

let subst_to_string = (fun subst -> (let _92_390 = (let _92_389 = (FStar_List.map (fun _27_17 -> (match (_27_17) with
| FStar_Util.Inl (a, t) -> begin
(let _92_386 = (strBvd a)
in (let _92_385 = (typ_to_string t)
in (FStar_Util.format2 "(%s -> %s)" _92_386 _92_385)))
end
| FStar_Util.Inr (x, e) -> begin
(let _92_388 = (strBvd x)
in (let _92_387 = (exp_to_string e)
in (FStar_Util.format2 "(%s -> %s)" _92_388 _92_387)))
end)) subst)
in (FStar_All.pipe_right _92_389 (FStar_String.concat ", ")))
in (FStar_All.pipe_left (FStar_Util.format1 "{%s}") _92_390)))

let freevars_to_string = (fun fvs -> (let f = (fun l -> (let _92_396 = (let _92_395 = (FStar_All.pipe_right l FStar_Util.set_elements)
in (FStar_All.pipe_right _92_395 (FStar_List.map (fun t -> (strBvd t.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _92_396 (FStar_String.concat ", "))))
in (let _92_398 = (f fvs.FStar_Absyn_Syntax.ftvs)
in (let _92_397 = (f fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_Util.format2 "ftvs={%s}, fxvs={%s}" _92_398 _92_397)))))

let qual_to_string = (fun _27_18 -> (match (_27_18) with
| FStar_Absyn_Syntax.Logic -> begin
"logic"
end
| FStar_Absyn_Syntax.Opaque -> begin
"opaque"
end
| FStar_Absyn_Syntax.Discriminator (_27_741) -> begin
"discriminator"
end
| FStar_Absyn_Syntax.Projector (_27_744) -> begin
"projector"
end
| FStar_Absyn_Syntax.RecordType (ids) -> begin
(let _92_403 = (let _92_402 = (FStar_All.pipe_right ids (FStar_List.map (fun lid -> lid.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText)))
in (FStar_All.pipe_right _92_402 (FStar_String.concat ", ")))
in (FStar_Util.format1 "record(%s)" _92_403))
end
| _27_750 -> begin
"other"
end))

let quals_to_string = (fun quals -> (let _92_406 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _92_406 (FStar_String.concat " "))))

let rec sigelt_to_string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.ResetOptions, _27_755) -> begin
"#reset-options"
end
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.SetOptions (s), _27_761) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _27_768, _27_770, quals, _27_773) -> begin
(let _92_411 = (quals_to_string quals)
in (let _92_410 = (binders_to_string " " tps)
in (let _92_409 = (kind_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _92_411 lid.FStar_Absyn_Syntax.str _92_410 _92_409))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, _27_781, _27_783) -> begin
(let _92_414 = (binders_to_string " " tps)
in (let _92_413 = (kind_to_string k)
in (let _92_412 = (typ_to_string t)
in (FStar_Util.format4 "type %s %s : %s = %s" lid.FStar_Absyn_Syntax.str _92_414 _92_413 _92_412))))
end
| FStar_Absyn_Syntax.Sig_datacon (lid, t, _27_789, _27_791, _27_793, _27_795) -> begin
(let _92_415 = (typ_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Absyn_Syntax.str _92_415))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _27_802) -> begin
(let _92_417 = (quals_to_string quals)
in (let _92_416 = (typ_to_string t)
in (FStar_Util.format3 "%s val %s : %s" _92_417 lid.FStar_Absyn_Syntax.str _92_416)))
end
| FStar_Absyn_Syntax.Sig_assume (lid, f, _27_808, _27_810) -> begin
(let _92_418 = (typ_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Absyn_Syntax.str _92_418))
end
| FStar_Absyn_Syntax.Sig_let (lbs, _27_815, _27_817, b) -> begin
(lbs_to_string lbs)
end
| FStar_Absyn_Syntax.Sig_main (e, _27_823) -> begin
(let _92_419 = (exp_to_string e)
in (FStar_Util.format1 "let _ = %s" _92_419))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _27_828, _27_830, _27_832) -> begin
(let _92_420 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _92_420 (FStar_String.concat "\n")))
end
| FStar_Absyn_Syntax.Sig_new_effect (_27_836) -> begin
"new_effect { ... }"
end
| FStar_Absyn_Syntax.Sig_sub_effect (_27_839) -> begin
"sub_effect ..."
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_27_842) -> begin
"kind ..."
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, tps, c, _27_848, _27_850) -> begin
(let _92_423 = (sli l)
in (let _92_422 = (binders_to_string " " tps)
in (let _92_421 = (comp_typ_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _92_423 _92_422 _92_421))))
end))

let format_error = (fun r msg -> (let _92_428 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _92_428 msg)))

let rec sigelt_to_string_short = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_let ((_27_857, {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _27_861; FStar_Absyn_Syntax.lbdef = _27_859}::[]), _27_869, _27_871, _27_873) -> begin
(let _92_431 = (typ_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Absyn_Syntax.str _92_431))
end
| _27_877 -> begin
(let _92_434 = (let _92_433 = (FStar_Absyn_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _92_433 (FStar_List.map (fun l -> l.FStar_Absyn_Syntax.str))))
in (FStar_All.pipe_right _92_434 (FStar_String.concat ", ")))
end))

let rec modul_to_string = (fun m -> (let _92_439 = (sli m.FStar_Absyn_Syntax.name)
in (let _92_438 = (let _92_437 = (FStar_List.map sigelt_to_string m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _92_437 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _92_439 _92_438))))
