
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

let rec reconstruct_lex = (fun e -> (match ((let _93_28 = (FStar_Absyn_Util.compress_exp e)
in _93_28.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (f, args) -> begin
(let args = (FStar_List.filter (fun a -> (((Prims.snd a) <> Some (FStar_Absyn_Syntax.Implicit)) && (is_inr (Prims.fst a)))) args)
in (let exps = (FStar_List.map (fun _27_2 -> (match (_27_2) with
| (FStar_Util.Inl (_27_72), _27_75) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Util.Inr (x), _27_80) -> begin
x
end)) args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = 2)) then begin
(match ((let _93_31 = (FStar_List.nth exps 1)
in (reconstruct_lex _93_31))) with
| Some (xs) -> begin
(let _93_33 = (let _93_32 = (FStar_List.nth exps 0)
in (_93_32)::xs)
in Some (_93_33))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _27_87 -> begin
if (is_lex_top e) then begin
Some ([])
end else begin
None
end
end))

let rec find = (fun f l -> (match (l) with
| [] -> begin
(FStar_All.failwith "blah")
end
| hd::tl -> begin
if (f hd) then begin
hd
end else begin
(find f tl)
end
end))

let find_lid = (fun x xs -> (let _93_47 = (find (fun p -> (FStar_Absyn_Syntax.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _93_47)))

let infix_prim_op_to_string = (fun e -> (let _93_49 = (get_lid e)
in (find_lid _93_49 infix_prim_ops)))

let unary_prim_op_to_string = (fun e -> (let _93_51 = (get_lid e)
in (find_lid _93_51 unary_prim_ops)))

let infix_type_op_to_string = (fun t -> (let _93_53 = (get_type_lid t)
in (find_lid _93_53 infix_type_ops)))

let unary_type_op_to_string = (fun t -> (let _93_55 = (get_type_lid t)
in (find_lid _93_55 unary_type_ops)))

let quant_to_string = (fun t -> (let _93_57 = (get_type_lid t)
in (find_lid _93_57 quants)))

let rec sli = (fun l -> if (FStar_ST.read FStar_Options.print_real_names) then begin
l.FStar_Absyn_Syntax.str
end else begin
l.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText
end)

let strBvd = (fun bvd -> if (FStar_ST.read FStar_Options.print_real_names) then begin
(Prims.strcat bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText bvd.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText)
end else begin
if ((FStar_ST.read FStar_Options.hide_genident_nums) && (FStar_Util.starts_with bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText "_")) then begin
(FStar_All.try_with (fun _27_106 -> (match (()) with
| () -> begin
(let _27_112 = (let _93_62 = (FStar_Util.substring_from bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText 1)
in (FStar_Util.int_of_string _93_62))
in "_?")
end)) (fun _27_105 -> (match (_27_105) with
| _27_109 -> begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText
end)))
end else begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText
end
end)

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
if b then begin
"true"
end else begin
"false"
end
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
(let _93_103 = (tag_of_typ head)
in (let _93_102 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.format2 "Typ_app(%s, [%s args])" _93_103 _93_102)))
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
(let _93_107 = (meta_e_to_string m)
in (Prims.strcat "Exp_meta_desugared " _93_107))
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
(let _93_113 = (FStar_All.pipe_right meta meta_to_string)
in (FStar_Util.format1 "(Meta %s)" _93_113))
end
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(strBvd btv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(sli v.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_fun (binders, c) -> begin
(let _93_115 = (binders_to_string " -> " binders)
in (let _93_114 = (comp_typ_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _93_115 _93_114)))
end
| FStar_Absyn_Syntax.Typ_refine (xt, f) -> begin
(let _93_118 = (strBvd xt.FStar_Absyn_Syntax.v)
in (let _93_117 = (FStar_All.pipe_right xt.FStar_Absyn_Syntax.sort typ_to_string)
in (let _93_116 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "%s:%s{%s}" _93_118 _93_117 _93_116))))
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
(let _93_129 = (tag_of_typ t)
in (let _93_128 = (typ_to_string t)
in (FStar_Util.format2 "<Expected a type-lambda! got %s>%s" _93_129 _93_128)))
end))
end
| FStar_Util.Inr (e) -> begin
(let _93_130 = (exp_to_string e)
in (FStar_Util.format1 "(<Expected a type!>%s)" _93_130))
end))
in (let qbinder_to_string = (q_to_string (fun x -> (binder_to_string (Prims.fst x))))
in (let qbody_to_string = (q_to_string (fun x -> (typ_to_string (Prims.snd x))))
in (let args' = if ((FStar_ST.read FStar_Options.print_implicits) && (not ((is_quant t)))) then begin
args
end else begin
(FStar_List.filter (fun _27_5 -> (match (_27_5) with
| (_27_296, Some (FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _27_301 -> begin
true
end)) args)
end
in if ((is_ite t) && ((FStar_List.length args) = 3)) then begin
(let _93_141 = (let _93_136 = (FStar_List.nth args 0)
in (arg_to_string _93_136))
in (let _93_140 = (let _93_137 = (FStar_List.nth args 1)
in (arg_to_string _93_137))
in (let _93_139 = (let _93_138 = (FStar_List.nth args 2)
in (arg_to_string _93_138))
in (FStar_Util.format3 "if %s then %s else %s" _93_141 _93_140 _93_139))))
end else begin
if ((is_b2t t) && ((FStar_List.length args) = 1)) then begin
(let _93_142 = (FStar_List.nth args 0)
in (FStar_All.pipe_right _93_142 arg_to_string))
end else begin
if ((is_quant t) && ((FStar_List.length args) <= 2)) then begin
(let _93_147 = (quant_to_string t)
in (let _93_146 = (let _93_143 = (FStar_List.nth args' 0)
in (qbinder_to_string _93_143))
in (let _93_145 = (let _93_144 = (FStar_List.nth args' 0)
in (qbody_to_string _93_144))
in (FStar_Util.format3 "(%s (%s). %s)" _93_147 _93_146 _93_145))))
end else begin
if ((is_infix_type_op t) && ((FStar_List.length args') = 2)) then begin
(let _93_152 = (let _93_148 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _93_148 arg_to_string))
in (let _93_151 = (FStar_All.pipe_right t infix_type_op_to_string)
in (let _93_150 = (let _93_149 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _93_149 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _93_152 _93_151 _93_150))))
end else begin
if ((is_unary_type_op t) && ((FStar_List.length args') = 1)) then begin
(let _93_155 = (FStar_All.pipe_right t unary_type_op_to_string)
in (let _93_154 = (let _93_153 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _93_153 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _93_155 _93_154)))
end else begin
(let _93_157 = (FStar_All.pipe_right t typ_to_string)
in (let _93_156 = (FStar_All.pipe_right args args_to_string)
in (FStar_Util.format2 "(%s %s)" _93_157 _93_156)))
end
end
end
end
end))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(let _93_159 = (binders_to_string " " binders)
in (let _93_158 = (FStar_All.pipe_right t2 typ_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _93_159 _93_158)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _93_161 = (typ_to_string t)
in (let _93_160 = (kind_to_string k)
in (FStar_Util.format2 "(%s <: %s)" _93_161 _93_160)))
end else begin
(FStar_All.pipe_right t typ_to_string)
end
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
if (false && (FStar_ST.read FStar_Options.print_real_names)) then begin
(let _93_165 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _93_163 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _93_163))
end
in (let _93_164 = (kind_to_string k)
in (FStar_Util.format2 "(U%s : %s)" _93_165 _93_164)))
end else begin
(let _93_167 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _93_166 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _93_166))
end
in (FStar_Util.format1 "U%s" _93_167))
end
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
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _93_172 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _93_172 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp a.FStar_Absyn_Syntax.v))) then begin
(kind_to_string a.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits)))) then begin
(let _93_173 = (strBvd a.FStar_Absyn_Syntax.v)
in (imp_to_string _93_173 imp))
end else begin
(let _93_177 = (let _93_176 = (let _93_174 = (strBvd a.FStar_Absyn_Syntax.v)
in (Prims.strcat _93_174 ":"))
in (let _93_175 = (kind_to_string a.FStar_Absyn_Syntax.sort)
in (Prims.strcat _93_176 _93_175)))
in (imp_to_string _93_177 imp))
end
end
end
| (FStar_Util.Inr (x), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _93_178 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _93_178 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp x.FStar_Absyn_Syntax.v))) then begin
(typ_to_string x.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits)))) then begin
(let _93_179 = (strBvd x.FStar_Absyn_Syntax.v)
in (imp_to_string _93_179 imp))
end else begin
(let _93_183 = (let _93_182 = (let _93_180 = (strBvd x.FStar_Absyn_Syntax.v)
in (Prims.strcat _93_180 ":"))
in (let _93_181 = (typ_to_string x.FStar_Absyn_Syntax.sort)
in (Prims.strcat _93_182 _93_181)))
in (imp_to_string _93_183 imp))
end
end
end))
and binder_to_string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string = (fun b -> (binder_to_string' true b))
and binders_to_string = (fun sep bs -> (let bs = if (FStar_ST.read FStar_Options.print_implicits) then begin
bs
end else begin
(filter_imp bs)
end
in if (sep = " -> ") then begin
(let _93_188 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _93_188 (FStar_String.concat sep)))
end else begin
(let _93_189 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _93_189 (FStar_String.concat sep)))
end))
and arg_to_string = (fun _27_7 -> (match (_27_7) with
| (FStar_Util.Inl (a), imp) -> begin
(let _93_191 = (typ_to_string a)
in (imp_to_string _93_191 imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _93_192 = (exp_to_string x)
in (imp_to_string _93_192 imp))
end))
and args_to_string = (fun args -> (let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _93_194 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _93_194 (FStar_String.concat " ")))))
and lcomp_typ_to_string = (fun lc -> (let _93_197 = (sli lc.FStar_Absyn_Syntax.eff_name)
in (let _93_196 = (typ_to_string lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _93_197 _93_196))))
and comp_typ_to_string = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _93_199 = (typ_to_string t)
in (FStar_Util.format1 "Tot %s" _93_199))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(let basic = if ((FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _27_8 -> (match (_27_8) with
| FStar_Absyn_Syntax.TOTAL -> begin
true
end
| _27_375 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args)))) then begin
(let _93_201 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _93_201))
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_Absyn_Syntax.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid)) then begin
(typ_to_string c.FStar_Absyn_Syntax.result_typ)
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _27_9 -> (match (_27_9) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _27_379 -> begin
false
end))))) then begin
(let _93_203 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _93_203))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _93_207 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _93_206 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (let _93_205 = (let _93_204 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.effect_args (FStar_List.map effect_arg_to_string))
in (FStar_All.pipe_right _93_204 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _93_207 _93_206 _93_205))))
end else begin
(let _93_209 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _93_208 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _93_209 _93_208)))
end
end
end
end
in (let dec = (let _93_213 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.collect (fun _27_10 -> (match (_27_10) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _93_212 = (let _93_211 = (exp_to_string e)
in (FStar_Util.format1 " (decreases %s)" _93_211))
in (_93_212)::[])
end
| _27_385 -> begin
[]
end))))
in (FStar_All.pipe_right _93_213 (FStar_String.concat " ")))
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
(let _93_225 = (formula_to_string t)
in (FStar_Util.format2 "%s %s" f _93_225))
end
| _27_414 -> begin
(FStar_All.failwith "impos")
end))
in (let bin_top = (fun f _27_12 -> (match (_27_12) with
| (FStar_Util.Inl (t1), _27_426)::(FStar_Util.Inl (t2), _27_421)::[] -> begin
(let _93_231 = (formula_to_string t1)
in (let _93_230 = (formula_to_string t2)
in (FStar_Util.format3 "%s %s %s" _93_231 f _93_230)))
end
| _27_430 -> begin
(FStar_All.failwith "Impos")
end))
in (let bin_eop = (fun f _27_13 -> (match (_27_13) with
| (FStar_Util.Inr (e1), _27_442)::(FStar_Util.Inr (e2), _27_437)::[] -> begin
(let _93_237 = (exp_to_string e1)
in (let _93_236 = (exp_to_string e2)
in (FStar_Util.format3 "%s %s %s" _93_237 f _93_236)))
end
| _27_446 -> begin
(FStar_All.failwith "impos")
end))
in (let ite = (fun _27_14 -> (match (_27_14) with
| (FStar_Util.Inl (t1), _27_461)::(FStar_Util.Inl (t2), _27_456)::(FStar_Util.Inl (t3), _27_451)::[] -> begin
(let _93_242 = (formula_to_string t1)
in (let _93_241 = (formula_to_string t2)
in (let _93_240 = (formula_to_string t3)
in (FStar_Util.format3 "if %s then %s else %s" _93_242 _93_241 _93_240))))
end
| _27_465 -> begin
(FStar_All.failwith "impos")
end))
in (let eq_op = (fun _27_15 -> (match (_27_15) with
| (FStar_Util.Inl (t1), _27_486)::(FStar_Util.Inl (t2), _27_481)::(FStar_Util.Inr (e1), _27_476)::(FStar_Util.Inr (e2), _27_471)::[] -> begin
if (FStar_ST.read FStar_Options.print_implicits) then begin
(let _93_248 = (typ_to_string t1)
in (let _93_247 = (typ_to_string t2)
in (let _93_246 = (exp_to_string e1)
in (let _93_245 = (exp_to_string e2)
in (FStar_Util.format4 "Eq2 %s %s %s %s" _93_248 _93_247 _93_246 _93_245)))))
end else begin
(let _93_250 = (exp_to_string e1)
in (let _93_249 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _93_250 _93_249)))
end
end
| (FStar_Util.Inr (e1), _27_497)::(FStar_Util.Inr (e2), _27_492)::[] -> begin
(let _93_252 = (exp_to_string e1)
in (let _93_251 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _93_252 _93_251)))
end
| _27_501 -> begin
(FStar_All.failwith "Impossible")
end))
in (let connectives = ((FStar_Absyn_Const.and_lid, (bin_top "/\\")))::((FStar_Absyn_Const.or_lid, (bin_top "\\/")))::((FStar_Absyn_Const.imp_lid, (bin_top "==>")))::((FStar_Absyn_Const.iff_lid, (bin_top "<==>")))::((FStar_Absyn_Const.ite_lid, ite))::((FStar_Absyn_Const.not_lid, (un_op "~")))::((FStar_Absyn_Const.eqT_lid, (bin_top "==")))::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op "True")))::((FStar_Absyn_Const.false_lid, (const_op "False")))::[]
in (let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (binders, phi) -> begin
(let _93_291 = (binders_to_string " " binders)
in (let _93_290 = (formula_to_string phi)
in (FStar_Util.format2 "(fun %s => %s)" _93_291 _93_290)))
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
(let _93_309 = (binders_to_string " " vars)
in (let _93_308 = (formula_to_string body)
in (FStar_Util.format2 "(forall %s. %s)" _93_309 _93_308)))
end
| Some (FStar_Absyn_Util.QEx (vars, _27_537, body)) -> begin
(let _93_311 = (binders_to_string " " vars)
in (let _93_310 = (formula_to_string body)
in (FStar_Util.format2 "(exists %s. %s)" _93_311 _93_310)))
end))))))))))
and exp_to_string = (fun x -> (match ((let _93_313 = (FStar_Absyn_Util.compress_exp x)
in _93_313.FStar_Absyn_Syntax.n)) with
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
(let _93_315 = (binders_to_string " " binders)
in (let _93_314 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _93_315 _93_314)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(let lex = if (FStar_ST.read FStar_Options.print_implicits) then begin
None
end else begin
(reconstruct_lex x)
end
in (match (lex) with
| Some (es) -> begin
(let _93_318 = (let _93_317 = (let _93_316 = (FStar_List.map exp_to_string es)
in (FStar_String.concat "; " _93_316))
in (Prims.strcat "%[" _93_317))
in (Prims.strcat _93_318 "]"))
end
| None -> begin
(let args' = (let _93_320 = (filter_imp args)
in (FStar_All.pipe_right _93_320 (FStar_List.filter (fun _27_16 -> (match (_27_16) with
| (FStar_Util.Inr (_27_579), _27_582) -> begin
true
end
| _27_585 -> begin
false
end)))))
in if ((is_infix_prim_op e) && ((FStar_List.length args') = 2)) then begin
(let _93_325 = (let _93_321 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _93_321 arg_to_string))
in (let _93_324 = (FStar_All.pipe_right e infix_prim_op_to_string)
in (let _93_323 = (let _93_322 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _93_322 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _93_325 _93_324 _93_323))))
end else begin
if ((is_unary_prim_op e) && ((FStar_List.length args') = 1)) then begin
(let _93_328 = (FStar_All.pipe_right e unary_prim_op_to_string)
in (let _93_327 = (let _93_326 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _93_326 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _93_328 _93_327)))
end else begin
(let _93_330 = (FStar_All.pipe_right e exp_to_string)
in (let _93_329 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _93_330 _93_329)))
end
end)
end))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _93_338 = (FStar_All.pipe_right e exp_to_string)
in (let _93_337 = (let _93_336 = (FStar_All.pipe_right pats (FStar_List.map (fun _27_594 -> (match (_27_594) with
| (p, wopt, e) -> begin
(let _93_335 = (FStar_All.pipe_right p pat_to_string)
in (let _93_334 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _93_332 = (FStar_All.pipe_right w exp_to_string)
in (FStar_Util.format1 "when %s" _93_332))
end)
in (let _93_333 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format3 "%s %s -> %s" _93_335 _93_334 _93_333))))
end))))
in (FStar_Util.concat_l "\n\t" _93_336))
in (FStar_Util.format2 "(match %s with %s)" _93_338 _93_337)))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _27_601) -> begin
(let _93_340 = (FStar_All.pipe_right e exp_to_string)
in (let _93_339 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "(%s:%s)" _93_340 _93_339)))
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(let _93_342 = (lbs_to_string lbs)
in (let _93_341 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "%s in %s" _93_342 _93_341)))
end))
and uvar_e_to_string = (fun _27_611 -> (match (_27_611) with
| (uv, _27_610) -> begin
(let _93_345 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _93_344 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _93_344))
end
in (Prims.strcat "\'e" _93_345))
end))
and lbs_to_string = (fun lbs -> (let _93_352 = (let _93_351 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _93_350 = (lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _93_349 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbtyp typ_to_string)
in (let _93_348 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbdef exp_to_string)
in (FStar_Util.format3 "%s:%s = %s" _93_350 _93_349 _93_348)))))))
in (FStar_Util.concat_l "\n and " _93_351))
in (FStar_Util.format2 "let %s %s" (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _93_352)))
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
and either_l_to_string = (fun delim l -> (let _93_357 = (FStar_All.pipe_right l (FStar_List.map either_to_string))
in (FStar_All.pipe_right _93_357 (FStar_Util.concat_l delim))))
and meta_to_string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Meta_refresh_label (t, _27_629, _27_631) -> begin
(let _93_359 = (typ_to_string t)
in (FStar_Util.format1 "(refresh) %s" _93_359))
end
| FStar_Absyn_Syntax.Meta_labeled (t, l, _27_637, _27_639) -> begin
(let _93_360 = (typ_to_string t)
in (FStar_Util.format2 "(labeled \"%s\") %s" l _93_360))
end
| FStar_Absyn_Syntax.Meta_named (_27_643, l) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Meta_pattern (t, ps) -> begin
(let _93_362 = (pats_to_string ps)
in (let _93_361 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "{:pattern %s} %s" _93_362 _93_361)))
end
| FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _27_654) -> begin
(let _93_364 = (formula_to_string t1)
in (let _93_363 = (formula_to_string t2)
in (FStar_Util.format2 "%s /\\ %s" _93_364 _93_363)))
end))
and pats_to_string = (fun ps -> (let _93_368 = (FStar_All.pipe_right ps (FStar_List.map (fun e -> (let _93_367 = (FStar_All.pipe_right e (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _93_367 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _93_368 (FStar_String.concat " \\/ "))))
and kind_to_string = (fun x -> (match ((let _93_370 = (FStar_Absyn_Util.compress_kind x)
in _93_370.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_lam (_27_661) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Kind_delayed (_27_664) -> begin
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
if (FStar_ST.read FStar_Options.print_real_names) then begin
(kind_to_string k)
end else begin
(let _93_372 = (sli n)
in (let _93_371 = (args_to_string args)
in (FStar_Util.format2 "%s %s" _93_372 _93_371)))
end
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(let _93_374 = (binders_to_string " -> " binders)
in (let _93_373 = (FStar_All.pipe_right k kind_to_string)
in (FStar_Util.format2 "(%s -> %s)" _93_374 _93_373)))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun uv -> (let _93_376 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _93_375 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _93_375))
end
in (Prims.strcat "\'k_" _93_376)))
and uvar_k_to_string' = (fun _27_686 -> (match (_27_686) with
| (uv, args) -> begin
(let str = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _93_378 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _93_378))
end
in (let _93_379 = (args_to_string args)
in (FStar_Util.format2 "(\'k_%s %s)" str _93_379)))
end))
and pat_to_string = (fun x -> (match (x.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (l, _27_691, pats) -> begin
(let _93_384 = (sli l.FStar_Absyn_Syntax.v)
in (let _93_383 = (let _93_382 = (FStar_List.map (fun _27_697 -> (match (_27_697) with
| (x, b) -> begin
(let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _93_382 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _93_384 _93_383)))
end
| FStar_Absyn_Syntax.Pat_dot_term (x, _27_701) -> begin
(let _93_385 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".%s" _93_385))
end
| FStar_Absyn_Syntax.Pat_dot_typ (x, _27_706) -> begin
(let _93_386 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".\'%s" _93_386))
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
| FStar_Absyn_Syntax.Pat_wild (_27_716) -> begin
"_"
end
| FStar_Absyn_Syntax.Pat_twild (_27_719) -> begin
"\'_"
end
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(let _93_387 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _93_387))
end))

let subst_to_string = (fun subst -> (let _93_395 = (let _93_394 = (FStar_List.map (fun _27_17 -> (match (_27_17) with
| FStar_Util.Inl (a, t) -> begin
(let _93_391 = (strBvd a)
in (let _93_390 = (typ_to_string t)
in (FStar_Util.format2 "(%s -> %s)" _93_391 _93_390)))
end
| FStar_Util.Inr (x, e) -> begin
(let _93_393 = (strBvd x)
in (let _93_392 = (exp_to_string e)
in (FStar_Util.format2 "(%s -> %s)" _93_393 _93_392)))
end)) subst)
in (FStar_All.pipe_right _93_394 (FStar_String.concat ", ")))
in (FStar_All.pipe_left (FStar_Util.format1 "{%s}") _93_395)))

let freevars_to_string = (fun fvs -> (let f = (fun l -> (let _93_401 = (let _93_400 = (FStar_All.pipe_right l FStar_Util.set_elements)
in (FStar_All.pipe_right _93_400 (FStar_List.map (fun t -> (strBvd t.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _93_401 (FStar_String.concat ", "))))
in (let _93_403 = (f fvs.FStar_Absyn_Syntax.ftvs)
in (let _93_402 = (f fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_Util.format2 "ftvs={%s}, fxvs={%s}" _93_403 _93_402)))))

let qual_to_string = (fun _27_18 -> (match (_27_18) with
| FStar_Absyn_Syntax.Logic -> begin
"logic"
end
| FStar_Absyn_Syntax.Opaque -> begin
"opaque"
end
| FStar_Absyn_Syntax.Discriminator (_27_743) -> begin
"discriminator"
end
| FStar_Absyn_Syntax.Projector (_27_746) -> begin
"projector"
end
| FStar_Absyn_Syntax.RecordType (ids) -> begin
(let _93_408 = (let _93_407 = (FStar_All.pipe_right ids (FStar_List.map (fun lid -> lid.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText)))
in (FStar_All.pipe_right _93_407 (FStar_String.concat ", ")))
in (FStar_Util.format1 "record(%s)" _93_408))
end
| _27_752 -> begin
"other"
end))

let quals_to_string = (fun quals -> (let _93_411 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _93_411 (FStar_String.concat " "))))

let rec sigelt_to_string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.ResetOptions, _27_757) -> begin
"#reset-options"
end
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.SetOptions (s), _27_763) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _27_770, _27_772, quals, _27_775) -> begin
(let _93_416 = (quals_to_string quals)
in (let _93_415 = (binders_to_string " " tps)
in (let _93_414 = (kind_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _93_416 lid.FStar_Absyn_Syntax.str _93_415 _93_414))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, _27_783, _27_785) -> begin
(let _93_419 = (binders_to_string " " tps)
in (let _93_418 = (kind_to_string k)
in (let _93_417 = (typ_to_string t)
in (FStar_Util.format4 "type %s %s : %s = %s" lid.FStar_Absyn_Syntax.str _93_419 _93_418 _93_417))))
end
| FStar_Absyn_Syntax.Sig_datacon (lid, t, _27_791, _27_793, _27_795, _27_797) -> begin
(let _93_420 = (typ_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Absyn_Syntax.str _93_420))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _27_804) -> begin
(let _93_422 = (quals_to_string quals)
in (let _93_421 = (typ_to_string t)
in (FStar_Util.format3 "%s val %s : %s" _93_422 lid.FStar_Absyn_Syntax.str _93_421)))
end
| FStar_Absyn_Syntax.Sig_assume (lid, f, _27_810, _27_812) -> begin
(let _93_423 = (typ_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Absyn_Syntax.str _93_423))
end
| FStar_Absyn_Syntax.Sig_let (lbs, _27_817, _27_819, b) -> begin
(lbs_to_string lbs)
end
| FStar_Absyn_Syntax.Sig_main (e, _27_825) -> begin
(let _93_424 = (exp_to_string e)
in (FStar_Util.format1 "let _ = %s" _93_424))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _27_830, _27_832, _27_834) -> begin
(let _93_425 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _93_425 (FStar_String.concat "\n")))
end
| FStar_Absyn_Syntax.Sig_new_effect (_27_838) -> begin
"new_effect { ... }"
end
| FStar_Absyn_Syntax.Sig_sub_effect (_27_841) -> begin
"sub_effect ..."
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_27_844) -> begin
"kind ..."
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, tps, c, _27_850, _27_852) -> begin
(let _93_428 = (sli l)
in (let _93_427 = (binders_to_string " " tps)
in (let _93_426 = (comp_typ_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _93_428 _93_427 _93_426))))
end))

let format_error = (fun r msg -> (let _93_433 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _93_433 msg)))

let rec sigelt_to_string_short = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_let ((_27_859, {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _27_863; FStar_Absyn_Syntax.lbdef = _27_861}::[]), _27_871, _27_873, _27_875) -> begin
(let _93_436 = (typ_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Absyn_Syntax.str _93_436))
end
| _27_879 -> begin
(let _93_439 = (let _93_438 = (FStar_Absyn_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _93_438 (FStar_List.map (fun l -> l.FStar_Absyn_Syntax.str))))
in (FStar_All.pipe_right _93_439 (FStar_String.concat ", ")))
end))

let rec modul_to_string = (fun m -> (let _93_444 = (sli m.FStar_Absyn_Syntax.name)
in (let _93_443 = (let _93_442 = (FStar_List.map sigelt_to_string m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _93_442 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _93_444 _93_443))))




