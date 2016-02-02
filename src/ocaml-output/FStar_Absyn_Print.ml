
open Prims
let infix_prim_ops = ((FStar_Absyn_Const.op_Addition, "+"))::((FStar_Absyn_Const.op_Subtraction, "-"))::((FStar_Absyn_Const.op_Multiply, "*"))::((FStar_Absyn_Const.op_Division, "/"))::((FStar_Absyn_Const.op_Eq, "="))::((FStar_Absyn_Const.op_ColonEq, ":="))::((FStar_Absyn_Const.op_notEq, "<>"))::((FStar_Absyn_Const.op_And, "&&"))::((FStar_Absyn_Const.op_Or, "||"))::((FStar_Absyn_Const.op_LTE, "<="))::((FStar_Absyn_Const.op_GTE, ">="))::((FStar_Absyn_Const.op_LT, "<"))::((FStar_Absyn_Const.op_GT, ">"))::((FStar_Absyn_Const.op_Modulus, "mod"))::[]

let unary_prim_ops = ((FStar_Absyn_Const.op_Negation, "not"))::((FStar_Absyn_Const.op_Minus, "-"))::[]

let infix_type_ops = ((FStar_Absyn_Const.and_lid, "/\\"))::((FStar_Absyn_Const.or_lid, "\\/"))::((FStar_Absyn_Const.imp_lid, "==>"))::((FStar_Absyn_Const.iff_lid, "<==>"))::((FStar_Absyn_Const.precedes_lid, "<<"))::((FStar_Absyn_Const.eq2_lid, "=="))::((FStar_Absyn_Const.eqT_lid, "=="))::[]

let unary_type_ops = ((FStar_Absyn_Const.not_lid, "~"))::[]

let is_prim_op = (fun ps f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _28_23) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _28_27 -> begin
false
end))

let is_type_op = (fun ps t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals ftv.FStar_Absyn_Syntax.v)))
end
| _28_33 -> begin
false
end))

let get_lid = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _28_37) -> begin
fv.FStar_Absyn_Syntax.v
end
| _28_41 -> begin
(FStar_All.failwith "get_lid")
end))

let get_type_lid = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
ftv.FStar_Absyn_Syntax.v
end
| _28_46 -> begin
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

let is_inr = (fun _28_1 -> (match (_28_1) with
| FStar_Util.Inl (_28_58) -> begin
false
end
| FStar_Util.Inr (_28_61) -> begin
true
end))

let rec reconstruct_lex = (fun e -> (match ((let _81_28 = (FStar_Absyn_Util.compress_exp e)
in _81_28.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (f, args) -> begin
(let args = (FStar_List.filter (fun a -> (((Prims.snd a) <> Some (FStar_Absyn_Syntax.Implicit)) && (is_inr (Prims.fst a)))) args)
in (let exps = (FStar_List.map (fun _28_2 -> (match (_28_2) with
| (FStar_Util.Inl (_28_72), _28_75) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Util.Inr (x), _28_80) -> begin
x
end)) args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = 2)) then begin
(match ((let _81_31 = (FStar_List.nth exps 1)
in (reconstruct_lex _81_31))) with
| Some (xs) -> begin
(let _81_33 = (let _81_32 = (FStar_List.nth exps 0)
in (_81_32)::xs)
in Some (_81_33))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _28_87 -> begin
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

let find_lid = (fun x xs -> (let _81_47 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _81_47)))

let infix_prim_op_to_string = (fun e -> (let _81_49 = (get_lid e)
in (find_lid _81_49 infix_prim_ops)))

let unary_prim_op_to_string = (fun e -> (let _81_51 = (get_lid e)
in (find_lid _81_51 unary_prim_ops)))

let infix_type_op_to_string = (fun t -> (let _81_53 = (get_type_lid t)
in (find_lid _81_53 infix_type_ops)))

let unary_type_op_to_string = (fun t -> (let _81_55 = (get_type_lid t)
in (find_lid _81_55 unary_type_ops)))

let quant_to_string = (fun t -> (let _81_57 = (get_type_lid t)
in (find_lid _81_57 quants)))

let rec sli = (fun l -> if (FStar_ST.read FStar_Options.print_real_names) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)

let strBvd = (fun bvd -> if (FStar_ST.read FStar_Options.print_real_names) then begin
(Prims.strcat bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText bvd.FStar_Absyn_Syntax.realname.FStar_Ident.idText)
end else begin
if ((FStar_ST.read FStar_Options.hide_genident_nums) && (FStar_Util.starts_with bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText "_")) then begin
(FStar_All.try_with (fun _28_106 -> (match (()) with
| () -> begin
(let _28_112 = (let _81_62 = (FStar_Util.substring_from bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText 1)
in (FStar_Util.int_of_string _81_62))
in "_?")
end)) (fun _28_105 -> (match (_28_105) with
| _28_109 -> begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end)))
end else begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end
end)

let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _28_3 -> (match (_28_3) with
| (_28_117, Some (FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _28_122 -> begin
true
end)))))

let const_to_string = (fun x -> (match (x) with
| FStar_Const.Const_effect -> begin
"eff"
end
| FStar_Const.Const_unit -> begin
"()"
end
| FStar_Const.Const_bool (b) -> begin
if b then begin
"true"
end else begin
"false"
end
end
| FStar_Const.Const_int32 (x) -> begin
(FStar_Util.string_of_int32 x)
end
| FStar_Const.Const_float (x) -> begin
(FStar_Util.string_of_float x)
end
| FStar_Const.Const_char (x) -> begin
(Prims.strcat (Prims.strcat "\'" (FStar_Util.string_of_char x)) "\'")
end
| FStar_Const.Const_string (bytes, _28_136) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_28_140) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x) -> begin
x
end
| FStar_Const.Const_int64 (_28_145) -> begin
"<int64>"
end
| FStar_Const.Const_uint8 (_28_148) -> begin
"<uint8>"
end))

let rec tag_of_typ = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_28_152) -> begin
"Typ_btvar"
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(Prims.strcat "Typ_const " v.FStar_Absyn_Syntax.v.FStar_Ident.str)
end
| FStar_Absyn_Syntax.Typ_fun (_28_157) -> begin
"Typ_fun"
end
| FStar_Absyn_Syntax.Typ_refine (_28_160) -> begin
"Typ_refine"
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let _81_103 = (tag_of_typ head)
in (let _81_102 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.format2 "Typ_app(%s, [%s args])" _81_103 _81_102)))
end
| FStar_Absyn_Syntax.Typ_lam (_28_167) -> begin
"Typ_lam"
end
| FStar_Absyn_Syntax.Typ_ascribed (_28_170) -> begin
"Typ_ascribed"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_28_173)) -> begin
"Typ_meta_pattern"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_28_177)) -> begin
"Typ_meta_named"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_28_181)) -> begin
"Typ_meta_labeled"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_28_185)) -> begin
"Typ_meta_refresh_label"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_28_189)) -> begin
"Typ_meta_slack_formula"
end
| FStar_Absyn_Syntax.Typ_uvar (_28_193) -> begin
"Typ_uvar"
end
| FStar_Absyn_Syntax.Typ_delayed (_28_196) -> begin
"Typ_delayed"
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"Typ_unknown"
end))
and tag_of_exp = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_28_201) -> begin
"Exp_bvar"
end
| FStar_Absyn_Syntax.Exp_fvar (_28_204) -> begin
"Exp_fvar"
end
| FStar_Absyn_Syntax.Exp_constant (_28_207) -> begin
"Exp_constant"
end
| FStar_Absyn_Syntax.Exp_abs (_28_210) -> begin
"Exp_abs"
end
| FStar_Absyn_Syntax.Exp_app (_28_213) -> begin
"Exp_app"
end
| FStar_Absyn_Syntax.Exp_match (_28_216) -> begin
"Exp_match"
end
| FStar_Absyn_Syntax.Exp_ascribed (_28_219) -> begin
"Exp_ascribed"
end
| FStar_Absyn_Syntax.Exp_let (_28_222) -> begin
"Exp_let"
end
| FStar_Absyn_Syntax.Exp_uvar (_28_225) -> begin
"Exp_uvar"
end
| FStar_Absyn_Syntax.Exp_delayed (_28_228) -> begin
"Exp_delayed"
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_28_231, m)) -> begin
(let _81_107 = (meta_e_to_string m)
in (Prims.strcat "Exp_meta_desugared " _81_107))
end))
and meta_e_to_string = (fun _28_4 -> (match (_28_4) with
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
| FStar_Absyn_Syntax.Typ_delayed (_28_245) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_28_248, l)) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Typ_meta (meta) -> begin
(let _81_113 = (FStar_All.pipe_right meta meta_to_string)
in (FStar_Util.format1 "(Meta %s)" _81_113))
end
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(strBvd btv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(sli v.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_fun (binders, c) -> begin
(let _81_115 = (binders_to_string " -> " binders)
in (let _81_114 = (comp_typ_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _81_115 _81_114)))
end
| FStar_Absyn_Syntax.Typ_refine (xt, f) -> begin
(let _81_118 = (strBvd xt.FStar_Absyn_Syntax.v)
in (let _81_117 = (FStar_All.pipe_right xt.FStar_Absyn_Syntax.sort typ_to_string)
in (let _81_116 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "%s:%s{%s}" _81_118 _81_117 _81_116))))
end
| FStar_Absyn_Syntax.Typ_app (_28_268, []) -> begin
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
| _28_288 -> begin
(let _81_129 = (tag_of_typ t)
in (let _81_128 = (typ_to_string t)
in (FStar_Util.format2 "<Expected a type-lambda! got %s>%s" _81_129 _81_128)))
end))
end
| FStar_Util.Inr (e) -> begin
(let _81_130 = (exp_to_string e)
in (FStar_Util.format1 "(<Expected a type!>%s)" _81_130))
end))
in (let qbinder_to_string = (q_to_string (fun x -> (binder_to_string (Prims.fst x))))
in (let qbody_to_string = (q_to_string (fun x -> (typ_to_string (Prims.snd x))))
in (let args' = if ((FStar_ST.read FStar_Options.print_implicits) && (not ((is_quant t)))) then begin
args
end else begin
(FStar_List.filter (fun _28_5 -> (match (_28_5) with
| (_28_297, Some (FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _28_302 -> begin
true
end)) args)
end
in if ((is_ite t) && ((FStar_List.length args) = 3)) then begin
(let _81_141 = (let _81_136 = (FStar_List.nth args 0)
in (arg_to_string _81_136))
in (let _81_140 = (let _81_137 = (FStar_List.nth args 1)
in (arg_to_string _81_137))
in (let _81_139 = (let _81_138 = (FStar_List.nth args 2)
in (arg_to_string _81_138))
in (FStar_Util.format3 "if %s then %s else %s" _81_141 _81_140 _81_139))))
end else begin
if ((is_b2t t) && ((FStar_List.length args) = 1)) then begin
(let _81_142 = (FStar_List.nth args 0)
in (FStar_All.pipe_right _81_142 arg_to_string))
end else begin
if ((is_quant t) && ((FStar_List.length args) <= 2)) then begin
(let _81_147 = (quant_to_string t)
in (let _81_146 = (let _81_143 = (FStar_List.nth args' 0)
in (qbinder_to_string _81_143))
in (let _81_145 = (let _81_144 = (FStar_List.nth args' 0)
in (qbody_to_string _81_144))
in (FStar_Util.format3 "(%s (%s). %s)" _81_147 _81_146 _81_145))))
end else begin
if ((is_infix_type_op t) && ((FStar_List.length args') = 2)) then begin
(let _81_152 = (let _81_148 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _81_148 arg_to_string))
in (let _81_151 = (FStar_All.pipe_right t infix_type_op_to_string)
in (let _81_150 = (let _81_149 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _81_149 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _81_152 _81_151 _81_150))))
end else begin
if ((is_unary_type_op t) && ((FStar_List.length args') = 1)) then begin
(let _81_155 = (FStar_All.pipe_right t unary_type_op_to_string)
in (let _81_154 = (let _81_153 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _81_153 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _81_155 _81_154)))
end else begin
(let _81_157 = (FStar_All.pipe_right t typ_to_string)
in (let _81_156 = (FStar_All.pipe_right args args_to_string)
in (FStar_Util.format2 "(%s %s)" _81_157 _81_156)))
end
end
end
end
end))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(let _81_159 = (binders_to_string " " binders)
in (let _81_158 = (FStar_All.pipe_right t2 typ_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _81_159 _81_158)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _81_161 = (typ_to_string t)
in (let _81_160 = (kind_to_string k)
in (FStar_Util.format2 "(%s <: %s)" _81_161 _81_160)))
end else begin
(FStar_All.pipe_right t typ_to_string)
end
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"<UNKNOWN>"
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(match ((FStar_Absyn_Visit.compress_typ_aux false x)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_28_326); FStar_Absyn_Syntax.tk = _28_324; FStar_Absyn_Syntax.pos = _28_322; FStar_Absyn_Syntax.fvs = _28_320; FStar_Absyn_Syntax.uvs = _28_318} -> begin
(uvar_t_to_string (uv, k))
end
| t -> begin
(FStar_All.pipe_right t typ_to_string)
end)
end)))
and uvar_t_to_string = (fun _28_332 -> (match (_28_332) with
| (uv, k) -> begin
if (false && (FStar_ST.read FStar_Options.print_real_names)) then begin
(let _81_165 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _81_163 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _81_163))
end
in (let _81_164 = (kind_to_string k)
in (FStar_Util.format2 "(U%s : %s)" _81_165 _81_164)))
end else begin
(let _81_167 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _81_166 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _81_166))
end
in (FStar_Util.format1 "U%s" _81_167))
end
end))
and imp_to_string = (fun s _28_6 -> (match (_28_6) with
| Some (FStar_Absyn_Syntax.Implicit) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Absyn_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _28_340 -> begin
s
end))
and binder_to_string' = (fun is_arrow b -> (match (b) with
| (FStar_Util.Inl (a), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _81_172 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _81_172 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp a.FStar_Absyn_Syntax.v))) then begin
(kind_to_string a.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits)))) then begin
(let _81_173 = (strBvd a.FStar_Absyn_Syntax.v)
in (imp_to_string _81_173 imp))
end else begin
(let _81_177 = (let _81_176 = (let _81_174 = (strBvd a.FStar_Absyn_Syntax.v)
in (Prims.strcat _81_174 ":"))
in (let _81_175 = (kind_to_string a.FStar_Absyn_Syntax.sort)
in (Prims.strcat _81_176 _81_175)))
in (imp_to_string _81_177 imp))
end
end
end
| (FStar_Util.Inr (x), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _81_178 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _81_178 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp x.FStar_Absyn_Syntax.v))) then begin
(typ_to_string x.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits)))) then begin
(let _81_179 = (strBvd x.FStar_Absyn_Syntax.v)
in (imp_to_string _81_179 imp))
end else begin
(let _81_183 = (let _81_182 = (let _81_180 = (strBvd x.FStar_Absyn_Syntax.v)
in (Prims.strcat _81_180 ":"))
in (let _81_181 = (typ_to_string x.FStar_Absyn_Syntax.sort)
in (Prims.strcat _81_182 _81_181)))
in (imp_to_string _81_183 imp))
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
(let _81_188 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _81_188 (FStar_String.concat sep)))
end else begin
(let _81_189 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _81_189 (FStar_String.concat sep)))
end))
and arg_to_string = (fun _28_7 -> (match (_28_7) with
| (FStar_Util.Inl (a), imp) -> begin
(let _81_191 = (typ_to_string a)
in (imp_to_string _81_191 imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _81_192 = (exp_to_string x)
in (imp_to_string _81_192 imp))
end))
and args_to_string = (fun args -> (let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _81_194 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _81_194 (FStar_String.concat " ")))))
and lcomp_typ_to_string = (fun lc -> (let _81_197 = (sli lc.FStar_Absyn_Syntax.eff_name)
in (let _81_196 = (typ_to_string lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _81_197 _81_196))))
and comp_typ_to_string = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _81_199 = (typ_to_string t)
in (FStar_Util.format1 "Tot %s" _81_199))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(let basic = if ((FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _28_8 -> (match (_28_8) with
| FStar_Absyn_Syntax.TOTAL -> begin
true
end
| _28_376 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args)))) then begin
(let _81_201 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _81_201))
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_Ident.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid)) then begin
(typ_to_string c.FStar_Absyn_Syntax.result_typ)
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _28_9 -> (match (_28_9) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _28_380 -> begin
false
end))))) then begin
(let _81_203 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _81_203))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _81_207 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _81_206 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (let _81_205 = (let _81_204 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.effect_args (FStar_List.map effect_arg_to_string))
in (FStar_All.pipe_right _81_204 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _81_207 _81_206 _81_205))))
end else begin
(let _81_209 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _81_208 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _81_209 _81_208)))
end
end
end
end
in (let dec = (let _81_213 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.collect (fun _28_10 -> (match (_28_10) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _81_212 = (let _81_211 = (exp_to_string e)
in (FStar_Util.format1 " (decreases %s)" _81_211))
in (_81_212)::[])
end
| _28_386 -> begin
[]
end))))
in (FStar_All.pipe_right _81_213 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and effect_arg_to_string = (fun e -> (match (e) with
| (FStar_Util.Inr (e), _28_392) -> begin
(exp_to_string e)
end
| (FStar_Util.Inl (wp), _28_397) -> begin
(formula_to_string wp)
end))
and formula_to_string = (fun phi -> (typ_to_string phi))
and formula_to_string_old_now_unused = (fun phi -> (let const_op = (fun f _28_403 -> f)
in (let un_op = (fun f _28_11 -> (match (_28_11) with
| (FStar_Util.Inl (t), _28_411)::[] -> begin
(let _81_225 = (formula_to_string t)
in (FStar_Util.format2 "%s %s" f _81_225))
end
| _28_415 -> begin
(FStar_All.failwith "impos")
end))
in (let bin_top = (fun f _28_12 -> (match (_28_12) with
| (FStar_Util.Inl (t1), _28_427)::(FStar_Util.Inl (t2), _28_422)::[] -> begin
(let _81_231 = (formula_to_string t1)
in (let _81_230 = (formula_to_string t2)
in (FStar_Util.format3 "%s %s %s" _81_231 f _81_230)))
end
| _28_431 -> begin
(FStar_All.failwith "Impos")
end))
in (let bin_eop = (fun f _28_13 -> (match (_28_13) with
| (FStar_Util.Inr (e1), _28_443)::(FStar_Util.Inr (e2), _28_438)::[] -> begin
(let _81_237 = (exp_to_string e1)
in (let _81_236 = (exp_to_string e2)
in (FStar_Util.format3 "%s %s %s" _81_237 f _81_236)))
end
| _28_447 -> begin
(FStar_All.failwith "impos")
end))
in (let ite = (fun _28_14 -> (match (_28_14) with
| (FStar_Util.Inl (t1), _28_462)::(FStar_Util.Inl (t2), _28_457)::(FStar_Util.Inl (t3), _28_452)::[] -> begin
(let _81_242 = (formula_to_string t1)
in (let _81_241 = (formula_to_string t2)
in (let _81_240 = (formula_to_string t3)
in (FStar_Util.format3 "if %s then %s else %s" _81_242 _81_241 _81_240))))
end
| _28_466 -> begin
(FStar_All.failwith "impos")
end))
in (let eq_op = (fun _28_15 -> (match (_28_15) with
| (FStar_Util.Inl (t1), _28_487)::(FStar_Util.Inl (t2), _28_482)::(FStar_Util.Inr (e1), _28_477)::(FStar_Util.Inr (e2), _28_472)::[] -> begin
if (FStar_ST.read FStar_Options.print_implicits) then begin
(let _81_248 = (typ_to_string t1)
in (let _81_247 = (typ_to_string t2)
in (let _81_246 = (exp_to_string e1)
in (let _81_245 = (exp_to_string e2)
in (FStar_Util.format4 "Eq2 %s %s %s %s" _81_248 _81_247 _81_246 _81_245)))))
end else begin
(let _81_250 = (exp_to_string e1)
in (let _81_249 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _81_250 _81_249)))
end
end
| (FStar_Util.Inr (e1), _28_498)::(FStar_Util.Inr (e2), _28_493)::[] -> begin
(let _81_252 = (exp_to_string e1)
in (let _81_251 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _81_252 _81_251)))
end
| _28_502 -> begin
(FStar_All.failwith "Impossible")
end))
in (let connectives = ((FStar_Absyn_Const.and_lid, (bin_top "/\\")))::((FStar_Absyn_Const.or_lid, (bin_top "\\/")))::((FStar_Absyn_Const.imp_lid, (bin_top "==>")))::((FStar_Absyn_Const.iff_lid, (bin_top "<==>")))::((FStar_Absyn_Const.ite_lid, ite))::((FStar_Absyn_Const.not_lid, (un_op "~")))::((FStar_Absyn_Const.eqT_lid, (bin_top "==")))::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op "True")))::((FStar_Absyn_Const.false_lid, (const_op "False")))::[]
in (let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (binders, phi) -> begin
(let _81_291 = (binders_to_string " " binders)
in (let _81_290 = (formula_to_string phi)
in (FStar_Util.format2 "(fun %s => %s)" _81_291 _81_290)))
end
| _28_512 -> begin
(typ_to_string phi)
end))
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _28_522 -> (match (_28_522) with
| (l, _28_521) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_28_525, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, _28_531, body)) -> begin
(let _81_309 = (binders_to_string " " vars)
in (let _81_308 = (formula_to_string body)
in (FStar_Util.format2 "(forall %s. %s)" _81_309 _81_308)))
end
| Some (FStar_Absyn_Util.QEx (vars, _28_538, body)) -> begin
(let _81_311 = (binders_to_string " " vars)
in (let _81_310 = (formula_to_string body)
in (FStar_Util.format2 "(exists %s. %s)" _81_311 _81_310)))
end))))))))))
and exp_to_string = (fun x -> (match ((let _81_313 = (FStar_Absyn_Util.compress_exp x)
in _81_313.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_delayed (_28_545) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _28_549)) -> begin
(exp_to_string e)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(uvar_e_to_string (uv, t))
end
| FStar_Absyn_Syntax.Exp_bvar (bvv) -> begin
(strBvd bvv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_fvar (fv, _28_561) -> begin
(sli fv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(FStar_All.pipe_right c const_to_string)
end
| FStar_Absyn_Syntax.Exp_abs (binders, e) -> begin
(let _81_315 = (binders_to_string " " binders)
in (let _81_314 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _81_315 _81_314)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(let lex = if (FStar_ST.read FStar_Options.print_implicits) then begin
None
end else begin
(reconstruct_lex x)
end
in (match (lex) with
| Some (es) -> begin
(let _81_318 = (let _81_317 = (let _81_316 = (FStar_List.map exp_to_string es)
in (FStar_String.concat "; " _81_316))
in (Prims.strcat "%[" _81_317))
in (Prims.strcat _81_318 "]"))
end
| None -> begin
(let args' = (let _81_320 = (filter_imp args)
in (FStar_All.pipe_right _81_320 (FStar_List.filter (fun _28_16 -> (match (_28_16) with
| (FStar_Util.Inr (_28_580), _28_583) -> begin
true
end
| _28_586 -> begin
false
end)))))
in if ((is_infix_prim_op e) && ((FStar_List.length args') = 2)) then begin
(let _81_325 = (let _81_321 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _81_321 arg_to_string))
in (let _81_324 = (FStar_All.pipe_right e infix_prim_op_to_string)
in (let _81_323 = (let _81_322 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _81_322 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _81_325 _81_324 _81_323))))
end else begin
if ((is_unary_prim_op e) && ((FStar_List.length args') = 1)) then begin
(let _81_328 = (FStar_All.pipe_right e unary_prim_op_to_string)
in (let _81_327 = (let _81_326 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _81_326 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _81_328 _81_327)))
end else begin
(let _81_330 = (FStar_All.pipe_right e exp_to_string)
in (let _81_329 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _81_330 _81_329)))
end
end)
end))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _81_338 = (FStar_All.pipe_right e exp_to_string)
in (let _81_337 = (let _81_336 = (FStar_All.pipe_right pats (FStar_List.map (fun _28_595 -> (match (_28_595) with
| (p, wopt, e) -> begin
(let _81_335 = (FStar_All.pipe_right p pat_to_string)
in (let _81_334 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _81_332 = (FStar_All.pipe_right w exp_to_string)
in (FStar_Util.format1 "when %s" _81_332))
end)
in (let _81_333 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format3 "%s %s -> %s" _81_335 _81_334 _81_333))))
end))))
in (FStar_Util.concat_l "\n\t" _81_336))
in (FStar_Util.format2 "(match %s with %s)" _81_338 _81_337)))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _28_602) -> begin
(let _81_340 = (FStar_All.pipe_right e exp_to_string)
in (let _81_339 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "(%s:%s)" _81_340 _81_339)))
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(let _81_342 = (lbs_to_string lbs)
in (let _81_341 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "%s in %s" _81_342 _81_341)))
end))
and uvar_e_to_string = (fun _28_612 -> (match (_28_612) with
| (uv, _28_611) -> begin
(let _81_345 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _81_344 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _81_344))
end
in (Prims.strcat "\'e" _81_345))
end))
and lbs_to_string = (fun lbs -> (let _81_352 = (let _81_351 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _81_350 = (lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _81_349 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbtyp typ_to_string)
in (let _81_348 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbdef exp_to_string)
in (FStar_Util.format3 "%s:%s = %s" _81_350 _81_349 _81_348)))))))
in (FStar_Util.concat_l "\n and " _81_351))
in (FStar_Util.format2 "let %s %s" (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _81_352)))
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
and either_l_to_string = (fun delim l -> (let _81_357 = (FStar_All.pipe_right l (FStar_List.map either_to_string))
in (FStar_All.pipe_right _81_357 (FStar_Util.concat_l delim))))
and meta_to_string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Meta_refresh_label (t, _28_630, _28_632) -> begin
(let _81_359 = (typ_to_string t)
in (FStar_Util.format1 "(refresh) %s" _81_359))
end
| FStar_Absyn_Syntax.Meta_labeled (t, l, _28_638, _28_640) -> begin
(let _81_360 = (typ_to_string t)
in (FStar_Util.format2 "(labeled \"%s\") %s" l _81_360))
end
| FStar_Absyn_Syntax.Meta_named (_28_644, l) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Meta_pattern (t, ps) -> begin
(let _81_362 = (pats_to_string ps)
in (let _81_361 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "{:pattern %s} %s" _81_362 _81_361)))
end
| FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _28_655) -> begin
(let _81_364 = (formula_to_string t1)
in (let _81_363 = (formula_to_string t2)
in (FStar_Util.format2 "%s /\\ %s" _81_364 _81_363)))
end))
and pats_to_string = (fun ps -> (let _81_368 = (FStar_All.pipe_right ps (FStar_List.map (fun e -> (let _81_367 = (FStar_All.pipe_right e (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _81_367 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _81_368 (FStar_String.concat " \\/ "))))
and kind_to_string = (fun x -> (match ((let _81_370 = (FStar_Absyn_Util.compress_kind x)
in _81_370.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_lam (_28_662) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Kind_delayed (_28_665) -> begin
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
(let _81_372 = (sli n)
in (let _81_371 = (args_to_string args)
in (FStar_Util.format2 "%s %s" _81_372 _81_371)))
end
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(let _81_374 = (binders_to_string " -> " binders)
in (let _81_373 = (FStar_All.pipe_right k kind_to_string)
in (FStar_Util.format2 "(%s -> %s)" _81_374 _81_373)))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun uv -> (let _81_376 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _81_375 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _81_375))
end
in (Prims.strcat "\'k_" _81_376)))
and uvar_k_to_string' = (fun _28_687 -> (match (_28_687) with
| (uv, args) -> begin
(let str = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _81_378 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _81_378))
end
in (let _81_379 = (args_to_string args)
in (FStar_Util.format2 "(\'k_%s %s)" str _81_379)))
end))
and pat_to_string = (fun x -> (match (x.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (l, _28_692, pats) -> begin
(let _81_384 = (sli l.FStar_Absyn_Syntax.v)
in (let _81_383 = (let _81_382 = (FStar_List.map (fun _28_698 -> (match (_28_698) with
| (x, b) -> begin
(let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _81_382 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _81_384 _81_383)))
end
| FStar_Absyn_Syntax.Pat_dot_term (x, _28_702) -> begin
(let _81_385 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".%s" _81_385))
end
| FStar_Absyn_Syntax.Pat_dot_typ (x, _28_707) -> begin
(let _81_386 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".\'%s" _81_386))
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
| FStar_Absyn_Syntax.Pat_wild (_28_717) -> begin
"_"
end
| FStar_Absyn_Syntax.Pat_twild (_28_720) -> begin
"\'_"
end
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(let _81_387 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _81_387))
end))

let subst_to_string = (fun subst -> (let _81_395 = (let _81_394 = (FStar_List.map (fun _28_17 -> (match (_28_17) with
| FStar_Util.Inl (a, t) -> begin
(let _81_391 = (strBvd a)
in (let _81_390 = (typ_to_string t)
in (FStar_Util.format2 "(%s -> %s)" _81_391 _81_390)))
end
| FStar_Util.Inr (x, e) -> begin
(let _81_393 = (strBvd x)
in (let _81_392 = (exp_to_string e)
in (FStar_Util.format2 "(%s -> %s)" _81_393 _81_392)))
end)) subst)
in (FStar_All.pipe_right _81_394 (FStar_String.concat ", ")))
in (FStar_All.pipe_left (FStar_Util.format1 "{%s}") _81_395)))

let freevars_to_string = (fun fvs -> (let f = (fun l -> (let _81_401 = (let _81_400 = (FStar_All.pipe_right l FStar_Util.set_elements)
in (FStar_All.pipe_right _81_400 (FStar_List.map (fun t -> (strBvd t.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _81_401 (FStar_String.concat ", "))))
in (let _81_403 = (f fvs.FStar_Absyn_Syntax.ftvs)
in (let _81_402 = (f fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_Util.format2 "ftvs={%s}, fxvs={%s}" _81_403 _81_402)))))

let qual_to_string = (fun _28_18 -> (match (_28_18) with
| FStar_Absyn_Syntax.Logic -> begin
"logic"
end
| FStar_Absyn_Syntax.Opaque -> begin
"opaque"
end
| FStar_Absyn_Syntax.Discriminator (_28_744) -> begin
"discriminator"
end
| FStar_Absyn_Syntax.Projector (_28_747) -> begin
"projector"
end
| FStar_Absyn_Syntax.RecordType (ids) -> begin
(let _81_408 = (let _81_407 = (FStar_All.pipe_right ids (FStar_List.map (fun lid -> lid.FStar_Ident.ident.FStar_Ident.idText)))
in (FStar_All.pipe_right _81_407 (FStar_String.concat ", ")))
in (FStar_Util.format1 "record(%s)" _81_408))
end
| _28_753 -> begin
"other"
end))

let quals_to_string = (fun quals -> (let _81_411 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _81_411 (FStar_String.concat " "))))

let rec sigelt_to_string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.ResetOptions, _28_758) -> begin
"#reset-options"
end
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.SetOptions (s), _28_764) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _28_771, _28_773, quals, _28_776) -> begin
(let _81_416 = (quals_to_string quals)
in (let _81_415 = (binders_to_string " " tps)
in (let _81_414 = (kind_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _81_416 lid.FStar_Ident.str _81_415 _81_414))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, _28_784, _28_786) -> begin
(let _81_419 = (binders_to_string " " tps)
in (let _81_418 = (kind_to_string k)
in (let _81_417 = (typ_to_string t)
in (FStar_Util.format4 "type %s %s : %s = %s" lid.FStar_Ident.str _81_419 _81_418 _81_417))))
end
| FStar_Absyn_Syntax.Sig_datacon (lid, t, _28_792, _28_794, _28_796, _28_798) -> begin
(let _81_420 = (typ_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _81_420))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _28_805) -> begin
(let _81_422 = (quals_to_string quals)
in (let _81_421 = (typ_to_string t)
in (FStar_Util.format3 "%s val %s : %s" _81_422 lid.FStar_Ident.str _81_421)))
end
| FStar_Absyn_Syntax.Sig_assume (lid, f, _28_811, _28_813) -> begin
(let _81_423 = (typ_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _81_423))
end
| FStar_Absyn_Syntax.Sig_let (lbs, _28_818, _28_820, b) -> begin
(lbs_to_string lbs)
end
| FStar_Absyn_Syntax.Sig_main (e, _28_826) -> begin
(let _81_424 = (exp_to_string e)
in (FStar_Util.format1 "let _ = %s" _81_424))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _28_831, _28_833, _28_835) -> begin
(let _81_425 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _81_425 (FStar_String.concat "\n")))
end
| FStar_Absyn_Syntax.Sig_new_effect (_28_839) -> begin
"new_effect { ... }"
end
| FStar_Absyn_Syntax.Sig_sub_effect (_28_842) -> begin
"sub_effect ..."
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_28_845) -> begin
"kind ..."
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, tps, c, _28_851, _28_853) -> begin
(let _81_428 = (sli l)
in (let _81_427 = (binders_to_string " " tps)
in (let _81_426 = (comp_typ_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _81_428 _81_427 _81_426))))
end))

let format_error = (fun r msg -> (let _81_433 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _81_433 msg)))

let rec sigelt_to_string_short = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_let ((_28_860, {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _28_864; FStar_Absyn_Syntax.lbdef = _28_862}::[]), _28_872, _28_874, _28_876) -> begin
(let _81_436 = (typ_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Ident.str _81_436))
end
| _28_880 -> begin
(let _81_439 = (let _81_438 = (FStar_Absyn_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _81_438 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _81_439 (FStar_String.concat ", ")))
end))

let rec modul_to_string = (fun m -> (let _81_444 = (sli m.FStar_Absyn_Syntax.name)
in (let _81_443 = (let _81_442 = (FStar_List.map sigelt_to_string m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _81_442 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _81_444 _81_443))))




