
open Prims
let infix_prim_ops = ((FStar_Absyn_Const.op_Addition, "+"))::((FStar_Absyn_Const.op_Subtraction, "-"))::((FStar_Absyn_Const.op_Multiply, "*"))::((FStar_Absyn_Const.op_Division, "/"))::((FStar_Absyn_Const.op_Eq, "="))::((FStar_Absyn_Const.op_ColonEq, ":="))::((FStar_Absyn_Const.op_notEq, "<>"))::((FStar_Absyn_Const.op_And, "&&"))::((FStar_Absyn_Const.op_Or, "||"))::((FStar_Absyn_Const.op_LTE, "<="))::((FStar_Absyn_Const.op_GTE, ">="))::((FStar_Absyn_Const.op_LT, "<"))::((FStar_Absyn_Const.op_GT, ">"))::((FStar_Absyn_Const.op_Modulus, "mod"))::[]

let unary_prim_ops = ((FStar_Absyn_Const.op_Negation, "not"))::((FStar_Absyn_Const.op_Minus, "-"))::[]

let infix_type_ops = ((FStar_Absyn_Const.and_lid, "/\\"))::((FStar_Absyn_Const.or_lid, "\\/"))::((FStar_Absyn_Const.imp_lid, "==>"))::((FStar_Absyn_Const.iff_lid, "<==>"))::((FStar_Absyn_Const.precedes_lid, "<<"))::((FStar_Absyn_Const.eq2_lid, "=="))::((FStar_Absyn_Const.eqT_lid, "=="))::[]

let unary_type_ops = ((FStar_Absyn_Const.not_lid, "~"))::[]

let is_prim_op = (fun ps f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _30_23) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _30_27 -> begin
false
end))

let is_type_op = (fun ps t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals ftv.FStar_Absyn_Syntax.v)))
end
| _30_33 -> begin
false
end))

let get_lid = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _30_37) -> begin
fv.FStar_Absyn_Syntax.v
end
| _30_41 -> begin
(FStar_All.failwith "get_lid")
end))

let get_type_lid = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
ftv.FStar_Absyn_Syntax.v
end
| _30_46 -> begin
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

let is_inr = (fun _30_1 -> (match (_30_1) with
| FStar_Util.Inl (_30_58) -> begin
false
end
| FStar_Util.Inr (_30_61) -> begin
true
end))

let rec reconstruct_lex = (fun e -> (match ((let _121_28 = (FStar_Absyn_Util.compress_exp e)
in _121_28.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (f, args) -> begin
(let args = (FStar_List.filter (fun a -> (((Prims.snd a) <> Some (FStar_Absyn_Syntax.Implicit)) && (is_inr (Prims.fst a)))) args)
in (let exps = (FStar_List.map (fun _30_2 -> (match (_30_2) with
| (FStar_Util.Inl (_30_72), _30_75) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Util.Inr (x), _30_80) -> begin
x
end)) args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = 2)) then begin
(match ((let _121_31 = (FStar_List.nth exps 1)
in (reconstruct_lex _121_31))) with
| Some (xs) -> begin
(let _121_33 = (let _121_32 = (FStar_List.nth exps 0)
in (_121_32)::xs)
in Some (_121_33))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _30_87 -> begin
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

let find_lid = (fun x xs -> (let _121_47 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _121_47)))

let infix_prim_op_to_string = (fun e -> (let _121_49 = (get_lid e)
in (find_lid _121_49 infix_prim_ops)))

let unary_prim_op_to_string = (fun e -> (let _121_51 = (get_lid e)
in (find_lid _121_51 unary_prim_ops)))

let infix_type_op_to_string = (fun t -> (let _121_53 = (get_type_lid t)
in (find_lid _121_53 infix_type_ops)))

let unary_type_op_to_string = (fun t -> (let _121_55 = (get_type_lid t)
in (find_lid _121_55 unary_type_ops)))

let quant_to_string = (fun t -> (let _121_57 = (get_type_lid t)
in (find_lid _121_57 quants)))

let rec sli = (fun l -> if (FStar_ST.read FStar_Options.print_real_names) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)

let strBvd = (fun bvd -> if (FStar_ST.read FStar_Options.print_real_names) then begin
(Prims.strcat bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText bvd.FStar_Absyn_Syntax.realname.FStar_Ident.idText)
end else begin
if ((FStar_ST.read FStar_Options.hide_genident_nums) && (FStar_Util.starts_with bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText "_")) then begin
(FStar_All.try_with (fun _30_106 -> (match (()) with
| () -> begin
(let _30_112 = (let _121_62 = (FStar_Util.substring_from bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText 1)
in (FStar_Util.int_of_string _121_62))
in "_?")
end)) (fun _30_105 -> (match (_30_105) with
| _30_109 -> begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end)))
end else begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end
end)

let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _30_3 -> (match (_30_3) with
| (_30_117, Some (FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _30_122 -> begin
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
| FStar_Const.Const_string (bytes, _30_136) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_30_140) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x) -> begin
x
end
| FStar_Const.Const_int64 (_30_145) -> begin
"<int64>"
end
| FStar_Const.Const_uint8 (_30_148) -> begin
"<uint8>"
end))

let rec tag_of_typ = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_30_152) -> begin
"Typ_btvar"
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(Prims.strcat "Typ_const " v.FStar_Absyn_Syntax.v.FStar_Ident.str)
end
| FStar_Absyn_Syntax.Typ_fun (_30_157) -> begin
"Typ_fun"
end
| FStar_Absyn_Syntax.Typ_refine (_30_160) -> begin
"Typ_refine"
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let _121_103 = (tag_of_typ head)
in (let _121_102 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.format2 "Typ_app(%s, [%s args])" _121_103 _121_102)))
end
| FStar_Absyn_Syntax.Typ_lam (_30_167) -> begin
"Typ_lam"
end
| FStar_Absyn_Syntax.Typ_ascribed (_30_170) -> begin
"Typ_ascribed"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_30_173)) -> begin
"Typ_meta_pattern"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_30_177)) -> begin
"Typ_meta_named"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_30_181)) -> begin
"Typ_meta_labeled"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_30_185)) -> begin
"Typ_meta_refresh_label"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_30_189)) -> begin
"Typ_meta_slack_formula"
end
| FStar_Absyn_Syntax.Typ_uvar (_30_193) -> begin
"Typ_uvar"
end
| FStar_Absyn_Syntax.Typ_delayed (_30_196) -> begin
"Typ_delayed"
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"Typ_unknown"
end))
and tag_of_exp = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_30_201) -> begin
"Exp_bvar"
end
| FStar_Absyn_Syntax.Exp_fvar (_30_204) -> begin
"Exp_fvar"
end
| FStar_Absyn_Syntax.Exp_constant (_30_207) -> begin
"Exp_constant"
end
| FStar_Absyn_Syntax.Exp_abs (_30_210) -> begin
"Exp_abs"
end
| FStar_Absyn_Syntax.Exp_app (_30_213) -> begin
"Exp_app"
end
| FStar_Absyn_Syntax.Exp_match (_30_216) -> begin
"Exp_match"
end
| FStar_Absyn_Syntax.Exp_ascribed (_30_219) -> begin
"Exp_ascribed"
end
| FStar_Absyn_Syntax.Exp_let (_30_222) -> begin
"Exp_let"
end
| FStar_Absyn_Syntax.Exp_uvar (_30_225) -> begin
"Exp_uvar"
end
| FStar_Absyn_Syntax.Exp_delayed (_30_228) -> begin
"Exp_delayed"
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_30_231, m)) -> begin
(let _121_107 = (meta_e_to_string m)
in (Prims.strcat "Exp_meta_desugared " _121_107))
end))
and meta_e_to_string = (fun _30_4 -> (match (_30_4) with
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
| FStar_Absyn_Syntax.Typ_delayed (_30_245) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_30_248, l)) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Typ_meta (meta) -> begin
(let _121_113 = (FStar_All.pipe_right meta meta_to_string)
in (FStar_Util.format1 "(Meta %s)" _121_113))
end
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(strBvd btv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(sli v.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_fun (binders, c) -> begin
(let _121_115 = (binders_to_string " -> " binders)
in (let _121_114 = (comp_typ_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _121_115 _121_114)))
end
| FStar_Absyn_Syntax.Typ_refine (xt, f) -> begin
(let _121_118 = (strBvd xt.FStar_Absyn_Syntax.v)
in (let _121_117 = (FStar_All.pipe_right xt.FStar_Absyn_Syntax.sort typ_to_string)
in (let _121_116 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "%s:%s{%s}" _121_118 _121_117 _121_116))))
end
| FStar_Absyn_Syntax.Typ_app (_30_268, []) -> begin
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
| _30_288 -> begin
(let _121_129 = (tag_of_typ t)
in (let _121_128 = (typ_to_string t)
in (FStar_Util.format2 "<Expected a type-lambda! got %s>%s" _121_129 _121_128)))
end))
end
| FStar_Util.Inr (e) -> begin
(let _121_130 = (exp_to_string e)
in (FStar_Util.format1 "(<Expected a type!>%s)" _121_130))
end))
in (let qbinder_to_string = (q_to_string (fun x -> (binder_to_string (Prims.fst x))))
in (let qbody_to_string = (q_to_string (fun x -> (typ_to_string (Prims.snd x))))
in (let args' = if ((FStar_ST.read FStar_Options.print_implicits) && (not ((is_quant t)))) then begin
args
end else begin
(FStar_List.filter (fun _30_5 -> (match (_30_5) with
| (_30_297, Some (FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _30_302 -> begin
true
end)) args)
end
in if ((is_ite t) && ((FStar_List.length args) = 3)) then begin
(let _121_141 = (let _121_136 = (FStar_List.nth args 0)
in (arg_to_string _121_136))
in (let _121_140 = (let _121_137 = (FStar_List.nth args 1)
in (arg_to_string _121_137))
in (let _121_139 = (let _121_138 = (FStar_List.nth args 2)
in (arg_to_string _121_138))
in (FStar_Util.format3 "if %s then %s else %s" _121_141 _121_140 _121_139))))
end else begin
if ((is_b2t t) && ((FStar_List.length args) = 1)) then begin
(let _121_142 = (FStar_List.nth args 0)
in (FStar_All.pipe_right _121_142 arg_to_string))
end else begin
if ((is_quant t) && ((FStar_List.length args) <= 2)) then begin
(let _121_147 = (quant_to_string t)
in (let _121_146 = (let _121_143 = (FStar_List.nth args' 0)
in (qbinder_to_string _121_143))
in (let _121_145 = (let _121_144 = (FStar_List.nth args' 0)
in (qbody_to_string _121_144))
in (FStar_Util.format3 "(%s (%s). %s)" _121_147 _121_146 _121_145))))
end else begin
if ((is_infix_type_op t) && ((FStar_List.length args') = 2)) then begin
(let _121_152 = (let _121_148 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _121_148 arg_to_string))
in (let _121_151 = (FStar_All.pipe_right t infix_type_op_to_string)
in (let _121_150 = (let _121_149 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _121_149 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _121_152 _121_151 _121_150))))
end else begin
if ((is_unary_type_op t) && ((FStar_List.length args') = 1)) then begin
(let _121_155 = (FStar_All.pipe_right t unary_type_op_to_string)
in (let _121_154 = (let _121_153 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _121_153 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _121_155 _121_154)))
end else begin
(let _121_157 = (FStar_All.pipe_right t typ_to_string)
in (let _121_156 = (FStar_All.pipe_right args args_to_string)
in (FStar_Util.format2 "(%s %s)" _121_157 _121_156)))
end
end
end
end
end))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(let _121_159 = (binders_to_string " " binders)
in (let _121_158 = (FStar_All.pipe_right t2 typ_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _121_159 _121_158)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _121_161 = (typ_to_string t)
in (let _121_160 = (kind_to_string k)
in (FStar_Util.format2 "(%s <: %s)" _121_161 _121_160)))
end else begin
(FStar_All.pipe_right t typ_to_string)
end
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"<UNKNOWN>"
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(match ((FStar_Absyn_Visit.compress_typ_aux false x)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_30_326); FStar_Absyn_Syntax.tk = _30_324; FStar_Absyn_Syntax.pos = _30_322; FStar_Absyn_Syntax.fvs = _30_320; FStar_Absyn_Syntax.uvs = _30_318} -> begin
(uvar_t_to_string (uv, k))
end
| t -> begin
(FStar_All.pipe_right t typ_to_string)
end)
end)))
and uvar_t_to_string = (fun _30_332 -> (match (_30_332) with
| (uv, k) -> begin
if (false && (FStar_ST.read FStar_Options.print_real_names)) then begin
(let _121_165 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _121_163 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _121_163))
end
in (let _121_164 = (kind_to_string k)
in (FStar_Util.format2 "(U%s : %s)" _121_165 _121_164)))
end else begin
(let _121_167 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _121_166 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _121_166))
end
in (FStar_Util.format1 "U%s" _121_167))
end
end))
and imp_to_string = (fun s _30_6 -> (match (_30_6) with
| Some (FStar_Absyn_Syntax.Implicit) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Absyn_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _30_340 -> begin
s
end))
and binder_to_string' = (fun is_arrow b -> (match (b) with
| (FStar_Util.Inl (a), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _121_172 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _121_172 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp a.FStar_Absyn_Syntax.v))) then begin
(kind_to_string a.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits)))) then begin
(let _121_173 = (strBvd a.FStar_Absyn_Syntax.v)
in (imp_to_string _121_173 imp))
end else begin
(let _121_177 = (let _121_176 = (let _121_174 = (strBvd a.FStar_Absyn_Syntax.v)
in (Prims.strcat _121_174 ":"))
in (let _121_175 = (kind_to_string a.FStar_Absyn_Syntax.sort)
in (Prims.strcat _121_176 _121_175)))
in (imp_to_string _121_177 imp))
end
end
end
| (FStar_Util.Inr (x), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _121_178 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _121_178 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp x.FStar_Absyn_Syntax.v))) then begin
(typ_to_string x.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits)))) then begin
(let _121_179 = (strBvd x.FStar_Absyn_Syntax.v)
in (imp_to_string _121_179 imp))
end else begin
(let _121_183 = (let _121_182 = (let _121_180 = (strBvd x.FStar_Absyn_Syntax.v)
in (Prims.strcat _121_180 ":"))
in (let _121_181 = (typ_to_string x.FStar_Absyn_Syntax.sort)
in (Prims.strcat _121_182 _121_181)))
in (imp_to_string _121_183 imp))
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
(let _121_188 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _121_188 (FStar_String.concat sep)))
end else begin
(let _121_189 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _121_189 (FStar_String.concat sep)))
end))
and arg_to_string = (fun _30_7 -> (match (_30_7) with
| (FStar_Util.Inl (a), imp) -> begin
(let _121_191 = (typ_to_string a)
in (imp_to_string _121_191 imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _121_192 = (exp_to_string x)
in (imp_to_string _121_192 imp))
end))
and args_to_string = (fun args -> (let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _121_194 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _121_194 (FStar_String.concat " ")))))
and lcomp_typ_to_string = (fun lc -> (let _121_197 = (sli lc.FStar_Absyn_Syntax.eff_name)
in (let _121_196 = (typ_to_string lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _121_197 _121_196))))
and comp_typ_to_string = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _121_199 = (typ_to_string t)
in (FStar_Util.format1 "Tot %s" _121_199))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(let basic = if ((FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _30_8 -> (match (_30_8) with
| FStar_Absyn_Syntax.TOTAL -> begin
true
end
| _30_376 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args)))) then begin
(let _121_201 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _121_201))
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_Ident.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid)) then begin
(typ_to_string c.FStar_Absyn_Syntax.result_typ)
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _30_9 -> (match (_30_9) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _30_380 -> begin
false
end))))) then begin
(let _121_203 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _121_203))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _121_207 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _121_206 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (let _121_205 = (let _121_204 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.effect_args (FStar_List.map effect_arg_to_string))
in (FStar_All.pipe_right _121_204 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _121_207 _121_206 _121_205))))
end else begin
(let _121_209 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _121_208 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _121_209 _121_208)))
end
end
end
end
in (let dec = (let _121_213 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.collect (fun _30_10 -> (match (_30_10) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _121_212 = (let _121_211 = (exp_to_string e)
in (FStar_Util.format1 " (decreases %s)" _121_211))
in (_121_212)::[])
end
| _30_386 -> begin
[]
end))))
in (FStar_All.pipe_right _121_213 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and effect_arg_to_string = (fun e -> (match (e) with
| (FStar_Util.Inr (e), _30_392) -> begin
(exp_to_string e)
end
| (FStar_Util.Inl (wp), _30_397) -> begin
(formula_to_string wp)
end))
and formula_to_string = (fun phi -> (typ_to_string phi))
and formula_to_string_old_now_unused = (fun phi -> (let const_op = (fun f _30_403 -> f)
in (let un_op = (fun f _30_11 -> (match (_30_11) with
| (FStar_Util.Inl (t), _30_411)::[] -> begin
(let _121_225 = (formula_to_string t)
in (FStar_Util.format2 "%s %s" f _121_225))
end
| _30_415 -> begin
(FStar_All.failwith "impos")
end))
in (let bin_top = (fun f _30_12 -> (match (_30_12) with
| (FStar_Util.Inl (t1), _30_427)::(FStar_Util.Inl (t2), _30_422)::[] -> begin
(let _121_231 = (formula_to_string t1)
in (let _121_230 = (formula_to_string t2)
in (FStar_Util.format3 "%s %s %s" _121_231 f _121_230)))
end
| _30_431 -> begin
(FStar_All.failwith "Impos")
end))
in (let bin_eop = (fun f _30_13 -> (match (_30_13) with
| (FStar_Util.Inr (e1), _30_443)::(FStar_Util.Inr (e2), _30_438)::[] -> begin
(let _121_237 = (exp_to_string e1)
in (let _121_236 = (exp_to_string e2)
in (FStar_Util.format3 "%s %s %s" _121_237 f _121_236)))
end
| _30_447 -> begin
(FStar_All.failwith "impos")
end))
in (let ite = (fun _30_14 -> (match (_30_14) with
| (FStar_Util.Inl (t1), _30_462)::(FStar_Util.Inl (t2), _30_457)::(FStar_Util.Inl (t3), _30_452)::[] -> begin
(let _121_242 = (formula_to_string t1)
in (let _121_241 = (formula_to_string t2)
in (let _121_240 = (formula_to_string t3)
in (FStar_Util.format3 "if %s then %s else %s" _121_242 _121_241 _121_240))))
end
| _30_466 -> begin
(FStar_All.failwith "impos")
end))
in (let eq_op = (fun _30_15 -> (match (_30_15) with
| (FStar_Util.Inl (t1), _30_487)::(FStar_Util.Inl (t2), _30_482)::(FStar_Util.Inr (e1), _30_477)::(FStar_Util.Inr (e2), _30_472)::[] -> begin
if (FStar_ST.read FStar_Options.print_implicits) then begin
(let _121_248 = (typ_to_string t1)
in (let _121_247 = (typ_to_string t2)
in (let _121_246 = (exp_to_string e1)
in (let _121_245 = (exp_to_string e2)
in (FStar_Util.format4 "Eq2 %s %s %s %s" _121_248 _121_247 _121_246 _121_245)))))
end else begin
(let _121_250 = (exp_to_string e1)
in (let _121_249 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _121_250 _121_249)))
end
end
| (FStar_Util.Inr (e1), _30_498)::(FStar_Util.Inr (e2), _30_493)::[] -> begin
(let _121_252 = (exp_to_string e1)
in (let _121_251 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _121_252 _121_251)))
end
| _30_502 -> begin
(FStar_All.failwith "Impossible")
end))
in (let connectives = ((FStar_Absyn_Const.and_lid, (bin_top "/\\")))::((FStar_Absyn_Const.or_lid, (bin_top "\\/")))::((FStar_Absyn_Const.imp_lid, (bin_top "==>")))::((FStar_Absyn_Const.iff_lid, (bin_top "<==>")))::((FStar_Absyn_Const.ite_lid, ite))::((FStar_Absyn_Const.not_lid, (un_op "~")))::((FStar_Absyn_Const.eqT_lid, (bin_top "==")))::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op "True")))::((FStar_Absyn_Const.false_lid, (const_op "False")))::[]
in (let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (binders, phi) -> begin
(let _121_291 = (binders_to_string " " binders)
in (let _121_290 = (formula_to_string phi)
in (FStar_Util.format2 "(fun %s => %s)" _121_291 _121_290)))
end
| _30_512 -> begin
(typ_to_string phi)
end))
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _30_522 -> (match (_30_522) with
| (l, _30_521) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_30_525, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, _30_531, body)) -> begin
(let _121_309 = (binders_to_string " " vars)
in (let _121_308 = (formula_to_string body)
in (FStar_Util.format2 "(forall %s. %s)" _121_309 _121_308)))
end
| Some (FStar_Absyn_Util.QEx (vars, _30_538, body)) -> begin
(let _121_311 = (binders_to_string " " vars)
in (let _121_310 = (formula_to_string body)
in (FStar_Util.format2 "(exists %s. %s)" _121_311 _121_310)))
end))))))))))
and exp_to_string = (fun x -> (match ((let _121_313 = (FStar_Absyn_Util.compress_exp x)
in _121_313.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_delayed (_30_545) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _30_549)) -> begin
(exp_to_string e)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(uvar_e_to_string (uv, t))
end
| FStar_Absyn_Syntax.Exp_bvar (bvv) -> begin
(strBvd bvv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_fvar (fv, _30_561) -> begin
(sli fv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(FStar_All.pipe_right c const_to_string)
end
| FStar_Absyn_Syntax.Exp_abs (binders, e) -> begin
(let _121_315 = (binders_to_string " " binders)
in (let _121_314 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _121_315 _121_314)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(let lex = if (FStar_ST.read FStar_Options.print_implicits) then begin
None
end else begin
(reconstruct_lex x)
end
in (match (lex) with
| Some (es) -> begin
(let _121_318 = (let _121_317 = (let _121_316 = (FStar_List.map exp_to_string es)
in (FStar_String.concat "; " _121_316))
in (Prims.strcat "%[" _121_317))
in (Prims.strcat _121_318 "]"))
end
| None -> begin
(let args' = (let _121_320 = (filter_imp args)
in (FStar_All.pipe_right _121_320 (FStar_List.filter (fun _30_16 -> (match (_30_16) with
| (FStar_Util.Inr (_30_580), _30_583) -> begin
true
end
| _30_586 -> begin
false
end)))))
in if ((is_infix_prim_op e) && ((FStar_List.length args') = 2)) then begin
(let _121_325 = (let _121_321 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _121_321 arg_to_string))
in (let _121_324 = (FStar_All.pipe_right e infix_prim_op_to_string)
in (let _121_323 = (let _121_322 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _121_322 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _121_325 _121_324 _121_323))))
end else begin
if ((is_unary_prim_op e) && ((FStar_List.length args') = 1)) then begin
(let _121_328 = (FStar_All.pipe_right e unary_prim_op_to_string)
in (let _121_327 = (let _121_326 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _121_326 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _121_328 _121_327)))
end else begin
(let _121_330 = (FStar_All.pipe_right e exp_to_string)
in (let _121_329 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _121_330 _121_329)))
end
end)
end))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _121_338 = (FStar_All.pipe_right e exp_to_string)
in (let _121_337 = (let _121_336 = (FStar_All.pipe_right pats (FStar_List.map (fun _30_595 -> (match (_30_595) with
| (p, wopt, e) -> begin
(let _121_335 = (FStar_All.pipe_right p pat_to_string)
in (let _121_334 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _121_332 = (FStar_All.pipe_right w exp_to_string)
in (FStar_Util.format1 "when %s" _121_332))
end)
in (let _121_333 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format3 "%s %s -> %s" _121_335 _121_334 _121_333))))
end))))
in (FStar_Util.concat_l "\n\t" _121_336))
in (FStar_Util.format2 "(match %s with %s)" _121_338 _121_337)))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _30_602) -> begin
(let _121_340 = (FStar_All.pipe_right e exp_to_string)
in (let _121_339 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "(%s:%s)" _121_340 _121_339)))
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(let _121_342 = (lbs_to_string lbs)
in (let _121_341 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "%s in %s" _121_342 _121_341)))
end))
and uvar_e_to_string = (fun _30_612 -> (match (_30_612) with
| (uv, _30_611) -> begin
(let _121_345 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _121_344 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _121_344))
end
in (Prims.strcat "\'e" _121_345))
end))
and lbs_to_string = (fun lbs -> (let _121_352 = (let _121_351 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _121_350 = (lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _121_349 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbtyp typ_to_string)
in (let _121_348 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbdef exp_to_string)
in (FStar_Util.format3 "%s:%s = %s" _121_350 _121_349 _121_348)))))))
in (FStar_Util.concat_l "\n and " _121_351))
in (FStar_Util.format2 "let %s %s" (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _121_352)))
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
and either_l_to_string = (fun delim l -> (let _121_357 = (FStar_All.pipe_right l (FStar_List.map either_to_string))
in (FStar_All.pipe_right _121_357 (FStar_Util.concat_l delim))))
and meta_to_string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Meta_refresh_label (t, _30_630, _30_632) -> begin
(let _121_359 = (typ_to_string t)
in (FStar_Util.format1 "(refresh) %s" _121_359))
end
| FStar_Absyn_Syntax.Meta_labeled (t, l, _30_638, _30_640) -> begin
(let _121_360 = (typ_to_string t)
in (FStar_Util.format2 "(labeled \"%s\") %s" l _121_360))
end
| FStar_Absyn_Syntax.Meta_named (_30_644, l) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Meta_pattern (t, ps) -> begin
(let _121_362 = (pats_to_string ps)
in (let _121_361 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "{:pattern %s} %s" _121_362 _121_361)))
end
| FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _30_655) -> begin
(let _121_364 = (formula_to_string t1)
in (let _121_363 = (formula_to_string t2)
in (FStar_Util.format2 "%s /\\ %s" _121_364 _121_363)))
end))
and pats_to_string = (fun ps -> (let _121_368 = (FStar_All.pipe_right ps (FStar_List.map (fun e -> (let _121_367 = (FStar_All.pipe_right e (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _121_367 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _121_368 (FStar_String.concat " \\/ "))))
and kind_to_string = (fun x -> (match ((let _121_370 = (FStar_Absyn_Util.compress_kind x)
in _121_370.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_lam (_30_662) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Kind_delayed (_30_665) -> begin
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
(let _121_372 = (sli n)
in (let _121_371 = (args_to_string args)
in (FStar_Util.format2 "%s %s" _121_372 _121_371)))
end
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(let _121_374 = (binders_to_string " -> " binders)
in (let _121_373 = (FStar_All.pipe_right k kind_to_string)
in (FStar_Util.format2 "(%s -> %s)" _121_374 _121_373)))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun uv -> (let _121_376 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _121_375 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _121_375))
end
in (Prims.strcat "\'k_" _121_376)))
and uvar_k_to_string' = (fun _30_687 -> (match (_30_687) with
| (uv, args) -> begin
(let str = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _121_378 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _121_378))
end
in (let _121_379 = (args_to_string args)
in (FStar_Util.format2 "(\'k_%s %s)" str _121_379)))
end))
and pat_to_string = (fun x -> (match (x.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (l, _30_692, pats) -> begin
(let _121_384 = (sli l.FStar_Absyn_Syntax.v)
in (let _121_383 = (let _121_382 = (FStar_List.map (fun _30_698 -> (match (_30_698) with
| (x, b) -> begin
(let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _121_382 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _121_384 _121_383)))
end
| FStar_Absyn_Syntax.Pat_dot_term (x, _30_702) -> begin
(let _121_385 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".%s" _121_385))
end
| FStar_Absyn_Syntax.Pat_dot_typ (x, _30_707) -> begin
(let _121_386 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".\'%s" _121_386))
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
| FStar_Absyn_Syntax.Pat_wild (_30_717) -> begin
"_"
end
| FStar_Absyn_Syntax.Pat_twild (_30_720) -> begin
"\'_"
end
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(let _121_387 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _121_387))
end))

let subst_to_string = (fun subst -> (let _121_395 = (let _121_394 = (FStar_List.map (fun _30_17 -> (match (_30_17) with
| FStar_Util.Inl (a, t) -> begin
(let _121_391 = (strBvd a)
in (let _121_390 = (typ_to_string t)
in (FStar_Util.format2 "(%s -> %s)" _121_391 _121_390)))
end
| FStar_Util.Inr (x, e) -> begin
(let _121_393 = (strBvd x)
in (let _121_392 = (exp_to_string e)
in (FStar_Util.format2 "(%s -> %s)" _121_393 _121_392)))
end)) subst)
in (FStar_All.pipe_right _121_394 (FStar_String.concat ", ")))
in (FStar_All.pipe_left (FStar_Util.format1 "{%s}") _121_395)))

let freevars_to_string = (fun fvs -> (let f = (fun l -> (let _121_401 = (let _121_400 = (FStar_All.pipe_right l FStar_Util.set_elements)
in (FStar_All.pipe_right _121_400 (FStar_List.map (fun t -> (strBvd t.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _121_401 (FStar_String.concat ", "))))
in (let _121_403 = (f fvs.FStar_Absyn_Syntax.ftvs)
in (let _121_402 = (f fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_Util.format2 "ftvs={%s}, fxvs={%s}" _121_403 _121_402)))))

let qual_to_string = (fun _30_18 -> (match (_30_18) with
| FStar_Absyn_Syntax.Logic -> begin
"logic"
end
| FStar_Absyn_Syntax.Opaque -> begin
"opaque"
end
| FStar_Absyn_Syntax.Discriminator (_30_744) -> begin
"discriminator"
end
| FStar_Absyn_Syntax.Projector (_30_747) -> begin
"projector"
end
| FStar_Absyn_Syntax.RecordType (ids) -> begin
(let _121_408 = (let _121_407 = (FStar_All.pipe_right ids (FStar_List.map (fun lid -> lid.FStar_Ident.ident.FStar_Ident.idText)))
in (FStar_All.pipe_right _121_407 (FStar_String.concat ", ")))
in (FStar_Util.format1 "record(%s)" _121_408))
end
| _30_753 -> begin
"other"
end))

let quals_to_string = (fun quals -> (let _121_411 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _121_411 (FStar_String.concat " "))))

let rec sigelt_to_string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.ResetOptions, _30_758) -> begin
"#reset-options"
end
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.SetOptions (s), _30_764) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _30_771, _30_773, quals, _30_776) -> begin
(let _121_416 = (quals_to_string quals)
in (let _121_415 = (binders_to_string " " tps)
in (let _121_414 = (kind_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _121_416 lid.FStar_Ident.str _121_415 _121_414))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, _30_784, _30_786) -> begin
(let _121_419 = (binders_to_string " " tps)
in (let _121_418 = (kind_to_string k)
in (let _121_417 = (typ_to_string t)
in (FStar_Util.format4 "type %s %s : %s = %s" lid.FStar_Ident.str _121_419 _121_418 _121_417))))
end
| FStar_Absyn_Syntax.Sig_datacon (lid, t, _30_792, _30_794, _30_796, _30_798) -> begin
(let _121_420 = (typ_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _121_420))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _30_805) -> begin
(let _121_422 = (quals_to_string quals)
in (let _121_421 = (typ_to_string t)
in (FStar_Util.format3 "%s val %s : %s" _121_422 lid.FStar_Ident.str _121_421)))
end
| FStar_Absyn_Syntax.Sig_assume (lid, f, _30_811, _30_813) -> begin
(let _121_423 = (typ_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _121_423))
end
| FStar_Absyn_Syntax.Sig_let (lbs, _30_818, _30_820, b) -> begin
(lbs_to_string lbs)
end
| FStar_Absyn_Syntax.Sig_main (e, _30_826) -> begin
(let _121_424 = (exp_to_string e)
in (FStar_Util.format1 "let _ = %s" _121_424))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _30_831, _30_833, _30_835) -> begin
(let _121_425 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _121_425 (FStar_String.concat "\n")))
end
| FStar_Absyn_Syntax.Sig_new_effect (_30_839) -> begin
"new_effect { ... }"
end
| FStar_Absyn_Syntax.Sig_sub_effect (_30_842) -> begin
"sub_effect ..."
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_30_845) -> begin
"kind ..."
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, tps, c, _30_851, _30_853) -> begin
(let _121_428 = (sli l)
in (let _121_427 = (binders_to_string " " tps)
in (let _121_426 = (comp_typ_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _121_428 _121_427 _121_426))))
end))

let format_error = (fun r msg -> (let _121_433 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _121_433 msg)))

let rec sigelt_to_string_short = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_let ((_30_860, {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _30_864; FStar_Absyn_Syntax.lbdef = _30_862}::[]), _30_872, _30_874, _30_876) -> begin
(let _121_436 = (typ_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Ident.str _121_436))
end
| _30_880 -> begin
(let _121_439 = (let _121_438 = (FStar_Absyn_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _121_438 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _121_439 (FStar_String.concat ", ")))
end))

let rec modul_to_string = (fun m -> (let _121_444 = (sli m.FStar_Absyn_Syntax.name)
in (let _121_443 = (let _121_442 = (FStar_List.map sigelt_to_string m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _121_442 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _121_444 _121_443))))




