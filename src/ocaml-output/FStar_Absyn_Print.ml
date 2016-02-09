
open Prims
let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.op_Addition, "+"))::((FStar_Absyn_Const.op_Subtraction, "-"))::((FStar_Absyn_Const.op_Multiply, "*"))::((FStar_Absyn_Const.op_Division, "/"))::((FStar_Absyn_Const.op_Eq, "="))::((FStar_Absyn_Const.op_ColonEq, ":="))::((FStar_Absyn_Const.op_notEq, "<>"))::((FStar_Absyn_Const.op_And, "&&"))::((FStar_Absyn_Const.op_Or, "||"))::((FStar_Absyn_Const.op_LTE, "<="))::((FStar_Absyn_Const.op_GTE, ">="))::((FStar_Absyn_Const.op_LT, "<"))::((FStar_Absyn_Const.op_GT, ">"))::((FStar_Absyn_Const.op_Modulus, "mod"))::[]

let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.op_Negation, "not"))::((FStar_Absyn_Const.op_Minus, "-"))::[]

let infix_type_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.and_lid, "/\\"))::((FStar_Absyn_Const.or_lid, "\\/"))::((FStar_Absyn_Const.imp_lid, "==>"))::((FStar_Absyn_Const.iff_lid, "<==>"))::((FStar_Absyn_Const.precedes_lid, "<<"))::((FStar_Absyn_Const.eq2_lid, "=="))::((FStar_Absyn_Const.eqT_lid, "=="))::[]

let unary_type_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.not_lid, "~"))::[]

let is_prim_op = (fun ps f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _29_23) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _29_27 -> begin
false
end))

let is_type_op = (fun ps t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals ftv.FStar_Absyn_Syntax.v)))
end
| _29_33 -> begin
false
end))

let get_lid = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _29_37) -> begin
fv.FStar_Absyn_Syntax.v
end
| _29_41 -> begin
(FStar_All.failwith "get_lid")
end))

let get_type_lid = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
ftv.FStar_Absyn_Syntax.v
end
| _29_46 -> begin
(FStar_All.failwith "get_type_lid")
end))

let is_infix_prim_op : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split infix_prim_ops)) e))

let is_unary_prim_op : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split unary_prim_ops)) e))

let is_infix_type_op : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op (Prims.fst (FStar_List.split infix_type_ops)) t))

let is_unary_type_op : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op (Prims.fst (FStar_List.split unary_type_ops)) t))

let quants : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.forall_lid, "forall"))::((FStar_Absyn_Const.exists_lid, "exists"))::((FStar_Absyn_Const.allTyp_lid, "forall"))::((FStar_Absyn_Const.exTyp_lid, "exists"))::[]

let is_b2t : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op ((FStar_Absyn_Const.b2t_lid)::[]) t))

let is_quant : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op (Prims.fst (FStar_List.split quants)) t))

let is_ite : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op ((FStar_Absyn_Const.ite_lid)::[]) t))

let is_lex_cons : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Absyn_Const.lexcons_lid)::[]) f))

let is_lex_top : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Absyn_Const.lextop_lid)::[]) f))

let is_inr = (fun _29_1 -> (match (_29_1) with
| FStar_Util.Inl (_29_58) -> begin
false
end
| FStar_Util.Inr (_29_61) -> begin
true
end))

let rec reconstruct_lex : FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _131_28 = (FStar_Absyn_Util.compress_exp e)
in _131_28.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (f, args) -> begin
(let args = (FStar_List.filter (fun a -> (((Prims.snd a) <> Some (FStar_Absyn_Syntax.Implicit)) && (is_inr (Prims.fst a)))) args)
in (let exps = (FStar_List.map (fun _29_2 -> (match (_29_2) with
| (FStar_Util.Inl (_29_72), _29_75) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Util.Inr (x), _29_80) -> begin
x
end)) args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = 2)) then begin
(match ((let _131_31 = (FStar_List.nth exps 1)
in (reconstruct_lex _131_31))) with
| Some (xs) -> begin
(let _131_33 = (let _131_32 = (FStar_List.nth exps 0)
in (_131_32)::xs)
in Some (_131_33))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _29_87 -> begin
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

let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _131_47 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _131_47)))

let infix_prim_op_to_string = (fun e -> (let _131_49 = (get_lid e)
in (find_lid _131_49 infix_prim_ops)))

let unary_prim_op_to_string = (fun e -> (let _131_51 = (get_lid e)
in (find_lid _131_51 unary_prim_ops)))

let infix_type_op_to_string = (fun t -> (let _131_53 = (get_type_lid t)
in (find_lid _131_53 infix_type_ops)))

let unary_type_op_to_string = (fun t -> (let _131_55 = (get_type_lid t)
in (find_lid _131_55 unary_type_ops)))

let quant_to_string = (fun t -> (let _131_57 = (get_type_lid t)
in (find_lid _131_57 quants)))

let rec sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_ST.read FStar_Options.print_real_names) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)

let strBvd = (fun bvd -> if (FStar_ST.read FStar_Options.print_real_names) then begin
(Prims.strcat bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText bvd.FStar_Absyn_Syntax.realname.FStar_Ident.idText)
end else begin
if ((FStar_ST.read FStar_Options.hide_genident_nums) && (FStar_Util.starts_with bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText "_")) then begin
(FStar_All.try_with (fun _29_106 -> (match (()) with
| () -> begin
(let _29_112 = (let _131_62 = (FStar_Util.substring_from bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText 1)
in (FStar_Util.int_of_string _131_62))
in "_?")
end)) (fun _29_105 -> (match (_29_105) with
| _29_109 -> begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end)))
end else begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end
end)

let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _29_3 -> (match (_29_3) with
| (_29_117, Some (FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _29_122 -> begin
true
end)))))

let const_to_string : FStar_Const.sconst  ->  Prims.string = (fun x -> (match (x) with
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
| FStar_Const.Const_string (bytes, _29_136) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_29_140) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x) -> begin
x
end
| FStar_Const.Const_int64 (_29_145) -> begin
"<int64>"
end
| FStar_Const.Const_uint8 (_29_148) -> begin
"<uint8>"
end))

let rec tag_of_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_29_152) -> begin
"Typ_btvar"
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(Prims.strcat "Typ_const " v.FStar_Absyn_Syntax.v.FStar_Ident.str)
end
| FStar_Absyn_Syntax.Typ_fun (_29_157) -> begin
"Typ_fun"
end
| FStar_Absyn_Syntax.Typ_refine (_29_160) -> begin
"Typ_refine"
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let _131_103 = (tag_of_typ head)
in (let _131_102 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.format2 "Typ_app(%s, [%s args])" _131_103 _131_102)))
end
| FStar_Absyn_Syntax.Typ_lam (_29_167) -> begin
"Typ_lam"
end
| FStar_Absyn_Syntax.Typ_ascribed (_29_170) -> begin
"Typ_ascribed"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_29_173)) -> begin
"Typ_meta_pattern"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_29_177)) -> begin
"Typ_meta_named"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_29_181)) -> begin
"Typ_meta_labeled"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_29_185)) -> begin
"Typ_meta_refresh_label"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_29_189)) -> begin
"Typ_meta_slack_formula"
end
| FStar_Absyn_Syntax.Typ_uvar (_29_193) -> begin
"Typ_uvar"
end
| FStar_Absyn_Syntax.Typ_delayed (_29_196) -> begin
"Typ_delayed"
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"Typ_unknown"
end))
and tag_of_exp = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_29_201) -> begin
"Exp_bvar"
end
| FStar_Absyn_Syntax.Exp_fvar (_29_204) -> begin
"Exp_fvar"
end
| FStar_Absyn_Syntax.Exp_constant (_29_207) -> begin
"Exp_constant"
end
| FStar_Absyn_Syntax.Exp_abs (_29_210) -> begin
"Exp_abs"
end
| FStar_Absyn_Syntax.Exp_app (_29_213) -> begin
"Exp_app"
end
| FStar_Absyn_Syntax.Exp_match (_29_216) -> begin
"Exp_match"
end
| FStar_Absyn_Syntax.Exp_ascribed (_29_219) -> begin
"Exp_ascribed"
end
| FStar_Absyn_Syntax.Exp_let (_29_222) -> begin
"Exp_let"
end
| FStar_Absyn_Syntax.Exp_uvar (_29_225) -> begin
"Exp_uvar"
end
| FStar_Absyn_Syntax.Exp_delayed (_29_228) -> begin
"Exp_delayed"
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_29_231, m)) -> begin
(let _131_107 = (meta_e_to_string m)
in (Prims.strcat "Exp_meta_desugared " _131_107))
end))
and meta_e_to_string : FStar_Absyn_Syntax.meta_source_info  ->  Prims.string = (fun _29_4 -> (match (_29_4) with
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
and typ_to_string : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun x -> (let x = (FStar_Absyn_Util.compress_typ x)
in (match (x.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_29_245) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_29_248, l)) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Typ_meta (meta) -> begin
(let _131_113 = (FStar_All.pipe_right meta meta_to_string)
in (FStar_Util.format1 "(Meta %s)" _131_113))
end
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(strBvd btv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(sli v.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_fun (binders, c) -> begin
(let _131_115 = (binders_to_string " -> " binders)
in (let _131_114 = (comp_typ_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _131_115 _131_114)))
end
| FStar_Absyn_Syntax.Typ_refine (xt, f) -> begin
(let _131_118 = (strBvd xt.FStar_Absyn_Syntax.v)
in (let _131_117 = (FStar_All.pipe_right xt.FStar_Absyn_Syntax.sort typ_to_string)
in (let _131_116 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "%s:%s{%s}" _131_118 _131_117 _131_116))))
end
| FStar_Absyn_Syntax.Typ_app (_29_268, []) -> begin
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
| _29_288 -> begin
(let _131_129 = (tag_of_typ t)
in (let _131_128 = (typ_to_string t)
in (FStar_Util.format2 "<Expected a type-lambda! got %s>%s" _131_129 _131_128)))
end))
end
| FStar_Util.Inr (e) -> begin
(let _131_130 = (exp_to_string e)
in (FStar_Util.format1 "(<Expected a type!>%s)" _131_130))
end))
in (let qbinder_to_string = (q_to_string (fun x -> (binder_to_string (Prims.fst x))))
in (let qbody_to_string = (q_to_string (fun x -> (typ_to_string (Prims.snd x))))
in (let args' = if ((FStar_ST.read FStar_Options.print_implicits) && (not ((is_quant t)))) then begin
args
end else begin
(FStar_List.filter (fun _29_5 -> (match (_29_5) with
| (_29_297, Some (FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _29_302 -> begin
true
end)) args)
end
in if ((is_ite t) && ((FStar_List.length args) = 3)) then begin
(let _131_141 = (let _131_136 = (FStar_List.nth args 0)
in (arg_to_string _131_136))
in (let _131_140 = (let _131_137 = (FStar_List.nth args 1)
in (arg_to_string _131_137))
in (let _131_139 = (let _131_138 = (FStar_List.nth args 2)
in (arg_to_string _131_138))
in (FStar_Util.format3 "if %s then %s else %s" _131_141 _131_140 _131_139))))
end else begin
if ((is_b2t t) && ((FStar_List.length args) = 1)) then begin
(let _131_142 = (FStar_List.nth args 0)
in (FStar_All.pipe_right _131_142 arg_to_string))
end else begin
if ((is_quant t) && ((FStar_List.length args) <= 2)) then begin
(let _131_147 = (quant_to_string t)
in (let _131_146 = (let _131_143 = (FStar_List.nth args' 0)
in (qbinder_to_string _131_143))
in (let _131_145 = (let _131_144 = (FStar_List.nth args' 0)
in (qbody_to_string _131_144))
in (FStar_Util.format3 "(%s (%s). %s)" _131_147 _131_146 _131_145))))
end else begin
if ((is_infix_type_op t) && ((FStar_List.length args') = 2)) then begin
(let _131_152 = (let _131_148 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _131_148 arg_to_string))
in (let _131_151 = (FStar_All.pipe_right t infix_type_op_to_string)
in (let _131_150 = (let _131_149 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _131_149 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _131_152 _131_151 _131_150))))
end else begin
if ((is_unary_type_op t) && ((FStar_List.length args') = 1)) then begin
(let _131_155 = (FStar_All.pipe_right t unary_type_op_to_string)
in (let _131_154 = (let _131_153 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _131_153 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _131_155 _131_154)))
end else begin
(let _131_157 = (FStar_All.pipe_right t typ_to_string)
in (let _131_156 = (FStar_All.pipe_right args args_to_string)
in (FStar_Util.format2 "(%s %s)" _131_157 _131_156)))
end
end
end
end
end))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(let _131_159 = (binders_to_string " " binders)
in (let _131_158 = (FStar_All.pipe_right t2 typ_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _131_159 _131_158)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _131_161 = (typ_to_string t)
in (let _131_160 = (kind_to_string k)
in (FStar_Util.format2 "(%s <: %s)" _131_161 _131_160)))
end else begin
(FStar_All.pipe_right t typ_to_string)
end
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"<UNKNOWN>"
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(match ((FStar_Absyn_Visit.compress_typ_aux false x)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_29_326); FStar_Absyn_Syntax.tk = _29_324; FStar_Absyn_Syntax.pos = _29_322; FStar_Absyn_Syntax.fvs = _29_320; FStar_Absyn_Syntax.uvs = _29_318} -> begin
(uvar_t_to_string (uv, k))
end
| t -> begin
(FStar_All.pipe_right t typ_to_string)
end)
end)))
and uvar_t_to_string : (FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd)  ->  Prims.string = (fun _29_332 -> (match (_29_332) with
| (uv, k) -> begin
if (false && (FStar_ST.read FStar_Options.print_real_names)) then begin
(let _131_165 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _131_163 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _131_163))
end
in (let _131_164 = (kind_to_string k)
in (FStar_Util.format2 "(U%s : %s)" _131_165 _131_164)))
end else begin
(let _131_167 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _131_166 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _131_166))
end
in (FStar_Util.format1 "U%s" _131_167))
end
end))
and imp_to_string : Prims.string  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s _29_6 -> (match (_29_6) with
| Some (FStar_Absyn_Syntax.Implicit) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Absyn_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _29_340 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (match (b) with
| (FStar_Util.Inl (a), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _131_172 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _131_172 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp a.FStar_Absyn_Syntax.v))) then begin
(kind_to_string a.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits)))) then begin
(let _131_173 = (strBvd a.FStar_Absyn_Syntax.v)
in (imp_to_string _131_173 imp))
end else begin
(let _131_177 = (let _131_176 = (let _131_174 = (strBvd a.FStar_Absyn_Syntax.v)
in (Prims.strcat _131_174 ":"))
in (let _131_175 = (kind_to_string a.FStar_Absyn_Syntax.sort)
in (Prims.strcat _131_176 _131_175)))
in (imp_to_string _131_177 imp))
end
end
end
| (FStar_Util.Inr (x), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _131_178 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _131_178 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp x.FStar_Absyn_Syntax.v))) then begin
(typ_to_string x.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits)))) then begin
(let _131_179 = (strBvd x.FStar_Absyn_Syntax.v)
in (imp_to_string _131_179 imp))
end else begin
(let _131_183 = (let _131_182 = (let _131_180 = (strBvd x.FStar_Absyn_Syntax.v)
in (Prims.strcat _131_180 ":"))
in (let _131_181 = (typ_to_string x.FStar_Absyn_Syntax.sort)
in (Prims.strcat _131_182 _131_181)))
in (imp_to_string _131_183 imp))
end
end
end))
and binder_to_string : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Absyn_Syntax.binders  ->  Prims.string = (fun sep bs -> (let bs = if (FStar_ST.read FStar_Options.print_implicits) then begin
bs
end else begin
(filter_imp bs)
end
in if (sep = " -> ") then begin
(let _131_188 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _131_188 (FStar_String.concat sep)))
end else begin
(let _131_189 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _131_189 (FStar_String.concat sep)))
end))
and arg_to_string : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _29_7 -> (match (_29_7) with
| (FStar_Util.Inl (a), imp) -> begin
(let _131_191 = (typ_to_string a)
in (imp_to_string _131_191 imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _131_192 = (exp_to_string x)
in (imp_to_string _131_192 imp))
end))
and args_to_string : FStar_Absyn_Syntax.args  ->  Prims.string = (fun args -> (let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _131_194 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _131_194 (FStar_String.concat " ")))))
and lcomp_typ_to_string : FStar_Absyn_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _131_197 = (sli lc.FStar_Absyn_Syntax.eff_name)
in (let _131_196 = (typ_to_string lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _131_197 _131_196))))
and comp_typ_to_string : FStar_Absyn_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _131_199 = (typ_to_string t)
in (FStar_Util.format1 "Tot %s" _131_199))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(let basic = if ((FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _29_8 -> (match (_29_8) with
| FStar_Absyn_Syntax.TOTAL -> begin
true
end
| _29_376 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args)))) then begin
(let _131_201 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _131_201))
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_Ident.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid)) then begin
(typ_to_string c.FStar_Absyn_Syntax.result_typ)
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _29_9 -> (match (_29_9) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _29_380 -> begin
false
end))))) then begin
(let _131_203 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _131_203))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _131_207 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _131_206 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (let _131_205 = (let _131_204 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.effect_args (FStar_List.map effect_arg_to_string))
in (FStar_All.pipe_right _131_204 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _131_207 _131_206 _131_205))))
end else begin
(let _131_209 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _131_208 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _131_209 _131_208)))
end
end
end
end
in (let dec = (let _131_213 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.collect (fun _29_10 -> (match (_29_10) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _131_212 = (let _131_211 = (exp_to_string e)
in (FStar_Util.format1 " (decreases %s)" _131_211))
in (_131_212)::[])
end
| _29_386 -> begin
[]
end))))
in (FStar_All.pipe_right _131_213 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and effect_arg_to_string : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun e -> (match (e) with
| (FStar_Util.Inr (e), _29_392) -> begin
(exp_to_string e)
end
| (FStar_Util.Inl (wp), _29_397) -> begin
(formula_to_string wp)
end))
and formula_to_string : FStar_Absyn_Syntax.typ  ->  Prims.string = (fun phi -> (typ_to_string phi))
and formula_to_string_old_now_unused : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun phi -> (let const_op = (fun f _29_403 -> f)
in (let un_op = (fun f _29_11 -> (match (_29_11) with
| (FStar_Util.Inl (t), _29_411)::[] -> begin
(let _131_225 = (formula_to_string t)
in (FStar_Util.format2 "%s %s" f _131_225))
end
| _29_415 -> begin
(FStar_All.failwith "impos")
end))
in (let bin_top = (fun f _29_12 -> (match (_29_12) with
| (FStar_Util.Inl (t1), _29_427)::(FStar_Util.Inl (t2), _29_422)::[] -> begin
(let _131_231 = (formula_to_string t1)
in (let _131_230 = (formula_to_string t2)
in (FStar_Util.format3 "%s %s %s" _131_231 f _131_230)))
end
| _29_431 -> begin
(FStar_All.failwith "Impos")
end))
in (let bin_eop = (fun f _29_13 -> (match (_29_13) with
| (FStar_Util.Inr (e1), _29_443)::(FStar_Util.Inr (e2), _29_438)::[] -> begin
(let _131_237 = (exp_to_string e1)
in (let _131_236 = (exp_to_string e2)
in (FStar_Util.format3 "%s %s %s" _131_237 f _131_236)))
end
| _29_447 -> begin
(FStar_All.failwith "impos")
end))
in (let ite = (fun _29_14 -> (match (_29_14) with
| (FStar_Util.Inl (t1), _29_462)::(FStar_Util.Inl (t2), _29_457)::(FStar_Util.Inl (t3), _29_452)::[] -> begin
(let _131_242 = (formula_to_string t1)
in (let _131_241 = (formula_to_string t2)
in (let _131_240 = (formula_to_string t3)
in (FStar_Util.format3 "if %s then %s else %s" _131_242 _131_241 _131_240))))
end
| _29_466 -> begin
(FStar_All.failwith "impos")
end))
in (let eq_op = (fun _29_15 -> (match (_29_15) with
| (FStar_Util.Inl (t1), _29_487)::(FStar_Util.Inl (t2), _29_482)::(FStar_Util.Inr (e1), _29_477)::(FStar_Util.Inr (e2), _29_472)::[] -> begin
if (FStar_ST.read FStar_Options.print_implicits) then begin
(let _131_248 = (typ_to_string t1)
in (let _131_247 = (typ_to_string t2)
in (let _131_246 = (exp_to_string e1)
in (let _131_245 = (exp_to_string e2)
in (FStar_Util.format4 "Eq2 %s %s %s %s" _131_248 _131_247 _131_246 _131_245)))))
end else begin
(let _131_250 = (exp_to_string e1)
in (let _131_249 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _131_250 _131_249)))
end
end
| (FStar_Util.Inr (e1), _29_498)::(FStar_Util.Inr (e2), _29_493)::[] -> begin
(let _131_252 = (exp_to_string e1)
in (let _131_251 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _131_252 _131_251)))
end
| _29_502 -> begin
(FStar_All.failwith "Impossible")
end))
in (let connectives = ((FStar_Absyn_Const.and_lid, (bin_top "/\\")))::((FStar_Absyn_Const.or_lid, (bin_top "\\/")))::((FStar_Absyn_Const.imp_lid, (bin_top "==>")))::((FStar_Absyn_Const.iff_lid, (bin_top "<==>")))::((FStar_Absyn_Const.ite_lid, ite))::((FStar_Absyn_Const.not_lid, (un_op "~")))::((FStar_Absyn_Const.eqT_lid, (bin_top "==")))::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op "True")))::((FStar_Absyn_Const.false_lid, (const_op "False")))::[]
in (let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (binders, phi) -> begin
(let _131_291 = (binders_to_string " " binders)
in (let _131_290 = (formula_to_string phi)
in (FStar_Util.format2 "(fun %s => %s)" _131_291 _131_290)))
end
| _29_512 -> begin
(typ_to_string phi)
end))
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _29_522 -> (match (_29_522) with
| (l, _29_521) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_29_525, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, _29_531, body)) -> begin
(let _131_309 = (binders_to_string " " vars)
in (let _131_308 = (formula_to_string body)
in (FStar_Util.format2 "(forall %s. %s)" _131_309 _131_308)))
end
| Some (FStar_Absyn_Util.QEx (vars, _29_538, body)) -> begin
(let _131_311 = (binders_to_string " " vars)
in (let _131_310 = (formula_to_string body)
in (FStar_Util.format2 "(exists %s. %s)" _131_311 _131_310)))
end))))))))))
and exp_to_string : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun x -> (match ((let _131_313 = (FStar_Absyn_Util.compress_exp x)
in _131_313.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_delayed (_29_545) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _29_549)) -> begin
(exp_to_string e)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(uvar_e_to_string (uv, t))
end
| FStar_Absyn_Syntax.Exp_bvar (bvv) -> begin
(strBvd bvv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_fvar (fv, _29_561) -> begin
(sli fv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(FStar_All.pipe_right c const_to_string)
end
| FStar_Absyn_Syntax.Exp_abs (binders, e) -> begin
(let _131_315 = (binders_to_string " " binders)
in (let _131_314 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _131_315 _131_314)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(let lex = if (FStar_ST.read FStar_Options.print_implicits) then begin
None
end else begin
(reconstruct_lex x)
end
in (match (lex) with
| Some (es) -> begin
(let _131_318 = (let _131_317 = (let _131_316 = (FStar_List.map exp_to_string es)
in (FStar_String.concat "; " _131_316))
in (Prims.strcat "%[" _131_317))
in (Prims.strcat _131_318 "]"))
end
| None -> begin
(let args' = (let _131_320 = (filter_imp args)
in (FStar_All.pipe_right _131_320 (FStar_List.filter (fun _29_16 -> (match (_29_16) with
| (FStar_Util.Inr (_29_580), _29_583) -> begin
true
end
| _29_586 -> begin
false
end)))))
in if ((is_infix_prim_op e) && ((FStar_List.length args') = 2)) then begin
(let _131_325 = (let _131_321 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _131_321 arg_to_string))
in (let _131_324 = (FStar_All.pipe_right e infix_prim_op_to_string)
in (let _131_323 = (let _131_322 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _131_322 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _131_325 _131_324 _131_323))))
end else begin
if ((is_unary_prim_op e) && ((FStar_List.length args') = 1)) then begin
(let _131_328 = (FStar_All.pipe_right e unary_prim_op_to_string)
in (let _131_327 = (let _131_326 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _131_326 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _131_328 _131_327)))
end else begin
(let _131_330 = (FStar_All.pipe_right e exp_to_string)
in (let _131_329 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _131_330 _131_329)))
end
end)
end))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _131_338 = (FStar_All.pipe_right e exp_to_string)
in (let _131_337 = (let _131_336 = (FStar_All.pipe_right pats (FStar_List.map (fun _29_595 -> (match (_29_595) with
| (p, wopt, e) -> begin
(let _131_335 = (FStar_All.pipe_right p pat_to_string)
in (let _131_334 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _131_332 = (FStar_All.pipe_right w exp_to_string)
in (FStar_Util.format1 "when %s" _131_332))
end)
in (let _131_333 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format3 "%s %s -> %s" _131_335 _131_334 _131_333))))
end))))
in (FStar_Util.concat_l "\n\t" _131_336))
in (FStar_Util.format2 "(match %s with %s)" _131_338 _131_337)))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _29_602) -> begin
(let _131_340 = (FStar_All.pipe_right e exp_to_string)
in (let _131_339 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "(%s:%s)" _131_340 _131_339)))
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(let _131_342 = (lbs_to_string lbs)
in (let _131_341 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "%s in %s" _131_342 _131_341)))
end))
and uvar_e_to_string : (FStar_Absyn_Syntax.uvar_e * FStar_Absyn_Syntax.typ)  ->  Prims.string = (fun _29_612 -> (match (_29_612) with
| (uv, _29_611) -> begin
(let _131_345 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _131_344 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _131_344))
end
in (Prims.strcat "\'e" _131_345))
end))
and lbs_to_string : FStar_Absyn_Syntax.letbindings  ->  Prims.string = (fun lbs -> (let _131_352 = (let _131_351 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _131_350 = (lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _131_349 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbtyp typ_to_string)
in (let _131_348 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbdef exp_to_string)
in (FStar_Util.format3 "%s:%s = %s" _131_350 _131_349 _131_348)))))))
in (FStar_Util.concat_l "\n and " _131_351))
in (FStar_Util.format2 "let %s %s" (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _131_352)))
and lbname_to_string : FStar_Absyn_Syntax.lbname  ->  Prims.string = (fun x -> (match (x) with
| FStar_Util.Inl (bvd) -> begin
(strBvd bvd)
end
| FStar_Util.Inr (lid) -> begin
(sli lid)
end))
and either_to_string : ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either  ->  Prims.string = (fun x -> (match (x) with
| FStar_Util.Inl (t) -> begin
(typ_to_string t)
end
| FStar_Util.Inr (e) -> begin
(exp_to_string e)
end))
and either_l_to_string : Prims.string  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either Prims.list  ->  Prims.string = (fun delim l -> (let _131_357 = (FStar_All.pipe_right l (FStar_List.map either_to_string))
in (FStar_All.pipe_right _131_357 (FStar_Util.concat_l delim))))
and meta_to_string : FStar_Absyn_Syntax.meta_t  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Meta_refresh_label (t, _29_630, _29_632) -> begin
(let _131_359 = (typ_to_string t)
in (FStar_Util.format1 "(refresh) %s" _131_359))
end
| FStar_Absyn_Syntax.Meta_labeled (t, l, _29_638, _29_640) -> begin
(let _131_360 = (typ_to_string t)
in (FStar_Util.format2 "(labeled \"%s\") %s" l _131_360))
end
| FStar_Absyn_Syntax.Meta_named (_29_644, l) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Meta_pattern (t, ps) -> begin
(let _131_362 = (pats_to_string ps)
in (let _131_361 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "{:pattern %s} %s" _131_362 _131_361)))
end
| FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _29_655) -> begin
(let _131_364 = (formula_to_string t1)
in (let _131_363 = (formula_to_string t2)
in (FStar_Util.format2 "%s /\\ %s" _131_364 _131_363)))
end))
and pats_to_string : FStar_Absyn_Syntax.arg Prims.list Prims.list  ->  Prims.string = (fun ps -> (let _131_368 = (FStar_All.pipe_right ps (FStar_List.map (fun e -> (let _131_367 = (FStar_All.pipe_right e (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _131_367 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _131_368 (FStar_String.concat " \\/ "))))
and kind_to_string : FStar_Absyn_Syntax.knd  ->  Prims.string = (fun x -> (match ((let _131_370 = (FStar_Absyn_Util.compress_kind x)
in _131_370.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_lam (_29_662) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Kind_delayed (_29_665) -> begin
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
(let _131_372 = (sli n)
in (let _131_371 = (args_to_string args)
in (FStar_Util.format2 "%s %s" _131_372 _131_371)))
end
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(let _131_374 = (binders_to_string " -> " binders)
in (let _131_373 = (FStar_All.pipe_right k kind_to_string)
in (FStar_Util.format2 "(%s -> %s)" _131_374 _131_373)))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun uv -> (let _131_376 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _131_375 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _131_375))
end
in (Prims.strcat "\'k_" _131_376)))
and uvar_k_to_string' : ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list)  ->  Prims.string = (fun _29_687 -> (match (_29_687) with
| (uv, args) -> begin
(let str = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _131_378 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _131_378))
end
in (let _131_379 = (args_to_string args)
in (FStar_Util.format2 "(\'k_%s %s)" str _131_379)))
end))
and pat_to_string : FStar_Absyn_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (l, _29_692, pats) -> begin
(let _131_384 = (sli l.FStar_Absyn_Syntax.v)
in (let _131_383 = (let _131_382 = (FStar_List.map (fun _29_698 -> (match (_29_698) with
| (x, b) -> begin
(let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _131_382 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _131_384 _131_383)))
end
| FStar_Absyn_Syntax.Pat_dot_term (x, _29_702) -> begin
(let _131_385 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".%s" _131_385))
end
| FStar_Absyn_Syntax.Pat_dot_typ (x, _29_707) -> begin
(let _131_386 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".\'%s" _131_386))
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
| FStar_Absyn_Syntax.Pat_wild (_29_717) -> begin
"_"
end
| FStar_Absyn_Syntax.Pat_twild (_29_720) -> begin
"\'_"
end
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(let _131_387 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _131_387))
end))

let subst_to_string = (fun subst -> (let _131_395 = (let _131_394 = (FStar_List.map (fun _29_17 -> (match (_29_17) with
| FStar_Util.Inl (a, t) -> begin
(let _131_391 = (strBvd a)
in (let _131_390 = (typ_to_string t)
in (FStar_Util.format2 "(%s -> %s)" _131_391 _131_390)))
end
| FStar_Util.Inr (x, e) -> begin
(let _131_393 = (strBvd x)
in (let _131_392 = (exp_to_string e)
in (FStar_Util.format2 "(%s -> %s)" _131_393 _131_392)))
end)) subst)
in (FStar_All.pipe_right _131_394 (FStar_String.concat ", ")))
in (FStar_All.pipe_left (FStar_Util.format1 "{%s}") _131_395)))

let freevars_to_string : FStar_Absyn_Syntax.freevars  ->  Prims.string = (fun fvs -> (let f = (fun l -> (let _131_401 = (let _131_400 = (FStar_All.pipe_right l FStar_Util.set_elements)
in (FStar_All.pipe_right _131_400 (FStar_List.map (fun t -> (strBvd t.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _131_401 (FStar_String.concat ", "))))
in (let _131_403 = (f fvs.FStar_Absyn_Syntax.ftvs)
in (let _131_402 = (f fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_Util.format2 "ftvs={%s}, fxvs={%s}" _131_403 _131_402)))))

let qual_to_string : FStar_Absyn_Syntax.qualifier  ->  Prims.string = (fun _29_18 -> (match (_29_18) with
| FStar_Absyn_Syntax.Logic -> begin
"logic"
end
| FStar_Absyn_Syntax.Opaque -> begin
"opaque"
end
| FStar_Absyn_Syntax.Discriminator (_29_744) -> begin
"discriminator"
end
| FStar_Absyn_Syntax.Projector (_29_747) -> begin
"projector"
end
| FStar_Absyn_Syntax.RecordType (ids) -> begin
(let _131_408 = (let _131_407 = (FStar_All.pipe_right ids (FStar_List.map (fun lid -> lid.FStar_Ident.ident.FStar_Ident.idText)))
in (FStar_All.pipe_right _131_407 (FStar_String.concat ", ")))
in (FStar_Util.format1 "record(%s)" _131_408))
end
| _29_753 -> begin
"other"
end))

let quals_to_string : FStar_Absyn_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (let _131_411 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _131_411 (FStar_String.concat " "))))

let rec sigelt_to_string : FStar_Absyn_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.ResetOptions, _29_758) -> begin
"#reset-options"
end
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.SetOptions (s), _29_764) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _29_771, _29_773, quals, _29_776) -> begin
(let _131_416 = (quals_to_string quals)
in (let _131_415 = (binders_to_string " " tps)
in (let _131_414 = (kind_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _131_416 lid.FStar_Ident.str _131_415 _131_414))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, _29_784, _29_786) -> begin
(let _131_419 = (binders_to_string " " tps)
in (let _131_418 = (kind_to_string k)
in (let _131_417 = (typ_to_string t)
in (FStar_Util.format4 "type %s %s : %s = %s" lid.FStar_Ident.str _131_419 _131_418 _131_417))))
end
| FStar_Absyn_Syntax.Sig_datacon (lid, t, _29_792, _29_794, _29_796, _29_798) -> begin
(let _131_420 = (typ_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _131_420))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _29_805) -> begin
(let _131_422 = (quals_to_string quals)
in (let _131_421 = (typ_to_string t)
in (FStar_Util.format3 "%s val %s : %s" _131_422 lid.FStar_Ident.str _131_421)))
end
| FStar_Absyn_Syntax.Sig_assume (lid, f, _29_811, _29_813) -> begin
(let _131_423 = (typ_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _131_423))
end
| FStar_Absyn_Syntax.Sig_let (lbs, _29_818, _29_820, b) -> begin
(lbs_to_string lbs)
end
| FStar_Absyn_Syntax.Sig_main (e, _29_826) -> begin
(let _131_424 = (exp_to_string e)
in (FStar_Util.format1 "let _ = %s" _131_424))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _29_831, _29_833, _29_835) -> begin
(let _131_425 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _131_425 (FStar_String.concat "\n")))
end
| FStar_Absyn_Syntax.Sig_new_effect (_29_839) -> begin
"new_effect { ... }"
end
| FStar_Absyn_Syntax.Sig_sub_effect (_29_842) -> begin
"sub_effect ..."
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_29_845) -> begin
"kind ..."
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, tps, c, _29_851, _29_853) -> begin
(let _131_428 = (sli l)
in (let _131_427 = (binders_to_string " " tps)
in (let _131_426 = (comp_typ_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _131_428 _131_427 _131_426))))
end))

let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _131_433 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _131_433 msg)))

let rec sigelt_to_string_short : FStar_Absyn_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_let ((_29_860, {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _29_864; FStar_Absyn_Syntax.lbdef = _29_862}::[]), _29_872, _29_874, _29_876) -> begin
(let _131_436 = (typ_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Ident.str _131_436))
end
| _29_880 -> begin
(let _131_439 = (let _131_438 = (FStar_Absyn_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _131_438 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _131_439 (FStar_String.concat ", ")))
end))

let rec modul_to_string : FStar_Absyn_Syntax.modul  ->  Prims.string = (fun m -> (let _131_444 = (sli m.FStar_Absyn_Syntax.name)
in (let _131_443 = (let _131_442 = (FStar_List.map sigelt_to_string m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _131_442 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _131_444 _131_443))))




