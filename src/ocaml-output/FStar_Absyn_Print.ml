
open Prims
let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.op_Addition, "+"))::((FStar_Absyn_Const.op_Subtraction, "-"))::((FStar_Absyn_Const.op_Multiply, "*"))::((FStar_Absyn_Const.op_Division, "/"))::((FStar_Absyn_Const.op_Eq, "="))::((FStar_Absyn_Const.op_ColonEq, ":="))::((FStar_Absyn_Const.op_notEq, "<>"))::((FStar_Absyn_Const.op_And, "&&"))::((FStar_Absyn_Const.op_Or, "||"))::((FStar_Absyn_Const.op_LTE, "<="))::((FStar_Absyn_Const.op_GTE, ">="))::((FStar_Absyn_Const.op_LT, "<"))::((FStar_Absyn_Const.op_GT, ">"))::((FStar_Absyn_Const.op_Modulus, "mod"))::[]

let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.op_Negation, "not"))::((FStar_Absyn_Const.op_Minus, "-"))::[]

let infix_type_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.and_lid, "/\\"))::((FStar_Absyn_Const.or_lid, "\\/"))::((FStar_Absyn_Const.imp_lid, "==>"))::((FStar_Absyn_Const.iff_lid, "<==>"))::((FStar_Absyn_Const.precedes_lid, "<<"))::((FStar_Absyn_Const.eq2_lid, "=="))::((FStar_Absyn_Const.eqT_lid, "=="))::[]

let unary_type_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.not_lid, "~"))::[]

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

let is_inr = (fun _30_1 -> (match (_30_1) with
| FStar_Util.Inl (_30_58) -> begin
false
end
| FStar_Util.Inr (_30_61) -> begin
true
end))

let rec reconstruct_lex : FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _133_28 = (FStar_Absyn_Util.compress_exp e)
in _133_28.FStar_Absyn_Syntax.n)) with
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
(match ((let _133_31 = (FStar_List.nth exps 1)
in (reconstruct_lex _133_31))) with
| Some (xs) -> begin
(let _133_33 = (let _133_32 = (FStar_List.nth exps 0)
in (_133_32)::xs)
in Some (_133_33))
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

let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _133_47 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _133_47)))

let infix_prim_op_to_string = (fun e -> (let _133_49 = (get_lid e)
in (find_lid _133_49 infix_prim_ops)))

let unary_prim_op_to_string = (fun e -> (let _133_51 = (get_lid e)
in (find_lid _133_51 unary_prim_ops)))

let infix_type_op_to_string = (fun t -> (let _133_53 = (get_type_lid t)
in (find_lid _133_53 infix_type_ops)))

let unary_type_op_to_string = (fun t -> (let _133_55 = (get_type_lid t)
in (find_lid _133_55 unary_type_ops)))

let quant_to_string = (fun t -> (let _133_57 = (get_type_lid t)
in (find_lid _133_57 quants)))

let rec sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_ST.read FStar_Options.print_real_names) then begin
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
(let _30_112 = (let _133_62 = (FStar_Util.substring_from bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText 1)
in (FStar_Util.int_of_string _133_62))
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

let rec tag_of_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
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
(let _133_103 = (tag_of_typ head)
in (let _133_102 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.format2 "Typ_app(%s, [%s args])" _133_103 _133_102)))
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
(let _133_107 = (meta_e_to_string m)
in (Prims.strcat "Exp_meta_desugared " _133_107))
end))
and meta_e_to_string : FStar_Absyn_Syntax.meta_source_info  ->  Prims.string = (fun _30_4 -> (match (_30_4) with
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
| FStar_Absyn_Syntax.Typ_delayed (_30_245) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_30_248, l)) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Typ_meta (meta) -> begin
(let _133_113 = (FStar_All.pipe_right meta meta_to_string)
in (FStar_Util.format1 "(Meta %s)" _133_113))
end
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(strBvd btv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(sli v.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_fun (binders, c) -> begin
(let _133_115 = (binders_to_string " -> " binders)
in (let _133_114 = (comp_typ_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _133_115 _133_114)))
end
| FStar_Absyn_Syntax.Typ_refine (xt, f) -> begin
(let _133_118 = (strBvd xt.FStar_Absyn_Syntax.v)
in (let _133_117 = (FStar_All.pipe_right xt.FStar_Absyn_Syntax.sort typ_to_string)
in (let _133_116 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "%s:%s{%s}" _133_118 _133_117 _133_116))))
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
(let _133_129 = (tag_of_typ t)
in (let _133_128 = (typ_to_string t)
in (FStar_Util.format2 "<Expected a type-lambda! got %s>%s" _133_129 _133_128)))
end))
end
| FStar_Util.Inr (e) -> begin
(let _133_130 = (exp_to_string e)
in (FStar_Util.format1 "(<Expected a type!>%s)" _133_130))
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
(let _133_141 = (let _133_136 = (FStar_List.nth args 0)
in (arg_to_string _133_136))
in (let _133_140 = (let _133_137 = (FStar_List.nth args 1)
in (arg_to_string _133_137))
in (let _133_139 = (let _133_138 = (FStar_List.nth args 2)
in (arg_to_string _133_138))
in (FStar_Util.format3 "if %s then %s else %s" _133_141 _133_140 _133_139))))
end else begin
if ((is_b2t t) && ((FStar_List.length args) = 1)) then begin
(let _133_142 = (FStar_List.nth args 0)
in (FStar_All.pipe_right _133_142 arg_to_string))
end else begin
if ((is_quant t) && ((FStar_List.length args) <= 2)) then begin
(let _133_147 = (quant_to_string t)
in (let _133_146 = (let _133_143 = (FStar_List.nth args' 0)
in (qbinder_to_string _133_143))
in (let _133_145 = (let _133_144 = (FStar_List.nth args' 0)
in (qbody_to_string _133_144))
in (FStar_Util.format3 "(%s (%s). %s)" _133_147 _133_146 _133_145))))
end else begin
if ((is_infix_type_op t) && ((FStar_List.length args') = 2)) then begin
(let _133_152 = (let _133_148 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _133_148 arg_to_string))
in (let _133_151 = (FStar_All.pipe_right t infix_type_op_to_string)
in (let _133_150 = (let _133_149 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _133_149 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _133_152 _133_151 _133_150))))
end else begin
if ((is_unary_type_op t) && ((FStar_List.length args') = 1)) then begin
(let _133_155 = (FStar_All.pipe_right t unary_type_op_to_string)
in (let _133_154 = (let _133_153 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _133_153 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _133_155 _133_154)))
end else begin
(let _133_157 = (FStar_All.pipe_right t typ_to_string)
in (let _133_156 = (FStar_All.pipe_right args args_to_string)
in (FStar_Util.format2 "(%s %s)" _133_157 _133_156)))
end
end
end
end
end))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(let _133_159 = (binders_to_string " " binders)
in (let _133_158 = (FStar_All.pipe_right t2 typ_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _133_159 _133_158)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _133_161 = (typ_to_string t)
in (let _133_160 = (kind_to_string k)
in (FStar_Util.format2 "(%s <: %s)" _133_161 _133_160)))
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
and uvar_t_to_string : (FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd)  ->  Prims.string = (fun _30_332 -> (match (_30_332) with
| (uv, k) -> begin
if (false && (FStar_ST.read FStar_Options.print_real_names)) then begin
(let _133_165 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _133_163 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _133_163))
end
in (let _133_164 = (kind_to_string k)
in (FStar_Util.format2 "(U%s : %s)" _133_165 _133_164)))
end else begin
(let _133_167 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _133_166 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _133_166))
end
in (FStar_Util.format1 "U%s" _133_167))
end
end))
and imp_to_string : Prims.string  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s _30_6 -> (match (_30_6) with
| Some (FStar_Absyn_Syntax.Implicit) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Absyn_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _30_340 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (match (b) with
| (FStar_Util.Inl (a), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _133_172 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _133_172 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp a.FStar_Absyn_Syntax.v))) then begin
(kind_to_string a.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits)))) then begin
(let _133_173 = (strBvd a.FStar_Absyn_Syntax.v)
in (imp_to_string _133_173 imp))
end else begin
(let _133_177 = (let _133_176 = (let _133_174 = (strBvd a.FStar_Absyn_Syntax.v)
in (Prims.strcat _133_174 ":"))
in (let _133_175 = (kind_to_string a.FStar_Absyn_Syntax.sort)
in (Prims.strcat _133_176 _133_175)))
in (imp_to_string _133_177 imp))
end
end
end
| (FStar_Util.Inr (x), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _133_178 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _133_178 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp x.FStar_Absyn_Syntax.v))) then begin
(typ_to_string x.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits)))) then begin
(let _133_179 = (strBvd x.FStar_Absyn_Syntax.v)
in (imp_to_string _133_179 imp))
end else begin
(let _133_183 = (let _133_182 = (let _133_180 = (strBvd x.FStar_Absyn_Syntax.v)
in (Prims.strcat _133_180 ":"))
in (let _133_181 = (typ_to_string x.FStar_Absyn_Syntax.sort)
in (Prims.strcat _133_182 _133_181)))
in (imp_to_string _133_183 imp))
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
(let _133_188 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _133_188 (FStar_String.concat sep)))
end else begin
(let _133_189 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _133_189 (FStar_String.concat sep)))
end))
and arg_to_string : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _30_7 -> (match (_30_7) with
| (FStar_Util.Inl (a), imp) -> begin
(let _133_191 = (typ_to_string a)
in (imp_to_string _133_191 imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _133_192 = (exp_to_string x)
in (imp_to_string _133_192 imp))
end))
and args_to_string : FStar_Absyn_Syntax.args  ->  Prims.string = (fun args -> (let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _133_194 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _133_194 (FStar_String.concat " ")))))
and lcomp_typ_to_string : FStar_Absyn_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _133_197 = (sli lc.FStar_Absyn_Syntax.eff_name)
in (let _133_196 = (typ_to_string lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _133_197 _133_196))))
and comp_typ_to_string : FStar_Absyn_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _133_199 = (typ_to_string t)
in (FStar_Util.format1 "Tot %s" _133_199))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(let basic = if ((FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _30_8 -> (match (_30_8) with
| FStar_Absyn_Syntax.TOTAL -> begin
true
end
| _30_376 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args)))) then begin
(let _133_201 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _133_201))
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
(let _133_203 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _133_203))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _133_207 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _133_206 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (let _133_205 = (let _133_204 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.effect_args (FStar_List.map effect_arg_to_string))
in (FStar_All.pipe_right _133_204 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _133_207 _133_206 _133_205))))
end else begin
(let _133_209 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _133_208 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _133_209 _133_208)))
end
end
end
end
in (let dec = (let _133_213 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.collect (fun _30_10 -> (match (_30_10) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _133_212 = (let _133_211 = (exp_to_string e)
in (FStar_Util.format1 " (decreases %s)" _133_211))
in (_133_212)::[])
end
| _30_386 -> begin
[]
end))))
in (FStar_All.pipe_right _133_213 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and effect_arg_to_string : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun e -> (match (e) with
| (FStar_Util.Inr (e), _30_392) -> begin
(exp_to_string e)
end
| (FStar_Util.Inl (wp), _30_397) -> begin
(formula_to_string wp)
end))
and formula_to_string : FStar_Absyn_Syntax.typ  ->  Prims.string = (fun phi -> (typ_to_string phi))
and formula_to_string_old_now_unused : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun phi -> (let const_op = (fun f _30_403 -> f)
in (let un_op = (fun f _30_11 -> (match (_30_11) with
| (FStar_Util.Inl (t), _30_411)::[] -> begin
(let _133_225 = (formula_to_string t)
in (FStar_Util.format2 "%s %s" f _133_225))
end
| _30_415 -> begin
(FStar_All.failwith "impos")
end))
in (let bin_top = (fun f _30_12 -> (match (_30_12) with
| (FStar_Util.Inl (t1), _30_427)::(FStar_Util.Inl (t2), _30_422)::[] -> begin
(let _133_231 = (formula_to_string t1)
in (let _133_230 = (formula_to_string t2)
in (FStar_Util.format3 "%s %s %s" _133_231 f _133_230)))
end
| _30_431 -> begin
(FStar_All.failwith "Impos")
end))
in (let bin_eop = (fun f _30_13 -> (match (_30_13) with
| (FStar_Util.Inr (e1), _30_443)::(FStar_Util.Inr (e2), _30_438)::[] -> begin
(let _133_237 = (exp_to_string e1)
in (let _133_236 = (exp_to_string e2)
in (FStar_Util.format3 "%s %s %s" _133_237 f _133_236)))
end
| _30_447 -> begin
(FStar_All.failwith "impos")
end))
in (let ite = (fun _30_14 -> (match (_30_14) with
| (FStar_Util.Inl (t1), _30_462)::(FStar_Util.Inl (t2), _30_457)::(FStar_Util.Inl (t3), _30_452)::[] -> begin
(let _133_242 = (formula_to_string t1)
in (let _133_241 = (formula_to_string t2)
in (let _133_240 = (formula_to_string t3)
in (FStar_Util.format3 "if %s then %s else %s" _133_242 _133_241 _133_240))))
end
| _30_466 -> begin
(FStar_All.failwith "impos")
end))
in (let eq_op = (fun _30_15 -> (match (_30_15) with
| (FStar_Util.Inl (t1), _30_487)::(FStar_Util.Inl (t2), _30_482)::(FStar_Util.Inr (e1), _30_477)::(FStar_Util.Inr (e2), _30_472)::[] -> begin
if (FStar_ST.read FStar_Options.print_implicits) then begin
(let _133_248 = (typ_to_string t1)
in (let _133_247 = (typ_to_string t2)
in (let _133_246 = (exp_to_string e1)
in (let _133_245 = (exp_to_string e2)
in (FStar_Util.format4 "Eq2 %s %s %s %s" _133_248 _133_247 _133_246 _133_245)))))
end else begin
(let _133_250 = (exp_to_string e1)
in (let _133_249 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _133_250 _133_249)))
end
end
| (FStar_Util.Inr (e1), _30_498)::(FStar_Util.Inr (e2), _30_493)::[] -> begin
(let _133_252 = (exp_to_string e1)
in (let _133_251 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _133_252 _133_251)))
end
| _30_502 -> begin
(FStar_All.failwith "Impossible")
end))
in (let connectives = ((FStar_Absyn_Const.and_lid, (bin_top "/\\")))::((FStar_Absyn_Const.or_lid, (bin_top "\\/")))::((FStar_Absyn_Const.imp_lid, (bin_top "==>")))::((FStar_Absyn_Const.iff_lid, (bin_top "<==>")))::((FStar_Absyn_Const.ite_lid, ite))::((FStar_Absyn_Const.not_lid, (un_op "~")))::((FStar_Absyn_Const.eqT_lid, (bin_top "==")))::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op "True")))::((FStar_Absyn_Const.false_lid, (const_op "False")))::[]
in (let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (binders, phi) -> begin
(let _133_291 = (binders_to_string " " binders)
in (let _133_290 = (formula_to_string phi)
in (FStar_Util.format2 "(fun %s => %s)" _133_291 _133_290)))
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
(let _133_309 = (binders_to_string " " vars)
in (let _133_308 = (formula_to_string body)
in (FStar_Util.format2 "(forall %s. %s)" _133_309 _133_308)))
end
| Some (FStar_Absyn_Util.QEx (vars, _30_538, body)) -> begin
(let _133_311 = (binders_to_string " " vars)
in (let _133_310 = (formula_to_string body)
in (FStar_Util.format2 "(exists %s. %s)" _133_311 _133_310)))
end))))))))))
and exp_to_string : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun x -> (match ((let _133_313 = (FStar_Absyn_Util.compress_exp x)
in _133_313.FStar_Absyn_Syntax.n)) with
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
(let _133_315 = (binders_to_string " " binders)
in (let _133_314 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _133_315 _133_314)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(let lex = if (FStar_ST.read FStar_Options.print_implicits) then begin
None
end else begin
(reconstruct_lex x)
end
in (match (lex) with
| Some (es) -> begin
(let _133_318 = (let _133_317 = (let _133_316 = (FStar_List.map exp_to_string es)
in (FStar_String.concat "; " _133_316))
in (Prims.strcat "%[" _133_317))
in (Prims.strcat _133_318 "]"))
end
| None -> begin
(let args' = (let _133_320 = (filter_imp args)
in (FStar_All.pipe_right _133_320 (FStar_List.filter (fun _30_16 -> (match (_30_16) with
| (FStar_Util.Inr (_30_580), _30_583) -> begin
true
end
| _30_586 -> begin
false
end)))))
in if ((is_infix_prim_op e) && ((FStar_List.length args') = 2)) then begin
(let _133_325 = (let _133_321 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _133_321 arg_to_string))
in (let _133_324 = (FStar_All.pipe_right e infix_prim_op_to_string)
in (let _133_323 = (let _133_322 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _133_322 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _133_325 _133_324 _133_323))))
end else begin
if ((is_unary_prim_op e) && ((FStar_List.length args') = 1)) then begin
(let _133_328 = (FStar_All.pipe_right e unary_prim_op_to_string)
in (let _133_327 = (let _133_326 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _133_326 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _133_328 _133_327)))
end else begin
(let _133_330 = (FStar_All.pipe_right e exp_to_string)
in (let _133_329 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _133_330 _133_329)))
end
end)
end))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _133_338 = (FStar_All.pipe_right e exp_to_string)
in (let _133_337 = (let _133_336 = (FStar_All.pipe_right pats (FStar_List.map (fun _30_595 -> (match (_30_595) with
| (p, wopt, e) -> begin
(let _133_335 = (FStar_All.pipe_right p pat_to_string)
in (let _133_334 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _133_332 = (FStar_All.pipe_right w exp_to_string)
in (FStar_Util.format1 "when %s" _133_332))
end)
in (let _133_333 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format3 "%s %s -> %s" _133_335 _133_334 _133_333))))
end))))
in (FStar_Util.concat_l "\n\t" _133_336))
in (FStar_Util.format2 "(match %s with %s)" _133_338 _133_337)))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _30_602) -> begin
(let _133_340 = (FStar_All.pipe_right e exp_to_string)
in (let _133_339 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "(%s:%s)" _133_340 _133_339)))
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(let _133_342 = (lbs_to_string lbs)
in (let _133_341 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "%s in %s" _133_342 _133_341)))
end))
and uvar_e_to_string : (FStar_Absyn_Syntax.uvar_e * FStar_Absyn_Syntax.typ)  ->  Prims.string = (fun _30_612 -> (match (_30_612) with
| (uv, _30_611) -> begin
(let _133_345 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _133_344 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _133_344))
end
in (Prims.strcat "\'e" _133_345))
end))
and lbs_to_string : FStar_Absyn_Syntax.letbindings  ->  Prims.string = (fun lbs -> (let _133_352 = (let _133_351 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _133_350 = (lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _133_349 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbtyp typ_to_string)
in (let _133_348 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbdef exp_to_string)
in (FStar_Util.format3 "%s:%s = %s" _133_350 _133_349 _133_348)))))))
in (FStar_Util.concat_l "\n and " _133_351))
in (FStar_Util.format2 "let %s %s" (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _133_352)))
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
and either_l_to_string : Prims.string  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either Prims.list  ->  Prims.string = (fun delim l -> (let _133_357 = (FStar_All.pipe_right l (FStar_List.map either_to_string))
in (FStar_All.pipe_right _133_357 (FStar_Util.concat_l delim))))
and meta_to_string : FStar_Absyn_Syntax.meta_t  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Meta_refresh_label (t, _30_630, _30_632) -> begin
(let _133_359 = (typ_to_string t)
in (FStar_Util.format1 "(refresh) %s" _133_359))
end
| FStar_Absyn_Syntax.Meta_labeled (t, l, _30_638, _30_640) -> begin
(let _133_360 = (typ_to_string t)
in (FStar_Util.format2 "(labeled \"%s\") %s" l _133_360))
end
| FStar_Absyn_Syntax.Meta_named (_30_644, l) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Meta_pattern (t, ps) -> begin
(let _133_362 = (pats_to_string ps)
in (let _133_361 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "{:pattern %s} %s" _133_362 _133_361)))
end
| FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _30_655) -> begin
(let _133_364 = (formula_to_string t1)
in (let _133_363 = (formula_to_string t2)
in (FStar_Util.format2 "%s /\\ %s" _133_364 _133_363)))
end))
and pats_to_string : FStar_Absyn_Syntax.arg Prims.list Prims.list  ->  Prims.string = (fun ps -> (let _133_368 = (FStar_All.pipe_right ps (FStar_List.map (fun e -> (let _133_367 = (FStar_All.pipe_right e (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _133_367 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _133_368 (FStar_String.concat " \\/ "))))
and kind_to_string : FStar_Absyn_Syntax.knd  ->  Prims.string = (fun x -> (match ((let _133_370 = (FStar_Absyn_Util.compress_kind x)
in _133_370.FStar_Absyn_Syntax.n)) with
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
(let _133_372 = (sli n)
in (let _133_371 = (args_to_string args)
in (FStar_Util.format2 "%s %s" _133_372 _133_371)))
end
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(let _133_374 = (binders_to_string " -> " binders)
in (let _133_373 = (FStar_All.pipe_right k kind_to_string)
in (FStar_Util.format2 "(%s -> %s)" _133_374 _133_373)))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun uv -> (let _133_376 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _133_375 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _133_375))
end
in (Prims.strcat "\'k_" _133_376)))
and uvar_k_to_string' : ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list)  ->  Prims.string = (fun _30_687 -> (match (_30_687) with
| (uv, args) -> begin
(let str = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _133_378 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _133_378))
end
in (let _133_379 = (args_to_string args)
in (FStar_Util.format2 "(\'k_%s %s)" str _133_379)))
end))
and pat_to_string : FStar_Absyn_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (l, _30_692, pats) -> begin
(let _133_384 = (sli l.FStar_Absyn_Syntax.v)
in (let _133_383 = (let _133_382 = (FStar_List.map (fun _30_698 -> (match (_30_698) with
| (x, b) -> begin
(let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _133_382 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _133_384 _133_383)))
end
| FStar_Absyn_Syntax.Pat_dot_term (x, _30_702) -> begin
(let _133_385 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".%s" _133_385))
end
| FStar_Absyn_Syntax.Pat_dot_typ (x, _30_707) -> begin
(let _133_386 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".\'%s" _133_386))
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
(let _133_387 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _133_387))
end))

let subst_to_string = (fun subst -> (let _133_395 = (let _133_394 = (FStar_List.map (fun _30_17 -> (match (_30_17) with
| FStar_Util.Inl (a, t) -> begin
(let _133_391 = (strBvd a)
in (let _133_390 = (typ_to_string t)
in (FStar_Util.format2 "(%s -> %s)" _133_391 _133_390)))
end
| FStar_Util.Inr (x, e) -> begin
(let _133_393 = (strBvd x)
in (let _133_392 = (exp_to_string e)
in (FStar_Util.format2 "(%s -> %s)" _133_393 _133_392)))
end)) subst)
in (FStar_All.pipe_right _133_394 (FStar_String.concat ", ")))
in (FStar_All.pipe_left (FStar_Util.format1 "{%s}") _133_395)))

let freevars_to_string : FStar_Absyn_Syntax.freevars  ->  Prims.string = (fun fvs -> (let f = (fun l -> (let _133_401 = (let _133_400 = (FStar_All.pipe_right l FStar_Util.set_elements)
in (FStar_All.pipe_right _133_400 (FStar_List.map (fun t -> (strBvd t.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _133_401 (FStar_String.concat ", "))))
in (let _133_403 = (f fvs.FStar_Absyn_Syntax.ftvs)
in (let _133_402 = (f fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_Util.format2 "ftvs={%s}, fxvs={%s}" _133_403 _133_402)))))

let qual_to_string : FStar_Absyn_Syntax.qualifier  ->  Prims.string = (fun _30_18 -> (match (_30_18) with
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
(let _133_408 = (let _133_407 = (FStar_All.pipe_right ids (FStar_List.map (fun lid -> lid.FStar_Ident.ident.FStar_Ident.idText)))
in (FStar_All.pipe_right _133_407 (FStar_String.concat ", ")))
in (FStar_Util.format1 "record(%s)" _133_408))
end
| _30_753 -> begin
"other"
end))

let quals_to_string : FStar_Absyn_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (let _133_411 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _133_411 (FStar_String.concat " "))))

let rec sigelt_to_string : FStar_Absyn_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.ResetOptions, _30_758) -> begin
"#reset-options"
end
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.SetOptions (s), _30_764) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _30_771, _30_773, quals, _30_776) -> begin
(let _133_416 = (quals_to_string quals)
in (let _133_415 = (binders_to_string " " tps)
in (let _133_414 = (kind_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _133_416 lid.FStar_Ident.str _133_415 _133_414))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, _30_784, _30_786) -> begin
(let _133_419 = (binders_to_string " " tps)
in (let _133_418 = (kind_to_string k)
in (let _133_417 = (typ_to_string t)
in (FStar_Util.format4 "type %s %s : %s = %s" lid.FStar_Ident.str _133_419 _133_418 _133_417))))
end
| FStar_Absyn_Syntax.Sig_datacon (lid, t, _30_792, _30_794, _30_796, _30_798) -> begin
(let _133_420 = (typ_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _133_420))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _30_805) -> begin
(let _133_422 = (quals_to_string quals)
in (let _133_421 = (typ_to_string t)
in (FStar_Util.format3 "%s val %s : %s" _133_422 lid.FStar_Ident.str _133_421)))
end
| FStar_Absyn_Syntax.Sig_assume (lid, f, _30_811, _30_813) -> begin
(let _133_423 = (typ_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _133_423))
end
| FStar_Absyn_Syntax.Sig_let (lbs, _30_818, _30_820, b) -> begin
(lbs_to_string lbs)
end
| FStar_Absyn_Syntax.Sig_main (e, _30_826) -> begin
(let _133_424 = (exp_to_string e)
in (FStar_Util.format1 "let _ = %s" _133_424))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _30_831, _30_833, _30_835) -> begin
(let _133_425 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _133_425 (FStar_String.concat "\n")))
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
(let _133_428 = (sli l)
in (let _133_427 = (binders_to_string " " tps)
in (let _133_426 = (comp_typ_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _133_428 _133_427 _133_426))))
end))

let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _133_433 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _133_433 msg)))

let rec sigelt_to_string_short : FStar_Absyn_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_let ((_30_860, {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _30_864; FStar_Absyn_Syntax.lbdef = _30_862}::[]), _30_872, _30_874, _30_876) -> begin
(let _133_436 = (typ_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Ident.str _133_436))
end
| _30_880 -> begin
(let _133_439 = (let _133_438 = (FStar_Absyn_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _133_438 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _133_439 (FStar_String.concat ", ")))
end))

let rec modul_to_string : FStar_Absyn_Syntax.modul  ->  Prims.string = (fun m -> (let _133_444 = (sli m.FStar_Absyn_Syntax.name)
in (let _133_443 = (let _133_442 = (FStar_List.map sigelt_to_string m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _133_442 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _133_444 _133_443))))




