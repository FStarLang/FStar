
open Prims
# 29 "FStar.Absyn.Print.fst"
let infix_prim_ops : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.op_Addition, "+"))::((FStar_Absyn_Const.op_Subtraction, "-"))::((FStar_Absyn_Const.op_Multiply, "*"))::((FStar_Absyn_Const.op_Division, "/"))::((FStar_Absyn_Const.op_Eq, "="))::((FStar_Absyn_Const.op_ColonEq, ":="))::((FStar_Absyn_Const.op_notEq, "<>"))::((FStar_Absyn_Const.op_And, "&&"))::((FStar_Absyn_Const.op_Or, "||"))::((FStar_Absyn_Const.op_LTE, "<="))::((FStar_Absyn_Const.op_GTE, ">="))::((FStar_Absyn_Const.op_LT, "<"))::((FStar_Absyn_Const.op_GT, ">"))::((FStar_Absyn_Const.op_Modulus, "mod"))::[]

# 46 "FStar.Absyn.Print.fst"
let unary_prim_ops : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.op_Negation, "not"))::((FStar_Absyn_Const.op_Minus, "-"))::[]

# 51 "FStar.Absyn.Print.fst"
let infix_type_ops : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.and_lid, "/\\"))::((FStar_Absyn_Const.or_lid, "\\/"))::((FStar_Absyn_Const.imp_lid, "==>"))::((FStar_Absyn_Const.iff_lid, "<==>"))::((FStar_Absyn_Const.precedes_lid, "<<"))::((FStar_Absyn_Const.eq2_lid, "=="))::((FStar_Absyn_Const.eqT_lid, "=="))::[]

# 61 "FStar.Absyn.Print.fst"
let unary_type_ops : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.not_lid, "~"))::[]

# 65 "FStar.Absyn.Print.fst"
let is_prim_op = (fun ps f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _28_22) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _28_26 -> begin
false
end))

# 69 "FStar.Absyn.Print.fst"
let is_type_op = (fun ps t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals ftv.FStar_Absyn_Syntax.v)))
end
| _28_32 -> begin
false
end))

# 73 "FStar.Absyn.Print.fst"
let get_lid = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _28_36) -> begin
fv.FStar_Absyn_Syntax.v
end
| _28_40 -> begin
(FStar_All.failwith "get_lid")
end))

# 77 "FStar.Absyn.Print.fst"
let get_type_lid = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
ftv.FStar_Absyn_Syntax.v
end
| _28_45 -> begin
(FStar_All.failwith "get_type_lid")
end))

# 81 "FStar.Absyn.Print.fst"
let is_infix_prim_op : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split infix_prim_ops)) e))

# 82 "FStar.Absyn.Print.fst"
let is_unary_prim_op : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split unary_prim_ops)) e))

# 83 "FStar.Absyn.Print.fst"
let is_infix_type_op : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op (Prims.fst (FStar_List.split infix_type_ops)) t))

# 84 "FStar.Absyn.Print.fst"
let is_unary_type_op : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op (Prims.fst (FStar_List.split unary_type_ops)) t))

# 86 "FStar.Absyn.Print.fst"
let quants : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.forall_lid, "forall"))::((FStar_Absyn_Const.exists_lid, "exists"))::((FStar_Absyn_Const.allTyp_lid, "forall"))::((FStar_Absyn_Const.exTyp_lid, "exists"))::[]

# 93 "FStar.Absyn.Print.fst"
let is_b2t : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op ((FStar_Absyn_Const.b2t_lid)::[]) t))

# 94 "FStar.Absyn.Print.fst"
let is_quant : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op (Prims.fst (FStar_List.split quants)) t))

# 95 "FStar.Absyn.Print.fst"
let is_ite : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op ((FStar_Absyn_Const.ite_lid)::[]) t))

# 97 "FStar.Absyn.Print.fst"
let is_lex_cons : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Absyn_Const.lexcons_lid)::[]) f))

# 98 "FStar.Absyn.Print.fst"
let is_lex_top : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Absyn_Const.lextop_lid)::[]) f))

# 99 "FStar.Absyn.Print.fst"
let is_inr = (fun _28_1 -> (match (_28_1) with
| FStar_Util.Inl (_28_57) -> begin
false
end
| FStar_Util.Inr (_28_60) -> begin
true
end))

# 100 "FStar.Absyn.Print.fst"
let rec reconstruct_lex : FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _107_28 = (FStar_Absyn_Util.compress_exp e)
in _107_28.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (f, args) -> begin
(
# 103 "FStar.Absyn.Print.fst"
let args = (FStar_List.filter (fun a -> (match (a) with
| ((FStar_Util.Inl (_), _)) | ((FStar_Util.Inr (_), Some (FStar_Absyn_Syntax.Implicit (_)))) -> begin
false
end
| _28_83 -> begin
true
end)) args)
in (
# 107 "FStar.Absyn.Print.fst"
let exps = (FStar_List.map (fun _28_2 -> (match (_28_2) with
| (FStar_Util.Inl (_28_87), _28_90) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Util.Inr (x), _28_95) -> begin
x
end)) args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = 2)) then begin
(match ((let _107_31 = (FStar_List.nth exps 1)
in (reconstruct_lex _107_31))) with
| Some (xs) -> begin
(let _107_33 = (let _107_32 = (FStar_List.nth exps 0)
in (_107_32)::xs)
in Some (_107_33))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _28_102 -> begin
if (is_lex_top e) then begin
Some ([])
end else begin
None
end
end))

# 116 "FStar.Absyn.Print.fst"
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

# 120 "FStar.Absyn.Print.fst"
let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _107_47 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _107_47)))

# 123 "FStar.Absyn.Print.fst"
let infix_prim_op_to_string = (fun e -> (let _107_49 = (get_lid e)
in (find_lid _107_49 infix_prim_ops)))

# 124 "FStar.Absyn.Print.fst"
let unary_prim_op_to_string = (fun e -> (let _107_51 = (get_lid e)
in (find_lid _107_51 unary_prim_ops)))

# 125 "FStar.Absyn.Print.fst"
let infix_type_op_to_string = (fun t -> (let _107_53 = (get_type_lid t)
in (find_lid _107_53 infix_type_ops)))

# 126 "FStar.Absyn.Print.fst"
let unary_type_op_to_string = (fun t -> (let _107_55 = (get_type_lid t)
in (find_lid _107_55 unary_type_ops)))

# 128 "FStar.Absyn.Print.fst"
let quant_to_string = (fun t -> (let _107_57 = (get_type_lid t)
in (find_lid _107_57 quants)))

# 130 "FStar.Absyn.Print.fst"
let rec sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_ST.read FStar_Options.print_real_names) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)

# 135 "FStar.Absyn.Print.fst"
let strBvd = (fun bvd -> if (FStar_ST.read FStar_Options.print_real_names) then begin
(Prims.strcat bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText bvd.FStar_Absyn_Syntax.realname.FStar_Ident.idText)
end else begin
if ((FStar_ST.read FStar_Options.hide_genident_nums) && (FStar_Util.starts_with bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText "_")) then begin
(FStar_All.try_with (fun _28_121 -> (match (()) with
| () -> begin
(
# 141 "FStar.Absyn.Print.fst"
let _28_127 = (let _107_62 = (FStar_Util.substring_from bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText 1)
in (FStar_Util.int_of_string _107_62))
in "_?")
end)) (fun _28_120 -> (match (_28_120) with
| _28_124 -> begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end)))
end else begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end
end)

# 145 "FStar.Absyn.Print.fst"
let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _28_3 -> (match (_28_3) with
| (_28_132, Some (FStar_Absyn_Syntax.Implicit (_28_134))) -> begin
false
end
| _28_139 -> begin
true
end)))))

# 146 "FStar.Absyn.Print.fst"
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
| FStar_Const.Const_string (bytes, _28_153) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_28_157) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x) -> begin
x
end
| FStar_Const.Const_int64 (_28_162) -> begin
"<int64>"
end
| FStar_Const.Const_uint8 (_28_165) -> begin
"<uint8>"
end))

# 159 "FStar.Absyn.Print.fst"
let rec tag_of_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_28_169) -> begin
"Typ_btvar"
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(Prims.strcat "Typ_const " v.FStar_Absyn_Syntax.v.FStar_Ident.str)
end
| FStar_Absyn_Syntax.Typ_fun (_28_174) -> begin
"Typ_fun"
end
| FStar_Absyn_Syntax.Typ_refine (_28_177) -> begin
"Typ_refine"
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let _107_103 = (tag_of_typ head)
in (let _107_102 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.format2 "Typ_app(%s, [%s args])" _107_103 _107_102)))
end
| FStar_Absyn_Syntax.Typ_lam (_28_184) -> begin
"Typ_lam"
end
| FStar_Absyn_Syntax.Typ_ascribed (_28_187) -> begin
"Typ_ascribed"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_28_190)) -> begin
"Typ_meta_pattern"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_28_194)) -> begin
"Typ_meta_named"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_28_198)) -> begin
"Typ_meta_labeled"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_28_202)) -> begin
"Typ_meta_refresh_label"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_28_206)) -> begin
"Typ_meta_slack_formula"
end
| FStar_Absyn_Syntax.Typ_uvar (_28_210) -> begin
"Typ_uvar"
end
| FStar_Absyn_Syntax.Typ_delayed (_28_213) -> begin
"Typ_delayed"
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"Typ_unknown"
end))
and tag_of_exp = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_28_218) -> begin
"Exp_bvar"
end
| FStar_Absyn_Syntax.Exp_fvar (_28_221) -> begin
"Exp_fvar"
end
| FStar_Absyn_Syntax.Exp_constant (_28_224) -> begin
"Exp_constant"
end
| FStar_Absyn_Syntax.Exp_abs (_28_227) -> begin
"Exp_abs"
end
| FStar_Absyn_Syntax.Exp_app (_28_230) -> begin
"Exp_app"
end
| FStar_Absyn_Syntax.Exp_match (_28_233) -> begin
"Exp_match"
end
| FStar_Absyn_Syntax.Exp_ascribed (_28_236) -> begin
"Exp_ascribed"
end
| FStar_Absyn_Syntax.Exp_let (_28_239) -> begin
"Exp_let"
end
| FStar_Absyn_Syntax.Exp_uvar (_28_242) -> begin
"Exp_uvar"
end
| FStar_Absyn_Syntax.Exp_delayed (_28_245) -> begin
"Exp_delayed"
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_28_248, m)) -> begin
(let _107_107 = (meta_e_to_string m)
in (Prims.strcat "Exp_meta_desugared " _107_107))
end))
and meta_e_to_string : FStar_Absyn_Syntax.meta_source_info  ->  Prims.string = (fun _28_4 -> (match (_28_4) with
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
and typ_to_string : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun x -> (
# 202 "FStar.Absyn.Print.fst"
let x = (FStar_Absyn_Util.compress_typ x)
in (match (x.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_28_262) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_28_265, l)) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Typ_meta (meta) -> begin
(let _107_113 = (FStar_All.pipe_right meta meta_to_string)
in (FStar_Util.format1 "(Meta %s)" _107_113))
end
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(strBvd btv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(sli v.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_fun (binders, c) -> begin
(let _107_115 = (binders_to_string " -> " binders)
in (let _107_114 = (comp_typ_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _107_115 _107_114)))
end
| FStar_Absyn_Syntax.Typ_refine (xt, f) -> begin
(let _107_118 = (strBvd xt.FStar_Absyn_Syntax.v)
in (let _107_117 = (FStar_All.pipe_right xt.FStar_Absyn_Syntax.sort typ_to_string)
in (let _107_116 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "%s:%s{%s}" _107_118 _107_117 _107_116))))
end
| FStar_Absyn_Syntax.Typ_app (_28_285, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(
# 214 "FStar.Absyn.Print.fst"
let q_to_string = (fun k a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(
# 215 "FStar.Absyn.Print.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (b::[], t) -> begin
(k (b, t))
end
| _28_305 -> begin
(let _107_129 = (tag_of_typ t)
in (let _107_128 = (typ_to_string t)
in (FStar_Util.format2 "<Expected a type-lambda! got %s>%s" _107_129 _107_128)))
end))
end
| FStar_Util.Inr (e) -> begin
(let _107_130 = (exp_to_string e)
in (FStar_Util.format1 "(<Expected a type!>%s)" _107_130))
end))
in (
# 220 "FStar.Absyn.Print.fst"
let qbinder_to_string = (q_to_string (fun x -> (binder_to_string (Prims.fst x))))
in (
# 221 "FStar.Absyn.Print.fst"
let qbody_to_string = (q_to_string (fun x -> (typ_to_string (Prims.snd x))))
in (
# 222 "FStar.Absyn.Print.fst"
let args' = if ((FStar_ST.read FStar_Options.print_implicits) && (not ((is_quant t)))) then begin
args
end else begin
(filter_imp args)
end
in if ((is_ite t) && ((FStar_List.length args) = 3)) then begin
(let _107_140 = (let _107_135 = (FStar_List.nth args 0)
in (arg_to_string _107_135))
in (let _107_139 = (let _107_136 = (FStar_List.nth args 1)
in (arg_to_string _107_136))
in (let _107_138 = (let _107_137 = (FStar_List.nth args 2)
in (arg_to_string _107_137))
in (FStar_Util.format3 "if %s then %s else %s" _107_140 _107_139 _107_138))))
end else begin
if ((is_b2t t) && ((FStar_List.length args) = 1)) then begin
(let _107_141 = (FStar_List.nth args 0)
in (FStar_All.pipe_right _107_141 arg_to_string))
end else begin
if ((is_quant t) && ((FStar_List.length args) <= 2)) then begin
(let _107_146 = (quant_to_string t)
in (let _107_145 = (let _107_142 = (FStar_List.nth args' 0)
in (qbinder_to_string _107_142))
in (let _107_144 = (let _107_143 = (FStar_List.nth args' 0)
in (qbody_to_string _107_143))
in (FStar_Util.format3 "(%s (%s). %s)" _107_146 _107_145 _107_144))))
end else begin
if ((is_infix_type_op t) && ((FStar_List.length args') = 2)) then begin
(let _107_151 = (let _107_147 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _107_147 arg_to_string))
in (let _107_150 = (FStar_All.pipe_right t infix_type_op_to_string)
in (let _107_149 = (let _107_148 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _107_148 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _107_151 _107_150 _107_149))))
end else begin
if ((is_unary_type_op t) && ((FStar_List.length args') = 1)) then begin
(let _107_154 = (FStar_All.pipe_right t unary_type_op_to_string)
in (let _107_153 = (let _107_152 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _107_152 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _107_154 _107_153)))
end else begin
(let _107_156 = (FStar_All.pipe_right t typ_to_string)
in (let _107_155 = (FStar_All.pipe_right args args_to_string)
in (FStar_Util.format2 "(%s %s)" _107_156 _107_155)))
end
end
end
end
end))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(let _107_158 = (binders_to_string " " binders)
in (let _107_157 = (FStar_All.pipe_right t2 typ_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _107_158 _107_157)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _107_160 = (typ_to_string t)
in (let _107_159 = (kind_to_string k)
in (FStar_Util.format2 "(%s <: %s)" _107_160 _107_159)))
end else begin
(FStar_All.pipe_right t typ_to_string)
end
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"<UNKNOWN>"
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(match ((FStar_Absyn_Visit.compress_typ_aux false x)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_28_335); FStar_Absyn_Syntax.tk = _28_333; FStar_Absyn_Syntax.pos = _28_331; FStar_Absyn_Syntax.fvs = _28_329; FStar_Absyn_Syntax.uvs = _28_327} -> begin
(uvar_t_to_string (uv, k))
end
| t -> begin
(FStar_All.pipe_right t typ_to_string)
end)
end)))
and uvar_t_to_string : (FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd)  ->  Prims.string = (fun _28_341 -> (match (_28_341) with
| (uv, k) -> begin
if (false && (FStar_ST.read FStar_Options.print_real_names)) then begin
(let _107_164 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _107_162 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _107_162))
end
in (let _107_163 = (kind_to_string k)
in (FStar_Util.format2 "(U%s : %s)" _107_164 _107_163)))
end else begin
(let _107_166 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _107_165 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _107_165))
end
in (FStar_Util.format1 "U%s" _107_166))
end
end))
and imp_to_string : Prims.string  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s _28_5 -> (match (_28_5) with
| Some (FStar_Absyn_Syntax.Implicit (_28_345)) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Absyn_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _28_351 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (match (b) with
| (FStar_Util.Inl (a), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _107_171 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _107_171 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp a.FStar_Absyn_Syntax.v))) then begin
(kind_to_string a.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits)))) then begin
(let _107_172 = (strBvd a.FStar_Absyn_Syntax.v)
in (imp_to_string _107_172 imp))
end else begin
(let _107_176 = (let _107_175 = (let _107_173 = (strBvd a.FStar_Absyn_Syntax.v)
in (Prims.strcat _107_173 ":"))
in (let _107_174 = (kind_to_string a.FStar_Absyn_Syntax.sort)
in (Prims.strcat _107_175 _107_174)))
in (imp_to_string _107_176 imp))
end
end
end
| (FStar_Util.Inr (x), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _107_177 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _107_177 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp x.FStar_Absyn_Syntax.v))) then begin
(typ_to_string x.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits)))) then begin
(let _107_178 = (strBvd x.FStar_Absyn_Syntax.v)
in (imp_to_string _107_178 imp))
end else begin
(let _107_182 = (let _107_181 = (let _107_179 = (strBvd x.FStar_Absyn_Syntax.v)
in (Prims.strcat _107_179 ":"))
in (let _107_180 = (typ_to_string x.FStar_Absyn_Syntax.sort)
in (Prims.strcat _107_181 _107_180)))
in (imp_to_string _107_182 imp))
end
end
end))
and binder_to_string : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Absyn_Syntax.binders  ->  Prims.string = (fun sep bs -> (
# 273 "FStar.Absyn.Print.fst"
let bs = if (FStar_ST.read FStar_Options.print_implicits) then begin
bs
end else begin
(filter_imp bs)
end
in if (sep = " -> ") then begin
(let _107_187 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _107_187 (FStar_String.concat sep)))
end else begin
(let _107_188 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _107_188 (FStar_String.concat sep)))
end))
and arg_to_string : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _28_6 -> (match (_28_6) with
| (FStar_Util.Inl (a), imp) -> begin
(let _107_190 = (typ_to_string a)
in (imp_to_string _107_190 imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _107_191 = (exp_to_string x)
in (imp_to_string _107_191 imp))
end))
and args_to_string : FStar_Absyn_Syntax.args  ->  Prims.string = (fun args -> (
# 283 "FStar.Absyn.Print.fst"
let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _107_193 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _107_193 (FStar_String.concat " ")))))
and lcomp_typ_to_string : FStar_Absyn_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _107_196 = (sli lc.FStar_Absyn_Syntax.eff_name)
in (let _107_195 = (typ_to_string lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _107_196 _107_195))))
and comp_typ_to_string : FStar_Absyn_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _107_198 = (typ_to_string t)
in (FStar_Util.format1 "Tot %s" _107_198))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(
# 293 "FStar.Absyn.Print.fst"
let basic = if ((FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _28_7 -> (match (_28_7) with
| FStar_Absyn_Syntax.TOTAL -> begin
true
end
| _28_387 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args)))) then begin
(let _107_200 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _107_200))
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_Ident.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid)) then begin
(typ_to_string c.FStar_Absyn_Syntax.result_typ)
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _28_8 -> (match (_28_8) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _28_391 -> begin
false
end))))) then begin
(let _107_202 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _107_202))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _107_206 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _107_205 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (let _107_204 = (let _107_203 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.effect_args (FStar_List.map effect_arg_to_string))
in (FStar_All.pipe_right _107_203 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _107_206 _107_205 _107_204))))
end else begin
(let _107_208 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _107_207 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _107_208 _107_207)))
end
end
end
end
in (
# 303 "FStar.Absyn.Print.fst"
let dec = (let _107_212 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.collect (fun _28_9 -> (match (_28_9) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _107_211 = (let _107_210 = (exp_to_string e)
in (FStar_Util.format1 " (decreases %s)" _107_210))
in (_107_211)::[])
end
| _28_397 -> begin
[]
end))))
in (FStar_All.pipe_right _107_212 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and effect_arg_to_string : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun e -> (match (e) with
| (FStar_Util.Inr (e), _28_403) -> begin
(exp_to_string e)
end
| (FStar_Util.Inl (wp), _28_408) -> begin
(formula_to_string wp)
end))
and formula_to_string : FStar_Absyn_Syntax.typ  ->  Prims.string = (fun phi -> (typ_to_string phi))
and formula_to_string_old_now_unused : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun phi -> (
# 315 "FStar.Absyn.Print.fst"
let const_op = (fun f _28_414 -> f)
in (
# 316 "FStar.Absyn.Print.fst"
let un_op = (fun f _28_10 -> (match (_28_10) with
| (FStar_Util.Inl (t), _28_422)::[] -> begin
(let _107_224 = (formula_to_string t)
in (FStar_Util.format2 "%s %s" f _107_224))
end
| _28_426 -> begin
(FStar_All.failwith "impos")
end))
in (
# 319 "FStar.Absyn.Print.fst"
let bin_top = (fun f _28_11 -> (match (_28_11) with
| (FStar_Util.Inl (t1), _28_438)::(FStar_Util.Inl (t2), _28_433)::[] -> begin
(let _107_230 = (formula_to_string t1)
in (let _107_229 = (formula_to_string t2)
in (FStar_Util.format3 "%s %s %s" _107_230 f _107_229)))
end
| _28_442 -> begin
(FStar_All.failwith "Impos")
end))
in (
# 326 "FStar.Absyn.Print.fst"
let bin_eop = (fun f _28_12 -> (match (_28_12) with
| (FStar_Util.Inr (e1), _28_454)::(FStar_Util.Inr (e2), _28_449)::[] -> begin
(let _107_236 = (exp_to_string e1)
in (let _107_235 = (exp_to_string e2)
in (FStar_Util.format3 "%s %s %s" _107_236 f _107_235)))
end
| _28_458 -> begin
(FStar_All.failwith "impos")
end))
in (
# 329 "FStar.Absyn.Print.fst"
let ite = (fun _28_13 -> (match (_28_13) with
| (FStar_Util.Inl (t1), _28_473)::(FStar_Util.Inl (t2), _28_468)::(FStar_Util.Inl (t3), _28_463)::[] -> begin
(let _107_241 = (formula_to_string t1)
in (let _107_240 = (formula_to_string t2)
in (let _107_239 = (formula_to_string t3)
in (FStar_Util.format3 "if %s then %s else %s" _107_241 _107_240 _107_239))))
end
| _28_477 -> begin
(FStar_All.failwith "impos")
end))
in (
# 332 "FStar.Absyn.Print.fst"
let eq_op = (fun _28_14 -> (match (_28_14) with
| (FStar_Util.Inl (t1), _28_498)::(FStar_Util.Inl (t2), _28_493)::(FStar_Util.Inr (e1), _28_488)::(FStar_Util.Inr (e2), _28_483)::[] -> begin
if (FStar_ST.read FStar_Options.print_implicits) then begin
(let _107_247 = (typ_to_string t1)
in (let _107_246 = (typ_to_string t2)
in (let _107_245 = (exp_to_string e1)
in (let _107_244 = (exp_to_string e2)
in (FStar_Util.format4 "Eq2 %s %s %s %s" _107_247 _107_246 _107_245 _107_244)))))
end else begin
(let _107_249 = (exp_to_string e1)
in (let _107_248 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _107_249 _107_248)))
end
end
| (FStar_Util.Inr (e1), _28_509)::(FStar_Util.Inr (e2), _28_504)::[] -> begin
(let _107_251 = (exp_to_string e1)
in (let _107_250 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _107_251 _107_250)))
end
| _28_513 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 339 "FStar.Absyn.Print.fst"
let connectives = ((FStar_Absyn_Const.and_lid, (bin_top "/\\")))::((FStar_Absyn_Const.or_lid, (bin_top "\\/")))::((FStar_Absyn_Const.imp_lid, (bin_top "==>")))::((FStar_Absyn_Const.iff_lid, (bin_top "<==>")))::((FStar_Absyn_Const.ite_lid, ite))::((FStar_Absyn_Const.not_lid, (un_op "~")))::((FStar_Absyn_Const.eqT_lid, (bin_top "==")))::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op "True")))::((FStar_Absyn_Const.false_lid, (const_op "False")))::[]
in (
# 351 "FStar.Absyn.Print.fst"
let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (binders, phi) -> begin
(let _107_290 = (binders_to_string " " binders)
in (let _107_289 = (formula_to_string phi)
in (FStar_Util.format2 "(fun %s => %s)" _107_290 _107_289)))
end
| _28_523 -> begin
(typ_to_string phi)
end))
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _28_533 -> (match (_28_533) with
| (l, _28_532) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_28_536, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, _28_542, body)) -> begin
(let _107_308 = (binders_to_string " " vars)
in (let _107_307 = (formula_to_string body)
in (FStar_Util.format2 "(forall %s. %s)" _107_308 _107_307)))
end
| Some (FStar_Absyn_Util.QEx (vars, _28_549, body)) -> begin
(let _107_310 = (binders_to_string " " vars)
in (let _107_309 = (formula_to_string body)
in (FStar_Util.format2 "(exists %s. %s)" _107_310 _107_309)))
end))))))))))
and exp_to_string : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun x -> (match ((let _107_312 = (FStar_Absyn_Util.compress_exp x)
in _107_312.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_delayed (_28_556) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _28_560)) -> begin
(exp_to_string e)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(uvar_e_to_string (uv, t))
end
| FStar_Absyn_Syntax.Exp_bvar (bvv) -> begin
(strBvd bvv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_fvar (fv, _28_572) -> begin
(sli fv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(FStar_All.pipe_right c const_to_string)
end
| FStar_Absyn_Syntax.Exp_abs (binders, e) -> begin
(let _107_314 = (binders_to_string " " binders)
in (let _107_313 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _107_314 _107_313)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(
# 378 "FStar.Absyn.Print.fst"
let lex = if (FStar_ST.read FStar_Options.print_implicits) then begin
None
end else begin
(reconstruct_lex x)
end
in (match (lex) with
| Some (es) -> begin
(let _107_317 = (let _107_316 = (let _107_315 = (FStar_List.map exp_to_string es)
in (FStar_String.concat "; " _107_315))
in (Prims.strcat "%[" _107_316))
in (Prims.strcat _107_317 "]"))
end
| None -> begin
(
# 382 "FStar.Absyn.Print.fst"
let args' = (let _107_319 = (filter_imp args)
in (FStar_All.pipe_right _107_319 (FStar_List.filter (fun _28_15 -> (match (_28_15) with
| (FStar_Util.Inr (_28_591), _28_594) -> begin
true
end
| _28_597 -> begin
false
end)))))
in if ((is_infix_prim_op e) && ((FStar_List.length args') = 2)) then begin
(let _107_324 = (let _107_320 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _107_320 arg_to_string))
in (let _107_323 = (FStar_All.pipe_right e infix_prim_op_to_string)
in (let _107_322 = (let _107_321 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _107_321 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _107_324 _107_323 _107_322))))
end else begin
if ((is_unary_prim_op e) && ((FStar_List.length args') = 1)) then begin
(let _107_327 = (FStar_All.pipe_right e unary_prim_op_to_string)
in (let _107_326 = (let _107_325 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _107_325 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _107_327 _107_326)))
end else begin
(let _107_329 = (FStar_All.pipe_right e exp_to_string)
in (let _107_328 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _107_329 _107_328)))
end
end)
end))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _107_337 = (FStar_All.pipe_right e exp_to_string)
in (let _107_336 = (let _107_335 = (FStar_All.pipe_right pats (FStar_List.map (fun _28_606 -> (match (_28_606) with
| (p, wopt, e) -> begin
(let _107_334 = (FStar_All.pipe_right p pat_to_string)
in (let _107_333 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _107_331 = (FStar_All.pipe_right w exp_to_string)
in (FStar_Util.format1 "when %s" _107_331))
end)
in (let _107_332 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format3 "%s %s -> %s" _107_334 _107_333 _107_332))))
end))))
in (FStar_Util.concat_l "\n\t" _107_335))
in (FStar_Util.format2 "(match %s with %s)" _107_337 _107_336)))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _28_613) -> begin
(let _107_339 = (FStar_All.pipe_right e exp_to_string)
in (let _107_338 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "(%s:%s)" _107_339 _107_338)))
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(let _107_341 = (lbs_to_string lbs)
in (let _107_340 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "%s in %s" _107_341 _107_340)))
end))
and uvar_e_to_string : (FStar_Absyn_Syntax.uvar_e * FStar_Absyn_Syntax.typ)  ->  Prims.string = (fun _28_623 -> (match (_28_623) with
| (uv, _28_622) -> begin
(let _107_344 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _107_343 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _107_343))
end
in (Prims.strcat "\'e" _107_344))
end))
and lbs_to_string : FStar_Absyn_Syntax.letbindings  ->  Prims.string = (fun lbs -> (let _107_351 = (let _107_350 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _107_349 = (lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _107_348 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbtyp typ_to_string)
in (let _107_347 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbdef exp_to_string)
in (FStar_Util.format3 "%s:%s = %s" _107_349 _107_348 _107_347)))))))
in (FStar_Util.concat_l "\n and " _107_350))
in (FStar_Util.format2 "let %s %s" (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _107_351)))
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
and either_l_to_string : Prims.string  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either Prims.list  ->  Prims.string = (fun delim l -> (let _107_356 = (FStar_All.pipe_right l (FStar_List.map either_to_string))
in (FStar_All.pipe_right _107_356 (FStar_Util.concat_l delim))))
and meta_to_string : FStar_Absyn_Syntax.meta_t  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Meta_refresh_label (t, _28_641, _28_643) -> begin
(let _107_358 = (typ_to_string t)
in (FStar_Util.format1 "(refresh) %s" _107_358))
end
| FStar_Absyn_Syntax.Meta_labeled (t, l, _28_649, _28_651) -> begin
(let _107_359 = (typ_to_string t)
in (FStar_Util.format2 "(labeled \"%s\") %s" l _107_359))
end
| FStar_Absyn_Syntax.Meta_named (_28_655, l) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Meta_pattern (t, ps) -> begin
(let _107_361 = (pats_to_string ps)
in (let _107_360 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "{:pattern %s} %s" _107_361 _107_360)))
end
| FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _28_666) -> begin
(let _107_363 = (formula_to_string t1)
in (let _107_362 = (formula_to_string t2)
in (FStar_Util.format2 "%s /\\ %s" _107_363 _107_362)))
end))
and pats_to_string : FStar_Absyn_Syntax.arg Prims.list Prims.list  ->  Prims.string = (fun ps -> (let _107_367 = (FStar_All.pipe_right ps (FStar_List.map (fun e -> (let _107_366 = (FStar_All.pipe_right e (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _107_366 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _107_367 (FStar_String.concat " \\/ "))))
and kind_to_string : FStar_Absyn_Syntax.knd  ->  Prims.string = (fun x -> (match ((let _107_369 = (FStar_Absyn_Util.compress_kind x)
in _107_369.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_lam (_28_673) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Kind_delayed (_28_676) -> begin
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
(let _107_371 = (sli n)
in (let _107_370 = (args_to_string args)
in (FStar_Util.format2 "%s %s" _107_371 _107_370)))
end
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(let _107_373 = (binders_to_string " -> " binders)
in (let _107_372 = (FStar_All.pipe_right k kind_to_string)
in (FStar_Util.format2 "(%s -> %s)" _107_373 _107_372)))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun uv -> (let _107_375 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _107_374 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _107_374))
end
in (Prims.strcat "\'k_" _107_375)))
and uvar_k_to_string' : ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list)  ->  Prims.string = (fun _28_698 -> (match (_28_698) with
| (uv, args) -> begin
(
# 448 "FStar.Absyn.Print.fst"
let str = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _107_377 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _107_377))
end
in (let _107_378 = (args_to_string args)
in (FStar_Util.format2 "(\'k_%s %s)" str _107_378)))
end))
and pat_to_string : FStar_Absyn_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (l, _28_703, pats) -> begin
(let _107_383 = (sli l.FStar_Absyn_Syntax.v)
in (let _107_382 = (let _107_381 = (FStar_List.map (fun _28_709 -> (match (_28_709) with
| (x, b) -> begin
(
# 452 "FStar.Absyn.Print.fst"
let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _107_381 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _107_383 _107_382)))
end
| FStar_Absyn_Syntax.Pat_dot_term (x, _28_713) -> begin
(let _107_384 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".%s" _107_384))
end
| FStar_Absyn_Syntax.Pat_dot_typ (x, _28_718) -> begin
(let _107_385 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".\'%s" _107_385))
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
| FStar_Absyn_Syntax.Pat_wild (_28_728) -> begin
"_"
end
| FStar_Absyn_Syntax.Pat_twild (_28_731) -> begin
"\'_"
end
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(let _107_386 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _107_386))
end))

# 462 "FStar.Absyn.Print.fst"
let subst_to_string = (fun subst -> (let _107_394 = (let _107_393 = (FStar_List.map (fun _28_16 -> (match (_28_16) with
| FStar_Util.Inl (a, t) -> begin
(let _107_390 = (strBvd a)
in (let _107_389 = (typ_to_string t)
in (FStar_Util.format2 "(%s -> %s)" _107_390 _107_389)))
end
| FStar_Util.Inr (x, e) -> begin
(let _107_392 = (strBvd x)
in (let _107_391 = (exp_to_string e)
in (FStar_Util.format2 "(%s -> %s)" _107_392 _107_391)))
end)) subst)
in (FStar_All.pipe_right _107_393 (FStar_String.concat ", ")))
in (FStar_All.pipe_left (FStar_Util.format1 "{%s}") _107_394)))

# 467 "FStar.Absyn.Print.fst"
let freevars_to_string : FStar_Absyn_Syntax.freevars  ->  Prims.string = (fun fvs -> (
# 468 "FStar.Absyn.Print.fst"
let f = (fun l -> (let _107_400 = (let _107_399 = (FStar_All.pipe_right l FStar_Util.set_elements)
in (FStar_All.pipe_right _107_399 (FStar_List.map (fun t -> (strBvd t.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _107_400 (FStar_String.concat ", "))))
in (let _107_402 = (f fvs.FStar_Absyn_Syntax.ftvs)
in (let _107_401 = (f fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_Util.format2 "ftvs={%s}, fxvs={%s}" _107_402 _107_401)))))

# 471 "FStar.Absyn.Print.fst"
let qual_to_string : FStar_Absyn_Syntax.qualifier  ->  Prims.string = (fun _28_17 -> (match (_28_17) with
| FStar_Absyn_Syntax.Logic -> begin
"logic"
end
| FStar_Absyn_Syntax.Opaque -> begin
"opaque"
end
| FStar_Absyn_Syntax.Discriminator (_28_755) -> begin
"discriminator"
end
| FStar_Absyn_Syntax.Projector (_28_758) -> begin
"projector"
end
| FStar_Absyn_Syntax.RecordType (ids) -> begin
(let _107_407 = (let _107_406 = (FStar_All.pipe_right ids (FStar_List.map (fun lid -> lid.FStar_Ident.ident.FStar_Ident.idText)))
in (FStar_All.pipe_right _107_406 (FStar_String.concat ", ")))
in (FStar_Util.format1 "record(%s)" _107_407))
end
| _28_764 -> begin
"other"
end))

# 478 "FStar.Absyn.Print.fst"
let quals_to_string : FStar_Absyn_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (let _107_410 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _107_410 (FStar_String.concat " "))))

# 479 "FStar.Absyn.Print.fst"
let rec sigelt_to_string : FStar_Absyn_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.ResetOptions, _28_769) -> begin
"#reset-options"
end
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.SetOptions (s), _28_775) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _28_782, _28_784, quals, _28_787) -> begin
(let _107_415 = (quals_to_string quals)
in (let _107_414 = (binders_to_string " " tps)
in (let _107_413 = (kind_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _107_415 lid.FStar_Ident.str _107_414 _107_413))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, _28_795, _28_797) -> begin
(let _107_418 = (binders_to_string " " tps)
in (let _107_417 = (kind_to_string k)
in (let _107_416 = (typ_to_string t)
in (FStar_Util.format4 "type %s %s : %s = %s" lid.FStar_Ident.str _107_418 _107_417 _107_416))))
end
| FStar_Absyn_Syntax.Sig_datacon (lid, t, _28_803, _28_805, _28_807, _28_809) -> begin
(let _107_419 = (typ_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _107_419))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _28_816) -> begin
(let _107_421 = (quals_to_string quals)
in (let _107_420 = (typ_to_string t)
in (FStar_Util.format3 "%s val %s : %s" _107_421 lid.FStar_Ident.str _107_420)))
end
| FStar_Absyn_Syntax.Sig_assume (lid, f, _28_822, _28_824) -> begin
(let _107_422 = (typ_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _107_422))
end
| FStar_Absyn_Syntax.Sig_let (lbs, _28_829, _28_831, b) -> begin
(lbs_to_string lbs)
end
| FStar_Absyn_Syntax.Sig_main (e, _28_837) -> begin
(let _107_423 = (exp_to_string e)
in (FStar_Util.format1 "let _ = %s" _107_423))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _28_842, _28_844, _28_846) -> begin
(let _107_424 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _107_424 (FStar_String.concat "\n")))
end
| FStar_Absyn_Syntax.Sig_new_effect (_28_850) -> begin
"new_effect { ... }"
end
| FStar_Absyn_Syntax.Sig_sub_effect (_28_853) -> begin
"sub_effect ..."
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_28_856) -> begin
"kind ..."
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, tps, c, _28_862, _28_864) -> begin
(let _107_427 = (sli l)
in (let _107_426 = (binders_to_string " " tps)
in (let _107_425 = (comp_typ_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _107_427 _107_426 _107_425))))
end))

# 495 "FStar.Absyn.Print.fst"
let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _107_432 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _107_432 msg)))

# 497 "FStar.Absyn.Print.fst"
let rec sigelt_to_string_short : FStar_Absyn_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_let ((_28_871, {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _28_875; FStar_Absyn_Syntax.lbdef = _28_873}::[]), _28_883, _28_885, _28_887) -> begin
(let _107_435 = (typ_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Ident.str _107_435))
end
| _28_891 -> begin
(let _107_438 = (let _107_437 = (FStar_Absyn_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _107_437 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _107_438 (FStar_String.concat ", ")))
end))

# 501 "FStar.Absyn.Print.fst"
let rec modul_to_string : FStar_Absyn_Syntax.modul  ->  Prims.string = (fun m -> (let _107_443 = (sli m.FStar_Absyn_Syntax.name)
in (let _107_442 = (let _107_441 = (FStar_List.map sigelt_to_string m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _107_441 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _107_443 _107_442))))




