
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
let rec reconstruct_lex : FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _110_28 = (FStar_Absyn_Util.compress_exp e)
in _110_28.FStar_Absyn_Syntax.n)) with
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
(match ((let _110_31 = (FStar_List.nth exps 1)
in (reconstruct_lex _110_31))) with
| Some (xs) -> begin
(let _110_33 = (let _110_32 = (FStar_List.nth exps 0)
in (_110_32)::xs)
in Some (_110_33))
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
let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _110_47 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _110_47)))

# 123 "FStar.Absyn.Print.fst"
let infix_prim_op_to_string = (fun e -> (let _110_49 = (get_lid e)
in (find_lid _110_49 infix_prim_ops)))

# 124 "FStar.Absyn.Print.fst"
let unary_prim_op_to_string = (fun e -> (let _110_51 = (get_lid e)
in (find_lid _110_51 unary_prim_ops)))

# 125 "FStar.Absyn.Print.fst"
let infix_type_op_to_string = (fun t -> (let _110_53 = (get_type_lid t)
in (find_lid _110_53 infix_type_ops)))

# 126 "FStar.Absyn.Print.fst"
let unary_type_op_to_string = (fun t -> (let _110_55 = (get_type_lid t)
in (find_lid _110_55 unary_type_ops)))

# 128 "FStar.Absyn.Print.fst"
let quant_to_string = (fun t -> (let _110_57 = (get_type_lid t)
in (find_lid _110_57 quants)))

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
let _28_127 = (let _110_62 = (FStar_Util.substring_from bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText 1)
in (FStar_Util.int_of_string _110_62))
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
(let _110_103 = (tag_of_typ head)
in (let _110_102 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.format2 "Typ_app(%s, [%s args])" _110_103 _110_102)))
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
(let _110_107 = (meta_e_to_string m)
in (Prims.strcat "Exp_meta_desugared " _110_107))
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
(let _110_113 = (FStar_All.pipe_right meta meta_to_string)
in (FStar_Util.format1 "(Meta %s)" _110_113))
end
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(strBvd btv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(sli v.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_fun (binders, c) -> begin
(let _110_115 = (binders_to_string " -> " binders)
in (let _110_114 = (comp_typ_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _110_115 _110_114)))
end
| FStar_Absyn_Syntax.Typ_refine (xt, f) -> begin
(let _110_118 = (strBvd xt.FStar_Absyn_Syntax.v)
in (let _110_117 = (FStar_All.pipe_right xt.FStar_Absyn_Syntax.sort typ_to_string)
in (let _110_116 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "%s:%s{%s}" _110_118 _110_117 _110_116))))
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
(let _110_129 = (tag_of_typ t)
in (let _110_128 = (typ_to_string t)
in (FStar_Util.format2 "<Expected a type-lambda! got %s>%s" _110_129 _110_128)))
end))
end
| FStar_Util.Inr (e) -> begin
(let _110_130 = (exp_to_string e)
in (FStar_Util.format1 "(<Expected a type!>%s)" _110_130))
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
(let _110_140 = (let _110_135 = (FStar_List.nth args 0)
in (arg_to_string _110_135))
in (let _110_139 = (let _110_136 = (FStar_List.nth args 1)
in (arg_to_string _110_136))
in (let _110_138 = (let _110_137 = (FStar_List.nth args 2)
in (arg_to_string _110_137))
in (FStar_Util.format3 "if %s then %s else %s" _110_140 _110_139 _110_138))))
end else begin
if ((is_b2t t) && ((FStar_List.length args) = 1)) then begin
(let _110_141 = (FStar_List.nth args 0)
in (FStar_All.pipe_right _110_141 arg_to_string))
end else begin
if ((is_quant t) && ((FStar_List.length args) <= 2)) then begin
(let _110_146 = (quant_to_string t)
in (let _110_145 = (let _110_142 = (FStar_List.nth args' 0)
in (qbinder_to_string _110_142))
in (let _110_144 = (let _110_143 = (FStar_List.nth args' 0)
in (qbody_to_string _110_143))
in (FStar_Util.format3 "(%s (%s). %s)" _110_146 _110_145 _110_144))))
end else begin
if ((is_infix_type_op t) && ((FStar_List.length args') = 2)) then begin
(let _110_151 = (let _110_147 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _110_147 arg_to_string))
in (let _110_150 = (FStar_All.pipe_right t infix_type_op_to_string)
in (let _110_149 = (let _110_148 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _110_148 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _110_151 _110_150 _110_149))))
end else begin
if ((is_unary_type_op t) && ((FStar_List.length args') = 1)) then begin
(let _110_154 = (FStar_All.pipe_right t unary_type_op_to_string)
in (let _110_153 = (let _110_152 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _110_152 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _110_154 _110_153)))
end else begin
(let _110_156 = (FStar_All.pipe_right t typ_to_string)
in (let _110_155 = (FStar_All.pipe_right args args_to_string)
in (FStar_Util.format2 "(%s %s)" _110_156 _110_155)))
end
end
end
end
end))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(let _110_158 = (binders_to_string " " binders)
in (let _110_157 = (FStar_All.pipe_right t2 typ_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _110_158 _110_157)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _110_160 = (typ_to_string t)
in (let _110_159 = (kind_to_string k)
in (FStar_Util.format2 "(%s <: %s)" _110_160 _110_159)))
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
(let _110_164 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _110_162 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _110_162))
end
in (let _110_163 = (kind_to_string k)
in (FStar_Util.format2 "(U%s : %s)" _110_164 _110_163)))
end else begin
(let _110_166 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _110_165 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _110_165))
end
in (FStar_Util.format1 "U%s" _110_166))
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
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _110_171 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _110_171 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp a.FStar_Absyn_Syntax.v))) then begin
(kind_to_string a.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits)))) then begin
(let _110_172 = (strBvd a.FStar_Absyn_Syntax.v)
in (imp_to_string _110_172 imp))
end else begin
(let _110_176 = (let _110_175 = (let _110_173 = (strBvd a.FStar_Absyn_Syntax.v)
in (Prims.strcat _110_173 ":"))
in (let _110_174 = (kind_to_string a.FStar_Absyn_Syntax.sort)
in (Prims.strcat _110_175 _110_174)))
in (imp_to_string _110_176 imp))
end
end
end
| (FStar_Util.Inr (x), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _110_177 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _110_177 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp x.FStar_Absyn_Syntax.v))) then begin
(typ_to_string x.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits)))) then begin
(let _110_178 = (strBvd x.FStar_Absyn_Syntax.v)
in (imp_to_string _110_178 imp))
end else begin
(let _110_182 = (let _110_181 = (let _110_179 = (strBvd x.FStar_Absyn_Syntax.v)
in (Prims.strcat _110_179 ":"))
in (let _110_180 = (typ_to_string x.FStar_Absyn_Syntax.sort)
in (Prims.strcat _110_181 _110_180)))
in (imp_to_string _110_182 imp))
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
(let _110_187 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _110_187 (FStar_String.concat sep)))
end else begin
(let _110_188 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _110_188 (FStar_String.concat sep)))
end))
and arg_to_string : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _28_6 -> (match (_28_6) with
| (FStar_Util.Inl (a), imp) -> begin
(let _110_190 = (typ_to_string a)
in (imp_to_string _110_190 imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _110_191 = (exp_to_string x)
in (imp_to_string _110_191 imp))
end))
and args_to_string : FStar_Absyn_Syntax.args  ->  Prims.string = (fun args -> (
# 283 "FStar.Absyn.Print.fst"
let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _110_193 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _110_193 (FStar_String.concat " ")))))
and lcomp_typ_to_string : FStar_Absyn_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _110_196 = (sli lc.FStar_Absyn_Syntax.eff_name)
in (let _110_195 = (typ_to_string lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _110_196 _110_195))))
and comp_typ_to_string : FStar_Absyn_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _110_198 = (typ_to_string t)
in (FStar_Util.format1 "Tot %s" _110_198))
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
(let _110_200 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _110_200))
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
(let _110_202 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _110_202))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _110_206 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _110_205 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (let _110_204 = (let _110_203 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.effect_args (FStar_List.map effect_arg_to_string))
in (FStar_All.pipe_right _110_203 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _110_206 _110_205 _110_204))))
end else begin
(let _110_208 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _110_207 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _110_208 _110_207)))
end
end
end
end
in (
# 303 "FStar.Absyn.Print.fst"
let dec = (let _110_212 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.collect (fun _28_9 -> (match (_28_9) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _110_211 = (let _110_210 = (exp_to_string e)
in (FStar_Util.format1 " (decreases %s)" _110_210))
in (_110_211)::[])
end
| _28_397 -> begin
[]
end))))
in (FStar_All.pipe_right _110_212 (FStar_String.concat " ")))
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
(let _110_224 = (formula_to_string t)
in (FStar_Util.format2 "%s %s" f _110_224))
end
| _28_426 -> begin
(FStar_All.failwith "impos")
end))
in (
# 319 "FStar.Absyn.Print.fst"
let bin_top = (fun f _28_11 -> (match (_28_11) with
| (FStar_Util.Inl (t1), _28_438)::(FStar_Util.Inl (t2), _28_433)::[] -> begin
(let _110_230 = (formula_to_string t1)
in (let _110_229 = (formula_to_string t2)
in (FStar_Util.format3 "%s %s %s" _110_230 f _110_229)))
end
| _28_442 -> begin
(FStar_All.failwith "Impos")
end))
in (
# 326 "FStar.Absyn.Print.fst"
let bin_eop = (fun f _28_12 -> (match (_28_12) with
| (FStar_Util.Inr (e1), _28_454)::(FStar_Util.Inr (e2), _28_449)::[] -> begin
(let _110_236 = (exp_to_string e1)
in (let _110_235 = (exp_to_string e2)
in (FStar_Util.format3 "%s %s %s" _110_236 f _110_235)))
end
| _28_458 -> begin
(FStar_All.failwith "impos")
end))
in (
# 329 "FStar.Absyn.Print.fst"
let ite = (fun _28_13 -> (match (_28_13) with
| (FStar_Util.Inl (t1), _28_473)::(FStar_Util.Inl (t2), _28_468)::(FStar_Util.Inl (t3), _28_463)::[] -> begin
(let _110_241 = (formula_to_string t1)
in (let _110_240 = (formula_to_string t2)
in (let _110_239 = (formula_to_string t3)
in (FStar_Util.format3 "if %s then %s else %s" _110_241 _110_240 _110_239))))
end
| _28_477 -> begin
(FStar_All.failwith "impos")
end))
in (
# 332 "FStar.Absyn.Print.fst"
let eq_op = (fun _28_14 -> (match (_28_14) with
| (FStar_Util.Inl (t1), _28_498)::(FStar_Util.Inl (t2), _28_493)::(FStar_Util.Inr (e1), _28_488)::(FStar_Util.Inr (e2), _28_483)::[] -> begin
if (FStar_ST.read FStar_Options.print_implicits) then begin
(let _110_247 = (typ_to_string t1)
in (let _110_246 = (typ_to_string t2)
in (let _110_245 = (exp_to_string e1)
in (let _110_244 = (exp_to_string e2)
in (FStar_Util.format4 "Eq2 %s %s %s %s" _110_247 _110_246 _110_245 _110_244)))))
end else begin
(let _110_249 = (exp_to_string e1)
in (let _110_248 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _110_249 _110_248)))
end
end
| (FStar_Util.Inr (e1), _28_509)::(FStar_Util.Inr (e2), _28_504)::[] -> begin
(let _110_251 = (exp_to_string e1)
in (let _110_250 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _110_251 _110_250)))
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
(let _110_290 = (binders_to_string " " binders)
in (let _110_289 = (formula_to_string phi)
in (FStar_Util.format2 "(fun %s => %s)" _110_290 _110_289)))
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
(let _110_308 = (binders_to_string " " vars)
in (let _110_307 = (formula_to_string body)
in (FStar_Util.format2 "(forall %s. %s)" _110_308 _110_307)))
end
| Some (FStar_Absyn_Util.QEx (vars, _28_549, body)) -> begin
(let _110_310 = (binders_to_string " " vars)
in (let _110_309 = (formula_to_string body)
in (FStar_Util.format2 "(exists %s. %s)" _110_310 _110_309)))
end))))))))))
and exp_to_string : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun x -> (match ((let _110_312 = (FStar_Absyn_Util.compress_exp x)
in _110_312.FStar_Absyn_Syntax.n)) with
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
(let _110_314 = (binders_to_string " " binders)
in (let _110_313 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _110_314 _110_313)))
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
(let _110_317 = (let _110_316 = (let _110_315 = (FStar_List.map exp_to_string es)
in (FStar_String.concat "; " _110_315))
in (Prims.strcat "%[" _110_316))
in (Prims.strcat _110_317 "]"))
end
| None -> begin
(
# 382 "FStar.Absyn.Print.fst"
let args' = (let _110_319 = (filter_imp args)
in (FStar_All.pipe_right _110_319 (FStar_List.filter (fun _28_15 -> (match (_28_15) with
| (FStar_Util.Inr (_28_591), _28_594) -> begin
true
end
| _28_597 -> begin
false
end)))))
in if ((is_infix_prim_op e) && ((FStar_List.length args') = 2)) then begin
(let _110_324 = (let _110_320 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _110_320 arg_to_string))
in (let _110_323 = (FStar_All.pipe_right e infix_prim_op_to_string)
in (let _110_322 = (let _110_321 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _110_321 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _110_324 _110_323 _110_322))))
end else begin
if ((is_unary_prim_op e) && ((FStar_List.length args') = 1)) then begin
(let _110_327 = (FStar_All.pipe_right e unary_prim_op_to_string)
in (let _110_326 = (let _110_325 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _110_325 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _110_327 _110_326)))
end else begin
(let _110_329 = (FStar_All.pipe_right e exp_to_string)
in (let _110_328 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _110_329 _110_328)))
end
end)
end))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _110_337 = (FStar_All.pipe_right e exp_to_string)
in (let _110_336 = (let _110_335 = (FStar_All.pipe_right pats (FStar_List.map (fun _28_606 -> (match (_28_606) with
| (p, wopt, e) -> begin
(let _110_334 = (FStar_All.pipe_right p pat_to_string)
in (let _110_333 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _110_331 = (FStar_All.pipe_right w exp_to_string)
in (FStar_Util.format1 "when %s" _110_331))
end)
in (let _110_332 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format3 "%s %s -> %s" _110_334 _110_333 _110_332))))
end))))
in (FStar_Util.concat_l "\n\t" _110_335))
in (FStar_Util.format2 "(match %s with %s)" _110_337 _110_336)))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _28_613) -> begin
(let _110_339 = (FStar_All.pipe_right e exp_to_string)
in (let _110_338 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "(%s:%s)" _110_339 _110_338)))
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(let _110_341 = (lbs_to_string lbs)
in (let _110_340 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "%s in %s" _110_341 _110_340)))
end))
and uvar_e_to_string : (FStar_Absyn_Syntax.uvar_e * FStar_Absyn_Syntax.typ)  ->  Prims.string = (fun _28_623 -> (match (_28_623) with
| (uv, _28_622) -> begin
(let _110_344 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _110_343 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _110_343))
end
in (Prims.strcat "\'e" _110_344))
end))
and lbs_to_string : FStar_Absyn_Syntax.letbindings  ->  Prims.string = (fun lbs -> (let _110_351 = (let _110_350 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _110_349 = (lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _110_348 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbtyp typ_to_string)
in (let _110_347 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbdef exp_to_string)
in (FStar_Util.format3 "%s:%s = %s" _110_349 _110_348 _110_347)))))))
in (FStar_Util.concat_l "\n and " _110_350))
in (FStar_Util.format2 "let %s %s" (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _110_351)))
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
and either_l_to_string : Prims.string  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either Prims.list  ->  Prims.string = (fun delim l -> (let _110_356 = (FStar_All.pipe_right l (FStar_List.map either_to_string))
in (FStar_All.pipe_right _110_356 (FStar_Util.concat_l delim))))
and meta_to_string : FStar_Absyn_Syntax.meta_t  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Meta_refresh_label (t, _28_641, _28_643) -> begin
(let _110_358 = (typ_to_string t)
in (FStar_Util.format1 "(refresh) %s" _110_358))
end
| FStar_Absyn_Syntax.Meta_labeled (t, l, _28_649, _28_651) -> begin
(let _110_359 = (typ_to_string t)
in (FStar_Util.format2 "(labeled \"%s\") %s" l _110_359))
end
| FStar_Absyn_Syntax.Meta_named (_28_655, l) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Meta_pattern (t, ps) -> begin
(let _110_361 = (pats_to_string ps)
in (let _110_360 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "{:pattern %s} %s" _110_361 _110_360)))
end
| FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _28_666) -> begin
(let _110_363 = (formula_to_string t1)
in (let _110_362 = (formula_to_string t2)
in (FStar_Util.format2 "%s /\\ %s" _110_363 _110_362)))
end))
and pats_to_string : FStar_Absyn_Syntax.arg Prims.list Prims.list  ->  Prims.string = (fun ps -> (let _110_367 = (FStar_All.pipe_right ps (FStar_List.map (fun e -> (let _110_366 = (FStar_All.pipe_right e (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _110_366 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _110_367 (FStar_String.concat " \\/ "))))
and kind_to_string : FStar_Absyn_Syntax.knd  ->  Prims.string = (fun x -> (match ((let _110_369 = (FStar_Absyn_Util.compress_kind x)
in _110_369.FStar_Absyn_Syntax.n)) with
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
(let _110_371 = (sli n)
in (let _110_370 = (args_to_string args)
in (FStar_Util.format2 "%s %s" _110_371 _110_370)))
end
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(let _110_373 = (binders_to_string " -> " binders)
in (let _110_372 = (FStar_All.pipe_right k kind_to_string)
in (FStar_Util.format2 "(%s -> %s)" _110_373 _110_372)))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun uv -> (let _110_375 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _110_374 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _110_374))
end
in (Prims.strcat "\'k_" _110_375)))
and uvar_k_to_string' : ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list)  ->  Prims.string = (fun _28_698 -> (match (_28_698) with
| (uv, args) -> begin
(
# 448 "FStar.Absyn.Print.fst"
let str = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _110_377 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _110_377))
end
in (let _110_378 = (args_to_string args)
in (FStar_Util.format2 "(\'k_%s %s)" str _110_378)))
end))
and pat_to_string : FStar_Absyn_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (l, _28_703, pats) -> begin
(let _110_383 = (sli l.FStar_Absyn_Syntax.v)
in (let _110_382 = (let _110_381 = (FStar_List.map (fun _28_709 -> (match (_28_709) with
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
in (FStar_All.pipe_right _110_381 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _110_383 _110_382)))
end
| FStar_Absyn_Syntax.Pat_dot_term (x, _28_713) -> begin
(let _110_384 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".%s" _110_384))
end
| FStar_Absyn_Syntax.Pat_dot_typ (x, _28_718) -> begin
(let _110_385 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".\'%s" _110_385))
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
(let _110_386 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _110_386))
end))

# 462 "FStar.Absyn.Print.fst"
let subst_to_string = (fun subst -> (let _110_394 = (let _110_393 = (FStar_List.map (fun _28_16 -> (match (_28_16) with
| FStar_Util.Inl (a, t) -> begin
(let _110_390 = (strBvd a)
in (let _110_389 = (typ_to_string t)
in (FStar_Util.format2 "(%s -> %s)" _110_390 _110_389)))
end
| FStar_Util.Inr (x, e) -> begin
(let _110_392 = (strBvd x)
in (let _110_391 = (exp_to_string e)
in (FStar_Util.format2 "(%s -> %s)" _110_392 _110_391)))
end)) subst)
in (FStar_All.pipe_right _110_393 (FStar_String.concat ", ")))
in (FStar_All.pipe_left (FStar_Util.format1 "{%s}") _110_394)))

# 467 "FStar.Absyn.Print.fst"
let freevars_to_string : FStar_Absyn_Syntax.freevars  ->  Prims.string = (fun fvs -> (
# 468 "FStar.Absyn.Print.fst"
let f = (fun l -> (let _110_400 = (let _110_399 = (FStar_All.pipe_right l FStar_Util.set_elements)
in (FStar_All.pipe_right _110_399 (FStar_List.map (fun t -> (strBvd t.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _110_400 (FStar_String.concat ", "))))
in (let _110_402 = (f fvs.FStar_Absyn_Syntax.ftvs)
in (let _110_401 = (f fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_Util.format2 "ftvs={%s}, fxvs={%s}" _110_402 _110_401)))))

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
(let _110_407 = (let _110_406 = (FStar_All.pipe_right ids (FStar_List.map (fun lid -> lid.FStar_Ident.ident.FStar_Ident.idText)))
in (FStar_All.pipe_right _110_406 (FStar_String.concat ", ")))
in (FStar_Util.format1 "record(%s)" _110_407))
end
| _28_764 -> begin
"other"
end))

# 478 "FStar.Absyn.Print.fst"
let quals_to_string : FStar_Absyn_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (let _110_410 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _110_410 (FStar_String.concat " "))))

# 479 "FStar.Absyn.Print.fst"
let rec sigelt_to_string : FStar_Absyn_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.ResetOptions, _28_769) -> begin
"#reset-options"
end
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.SetOptions (s), _28_775) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _28_782, _28_784, quals, _28_787) -> begin
(let _110_415 = (quals_to_string quals)
in (let _110_414 = (binders_to_string " " tps)
in (let _110_413 = (kind_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _110_415 lid.FStar_Ident.str _110_414 _110_413))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, _28_795, _28_797) -> begin
(let _110_418 = (binders_to_string " " tps)
in (let _110_417 = (kind_to_string k)
in (let _110_416 = (typ_to_string t)
in (FStar_Util.format4 "type %s %s : %s = %s" lid.FStar_Ident.str _110_418 _110_417 _110_416))))
end
| FStar_Absyn_Syntax.Sig_datacon (lid, t, _28_803, _28_805, _28_807, _28_809) -> begin
(let _110_419 = (typ_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _110_419))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _28_816) -> begin
(let _110_421 = (quals_to_string quals)
in (let _110_420 = (typ_to_string t)
in (FStar_Util.format3 "%s val %s : %s" _110_421 lid.FStar_Ident.str _110_420)))
end
| FStar_Absyn_Syntax.Sig_assume (lid, f, _28_822, _28_824) -> begin
(let _110_422 = (typ_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _110_422))
end
| FStar_Absyn_Syntax.Sig_let (lbs, _28_829, _28_831, b) -> begin
(lbs_to_string lbs)
end
| FStar_Absyn_Syntax.Sig_main (e, _28_837) -> begin
(let _110_423 = (exp_to_string e)
in (FStar_Util.format1 "let _ = %s" _110_423))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _28_842, _28_844, _28_846) -> begin
(let _110_424 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _110_424 (FStar_String.concat "\n")))
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
(let _110_427 = (sli l)
in (let _110_426 = (binders_to_string " " tps)
in (let _110_425 = (comp_typ_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _110_427 _110_426 _110_425))))
end))

# 495 "FStar.Absyn.Print.fst"
let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _110_432 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _110_432 msg)))

# 497 "FStar.Absyn.Print.fst"
let rec sigelt_to_string_short : FStar_Absyn_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_let ((_28_871, {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _28_875; FStar_Absyn_Syntax.lbdef = _28_873}::[]), _28_883, _28_885, _28_887) -> begin
(let _110_435 = (typ_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Ident.str _110_435))
end
| _28_891 -> begin
(let _110_438 = (let _110_437 = (FStar_Absyn_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _110_437 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _110_438 (FStar_String.concat ", ")))
end))

# 501 "FStar.Absyn.Print.fst"
let rec modul_to_string : FStar_Absyn_Syntax.modul  ->  Prims.string = (fun m -> (let _110_443 = (sli m.FStar_Absyn_Syntax.name)
in (let _110_442 = (let _110_441 = (FStar_List.map sigelt_to_string m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _110_441 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _110_443 _110_442))))




