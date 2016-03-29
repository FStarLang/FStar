
open Prims
# 26 "FStar.Absyn.Print.fst"
let infix_prim_ops : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.op_Addition, "+"))::((FStar_Absyn_Const.op_Subtraction, "-"))::((FStar_Absyn_Const.op_Multiply, "*"))::((FStar_Absyn_Const.op_Division, "/"))::((FStar_Absyn_Const.op_Eq, "="))::((FStar_Absyn_Const.op_ColonEq, ":="))::((FStar_Absyn_Const.op_notEq, "<>"))::((FStar_Absyn_Const.op_And, "&&"))::((FStar_Absyn_Const.op_Or, "||"))::((FStar_Absyn_Const.op_LTE, "<="))::((FStar_Absyn_Const.op_GTE, ">="))::((FStar_Absyn_Const.op_LT, "<"))::((FStar_Absyn_Const.op_GT, ">"))::((FStar_Absyn_Const.op_Modulus, "mod"))::[]

# 44 "FStar.Absyn.Print.fst"
let unary_prim_ops : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.op_Negation, "not"))::((FStar_Absyn_Const.op_Minus, "-"))::[]

# 49 "FStar.Absyn.Print.fst"
let infix_type_ops : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.and_lid, "/\\"))::((FStar_Absyn_Const.or_lid, "\\/"))::((FStar_Absyn_Const.imp_lid, "==>"))::((FStar_Absyn_Const.iff_lid, "<==>"))::((FStar_Absyn_Const.precedes_lid, "<<"))::((FStar_Absyn_Const.eq2_lid, "=="))::((FStar_Absyn_Const.eqT_lid, "=="))::[]

# 59 "FStar.Absyn.Print.fst"
let unary_type_ops : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.not_lid, "~"))::[]

# 63 "FStar.Absyn.Print.fst"
let is_prim_op = (fun ps f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _22_22) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _22_26 -> begin
false
end))

# 67 "FStar.Absyn.Print.fst"
let is_type_op = (fun ps t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals ftv.FStar_Absyn_Syntax.v)))
end
| _22_32 -> begin
false
end))

# 71 "FStar.Absyn.Print.fst"
let get_lid = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _22_36) -> begin
fv.FStar_Absyn_Syntax.v
end
| _22_40 -> begin
(FStar_All.failwith "get_lid")
end))

# 75 "FStar.Absyn.Print.fst"
let get_type_lid = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
ftv.FStar_Absyn_Syntax.v
end
| _22_45 -> begin
(FStar_All.failwith "get_type_lid")
end))

# 79 "FStar.Absyn.Print.fst"
let is_infix_prim_op : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split infix_prim_ops)) e))

# 81 "FStar.Absyn.Print.fst"
let is_unary_prim_op : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split unary_prim_ops)) e))

# 82 "FStar.Absyn.Print.fst"
let is_infix_type_op : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op (Prims.fst (FStar_List.split infix_type_ops)) t))

# 83 "FStar.Absyn.Print.fst"
let is_unary_type_op : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op (Prims.fst (FStar_List.split unary_type_ops)) t))

# 84 "FStar.Absyn.Print.fst"
let quants : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.forall_lid, "forall"))::((FStar_Absyn_Const.exists_lid, "exists"))::((FStar_Absyn_Const.allTyp_lid, "forall"))::((FStar_Absyn_Const.exTyp_lid, "exists"))::[]

# 91 "FStar.Absyn.Print.fst"
let is_b2t : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op ((FStar_Absyn_Const.b2t_lid)::[]) t))

# 93 "FStar.Absyn.Print.fst"
let is_quant : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op (Prims.fst (FStar_List.split quants)) t))

# 94 "FStar.Absyn.Print.fst"
let is_ite : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op ((FStar_Absyn_Const.ite_lid)::[]) t))

# 95 "FStar.Absyn.Print.fst"
let is_lex_cons : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Absyn_Const.lexcons_lid)::[]) f))

# 97 "FStar.Absyn.Print.fst"
let is_lex_top : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Absyn_Const.lextop_lid)::[]) f))

# 98 "FStar.Absyn.Print.fst"
let is_inr = (fun _22_1 -> (match (_22_1) with
| FStar_Util.Inl (_22_57) -> begin
false
end
| FStar_Util.Inr (_22_60) -> begin
true
end))

# 99 "FStar.Absyn.Print.fst"
let rec reconstruct_lex : FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _101_28 = (FStar_Absyn_Util.compress_exp e)
in _101_28.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (f, args) -> begin
(
# 103 "FStar.Absyn.Print.fst"
let args = (FStar_List.filter (fun a -> (match (a) with
| ((FStar_Util.Inl (_), _)) | ((FStar_Util.Inr (_), Some (FStar_Absyn_Syntax.Implicit (_)))) -> begin
false
end
| _22_83 -> begin
true
end)) args)
in (
# 107 "FStar.Absyn.Print.fst"
let exps = (FStar_List.map (fun _22_2 -> (match (_22_2) with
| (FStar_Util.Inl (_22_87), _22_90) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Util.Inr (x), _22_95) -> begin
x
end)) args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = 2)) then begin
(match ((let _101_31 = (FStar_List.nth exps 1)
in (reconstruct_lex _101_31))) with
| Some (xs) -> begin
(let _101_33 = (let _101_32 = (FStar_List.nth exps 0)
in (_101_32)::xs)
in Some (_101_33))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _22_102 -> begin
if (is_lex_top e) then begin
Some ([])
end else begin
None
end
end))

# 113 "FStar.Absyn.Print.fst"
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

# 118 "FStar.Absyn.Print.fst"
let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _101_47 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _101_47)))

# 121 "FStar.Absyn.Print.fst"
let infix_prim_op_to_string = (fun e -> (let _101_49 = (get_lid e)
in (find_lid _101_49 infix_prim_ops)))

# 123 "FStar.Absyn.Print.fst"
let unary_prim_op_to_string = (fun e -> (let _101_51 = (get_lid e)
in (find_lid _101_51 unary_prim_ops)))

# 124 "FStar.Absyn.Print.fst"
let infix_type_op_to_string = (fun t -> (let _101_53 = (get_type_lid t)
in (find_lid _101_53 infix_type_ops)))

# 125 "FStar.Absyn.Print.fst"
let unary_type_op_to_string = (fun t -> (let _101_55 = (get_type_lid t)
in (find_lid _101_55 unary_type_ops)))

# 126 "FStar.Absyn.Print.fst"
let quant_to_string = (fun t -> (let _101_57 = (get_type_lid t)
in (find_lid _101_57 quants)))

# 128 "FStar.Absyn.Print.fst"
let rec sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_ST.read FStar_Options.print_real_names) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)

# 133 "FStar.Absyn.Print.fst"
let strBvd = (fun bvd -> if (FStar_ST.read FStar_Options.print_real_names) then begin
(Prims.strcat bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText bvd.FStar_Absyn_Syntax.realname.FStar_Ident.idText)
end else begin
if ((FStar_ST.read FStar_Options.hide_genident_nums) && (FStar_Util.starts_with bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText "_")) then begin
try
(match (()) with
| () -> begin
(
# 141 "FStar.Absyn.Print.fst"
let _22_127 = (let _101_62 = (FStar_Util.substring_from bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText 1)
in (FStar_Util.int_of_string _101_62))
in "_?")
end)
with
| _22_124 -> begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end
end else begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end
end)

# 143 "FStar.Absyn.Print.fst"
let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _22_3 -> (match (_22_3) with
| (_22_132, Some (FStar_Absyn_Syntax.Implicit (_22_134))) -> begin
false
end
| _22_139 -> begin
true
end)))))

# 145 "FStar.Absyn.Print.fst"
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
| FStar_Const.Const_string (bytes, _22_153) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_22_157) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x) -> begin
x
end
| FStar_Const.Const_int64 (_22_162) -> begin
"<int64>"
end
| FStar_Const.Const_uint8 (_22_165) -> begin
"<uint8>"
end
| FStar_Const.Const_range (r) -> begin
(FStar_Range.string_of_range r)
end))

# 158 "FStar.Absyn.Print.fst"
let rec tag_of_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_22_171) -> begin
"Typ_btvar"
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(Prims.strcat "Typ_const " v.FStar_Absyn_Syntax.v.FStar_Ident.str)
end
| FStar_Absyn_Syntax.Typ_fun (_22_176) -> begin
"Typ_fun"
end
| FStar_Absyn_Syntax.Typ_refine (_22_179) -> begin
"Typ_refine"
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let _101_103 = (tag_of_typ head)
in (let _101_102 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.format2 "Typ_app(%s, [%s args])" _101_103 _101_102)))
end
| FStar_Absyn_Syntax.Typ_lam (_22_186) -> begin
"Typ_lam"
end
| FStar_Absyn_Syntax.Typ_ascribed (_22_189) -> begin
"Typ_ascribed"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_22_192)) -> begin
"Typ_meta_pattern"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_22_196)) -> begin
"Typ_meta_named"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_22_200)) -> begin
"Typ_meta_labeled"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_22_204)) -> begin
"Typ_meta_refresh_label"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_22_208)) -> begin
"Typ_meta_slack_formula"
end
| FStar_Absyn_Syntax.Typ_uvar (_22_212) -> begin
"Typ_uvar"
end
| FStar_Absyn_Syntax.Typ_delayed (_22_215) -> begin
"Typ_delayed"
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"Typ_unknown"
end))
and tag_of_exp = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_22_220) -> begin
"Exp_bvar"
end
| FStar_Absyn_Syntax.Exp_fvar (_22_223) -> begin
"Exp_fvar"
end
| FStar_Absyn_Syntax.Exp_constant (_22_226) -> begin
"Exp_constant"
end
| FStar_Absyn_Syntax.Exp_abs (_22_229) -> begin
"Exp_abs"
end
| FStar_Absyn_Syntax.Exp_app (_22_232) -> begin
"Exp_app"
end
| FStar_Absyn_Syntax.Exp_match (_22_235) -> begin
"Exp_match"
end
| FStar_Absyn_Syntax.Exp_ascribed (_22_238) -> begin
"Exp_ascribed"
end
| FStar_Absyn_Syntax.Exp_let (_22_241) -> begin
"Exp_let"
end
| FStar_Absyn_Syntax.Exp_uvar (_22_244) -> begin
"Exp_uvar"
end
| FStar_Absyn_Syntax.Exp_delayed (_22_247) -> begin
"Exp_delayed"
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_22_250, m)) -> begin
(let _101_107 = (meta_e_to_string m)
in (Prims.strcat "Exp_meta_desugared " _101_107))
end))
and meta_e_to_string : FStar_Absyn_Syntax.meta_source_info  ->  Prims.string = (fun _22_4 -> (match (_22_4) with
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
# 203 "FStar.Absyn.Print.fst"
let x = (FStar_Absyn_Util.compress_typ x)
in (match (x.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_22_264) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_22_267, l)) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Typ_meta (meta) -> begin
(let _101_113 = (FStar_All.pipe_right meta meta_to_string)
in (FStar_Util.format1 "(Meta %s)" _101_113))
end
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(strBvd btv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(sli v.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_fun (binders, c) -> begin
(let _101_115 = (binders_to_string " -> " binders)
in (let _101_114 = (comp_typ_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _101_115 _101_114)))
end
| FStar_Absyn_Syntax.Typ_refine (xt, f) -> begin
(let _101_118 = (strBvd xt.FStar_Absyn_Syntax.v)
in (let _101_117 = (FStar_All.pipe_right xt.FStar_Absyn_Syntax.sort typ_to_string)
in (let _101_116 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "%s:%s{%s}" _101_118 _101_117 _101_116))))
end
| FStar_Absyn_Syntax.Typ_app (_22_287, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(
# 215 "FStar.Absyn.Print.fst"
let q_to_string = (fun k a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(
# 216 "FStar.Absyn.Print.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (b::[], t) -> begin
(k (b, t))
end
| _22_307 -> begin
(let _101_129 = (tag_of_typ t)
in (let _101_128 = (typ_to_string t)
in (FStar_Util.format2 "<Expected a type-lambda! got %s>%s" _101_129 _101_128)))
end))
end
| FStar_Util.Inr (e) -> begin
(let _101_130 = (exp_to_string e)
in (FStar_Util.format1 "(<Expected a type!>%s)" _101_130))
end))
in (
# 221 "FStar.Absyn.Print.fst"
let qbinder_to_string = (q_to_string (fun x -> (binder_to_string (Prims.fst x))))
in (
# 222 "FStar.Absyn.Print.fst"
let qbody_to_string = (q_to_string (fun x -> (typ_to_string (Prims.snd x))))
in (
# 223 "FStar.Absyn.Print.fst"
let args' = if ((FStar_ST.read FStar_Options.print_implicits) && (not ((is_quant t)))) then begin
args
end else begin
(filter_imp args)
end
in if ((is_ite t) && ((FStar_List.length args) = 3)) then begin
(let _101_140 = (let _101_135 = (FStar_List.nth args 0)
in (arg_to_string _101_135))
in (let _101_139 = (let _101_136 = (FStar_List.nth args 1)
in (arg_to_string _101_136))
in (let _101_138 = (let _101_137 = (FStar_List.nth args 2)
in (arg_to_string _101_137))
in (FStar_Util.format3 "if %s then %s else %s" _101_140 _101_139 _101_138))))
end else begin
if ((is_b2t t) && ((FStar_List.length args) = 1)) then begin
(let _101_141 = (FStar_List.nth args 0)
in (FStar_All.pipe_right _101_141 arg_to_string))
end else begin
if ((is_quant t) && ((FStar_List.length args) <= 2)) then begin
(let _101_146 = (quant_to_string t)
in (let _101_145 = (let _101_142 = (FStar_List.nth args' 0)
in (qbinder_to_string _101_142))
in (let _101_144 = (let _101_143 = (FStar_List.nth args' 0)
in (qbody_to_string _101_143))
in (FStar_Util.format3 "(%s (%s). %s)" _101_146 _101_145 _101_144))))
end else begin
if ((is_infix_type_op t) && ((FStar_List.length args') = 2)) then begin
(let _101_151 = (let _101_147 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _101_147 arg_to_string))
in (let _101_150 = (FStar_All.pipe_right t infix_type_op_to_string)
in (let _101_149 = (let _101_148 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _101_148 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _101_151 _101_150 _101_149))))
end else begin
if ((is_unary_type_op t) && ((FStar_List.length args') = 1)) then begin
(let _101_154 = (FStar_All.pipe_right t unary_type_op_to_string)
in (let _101_153 = (let _101_152 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _101_152 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _101_154 _101_153)))
end else begin
(let _101_156 = (FStar_All.pipe_right t typ_to_string)
in (let _101_155 = (FStar_All.pipe_right args args_to_string)
in (FStar_Util.format2 "(%s %s)" _101_156 _101_155)))
end
end
end
end
end))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(let _101_158 = (binders_to_string " " binders)
in (let _101_157 = (FStar_All.pipe_right t2 typ_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _101_158 _101_157)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _101_160 = (typ_to_string t)
in (let _101_159 = (kind_to_string k)
in (FStar_Util.format2 "(%s <: %s)" _101_160 _101_159)))
end else begin
(FStar_All.pipe_right t typ_to_string)
end
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"<UNKNOWN>"
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(match ((FStar_Absyn_Visit.compress_typ_aux false x)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_22_337); FStar_Absyn_Syntax.tk = _22_335; FStar_Absyn_Syntax.pos = _22_333; FStar_Absyn_Syntax.fvs = _22_331; FStar_Absyn_Syntax.uvs = _22_329} -> begin
(uvar_t_to_string (uv, k))
end
| t -> begin
(FStar_All.pipe_right t typ_to_string)
end)
end)))
and uvar_t_to_string : (FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd)  ->  Prims.string = (fun _22_343 -> (match (_22_343) with
| (uv, k) -> begin
if (false && (FStar_ST.read FStar_Options.print_real_names)) then begin
(let _101_164 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _101_162 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _101_162))
end
in (let _101_163 = (kind_to_string k)
in (FStar_Util.format2 "(U%s : %s)" _101_164 _101_163)))
end else begin
(let _101_166 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _101_165 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _101_165))
end
in (FStar_Util.format1 "U%s" _101_166))
end
end))
and imp_to_string : Prims.string  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s _22_5 -> (match (_22_5) with
| Some (FStar_Absyn_Syntax.Implicit (_22_347)) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Absyn_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _22_353 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (match (b) with
| (FStar_Util.Inl (a), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _101_171 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _101_171 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp a.FStar_Absyn_Syntax.v))) then begin
(kind_to_string a.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits)))) then begin
(let _101_172 = (strBvd a.FStar_Absyn_Syntax.v)
in (imp_to_string _101_172 imp))
end else begin
(let _101_176 = (let _101_175 = (let _101_173 = (strBvd a.FStar_Absyn_Syntax.v)
in (Prims.strcat _101_173 ":"))
in (let _101_174 = (kind_to_string a.FStar_Absyn_Syntax.sort)
in (Prims.strcat _101_175 _101_174)))
in (imp_to_string _101_176 imp))
end
end
end
| (FStar_Util.Inr (x), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _101_177 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _101_177 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp x.FStar_Absyn_Syntax.v))) then begin
(typ_to_string x.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits)))) then begin
(let _101_178 = (strBvd x.FStar_Absyn_Syntax.v)
in (imp_to_string _101_178 imp))
end else begin
(let _101_182 = (let _101_181 = (let _101_179 = (strBvd x.FStar_Absyn_Syntax.v)
in (Prims.strcat _101_179 ":"))
in (let _101_180 = (typ_to_string x.FStar_Absyn_Syntax.sort)
in (Prims.strcat _101_181 _101_180)))
in (imp_to_string _101_182 imp))
end
end
end))
and binder_to_string : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Absyn_Syntax.binders  ->  Prims.string = (fun sep bs -> (
# 274 "FStar.Absyn.Print.fst"
let bs = if (FStar_ST.read FStar_Options.print_implicits) then begin
bs
end else begin
(filter_imp bs)
end
in if (sep = " -> ") then begin
(let _101_187 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _101_187 (FStar_String.concat sep)))
end else begin
(let _101_188 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _101_188 (FStar_String.concat sep)))
end))
and arg_to_string : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _22_6 -> (match (_22_6) with
| (FStar_Util.Inl (a), imp) -> begin
(let _101_190 = (typ_to_string a)
in (imp_to_string _101_190 imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _101_191 = (exp_to_string x)
in (imp_to_string _101_191 imp))
end))
and args_to_string : FStar_Absyn_Syntax.args  ->  Prims.string = (fun args -> (
# 284 "FStar.Absyn.Print.fst"
let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _101_193 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _101_193 (FStar_String.concat " ")))))
and lcomp_typ_to_string : FStar_Absyn_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _101_196 = (sli lc.FStar_Absyn_Syntax.eff_name)
in (let _101_195 = (typ_to_string lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _101_196 _101_195))))
and comp_typ_to_string : FStar_Absyn_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _101_198 = (typ_to_string t)
in (FStar_Util.format1 "Tot %s" _101_198))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(
# 294 "FStar.Absyn.Print.fst"
let basic = if ((FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _22_7 -> (match (_22_7) with
| FStar_Absyn_Syntax.TOTAL -> begin
true
end
| _22_389 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args)))) then begin
(let _101_200 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _101_200))
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_Ident.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid)) then begin
(typ_to_string c.FStar_Absyn_Syntax.result_typ)
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _22_8 -> (match (_22_8) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _22_393 -> begin
false
end))))) then begin
(let _101_202 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _101_202))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _101_206 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _101_205 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (let _101_204 = (let _101_203 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.effect_args (FStar_List.map effect_arg_to_string))
in (FStar_All.pipe_right _101_203 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _101_206 _101_205 _101_204))))
end else begin
(let _101_208 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _101_207 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _101_208 _101_207)))
end
end
end
end
in (
# 304 "FStar.Absyn.Print.fst"
let dec = (let _101_212 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.collect (fun _22_9 -> (match (_22_9) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _101_211 = (let _101_210 = (exp_to_string e)
in (FStar_Util.format1 " (decreases %s)" _101_210))
in (_101_211)::[])
end
| _22_399 -> begin
[]
end))))
in (FStar_All.pipe_right _101_212 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and effect_arg_to_string : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun e -> (match (e) with
| (FStar_Util.Inr (e), _22_405) -> begin
(exp_to_string e)
end
| (FStar_Util.Inl (wp), _22_410) -> begin
(formula_to_string wp)
end))
and formula_to_string : FStar_Absyn_Syntax.typ  ->  Prims.string = (fun phi -> (typ_to_string phi))
and formula_to_string_old_now_unused : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun phi -> (
# 316 "FStar.Absyn.Print.fst"
let const_op = (fun f _22_416 -> f)
in (
# 317 "FStar.Absyn.Print.fst"
let un_op = (fun f _22_10 -> (match (_22_10) with
| (FStar_Util.Inl (t), _22_424)::[] -> begin
(let _101_224 = (formula_to_string t)
in (FStar_Util.format2 "%s %s" f _101_224))
end
| _22_428 -> begin
(FStar_All.failwith "impos")
end))
in (
# 320 "FStar.Absyn.Print.fst"
let bin_top = (fun f _22_11 -> (match (_22_11) with
| (FStar_Util.Inl (t1), _22_440)::(FStar_Util.Inl (t2), _22_435)::[] -> begin
(let _101_230 = (formula_to_string t1)
in (let _101_229 = (formula_to_string t2)
in (FStar_Util.format3 "%s %s %s" _101_230 f _101_229)))
end
| _22_444 -> begin
(FStar_All.failwith "Impos")
end))
in (
# 327 "FStar.Absyn.Print.fst"
let bin_eop = (fun f _22_12 -> (match (_22_12) with
| (FStar_Util.Inr (e1), _22_456)::(FStar_Util.Inr (e2), _22_451)::[] -> begin
(let _101_236 = (exp_to_string e1)
in (let _101_235 = (exp_to_string e2)
in (FStar_Util.format3 "%s %s %s" _101_236 f _101_235)))
end
| _22_460 -> begin
(FStar_All.failwith "impos")
end))
in (
# 330 "FStar.Absyn.Print.fst"
let ite = (fun _22_13 -> (match (_22_13) with
| (FStar_Util.Inl (t1), _22_475)::(FStar_Util.Inl (t2), _22_470)::(FStar_Util.Inl (t3), _22_465)::[] -> begin
(let _101_241 = (formula_to_string t1)
in (let _101_240 = (formula_to_string t2)
in (let _101_239 = (formula_to_string t3)
in (FStar_Util.format3 "if %s then %s else %s" _101_241 _101_240 _101_239))))
end
| _22_479 -> begin
(FStar_All.failwith "impos")
end))
in (
# 333 "FStar.Absyn.Print.fst"
let eq_op = (fun _22_14 -> (match (_22_14) with
| (FStar_Util.Inl (t1), _22_500)::(FStar_Util.Inl (t2), _22_495)::(FStar_Util.Inr (e1), _22_490)::(FStar_Util.Inr (e2), _22_485)::[] -> begin
if (FStar_ST.read FStar_Options.print_implicits) then begin
(let _101_247 = (typ_to_string t1)
in (let _101_246 = (typ_to_string t2)
in (let _101_245 = (exp_to_string e1)
in (let _101_244 = (exp_to_string e2)
in (FStar_Util.format4 "Eq2 %s %s %s %s" _101_247 _101_246 _101_245 _101_244)))))
end else begin
(let _101_249 = (exp_to_string e1)
in (let _101_248 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _101_249 _101_248)))
end
end
| (FStar_Util.Inr (e1), _22_511)::(FStar_Util.Inr (e2), _22_506)::[] -> begin
(let _101_251 = (exp_to_string e1)
in (let _101_250 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _101_251 _101_250)))
end
| _22_515 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 340 "FStar.Absyn.Print.fst"
let connectives = ((FStar_Absyn_Const.and_lid, (bin_top "/\\")))::((FStar_Absyn_Const.or_lid, (bin_top "\\/")))::((FStar_Absyn_Const.imp_lid, (bin_top "==>")))::((FStar_Absyn_Const.iff_lid, (bin_top "<==>")))::((FStar_Absyn_Const.ite_lid, ite))::((FStar_Absyn_Const.not_lid, (un_op "~")))::((FStar_Absyn_Const.eqT_lid, (bin_top "==")))::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op "True")))::((FStar_Absyn_Const.false_lid, (const_op "False")))::[]
in (
# 352 "FStar.Absyn.Print.fst"
let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (binders, phi) -> begin
(let _101_290 = (binders_to_string " " binders)
in (let _101_289 = (formula_to_string phi)
in (FStar_Util.format2 "(fun %s => %s)" _101_290 _101_289)))
end
| _22_525 -> begin
(typ_to_string phi)
end))
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _22_535 -> (match (_22_535) with
| (l, _22_534) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_22_538, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, _22_544, body)) -> begin
(let _101_308 = (binders_to_string " " vars)
in (let _101_307 = (formula_to_string body)
in (FStar_Util.format2 "(forall %s. %s)" _101_308 _101_307)))
end
| Some (FStar_Absyn_Util.QEx (vars, _22_551, body)) -> begin
(let _101_310 = (binders_to_string " " vars)
in (let _101_309 = (formula_to_string body)
in (FStar_Util.format2 "(exists %s. %s)" _101_310 _101_309)))
end))))))))))
and exp_to_string : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun x -> (match ((let _101_312 = (FStar_Absyn_Util.compress_exp x)
in _101_312.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_delayed (_22_558) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _22_562)) -> begin
(exp_to_string e)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(uvar_e_to_string (uv, t))
end
| FStar_Absyn_Syntax.Exp_bvar (bvv) -> begin
(strBvd bvv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_fvar (fv, _22_574) -> begin
(sli fv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(FStar_All.pipe_right c const_to_string)
end
| FStar_Absyn_Syntax.Exp_abs (binders, e) -> begin
(let _101_314 = (binders_to_string " " binders)
in (let _101_313 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _101_314 _101_313)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(
# 379 "FStar.Absyn.Print.fst"
let lex = if (FStar_ST.read FStar_Options.print_implicits) then begin
None
end else begin
(reconstruct_lex x)
end
in (match (lex) with
| Some (es) -> begin
(let _101_317 = (let _101_316 = (let _101_315 = (FStar_List.map exp_to_string es)
in (FStar_String.concat "; " _101_315))
in (Prims.strcat "%[" _101_316))
in (Prims.strcat _101_317 "]"))
end
| None -> begin
(
# 383 "FStar.Absyn.Print.fst"
let args' = (let _101_319 = (filter_imp args)
in (FStar_All.pipe_right _101_319 (FStar_List.filter (fun _22_15 -> (match (_22_15) with
| (FStar_Util.Inr (_22_593), _22_596) -> begin
true
end
| _22_599 -> begin
false
end)))))
in if ((is_infix_prim_op e) && ((FStar_List.length args') = 2)) then begin
(let _101_324 = (let _101_320 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _101_320 arg_to_string))
in (let _101_323 = (FStar_All.pipe_right e infix_prim_op_to_string)
in (let _101_322 = (let _101_321 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _101_321 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _101_324 _101_323 _101_322))))
end else begin
if ((is_unary_prim_op e) && ((FStar_List.length args') = 1)) then begin
(let _101_327 = (FStar_All.pipe_right e unary_prim_op_to_string)
in (let _101_326 = (let _101_325 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _101_325 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _101_327 _101_326)))
end else begin
(let _101_329 = (FStar_All.pipe_right e exp_to_string)
in (let _101_328 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _101_329 _101_328)))
end
end)
end))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _101_337 = (FStar_All.pipe_right e exp_to_string)
in (let _101_336 = (let _101_335 = (FStar_All.pipe_right pats (FStar_List.map (fun _22_608 -> (match (_22_608) with
| (p, wopt, e) -> begin
(let _101_334 = (FStar_All.pipe_right p pat_to_string)
in (let _101_333 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _101_331 = (FStar_All.pipe_right w exp_to_string)
in (FStar_Util.format1 "when %s" _101_331))
end)
in (let _101_332 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format3 "%s %s -> %s" _101_334 _101_333 _101_332))))
end))))
in (FStar_Util.concat_l "\n\t" _101_335))
in (FStar_Util.format2 "(match %s with %s)" _101_337 _101_336)))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _22_615) -> begin
(let _101_339 = (FStar_All.pipe_right e exp_to_string)
in (let _101_338 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "(%s:%s)" _101_339 _101_338)))
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(let _101_341 = (lbs_to_string lbs)
in (let _101_340 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "%s in %s" _101_341 _101_340)))
end))
and uvar_e_to_string : (FStar_Absyn_Syntax.uvar_e * FStar_Absyn_Syntax.typ)  ->  Prims.string = (fun _22_625 -> (match (_22_625) with
| (uv, _22_624) -> begin
(let _101_344 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _101_343 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _101_343))
end
in (Prims.strcat "\'e" _101_344))
end))
and lbs_to_string : FStar_Absyn_Syntax.letbindings  ->  Prims.string = (fun lbs -> (let _101_351 = (let _101_350 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _101_349 = (lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _101_348 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbtyp typ_to_string)
in (let _101_347 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbdef exp_to_string)
in (FStar_Util.format3 "%s:%s = %s" _101_349 _101_348 _101_347)))))))
in (FStar_Util.concat_l "\n and " _101_350))
in (FStar_Util.format2 "let %s %s" (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _101_351)))
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
and either_l_to_string : Prims.string  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either Prims.list  ->  Prims.string = (fun delim l -> (let _101_356 = (FStar_All.pipe_right l (FStar_List.map either_to_string))
in (FStar_All.pipe_right _101_356 (FStar_Util.concat_l delim))))
and meta_to_string : FStar_Absyn_Syntax.meta_t  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Meta_refresh_label (t, _22_643, _22_645) -> begin
(let _101_358 = (typ_to_string t)
in (FStar_Util.format1 "(refresh) %s" _101_358))
end
| FStar_Absyn_Syntax.Meta_labeled (t, l, _22_651, _22_653) -> begin
(let _101_359 = (typ_to_string t)
in (FStar_Util.format2 "(labeled \"%s\") %s" l _101_359))
end
| FStar_Absyn_Syntax.Meta_named (_22_657, l) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Meta_pattern (t, ps) -> begin
(let _101_361 = (pats_to_string ps)
in (let _101_360 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "{:pattern %s} %s" _101_361 _101_360)))
end
| FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _22_668) -> begin
(let _101_363 = (formula_to_string t1)
in (let _101_362 = (formula_to_string t2)
in (FStar_Util.format2 "%s /\\ %s" _101_363 _101_362)))
end))
and pats_to_string : FStar_Absyn_Syntax.arg Prims.list Prims.list  ->  Prims.string = (fun ps -> (let _101_367 = (FStar_All.pipe_right ps (FStar_List.map (fun e -> (let _101_366 = (FStar_All.pipe_right e (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _101_366 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _101_367 (FStar_String.concat " \\/ "))))
and kind_to_string : FStar_Absyn_Syntax.knd  ->  Prims.string = (fun x -> (match ((let _101_369 = (FStar_Absyn_Util.compress_kind x)
in _101_369.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_lam (_22_675) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Kind_delayed (_22_678) -> begin
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
(let _101_371 = (sli n)
in (let _101_370 = (args_to_string args)
in (FStar_Util.format2 "%s %s" _101_371 _101_370)))
end
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(let _101_373 = (binders_to_string " -> " binders)
in (let _101_372 = (FStar_All.pipe_right k kind_to_string)
in (FStar_Util.format2 "(%s -> %s)" _101_373 _101_372)))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun uv -> (let _101_375 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _101_374 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _101_374))
end
in (Prims.strcat "\'k_" _101_375)))
and uvar_k_to_string' : ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list)  ->  Prims.string = (fun _22_700 -> (match (_22_700) with
| (uv, args) -> begin
(
# 449 "FStar.Absyn.Print.fst"
let str = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _101_377 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _101_377))
end
in (let _101_378 = (args_to_string args)
in (FStar_Util.format2 "(\'k_%s %s)" str _101_378)))
end))
and pat_to_string : FStar_Absyn_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (l, _22_705, pats) -> begin
(let _101_383 = (sli l.FStar_Absyn_Syntax.v)
in (let _101_382 = (let _101_381 = (FStar_List.map (fun _22_711 -> (match (_22_711) with
| (x, b) -> begin
(
# 453 "FStar.Absyn.Print.fst"
let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _101_381 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _101_383 _101_382)))
end
| FStar_Absyn_Syntax.Pat_dot_term (x, _22_715) -> begin
(let _101_384 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".%s" _101_384))
end
| FStar_Absyn_Syntax.Pat_dot_typ (x, _22_720) -> begin
(let _101_385 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".\'%s" _101_385))
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
| FStar_Absyn_Syntax.Pat_wild (_22_730) -> begin
"_"
end
| FStar_Absyn_Syntax.Pat_twild (_22_733) -> begin
"\'_"
end
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(let _101_386 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _101_386))
end))

# 461 "FStar.Absyn.Print.fst"
let subst_to_string = (fun subst -> (let _101_394 = (let _101_393 = (FStar_List.map (fun _22_16 -> (match (_22_16) with
| FStar_Util.Inl (a, t) -> begin
(let _101_390 = (strBvd a)
in (let _101_389 = (typ_to_string t)
in (FStar_Util.format2 "(%s -> %s)" _101_390 _101_389)))
end
| FStar_Util.Inr (x, e) -> begin
(let _101_392 = (strBvd x)
in (let _101_391 = (exp_to_string e)
in (FStar_Util.format2 "(%s -> %s)" _101_392 _101_391)))
end)) subst)
in (FStar_All.pipe_right _101_393 (FStar_String.concat ", ")))
in (FStar_All.pipe_left (FStar_Util.format1 "{%s}") _101_394)))

# 467 "FStar.Absyn.Print.fst"
let freevars_to_string : FStar_Absyn_Syntax.freevars  ->  Prims.string = (fun fvs -> (
# 469 "FStar.Absyn.Print.fst"
let f = (fun l -> (let _101_400 = (let _101_399 = (FStar_All.pipe_right l FStar_Util.set_elements)
in (FStar_All.pipe_right _101_399 (FStar_List.map (fun t -> (strBvd t.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _101_400 (FStar_String.concat ", "))))
in (let _101_402 = (f fvs.FStar_Absyn_Syntax.ftvs)
in (let _101_401 = (f fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_Util.format2 "ftvs={%s}, fxvs={%s}" _101_402 _101_401)))))

# 470 "FStar.Absyn.Print.fst"
let qual_to_string : FStar_Absyn_Syntax.qualifier  ->  Prims.string = (fun _22_17 -> (match (_22_17) with
| FStar_Absyn_Syntax.Logic -> begin
"logic"
end
| FStar_Absyn_Syntax.Opaque -> begin
"opaque"
end
| FStar_Absyn_Syntax.Discriminator (_22_757) -> begin
"discriminator"
end
| FStar_Absyn_Syntax.Projector (_22_760) -> begin
"projector"
end
| FStar_Absyn_Syntax.RecordType (ids) -> begin
(let _101_407 = (let _101_406 = (FStar_All.pipe_right ids (FStar_List.map (fun lid -> lid.FStar_Ident.ident.FStar_Ident.idText)))
in (FStar_All.pipe_right _101_406 (FStar_String.concat ", ")))
in (FStar_Util.format1 "record(%s)" _101_407))
end
| _22_766 -> begin
"other"
end))

# 478 "FStar.Absyn.Print.fst"
let quals_to_string : FStar_Absyn_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (let _101_410 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _101_410 (FStar_String.concat " "))))

# 479 "FStar.Absyn.Print.fst"
let rec sigelt_to_string : FStar_Absyn_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.ResetOptions (None), _22_772) -> begin
"#reset-options"
end
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.ResetOptions (Some (s)), _22_779) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.SetOptions (s), _22_785) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _22_792, _22_794, quals, _22_797) -> begin
(let _101_415 = (quals_to_string quals)
in (let _101_414 = (binders_to_string " " tps)
in (let _101_413 = (kind_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _101_415 lid.FStar_Ident.str _101_414 _101_413))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, _22_805, _22_807) -> begin
(let _101_418 = (binders_to_string " " tps)
in (let _101_417 = (kind_to_string k)
in (let _101_416 = (typ_to_string t)
in (FStar_Util.format4 "type %s %s : %s = %s" lid.FStar_Ident.str _101_418 _101_417 _101_416))))
end
| FStar_Absyn_Syntax.Sig_datacon (lid, t, _22_813, _22_815, _22_817, _22_819) -> begin
(let _101_419 = (typ_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _101_419))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _22_826) -> begin
(let _101_421 = (quals_to_string quals)
in (let _101_420 = (typ_to_string t)
in (FStar_Util.format3 "%s val %s : %s" _101_421 lid.FStar_Ident.str _101_420)))
end
| FStar_Absyn_Syntax.Sig_assume (lid, f, _22_832, _22_834) -> begin
(let _101_422 = (typ_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _101_422))
end
| FStar_Absyn_Syntax.Sig_let (lbs, _22_839, _22_841, b) -> begin
(lbs_to_string lbs)
end
| FStar_Absyn_Syntax.Sig_main (e, _22_847) -> begin
(let _101_423 = (exp_to_string e)
in (FStar_Util.format1 "let _ = %s" _101_423))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _22_852, _22_854, _22_856) -> begin
(let _101_424 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _101_424 (FStar_String.concat "\n")))
end
| FStar_Absyn_Syntax.Sig_new_effect (_22_860) -> begin
"new_effect { ... }"
end
| FStar_Absyn_Syntax.Sig_sub_effect (_22_863) -> begin
"sub_effect ..."
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_22_866) -> begin
"kind ..."
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, tps, c, _22_872, _22_874) -> begin
(let _101_427 = (sli l)
in (let _101_426 = (binders_to_string " " tps)
in (let _101_425 = (comp_typ_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _101_427 _101_426 _101_425))))
end))

# 495 "FStar.Absyn.Print.fst"
let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _101_432 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _101_432 msg)))

# 497 "FStar.Absyn.Print.fst"
let rec sigelt_to_string_short : FStar_Absyn_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_let ((_22_881, {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _22_885; FStar_Absyn_Syntax.lbdef = _22_883}::[]), _22_893, _22_895, _22_897) -> begin
(let _101_435 = (typ_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Ident.str _101_435))
end
| _22_901 -> begin
(let _101_438 = (let _101_437 = (FStar_Absyn_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _101_437 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _101_438 (FStar_String.concat ", ")))
end))

# 501 "FStar.Absyn.Print.fst"
let rec modul_to_string : FStar_Absyn_Syntax.modul  ->  Prims.string = (fun m -> (let _101_443 = (sli m.FStar_Absyn_Syntax.name)
in (let _101_442 = (let _101_441 = (FStar_List.map sigelt_to_string m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _101_441 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _101_443 _101_442))))




