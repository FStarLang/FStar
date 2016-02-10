
open Prims
# 26 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.op_Addition, "+"))::((FStar_Absyn_Const.op_Subtraction, "-"))::((FStar_Absyn_Const.op_Multiply, "*"))::((FStar_Absyn_Const.op_Division, "/"))::((FStar_Absyn_Const.op_Eq, "="))::((FStar_Absyn_Const.op_ColonEq, ":="))::((FStar_Absyn_Const.op_notEq, "<>"))::((FStar_Absyn_Const.op_And, "&&"))::((FStar_Absyn_Const.op_Or, "||"))::((FStar_Absyn_Const.op_LTE, "<="))::((FStar_Absyn_Const.op_GTE, ">="))::((FStar_Absyn_Const.op_LT, "<"))::((FStar_Absyn_Const.op_GT, ">"))::((FStar_Absyn_Const.op_Modulus, "mod"))::[]

# 44 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.op_Negation, "not"))::((FStar_Absyn_Const.op_Minus, "-"))::[]

# 49 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let infix_type_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.and_lid, "/\\"))::((FStar_Absyn_Const.or_lid, "\\/"))::((FStar_Absyn_Const.imp_lid, "==>"))::((FStar_Absyn_Const.iff_lid, "<==>"))::((FStar_Absyn_Const.precedes_lid, "<<"))::((FStar_Absyn_Const.eq2_lid, "=="))::((FStar_Absyn_Const.eqT_lid, "=="))::[]

# 59 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let unary_type_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.not_lid, "~"))::[]

# 63 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let is_prim_op = (fun ps f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _29_22) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _29_26 -> begin
false
end))

# 67 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let is_type_op = (fun ps t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals ftv.FStar_Absyn_Syntax.v)))
end
| _29_32 -> begin
false
end))

# 71 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let get_lid = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _29_36) -> begin
fv.FStar_Absyn_Syntax.v
end
| _29_40 -> begin
(FStar_All.failwith "get_lid")
end))

# 75 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let get_type_lid = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
ftv.FStar_Absyn_Syntax.v
end
| _29_45 -> begin
(FStar_All.failwith "get_type_lid")
end))

# 79 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let is_infix_prim_op : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split infix_prim_ops)) e))

# 81 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let is_unary_prim_op : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split unary_prim_ops)) e))

# 82 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let is_infix_type_op : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op (Prims.fst (FStar_List.split infix_type_ops)) t))

# 83 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let is_unary_type_op : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op (Prims.fst (FStar_List.split unary_type_ops)) t))

# 84 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let quants : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Absyn_Const.forall_lid, "forall"))::((FStar_Absyn_Const.exists_lid, "exists"))::((FStar_Absyn_Const.allTyp_lid, "forall"))::((FStar_Absyn_Const.exTyp_lid, "exists"))::[]

# 91 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let is_b2t : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op ((FStar_Absyn_Const.b2t_lid)::[]) t))

# 93 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let is_quant : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op (Prims.fst (FStar_List.split quants)) t))

# 94 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let is_ite : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op ((FStar_Absyn_Const.ite_lid)::[]) t))

# 95 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let is_lex_cons : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Absyn_Const.lexcons_lid)::[]) f))

# 97 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let is_lex_top : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Absyn_Const.lextop_lid)::[]) f))

# 98 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let is_inr = (fun _29_1 -> (match (_29_1) with
| FStar_Util.Inl (_29_57) -> begin
false
end
| FStar_Util.Inr (_29_60) -> begin
true
end))

# 99 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let rec reconstruct_lex : FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _131_28 = (FStar_Absyn_Util.compress_exp e)
in _131_28.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (f, args) -> begin
(let args = (FStar_List.filter (fun a -> (match (a) with
| ((FStar_Util.Inl (_), _)) | ((FStar_Util.Inr (_), Some (FStar_Absyn_Syntax.Implicit (_)))) -> begin
false
end
| _29_83 -> begin
true
end)) args)
in (let exps = (FStar_List.map (fun _29_2 -> (match (_29_2) with
| (FStar_Util.Inl (_29_87), _29_90) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Util.Inr (x), _29_95) -> begin
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
| _29_102 -> begin
if (is_lex_top e) then begin
Some ([])
end else begin
None
end
end))

# 113 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

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

# 118 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _131_47 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _131_47)))

# 121 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let infix_prim_op_to_string = (fun e -> (let _131_49 = (get_lid e)
in (find_lid _131_49 infix_prim_ops)))

# 123 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let unary_prim_op_to_string = (fun e -> (let _131_51 = (get_lid e)
in (find_lid _131_51 unary_prim_ops)))

# 124 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let infix_type_op_to_string = (fun t -> (let _131_53 = (get_type_lid t)
in (find_lid _131_53 infix_type_ops)))

# 125 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let unary_type_op_to_string = (fun t -> (let _131_55 = (get_type_lid t)
in (find_lid _131_55 unary_type_ops)))

# 126 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let quant_to_string = (fun t -> (let _131_57 = (get_type_lid t)
in (find_lid _131_57 quants)))

# 128 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let rec sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_ST.read FStar_Options.print_real_names) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)

# 133 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let strBvd = (fun bvd -> if (FStar_ST.read FStar_Options.print_real_names) then begin
(Prims.strcat bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText bvd.FStar_Absyn_Syntax.realname.FStar_Ident.idText)
end else begin
if ((FStar_ST.read FStar_Options.hide_genident_nums) && (FStar_Util.starts_with bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText "_")) then begin
(FStar_All.try_with (fun _29_121 -> (match (()) with
| () -> begin
(let _29_127 = (let _131_62 = (FStar_Util.substring_from bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText 1)
in (FStar_Util.int_of_string _131_62))
in "_?")
end)) (fun _29_120 -> (match (_29_120) with
| _29_124 -> begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end)))
end else begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end
end)

# 143 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _29_3 -> (match (_29_3) with
| (_29_132, Some (FStar_Absyn_Syntax.Implicit (_29_134))) -> begin
false
end
| _29_139 -> begin
true
end)))))

# 145 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

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
| FStar_Const.Const_string (bytes, _29_153) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_29_157) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x) -> begin
x
end
| FStar_Const.Const_int64 (_29_162) -> begin
"<int64>"
end
| FStar_Const.Const_uint8 (_29_165) -> begin
"<uint8>"
end))

# 157 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let rec tag_of_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_29_169) -> begin
"Typ_btvar"
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(Prims.strcat "Typ_const " v.FStar_Absyn_Syntax.v.FStar_Ident.str)
end
| FStar_Absyn_Syntax.Typ_fun (_29_174) -> begin
"Typ_fun"
end
| FStar_Absyn_Syntax.Typ_refine (_29_177) -> begin
"Typ_refine"
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let _131_103 = (tag_of_typ head)
in (let _131_102 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.format2 "Typ_app(%s, [%s args])" _131_103 _131_102)))
end
| FStar_Absyn_Syntax.Typ_lam (_29_184) -> begin
"Typ_lam"
end
| FStar_Absyn_Syntax.Typ_ascribed (_29_187) -> begin
"Typ_ascribed"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_29_190)) -> begin
"Typ_meta_pattern"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_29_194)) -> begin
"Typ_meta_named"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_29_198)) -> begin
"Typ_meta_labeled"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_29_202)) -> begin
"Typ_meta_refresh_label"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_29_206)) -> begin
"Typ_meta_slack_formula"
end
| FStar_Absyn_Syntax.Typ_uvar (_29_210) -> begin
"Typ_uvar"
end
| FStar_Absyn_Syntax.Typ_delayed (_29_213) -> begin
"Typ_delayed"
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"Typ_unknown"
end))
and tag_of_exp = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_29_218) -> begin
"Exp_bvar"
end
| FStar_Absyn_Syntax.Exp_fvar (_29_221) -> begin
"Exp_fvar"
end
| FStar_Absyn_Syntax.Exp_constant (_29_224) -> begin
"Exp_constant"
end
| FStar_Absyn_Syntax.Exp_abs (_29_227) -> begin
"Exp_abs"
end
| FStar_Absyn_Syntax.Exp_app (_29_230) -> begin
"Exp_app"
end
| FStar_Absyn_Syntax.Exp_match (_29_233) -> begin
"Exp_match"
end
| FStar_Absyn_Syntax.Exp_ascribed (_29_236) -> begin
"Exp_ascribed"
end
| FStar_Absyn_Syntax.Exp_let (_29_239) -> begin
"Exp_let"
end
| FStar_Absyn_Syntax.Exp_uvar (_29_242) -> begin
"Exp_uvar"
end
| FStar_Absyn_Syntax.Exp_delayed (_29_245) -> begin
"Exp_delayed"
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_29_248, m)) -> begin
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
| FStar_Absyn_Syntax.Typ_delayed (_29_262) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_29_265, l)) -> begin
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
| FStar_Absyn_Syntax.Typ_app (_29_285, []) -> begin
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
| _29_305 -> begin
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
(filter_imp args)
end
in if ((is_ite t) && ((FStar_List.length args) = 3)) then begin
(let _131_140 = (let _131_135 = (FStar_List.nth args 0)
in (arg_to_string _131_135))
in (let _131_139 = (let _131_136 = (FStar_List.nth args 1)
in (arg_to_string _131_136))
in (let _131_138 = (let _131_137 = (FStar_List.nth args 2)
in (arg_to_string _131_137))
in (FStar_Util.format3 "if %s then %s else %s" _131_140 _131_139 _131_138))))
end else begin
if ((is_b2t t) && ((FStar_List.length args) = 1)) then begin
(let _131_141 = (FStar_List.nth args 0)
in (FStar_All.pipe_right _131_141 arg_to_string))
end else begin
if ((is_quant t) && ((FStar_List.length args) <= 2)) then begin
(let _131_146 = (quant_to_string t)
in (let _131_145 = (let _131_142 = (FStar_List.nth args' 0)
in (qbinder_to_string _131_142))
in (let _131_144 = (let _131_143 = (FStar_List.nth args' 0)
in (qbody_to_string _131_143))
in (FStar_Util.format3 "(%s (%s). %s)" _131_146 _131_145 _131_144))))
end else begin
if ((is_infix_type_op t) && ((FStar_List.length args') = 2)) then begin
(let _131_151 = (let _131_147 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _131_147 arg_to_string))
in (let _131_150 = (FStar_All.pipe_right t infix_type_op_to_string)
in (let _131_149 = (let _131_148 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _131_148 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _131_151 _131_150 _131_149))))
end else begin
if ((is_unary_type_op t) && ((FStar_List.length args') = 1)) then begin
(let _131_154 = (FStar_All.pipe_right t unary_type_op_to_string)
in (let _131_153 = (let _131_152 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _131_152 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _131_154 _131_153)))
end else begin
(let _131_156 = (FStar_All.pipe_right t typ_to_string)
in (let _131_155 = (FStar_All.pipe_right args args_to_string)
in (FStar_Util.format2 "(%s %s)" _131_156 _131_155)))
end
end
end
end
end))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(let _131_158 = (binders_to_string " " binders)
in (let _131_157 = (FStar_All.pipe_right t2 typ_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _131_158 _131_157)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _131_160 = (typ_to_string t)
in (let _131_159 = (kind_to_string k)
in (FStar_Util.format2 "(%s <: %s)" _131_160 _131_159)))
end else begin
(FStar_All.pipe_right t typ_to_string)
end
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"<UNKNOWN>"
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(match ((FStar_Absyn_Visit.compress_typ_aux false x)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_29_335); FStar_Absyn_Syntax.tk = _29_333; FStar_Absyn_Syntax.pos = _29_331; FStar_Absyn_Syntax.fvs = _29_329; FStar_Absyn_Syntax.uvs = _29_327} -> begin
(uvar_t_to_string (uv, k))
end
| t -> begin
(FStar_All.pipe_right t typ_to_string)
end)
end)))
and uvar_t_to_string : (FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd)  ->  Prims.string = (fun _29_341 -> (match (_29_341) with
| (uv, k) -> begin
if (false && (FStar_ST.read FStar_Options.print_real_names)) then begin
(let _131_164 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _131_162 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _131_162))
end
in (let _131_163 = (kind_to_string k)
in (FStar_Util.format2 "(U%s : %s)" _131_164 _131_163)))
end else begin
(let _131_166 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _131_165 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _131_165))
end
in (FStar_Util.format1 "U%s" _131_166))
end
end))
and imp_to_string : Prims.string  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s _29_5 -> (match (_29_5) with
| Some (FStar_Absyn_Syntax.Implicit (_29_345)) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Absyn_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _29_351 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (match (b) with
| (FStar_Util.Inl (a), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _131_171 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _131_171 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp a.FStar_Absyn_Syntax.v))) then begin
(kind_to_string a.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits)))) then begin
(let _131_172 = (strBvd a.FStar_Absyn_Syntax.v)
in (imp_to_string _131_172 imp))
end else begin
(let _131_176 = (let _131_175 = (let _131_173 = (strBvd a.FStar_Absyn_Syntax.v)
in (Prims.strcat _131_173 ":"))
in (let _131_174 = (kind_to_string a.FStar_Absyn_Syntax.sort)
in (Prims.strcat _131_175 _131_174)))
in (imp_to_string _131_176 imp))
end
end
end
| (FStar_Util.Inr (x), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _131_177 = (FStar_ST.read FStar_Options.print_real_names)
in (FStar_All.pipe_right _131_177 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp x.FStar_Absyn_Syntax.v))) then begin
(typ_to_string x.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_implicits)))) then begin
(let _131_178 = (strBvd x.FStar_Absyn_Syntax.v)
in (imp_to_string _131_178 imp))
end else begin
(let _131_182 = (let _131_181 = (let _131_179 = (strBvd x.FStar_Absyn_Syntax.v)
in (Prims.strcat _131_179 ":"))
in (let _131_180 = (typ_to_string x.FStar_Absyn_Syntax.sort)
in (Prims.strcat _131_181 _131_180)))
in (imp_to_string _131_182 imp))
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
(let _131_187 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _131_187 (FStar_String.concat sep)))
end else begin
(let _131_188 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _131_188 (FStar_String.concat sep)))
end))
and arg_to_string : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _29_6 -> (match (_29_6) with
| (FStar_Util.Inl (a), imp) -> begin
(let _131_190 = (typ_to_string a)
in (imp_to_string _131_190 imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _131_191 = (exp_to_string x)
in (imp_to_string _131_191 imp))
end))
and args_to_string : FStar_Absyn_Syntax.args  ->  Prims.string = (fun args -> (let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _131_193 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _131_193 (FStar_String.concat " ")))))
and lcomp_typ_to_string : FStar_Absyn_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _131_196 = (sli lc.FStar_Absyn_Syntax.eff_name)
in (let _131_195 = (typ_to_string lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _131_196 _131_195))))
and comp_typ_to_string : FStar_Absyn_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _131_198 = (typ_to_string t)
in (FStar_Util.format1 "Tot %s" _131_198))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(let basic = if ((FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _29_7 -> (match (_29_7) with
| FStar_Absyn_Syntax.TOTAL -> begin
true
end
| _29_387 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args)))) then begin
(let _131_200 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _131_200))
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_Ident.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid)) then begin
(typ_to_string c.FStar_Absyn_Syntax.result_typ)
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _29_8 -> (match (_29_8) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _29_391 -> begin
false
end))))) then begin
(let _131_202 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _131_202))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _131_206 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _131_205 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (let _131_204 = (let _131_203 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.effect_args (FStar_List.map effect_arg_to_string))
in (FStar_All.pipe_right _131_203 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _131_206 _131_205 _131_204))))
end else begin
(let _131_208 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _131_207 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _131_208 _131_207)))
end
end
end
end
in (let dec = (let _131_212 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.collect (fun _29_9 -> (match (_29_9) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _131_211 = (let _131_210 = (exp_to_string e)
in (FStar_Util.format1 " (decreases %s)" _131_210))
in (_131_211)::[])
end
| _29_397 -> begin
[]
end))))
in (FStar_All.pipe_right _131_212 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and effect_arg_to_string : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun e -> (match (e) with
| (FStar_Util.Inr (e), _29_403) -> begin
(exp_to_string e)
end
| (FStar_Util.Inl (wp), _29_408) -> begin
(formula_to_string wp)
end))
and formula_to_string : FStar_Absyn_Syntax.typ  ->  Prims.string = (fun phi -> (typ_to_string phi))
and formula_to_string_old_now_unused : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun phi -> (let const_op = (fun f _29_414 -> f)
in (let un_op = (fun f _29_10 -> (match (_29_10) with
| (FStar_Util.Inl (t), _29_422)::[] -> begin
(let _131_224 = (formula_to_string t)
in (FStar_Util.format2 "%s %s" f _131_224))
end
| _29_426 -> begin
(FStar_All.failwith "impos")
end))
in (let bin_top = (fun f _29_11 -> (match (_29_11) with
| (FStar_Util.Inl (t1), _29_438)::(FStar_Util.Inl (t2), _29_433)::[] -> begin
(let _131_230 = (formula_to_string t1)
in (let _131_229 = (formula_to_string t2)
in (FStar_Util.format3 "%s %s %s" _131_230 f _131_229)))
end
| _29_442 -> begin
(FStar_All.failwith "Impos")
end))
in (let bin_eop = (fun f _29_12 -> (match (_29_12) with
| (FStar_Util.Inr (e1), _29_454)::(FStar_Util.Inr (e2), _29_449)::[] -> begin
(let _131_236 = (exp_to_string e1)
in (let _131_235 = (exp_to_string e2)
in (FStar_Util.format3 "%s %s %s" _131_236 f _131_235)))
end
| _29_458 -> begin
(FStar_All.failwith "impos")
end))
in (let ite = (fun _29_13 -> (match (_29_13) with
| (FStar_Util.Inl (t1), _29_473)::(FStar_Util.Inl (t2), _29_468)::(FStar_Util.Inl (t3), _29_463)::[] -> begin
(let _131_241 = (formula_to_string t1)
in (let _131_240 = (formula_to_string t2)
in (let _131_239 = (formula_to_string t3)
in (FStar_Util.format3 "if %s then %s else %s" _131_241 _131_240 _131_239))))
end
| _29_477 -> begin
(FStar_All.failwith "impos")
end))
in (let eq_op = (fun _29_14 -> (match (_29_14) with
| (FStar_Util.Inl (t1), _29_498)::(FStar_Util.Inl (t2), _29_493)::(FStar_Util.Inr (e1), _29_488)::(FStar_Util.Inr (e2), _29_483)::[] -> begin
if (FStar_ST.read FStar_Options.print_implicits) then begin
(let _131_247 = (typ_to_string t1)
in (let _131_246 = (typ_to_string t2)
in (let _131_245 = (exp_to_string e1)
in (let _131_244 = (exp_to_string e2)
in (FStar_Util.format4 "Eq2 %s %s %s %s" _131_247 _131_246 _131_245 _131_244)))))
end else begin
(let _131_249 = (exp_to_string e1)
in (let _131_248 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _131_249 _131_248)))
end
end
| (FStar_Util.Inr (e1), _29_509)::(FStar_Util.Inr (e2), _29_504)::[] -> begin
(let _131_251 = (exp_to_string e1)
in (let _131_250 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _131_251 _131_250)))
end
| _29_513 -> begin
(FStar_All.failwith "Impossible")
end))
in (let connectives = ((FStar_Absyn_Const.and_lid, (bin_top "/\\")))::((FStar_Absyn_Const.or_lid, (bin_top "\\/")))::((FStar_Absyn_Const.imp_lid, (bin_top "==>")))::((FStar_Absyn_Const.iff_lid, (bin_top "<==>")))::((FStar_Absyn_Const.ite_lid, ite))::((FStar_Absyn_Const.not_lid, (un_op "~")))::((FStar_Absyn_Const.eqT_lid, (bin_top "==")))::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op "True")))::((FStar_Absyn_Const.false_lid, (const_op "False")))::[]
in (let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (binders, phi) -> begin
(let _131_290 = (binders_to_string " " binders)
in (let _131_289 = (formula_to_string phi)
in (FStar_Util.format2 "(fun %s => %s)" _131_290 _131_289)))
end
| _29_523 -> begin
(typ_to_string phi)
end))
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _29_533 -> (match (_29_533) with
| (l, _29_532) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_29_536, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, _29_542, body)) -> begin
(let _131_308 = (binders_to_string " " vars)
in (let _131_307 = (formula_to_string body)
in (FStar_Util.format2 "(forall %s. %s)" _131_308 _131_307)))
end
| Some (FStar_Absyn_Util.QEx (vars, _29_549, body)) -> begin
(let _131_310 = (binders_to_string " " vars)
in (let _131_309 = (formula_to_string body)
in (FStar_Util.format2 "(exists %s. %s)" _131_310 _131_309)))
end))))))))))
and exp_to_string : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun x -> (match ((let _131_312 = (FStar_Absyn_Util.compress_exp x)
in _131_312.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_delayed (_29_556) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _29_560)) -> begin
(exp_to_string e)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(uvar_e_to_string (uv, t))
end
| FStar_Absyn_Syntax.Exp_bvar (bvv) -> begin
(strBvd bvv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_fvar (fv, _29_572) -> begin
(sli fv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(FStar_All.pipe_right c const_to_string)
end
| FStar_Absyn_Syntax.Exp_abs (binders, e) -> begin
(let _131_314 = (binders_to_string " " binders)
in (let _131_313 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _131_314 _131_313)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(let lex = if (FStar_ST.read FStar_Options.print_implicits) then begin
None
end else begin
(reconstruct_lex x)
end
in (match (lex) with
| Some (es) -> begin
(let _131_317 = (let _131_316 = (let _131_315 = (FStar_List.map exp_to_string es)
in (FStar_String.concat "; " _131_315))
in (Prims.strcat "%[" _131_316))
in (Prims.strcat _131_317 "]"))
end
| None -> begin
(let args' = (let _131_319 = (filter_imp args)
in (FStar_All.pipe_right _131_319 (FStar_List.filter (fun _29_15 -> (match (_29_15) with
| (FStar_Util.Inr (_29_591), _29_594) -> begin
true
end
| _29_597 -> begin
false
end)))))
in if ((is_infix_prim_op e) && ((FStar_List.length args') = 2)) then begin
(let _131_324 = (let _131_320 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _131_320 arg_to_string))
in (let _131_323 = (FStar_All.pipe_right e infix_prim_op_to_string)
in (let _131_322 = (let _131_321 = (FStar_List.nth args' 1)
in (FStar_All.pipe_right _131_321 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _131_324 _131_323 _131_322))))
end else begin
if ((is_unary_prim_op e) && ((FStar_List.length args') = 1)) then begin
(let _131_327 = (FStar_All.pipe_right e unary_prim_op_to_string)
in (let _131_326 = (let _131_325 = (FStar_List.nth args' 0)
in (FStar_All.pipe_right _131_325 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _131_327 _131_326)))
end else begin
(let _131_329 = (FStar_All.pipe_right e exp_to_string)
in (let _131_328 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _131_329 _131_328)))
end
end)
end))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _131_337 = (FStar_All.pipe_right e exp_to_string)
in (let _131_336 = (let _131_335 = (FStar_All.pipe_right pats (FStar_List.map (fun _29_606 -> (match (_29_606) with
| (p, wopt, e) -> begin
(let _131_334 = (FStar_All.pipe_right p pat_to_string)
in (let _131_333 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _131_331 = (FStar_All.pipe_right w exp_to_string)
in (FStar_Util.format1 "when %s" _131_331))
end)
in (let _131_332 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format3 "%s %s -> %s" _131_334 _131_333 _131_332))))
end))))
in (FStar_Util.concat_l "\n\t" _131_335))
in (FStar_Util.format2 "(match %s with %s)" _131_337 _131_336)))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _29_613) -> begin
(let _131_339 = (FStar_All.pipe_right e exp_to_string)
in (let _131_338 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "(%s:%s)" _131_339 _131_338)))
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(let _131_341 = (lbs_to_string lbs)
in (let _131_340 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "%s in %s" _131_341 _131_340)))
end))
and uvar_e_to_string : (FStar_Absyn_Syntax.uvar_e * FStar_Absyn_Syntax.typ)  ->  Prims.string = (fun _29_623 -> (match (_29_623) with
| (uv, _29_622) -> begin
(let _131_344 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _131_343 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _131_343))
end
in (Prims.strcat "\'e" _131_344))
end))
and lbs_to_string : FStar_Absyn_Syntax.letbindings  ->  Prims.string = (fun lbs -> (let _131_351 = (let _131_350 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _131_349 = (lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _131_348 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbtyp typ_to_string)
in (let _131_347 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbdef exp_to_string)
in (FStar_Util.format3 "%s:%s = %s" _131_349 _131_348 _131_347)))))))
in (FStar_Util.concat_l "\n and " _131_350))
in (FStar_Util.format2 "let %s %s" (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _131_351)))
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
and either_l_to_string : Prims.string  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either Prims.list  ->  Prims.string = (fun delim l -> (let _131_356 = (FStar_All.pipe_right l (FStar_List.map either_to_string))
in (FStar_All.pipe_right _131_356 (FStar_Util.concat_l delim))))
and meta_to_string : FStar_Absyn_Syntax.meta_t  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Meta_refresh_label (t, _29_641, _29_643) -> begin
(let _131_358 = (typ_to_string t)
in (FStar_Util.format1 "(refresh) %s" _131_358))
end
| FStar_Absyn_Syntax.Meta_labeled (t, l, _29_649, _29_651) -> begin
(let _131_359 = (typ_to_string t)
in (FStar_Util.format2 "(labeled \"%s\") %s" l _131_359))
end
| FStar_Absyn_Syntax.Meta_named (_29_655, l) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Meta_pattern (t, ps) -> begin
(let _131_361 = (pats_to_string ps)
in (let _131_360 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "{:pattern %s} %s" _131_361 _131_360)))
end
| FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _29_666) -> begin
(let _131_363 = (formula_to_string t1)
in (let _131_362 = (formula_to_string t2)
in (FStar_Util.format2 "%s /\\ %s" _131_363 _131_362)))
end))
and pats_to_string : FStar_Absyn_Syntax.arg Prims.list Prims.list  ->  Prims.string = (fun ps -> (let _131_367 = (FStar_All.pipe_right ps (FStar_List.map (fun e -> (let _131_366 = (FStar_All.pipe_right e (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _131_366 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _131_367 (FStar_String.concat " \\/ "))))
and kind_to_string : FStar_Absyn_Syntax.knd  ->  Prims.string = (fun x -> (match ((let _131_369 = (FStar_Absyn_Util.compress_kind x)
in _131_369.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_lam (_29_673) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Kind_delayed (_29_676) -> begin
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
(let _131_371 = (sli n)
in (let _131_370 = (args_to_string args)
in (FStar_Util.format2 "%s %s" _131_371 _131_370)))
end
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(let _131_373 = (binders_to_string " -> " binders)
in (let _131_372 = (FStar_All.pipe_right k kind_to_string)
in (FStar_Util.format2 "(%s -> %s)" _131_373 _131_372)))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun uv -> (let _131_375 = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _131_374 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _131_374))
end
in (Prims.strcat "\'k_" _131_375)))
and uvar_k_to_string' : ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list)  ->  Prims.string = (fun _29_698 -> (match (_29_698) with
| (uv, args) -> begin
(let str = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _131_377 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _131_377))
end
in (let _131_378 = (args_to_string args)
in (FStar_Util.format2 "(\'k_%s %s)" str _131_378)))
end))
and pat_to_string : FStar_Absyn_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (l, _29_703, pats) -> begin
(let _131_383 = (sli l.FStar_Absyn_Syntax.v)
in (let _131_382 = (let _131_381 = (FStar_List.map (fun _29_709 -> (match (_29_709) with
| (x, b) -> begin
(let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _131_381 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _131_383 _131_382)))
end
| FStar_Absyn_Syntax.Pat_dot_term (x, _29_713) -> begin
(let _131_384 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".%s" _131_384))
end
| FStar_Absyn_Syntax.Pat_dot_typ (x, _29_718) -> begin
(let _131_385 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".\'%s" _131_385))
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
| FStar_Absyn_Syntax.Pat_wild (_29_728) -> begin
"_"
end
| FStar_Absyn_Syntax.Pat_twild (_29_731) -> begin
"\'_"
end
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(let _131_386 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _131_386))
end))

# 460 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let subst_to_string = (fun subst -> (let _131_394 = (let _131_393 = (FStar_List.map (fun _29_16 -> (match (_29_16) with
| FStar_Util.Inl (a, t) -> begin
(let _131_390 = (strBvd a)
in (let _131_389 = (typ_to_string t)
in (FStar_Util.format2 "(%s -> %s)" _131_390 _131_389)))
end
| FStar_Util.Inr (x, e) -> begin
(let _131_392 = (strBvd x)
in (let _131_391 = (exp_to_string e)
in (FStar_Util.format2 "(%s -> %s)" _131_392 _131_391)))
end)) subst)
in (FStar_All.pipe_right _131_393 (FStar_String.concat ", ")))
in (FStar_All.pipe_left (FStar_Util.format1 "{%s}") _131_394)))

# 466 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let freevars_to_string : FStar_Absyn_Syntax.freevars  ->  Prims.string = (fun fvs -> (let f = (fun l -> (let _131_400 = (let _131_399 = (FStar_All.pipe_right l FStar_Util.set_elements)
in (FStar_All.pipe_right _131_399 (FStar_List.map (fun t -> (strBvd t.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _131_400 (FStar_String.concat ", "))))
in (let _131_402 = (f fvs.FStar_Absyn_Syntax.ftvs)
in (let _131_401 = (f fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_Util.format2 "ftvs={%s}, fxvs={%s}" _131_402 _131_401)))))

# 469 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let qual_to_string : FStar_Absyn_Syntax.qualifier  ->  Prims.string = (fun _29_17 -> (match (_29_17) with
| FStar_Absyn_Syntax.Logic -> begin
"logic"
end
| FStar_Absyn_Syntax.Opaque -> begin
"opaque"
end
| FStar_Absyn_Syntax.Discriminator (_29_755) -> begin
"discriminator"
end
| FStar_Absyn_Syntax.Projector (_29_758) -> begin
"projector"
end
| FStar_Absyn_Syntax.RecordType (ids) -> begin
(let _131_407 = (let _131_406 = (FStar_All.pipe_right ids (FStar_List.map (fun lid -> lid.FStar_Ident.ident.FStar_Ident.idText)))
in (FStar_All.pipe_right _131_406 (FStar_String.concat ", ")))
in (FStar_Util.format1 "record(%s)" _131_407))
end
| _29_764 -> begin
"other"
end))

# 477 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let quals_to_string : FStar_Absyn_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (let _131_410 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _131_410 (FStar_String.concat " "))))

# 478 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let rec sigelt_to_string : FStar_Absyn_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.ResetOptions, _29_769) -> begin
"#reset-options"
end
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.SetOptions (s), _29_775) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _29_782, _29_784, quals, _29_787) -> begin
(let _131_415 = (quals_to_string quals)
in (let _131_414 = (binders_to_string " " tps)
in (let _131_413 = (kind_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _131_415 lid.FStar_Ident.str _131_414 _131_413))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, _29_795, _29_797) -> begin
(let _131_418 = (binders_to_string " " tps)
in (let _131_417 = (kind_to_string k)
in (let _131_416 = (typ_to_string t)
in (FStar_Util.format4 "type %s %s : %s = %s" lid.FStar_Ident.str _131_418 _131_417 _131_416))))
end
| FStar_Absyn_Syntax.Sig_datacon (lid, t, _29_803, _29_805, _29_807, _29_809) -> begin
(let _131_419 = (typ_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _131_419))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _29_816) -> begin
(let _131_421 = (quals_to_string quals)
in (let _131_420 = (typ_to_string t)
in (FStar_Util.format3 "%s val %s : %s" _131_421 lid.FStar_Ident.str _131_420)))
end
| FStar_Absyn_Syntax.Sig_assume (lid, f, _29_822, _29_824) -> begin
(let _131_422 = (typ_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _131_422))
end
| FStar_Absyn_Syntax.Sig_let (lbs, _29_829, _29_831, b) -> begin
(lbs_to_string lbs)
end
| FStar_Absyn_Syntax.Sig_main (e, _29_837) -> begin
(let _131_423 = (exp_to_string e)
in (FStar_Util.format1 "let _ = %s" _131_423))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _29_842, _29_844, _29_846) -> begin
(let _131_424 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _131_424 (FStar_String.concat "\n")))
end
| FStar_Absyn_Syntax.Sig_new_effect (_29_850) -> begin
"new_effect { ... }"
end
| FStar_Absyn_Syntax.Sig_sub_effect (_29_853) -> begin
"sub_effect ..."
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_29_856) -> begin
"kind ..."
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, tps, c, _29_862, _29_864) -> begin
(let _131_427 = (sli l)
in (let _131_426 = (binders_to_string " " tps)
in (let _131_425 = (comp_typ_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _131_427 _131_426 _131_425))))
end))

# 493 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _131_432 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _131_432 msg)))

# 495 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let rec sigelt_to_string_short : FStar_Absyn_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_let ((_29_871, {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _29_875; FStar_Absyn_Syntax.lbdef = _29_873}::[]), _29_883, _29_885, _29_887) -> begin
(let _131_435 = (typ_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Ident.str _131_435))
end
| _29_891 -> begin
(let _131_438 = (let _131_437 = (FStar_Absyn_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _131_437 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _131_438 (FStar_String.concat ", ")))
end))

# 499 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\print.fs"

let rec modul_to_string : FStar_Absyn_Syntax.modul  ->  Prims.string = (fun m -> (let _131_443 = (sli m.FStar_Absyn_Syntax.name)
in (let _131_442 = (let _131_441 = (FStar_List.map sigelt_to_string m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _131_441 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _131_443 _131_442))))




