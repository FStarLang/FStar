
open Prims

let infix_prim_ops : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = (((FStar_Absyn_Const.op_Addition), ("+")))::(((FStar_Absyn_Const.op_Subtraction), ("-")))::(((FStar_Absyn_Const.op_Multiply), ("*")))::(((FStar_Absyn_Const.op_Division), ("/")))::(((FStar_Absyn_Const.op_Eq), ("=")))::(((FStar_Absyn_Const.op_ColonEq), (":=")))::(((FStar_Absyn_Const.op_notEq), ("<>")))::(((FStar_Absyn_Const.op_And), ("&&")))::(((FStar_Absyn_Const.op_Or), ("||")))::(((FStar_Absyn_Const.op_LTE), ("<=")))::(((FStar_Absyn_Const.op_GTE), (">=")))::(((FStar_Absyn_Const.op_LT), ("<")))::(((FStar_Absyn_Const.op_GT), (">")))::(((FStar_Absyn_Const.op_Modulus), ("mod")))::[]


let unary_prim_ops : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = (((FStar_Absyn_Const.op_Negation), ("not")))::(((FStar_Absyn_Const.op_Minus), ("-")))::[]


let infix_type_ops : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = (((FStar_Absyn_Const.and_lid), ("/\\")))::(((FStar_Absyn_Const.or_lid), ("\\/")))::(((FStar_Absyn_Const.imp_lid), ("==>")))::(((FStar_Absyn_Const.iff_lid), ("<==>")))::(((FStar_Absyn_Const.precedes_lid), ("<<")))::(((FStar_Absyn_Const.eq2_lid), ("==")))::(((FStar_Absyn_Const.eqT_lid), ("==")))::[]


let unary_type_ops : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = (((FStar_Absyn_Const.not_lid), ("~")))::[]


let is_prim_op = (fun ps f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _33_22) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _33_26 -> begin
false
end))


let is_type_op = (fun ps t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals ftv.FStar_Absyn_Syntax.v)))
end
| _33_32 -> begin
false
end))


let get_lid = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _33_36) -> begin
fv.FStar_Absyn_Syntax.v
end
| _33_40 -> begin
(failwith "get_lid")
end))


let get_type_lid = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
ftv.FStar_Absyn_Syntax.v
end
| _33_45 -> begin
(failwith "get_type_lid")
end))


let is_infix_prim_op : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split infix_prim_ops)) e))


let is_unary_prim_op : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split unary_prim_ops)) e))


let is_infix_type_op : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op (Prims.fst (FStar_List.split infix_type_ops)) t))


let is_unary_type_op : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op (Prims.fst (FStar_List.split unary_type_ops)) t))


let quants : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = (((FStar_Absyn_Const.forall_lid), ("forall")))::(((FStar_Absyn_Const.exists_lid), ("exists")))::(((FStar_Absyn_Const.allTyp_lid), ("forall")))::(((FStar_Absyn_Const.exTyp_lid), ("exists")))::[]


let is_b2t : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op ((FStar_Absyn_Const.b2t_lid)::[]) t))


let is_quant : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op (Prims.fst (FStar_List.split quants)) t))


let is_ite : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (is_type_op ((FStar_Absyn_Const.ite_lid)::[]) t))


let is_lex_cons : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Absyn_Const.lexcons_lid)::[]) f))


let is_lex_top : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Absyn_Const.lextop_lid)::[]) f))


let is_inr = (fun _33_1 -> (match (_33_1) with
| FStar_Util.Inl (_33_57) -> begin
false
end
| FStar_Util.Inr (_33_60) -> begin
true
end))


let rec reconstruct_lex : FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _133_28 = (FStar_Absyn_Util.compress_exp e)
in _133_28.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (f, args) -> begin
(

let args = (FStar_List.filter (fun a -> (match (a) with
| ((FStar_Util.Inl (_), _)) | ((FStar_Util.Inr (_), Some (FStar_Absyn_Syntax.Implicit (_)))) -> begin
false
end
| _33_83 -> begin
true
end)) args)
in (

let exps = (FStar_List.map (fun _33_2 -> (match (_33_2) with
| (FStar_Util.Inl (_33_87), _33_90) -> begin
(failwith "impossible")
end
| (FStar_Util.Inr (x), _33_95) -> begin
x
end)) args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = (Prims.parse_int "2"))) then begin
(match ((let _133_31 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex _133_31))) with
| Some (xs) -> begin
(let _133_33 = (let _133_32 = (FStar_List.nth exps (Prims.parse_int "0"))
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
| _33_102 -> begin
if (is_lex_top e) then begin
Some ([])
end else begin
None
end
end))


let rec find = (fun f l -> (match (l) with
| [] -> begin
(failwith "blah")
end
| (hd)::tl -> begin
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


let rec sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_Options.print_real_names ()) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)


let strBvd = (fun bvd -> if (FStar_Options.print_real_names ()) then begin
(Prims.strcat bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText bvd.FStar_Absyn_Syntax.realname.FStar_Ident.idText)
end else begin
if ((FStar_Options.hide_genident_nums ()) && (FStar_Util.starts_with bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText "_")) then begin
try
(match (()) with
| () -> begin
(

let _33_127 = (let _133_62 = (FStar_Util.substring_from bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText (Prims.parse_int "1"))
in (FStar_Util.int_of_string _133_62))
in "_?")
end)
with
| _33_124 -> begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end
end else begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end
end)


let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _33_3 -> (match (_33_3) with
| (_33_132, Some (FStar_Absyn_Syntax.Implicit (_33_134))) -> begin
false
end
| _33_139 -> begin
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
| FStar_Const.Const_float (x) -> begin
(FStar_Util.string_of_float x)
end
| FStar_Const.Const_char (x) -> begin
(Prims.strcat "\'" (Prims.strcat (FStar_Util.string_of_char x) "\'"))
end
| FStar_Const.Const_string (bytes, _33_151) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_33_155) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x, _33_159) -> begin
x
end
| FStar_Const.Const_range (r) -> begin
(FStar_Range.string_of_range r)
end
| (FStar_Const.Const_reify) | (FStar_Const.Const_reflect (_)) -> begin
"unsupported constant"
end))


let rec tag_of_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_33_170) -> begin
"Typ_btvar"
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(Prims.strcat "Typ_const " v.FStar_Absyn_Syntax.v.FStar_Ident.str)
end
| FStar_Absyn_Syntax.Typ_fun (_33_175) -> begin
"Typ_fun"
end
| FStar_Absyn_Syntax.Typ_refine (_33_178) -> begin
"Typ_refine"
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let _133_103 = (tag_of_typ head)
in (let _133_102 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.format2 "Typ_app(%s, [%s args])" _133_103 _133_102)))
end
| FStar_Absyn_Syntax.Typ_lam (_33_185) -> begin
"Typ_lam"
end
| FStar_Absyn_Syntax.Typ_ascribed (_33_188) -> begin
"Typ_ascribed"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_33_191)) -> begin
"Typ_meta_pattern"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_33_195)) -> begin
"Typ_meta_named"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_33_199)) -> begin
"Typ_meta_labeled"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_33_203)) -> begin
"Typ_meta_refresh_label"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_33_207)) -> begin
"Typ_meta_slack_formula"
end
| FStar_Absyn_Syntax.Typ_uvar (_33_211) -> begin
"Typ_uvar"
end
| FStar_Absyn_Syntax.Typ_delayed (_33_214) -> begin
"Typ_delayed"
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"Typ_unknown"
end))
and tag_of_exp = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_33_219) -> begin
"Exp_bvar"
end
| FStar_Absyn_Syntax.Exp_fvar (_33_222) -> begin
"Exp_fvar"
end
| FStar_Absyn_Syntax.Exp_constant (_33_225) -> begin
"Exp_constant"
end
| FStar_Absyn_Syntax.Exp_abs (_33_228) -> begin
"Exp_abs"
end
| FStar_Absyn_Syntax.Exp_app (_33_231) -> begin
"Exp_app"
end
| FStar_Absyn_Syntax.Exp_match (_33_234) -> begin
"Exp_match"
end
| FStar_Absyn_Syntax.Exp_ascribed (_33_237) -> begin
"Exp_ascribed"
end
| FStar_Absyn_Syntax.Exp_let (_33_240) -> begin
"Exp_let"
end
| FStar_Absyn_Syntax.Exp_uvar (_33_243) -> begin
"Exp_uvar"
end
| FStar_Absyn_Syntax.Exp_delayed (_33_246) -> begin
"Exp_delayed"
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_33_249, m)) -> begin
(let _133_107 = (meta_e_to_string m)
in (Prims.strcat "Exp_meta_desugared " _133_107))
end))
and meta_e_to_string : FStar_Absyn_Syntax.meta_source_info  ->  Prims.string = (fun _33_4 -> (match (_33_4) with
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

let x = (FStar_Absyn_Util.compress_typ x)
in (match (x.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_33_263) -> begin
(failwith "impossible")
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_33_266, l)) -> begin
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
| FStar_Absyn_Syntax.Typ_app (_33_286, []) -> begin
(failwith "Empty args!")
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(

let q_to_string = (fun k a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(

let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam ((b)::[], t) -> begin
(k ((b), (t)))
end
| _33_306 -> begin
(let _133_129 = (tag_of_typ t)
in (let _133_128 = (typ_to_string t)
in (FStar_Util.format2 "<Expected a type-lambda! got %s>%s" _133_129 _133_128)))
end))
end
| FStar_Util.Inr (e) -> begin
(let _133_130 = (exp_to_string e)
in (FStar_Util.format1 "(<Expected a type!>%s)" _133_130))
end))
in (

let qbinder_to_string = (q_to_string (fun x -> (binder_to_string (Prims.fst x))))
in (

let qbody_to_string = (q_to_string (fun x -> (typ_to_string (Prims.snd x))))
in (

let args' = if ((FStar_Options.print_implicits ()) && (not ((is_quant t)))) then begin
args
end else begin
(filter_imp args)
end
in if ((is_ite t) && ((FStar_List.length args) = (Prims.parse_int "3"))) then begin
(let _133_140 = (let _133_135 = (FStar_List.nth args (Prims.parse_int "0"))
in (arg_to_string _133_135))
in (let _133_139 = (let _133_136 = (FStar_List.nth args (Prims.parse_int "1"))
in (arg_to_string _133_136))
in (let _133_138 = (let _133_137 = (FStar_List.nth args (Prims.parse_int "2"))
in (arg_to_string _133_137))
in (FStar_Util.format3 "if %s then %s else %s" _133_140 _133_139 _133_138))))
end else begin
if ((is_b2t t) && ((FStar_List.length args) = (Prims.parse_int "1"))) then begin
(let _133_141 = (FStar_List.nth args (Prims.parse_int "0"))
in (FStar_All.pipe_right _133_141 arg_to_string))
end else begin
if ((is_quant t) && ((FStar_List.length args) <= (Prims.parse_int "2"))) then begin
(let _133_146 = (quant_to_string t)
in (let _133_145 = (let _133_142 = (FStar_List.nth args' (Prims.parse_int "0"))
in (qbinder_to_string _133_142))
in (let _133_144 = (let _133_143 = (FStar_List.nth args' (Prims.parse_int "0"))
in (qbody_to_string _133_143))
in (FStar_Util.format3 "(%s (%s). %s)" _133_146 _133_145 _133_144))))
end else begin
if ((is_infix_type_op t) && ((FStar_List.length args') = (Prims.parse_int "2"))) then begin
(let _133_151 = (let _133_147 = (FStar_List.nth args' (Prims.parse_int "0"))
in (FStar_All.pipe_right _133_147 arg_to_string))
in (let _133_150 = (FStar_All.pipe_right t infix_type_op_to_string)
in (let _133_149 = (let _133_148 = (FStar_List.nth args' (Prims.parse_int "1"))
in (FStar_All.pipe_right _133_148 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _133_151 _133_150 _133_149))))
end else begin
if ((is_unary_type_op t) && ((FStar_List.length args') = (Prims.parse_int "1"))) then begin
(let _133_154 = (FStar_All.pipe_right t unary_type_op_to_string)
in (let _133_153 = (let _133_152 = (FStar_List.nth args' (Prims.parse_int "0"))
in (FStar_All.pipe_right _133_152 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _133_154 _133_153)))
end else begin
(let _133_156 = (FStar_All.pipe_right t typ_to_string)
in (let _133_155 = (FStar_All.pipe_right args args_to_string)
in (FStar_Util.format2 "(%s %s)" _133_156 _133_155)))
end
end
end
end
end))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(let _133_158 = (binders_to_string " " binders)
in (let _133_157 = (FStar_All.pipe_right t2 typ_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _133_158 _133_157)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
if (FStar_Options.print_real_names ()) then begin
(let _133_160 = (typ_to_string t)
in (let _133_159 = (kind_to_string k)
in (FStar_Util.format2 "(%s <: %s)" _133_160 _133_159)))
end else begin
(FStar_All.pipe_right t typ_to_string)
end
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"<UNKNOWN>"
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(match ((FStar_Absyn_Visit.compress_typ_aux false x)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_33_336); FStar_Absyn_Syntax.tk = _33_334; FStar_Absyn_Syntax.pos = _33_332; FStar_Absyn_Syntax.fvs = _33_330; FStar_Absyn_Syntax.uvs = _33_328} -> begin
(uvar_t_to_string ((uv), (k)))
end
| t -> begin
(FStar_All.pipe_right t typ_to_string)
end)
end)))
and uvar_t_to_string : (FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd)  ->  Prims.string = (fun _33_342 -> (match (_33_342) with
| (uv, k) -> begin
if (false && (FStar_Options.print_real_names ())) then begin
(let _133_164 = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _133_162 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _133_162))
end
in (let _133_163 = (kind_to_string k)
in (FStar_Util.format2 "(U%s : %s)" _133_164 _133_163)))
end else begin
(let _133_166 = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _133_165 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _133_165))
end
in (FStar_Util.format1 "U%s" _133_166))
end
end))
and imp_to_string : Prims.string  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s _33_5 -> (match (_33_5) with
| Some (FStar_Absyn_Syntax.Implicit (_33_346)) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Absyn_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _33_352 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (match (b) with
| (FStar_Util.Inl (a), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _133_171 = (FStar_Options.print_real_names ())
in (FStar_All.pipe_right _133_171 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp a.FStar_Absyn_Syntax.v))) then begin
(kind_to_string a.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_implicits ())))) then begin
(let _133_172 = (strBvd a.FStar_Absyn_Syntax.v)
in (imp_to_string _133_172 imp))
end else begin
(let _133_176 = (let _133_175 = (strBvd a.FStar_Absyn_Syntax.v)
in (let _133_174 = (let _133_173 = (kind_to_string a.FStar_Absyn_Syntax.sort)
in (Prims.strcat ":" _133_173))
in (Prims.strcat _133_175 _133_174)))
in (imp_to_string _133_176 imp))
end
end
end
| (FStar_Util.Inr (x), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _133_177 = (FStar_Options.print_real_names ())
in (FStar_All.pipe_right _133_177 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp x.FStar_Absyn_Syntax.v))) then begin
(typ_to_string x.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_implicits ())))) then begin
(let _133_178 = (strBvd x.FStar_Absyn_Syntax.v)
in (imp_to_string _133_178 imp))
end else begin
(let _133_182 = (let _133_181 = (strBvd x.FStar_Absyn_Syntax.v)
in (let _133_180 = (let _133_179 = (typ_to_string x.FStar_Absyn_Syntax.sort)
in (Prims.strcat ":" _133_179))
in (Prims.strcat _133_181 _133_180)))
in (imp_to_string _133_182 imp))
end
end
end))
and binder_to_string : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Absyn_Syntax.binders  ->  Prims.string = (fun sep bs -> (

let bs = if (FStar_Options.print_implicits ()) then begin
bs
end else begin
(filter_imp bs)
end
in if (sep = " -> ") then begin
(let _133_187 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _133_187 (FStar_String.concat sep)))
end else begin
(let _133_188 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _133_188 (FStar_String.concat sep)))
end))
and arg_to_string : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _33_6 -> (match (_33_6) with
| (FStar_Util.Inl (a), imp) -> begin
(let _133_190 = (typ_to_string a)
in (imp_to_string _133_190 imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _133_191 = (exp_to_string x)
in (imp_to_string _133_191 imp))
end))
and args_to_string : FStar_Absyn_Syntax.args  ->  Prims.string = (fun args -> (

let args = if (FStar_Options.print_implicits ()) then begin
args
end else begin
(filter_imp args)
end
in (let _133_193 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _133_193 (FStar_String.concat " ")))))
and lcomp_typ_to_string : FStar_Absyn_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _133_196 = (sli lc.FStar_Absyn_Syntax.eff_name)
in (let _133_195 = (typ_to_string lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _133_196 _133_195))))
and comp_typ_to_string : FStar_Absyn_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _133_198 = (typ_to_string t)
in (FStar_Util.format1 "Tot %s" _133_198))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(

let basic = if ((FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _33_7 -> (match (_33_7) with
| FStar_Absyn_Syntax.TOTAL -> begin
true
end
| _33_388 -> begin
false
end)))) && (not ((FStar_Options.print_effect_args ())))) then begin
(let _133_200 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _133_200))
end else begin
if ((not ((FStar_Options.print_effect_args ()))) && (FStar_Ident.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid)) then begin
(typ_to_string c.FStar_Absyn_Syntax.result_typ)
end else begin
if ((not ((FStar_Options.print_effect_args ()))) && (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _33_8 -> (match (_33_8) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _33_392 -> begin
false
end))))) then begin
(let _133_202 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _133_202))
end else begin
if (FStar_Options.print_effect_args ()) then begin
(let _133_206 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _133_205 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (let _133_204 = (let _133_203 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.effect_args (FStar_List.map effect_arg_to_string))
in (FStar_All.pipe_right _133_203 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _133_206 _133_205 _133_204))))
end else begin
(let _133_208 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _133_207 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _133_208 _133_207)))
end
end
end
end
in (

let dec = (let _133_212 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.collect (fun _33_9 -> (match (_33_9) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _133_211 = (let _133_210 = (exp_to_string e)
in (FStar_Util.format1 " (decreases %s)" _133_210))
in (_133_211)::[])
end
| _33_398 -> begin
[]
end))))
in (FStar_All.pipe_right _133_212 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and effect_arg_to_string : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun e -> (match (e) with
| (FStar_Util.Inr (e), _33_404) -> begin
(exp_to_string e)
end
| (FStar_Util.Inl (wp), _33_409) -> begin
(formula_to_string wp)
end))
and formula_to_string : FStar_Absyn_Syntax.typ  ->  Prims.string = (fun phi -> (typ_to_string phi))
and formula_to_string_old_now_unused : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun phi -> (

let const_op = (fun f _33_415 -> f)
in (

let un_op = (fun f _33_10 -> (match (_33_10) with
| ((FStar_Util.Inl (t), _33_423))::[] -> begin
(let _133_224 = (formula_to_string t)
in (FStar_Util.format2 "%s %s" f _133_224))
end
| _33_427 -> begin
(failwith "impos")
end))
in (

let bin_top = (fun f _33_11 -> (match (_33_11) with
| ((FStar_Util.Inl (t1), _33_439))::((FStar_Util.Inl (t2), _33_434))::[] -> begin
(let _133_230 = (formula_to_string t1)
in (let _133_229 = (formula_to_string t2)
in (FStar_Util.format3 "%s %s %s" _133_230 f _133_229)))
end
| _33_443 -> begin
(failwith "Impos")
end))
in (

let bin_eop = (fun f _33_12 -> (match (_33_12) with
| ((FStar_Util.Inr (e1), _33_455))::((FStar_Util.Inr (e2), _33_450))::[] -> begin
(let _133_236 = (exp_to_string e1)
in (let _133_235 = (exp_to_string e2)
in (FStar_Util.format3 "%s %s %s" _133_236 f _133_235)))
end
| _33_459 -> begin
(failwith "impos")
end))
in (

let ite = (fun _33_13 -> (match (_33_13) with
| ((FStar_Util.Inl (t1), _33_474))::((FStar_Util.Inl (t2), _33_469))::((FStar_Util.Inl (t3), _33_464))::[] -> begin
(let _133_241 = (formula_to_string t1)
in (let _133_240 = (formula_to_string t2)
in (let _133_239 = (formula_to_string t3)
in (FStar_Util.format3 "if %s then %s else %s" _133_241 _133_240 _133_239))))
end
| _33_478 -> begin
(failwith "impos")
end))
in (

let eq_op = (fun _33_14 -> (match (_33_14) with
| ((FStar_Util.Inl (t1), _33_499))::((FStar_Util.Inl (t2), _33_494))::((FStar_Util.Inr (e1), _33_489))::((FStar_Util.Inr (e2), _33_484))::[] -> begin
if (FStar_Options.print_implicits ()) then begin
(let _133_247 = (typ_to_string t1)
in (let _133_246 = (typ_to_string t2)
in (let _133_245 = (exp_to_string e1)
in (let _133_244 = (exp_to_string e2)
in (FStar_Util.format4 "Eq2 %s %s %s %s" _133_247 _133_246 _133_245 _133_244)))))
end else begin
(let _133_249 = (exp_to_string e1)
in (let _133_248 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _133_249 _133_248)))
end
end
| ((FStar_Util.Inr (e1), _33_510))::((FStar_Util.Inr (e2), _33_505))::[] -> begin
(let _133_251 = (exp_to_string e1)
in (let _133_250 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _133_251 _133_250)))
end
| _33_514 -> begin
(failwith "Impossible")
end))
in (

let connectives = (((FStar_Absyn_Const.and_lid), ((bin_top "/\\"))))::(((FStar_Absyn_Const.or_lid), ((bin_top "\\/"))))::(((FStar_Absyn_Const.imp_lid), ((bin_top "==>"))))::(((FStar_Absyn_Const.iff_lid), ((bin_top "<==>"))))::(((FStar_Absyn_Const.ite_lid), (ite)))::(((FStar_Absyn_Const.not_lid), ((un_op "~"))))::(((FStar_Absyn_Const.eqT_lid), ((bin_top "=="))))::(((FStar_Absyn_Const.eq2_lid), (eq_op)))::(((FStar_Absyn_Const.true_lid), ((const_op "True"))))::(((FStar_Absyn_Const.false_lid), ((const_op "False"))))::[]
in (

let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (binders, phi) -> begin
(let _133_290 = (binders_to_string " " binders)
in (let _133_289 = (formula_to_string phi)
in (FStar_Util.format2 "(fun %s => %s)" _133_290 _133_289)))
end
| _33_524 -> begin
(typ_to_string phi)
end))
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _33_534 -> (match (_33_534) with
| (l, _33_533) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_33_537, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, _33_543, body)) -> begin
(let _133_308 = (binders_to_string " " vars)
in (let _133_307 = (formula_to_string body)
in (FStar_Util.format2 "(forall %s. %s)" _133_308 _133_307)))
end
| Some (FStar_Absyn_Util.QEx (vars, _33_550, body)) -> begin
(let _133_310 = (binders_to_string " " vars)
in (let _133_309 = (formula_to_string body)
in (FStar_Util.format2 "(exists %s. %s)" _133_310 _133_309)))
end))))))))))
and exp_to_string : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun x -> (match ((let _133_312 = (FStar_Absyn_Util.compress_exp x)
in _133_312.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_delayed (_33_557) -> begin
(failwith "Impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _33_561)) -> begin
(exp_to_string e)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(uvar_e_to_string ((uv), (t)))
end
| FStar_Absyn_Syntax.Exp_bvar (bvv) -> begin
(strBvd bvv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_fvar (fv, _33_573) -> begin
(sli fv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(FStar_All.pipe_right c const_to_string)
end
| FStar_Absyn_Syntax.Exp_abs (binders, e) -> begin
(let _133_314 = (binders_to_string " " binders)
in (let _133_313 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _133_314 _133_313)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(

let lex = if (FStar_Options.print_implicits ()) then begin
None
end else begin
(reconstruct_lex x)
end
in (match (lex) with
| Some (es) -> begin
(let _133_317 = (let _133_316 = (let _133_315 = (FStar_List.map exp_to_string es)
in (FStar_String.concat "; " _133_315))
in (Prims.strcat _133_316 "]"))
in (Prims.strcat "%[" _133_317))
end
| None -> begin
(

let args' = (let _133_319 = (filter_imp args)
in (FStar_All.pipe_right _133_319 (FStar_List.filter (fun _33_15 -> (match (_33_15) with
| (FStar_Util.Inr (_33_592), _33_595) -> begin
true
end
| _33_598 -> begin
false
end)))))
in if ((is_infix_prim_op e) && ((FStar_List.length args') = (Prims.parse_int "2"))) then begin
(let _133_324 = (let _133_320 = (FStar_List.nth args' (Prims.parse_int "0"))
in (FStar_All.pipe_right _133_320 arg_to_string))
in (let _133_323 = (FStar_All.pipe_right e infix_prim_op_to_string)
in (let _133_322 = (let _133_321 = (FStar_List.nth args' (Prims.parse_int "1"))
in (FStar_All.pipe_right _133_321 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _133_324 _133_323 _133_322))))
end else begin
if ((is_unary_prim_op e) && ((FStar_List.length args') = (Prims.parse_int "1"))) then begin
(let _133_327 = (FStar_All.pipe_right e unary_prim_op_to_string)
in (let _133_326 = (let _133_325 = (FStar_List.nth args' (Prims.parse_int "0"))
in (FStar_All.pipe_right _133_325 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _133_327 _133_326)))
end else begin
(let _133_329 = (FStar_All.pipe_right e exp_to_string)
in (let _133_328 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _133_329 _133_328)))
end
end)
end))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _133_337 = (FStar_All.pipe_right e exp_to_string)
in (let _133_336 = (let _133_335 = (FStar_All.pipe_right pats (FStar_List.map (fun _33_607 -> (match (_33_607) with
| (p, wopt, e) -> begin
(let _133_334 = (FStar_All.pipe_right p pat_to_string)
in (let _133_333 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _133_331 = (FStar_All.pipe_right w exp_to_string)
in (FStar_Util.format1 "when %s" _133_331))
end)
in (let _133_332 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format3 "%s %s -> %s" _133_334 _133_333 _133_332))))
end))))
in (FStar_Util.concat_l "\n\t" _133_335))
in (FStar_Util.format2 "(match %s with %s)" _133_337 _133_336)))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _33_614) -> begin
(let _133_339 = (FStar_All.pipe_right e exp_to_string)
in (let _133_338 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "(%s:%s)" _133_339 _133_338)))
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(let _133_341 = (lbs_to_string lbs)
in (let _133_340 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "%s in %s" _133_341 _133_340)))
end))
and uvar_e_to_string : (FStar_Absyn_Syntax.uvar_e * FStar_Absyn_Syntax.typ)  ->  Prims.string = (fun _33_624 -> (match (_33_624) with
| (uv, _33_623) -> begin
(let _133_344 = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _133_343 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _133_343))
end
in (Prims.strcat "\'e" _133_344))
end))
and lbs_to_string : FStar_Absyn_Syntax.letbindings  ->  Prims.string = (fun lbs -> (let _133_351 = (let _133_350 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _133_349 = (lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _133_348 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbtyp typ_to_string)
in (let _133_347 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbdef exp_to_string)
in (FStar_Util.format3 "%s:%s = %s" _133_349 _133_348 _133_347)))))))
in (FStar_Util.concat_l "\n and " _133_350))
in (FStar_Util.format2 "let %s %s" (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _133_351)))
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
and either_l_to_string : Prims.string  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either Prims.list  ->  Prims.string = (fun delim l -> (let _133_356 = (FStar_All.pipe_right l (FStar_List.map either_to_string))
in (FStar_All.pipe_right _133_356 (FStar_Util.concat_l delim))))
and meta_to_string : FStar_Absyn_Syntax.meta_t  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Meta_refresh_label (t, _33_642, _33_644) -> begin
(let _133_358 = (typ_to_string t)
in (FStar_Util.format1 "(refresh) %s" _133_358))
end
| FStar_Absyn_Syntax.Meta_labeled (t, l, _33_650, _33_652) -> begin
(let _133_359 = (typ_to_string t)
in (FStar_Util.format2 "(labeled \"%s\") %s" l _133_359))
end
| FStar_Absyn_Syntax.Meta_named (_33_656, l) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Meta_pattern (t, ps) -> begin
(let _133_361 = (pats_to_string ps)
in (let _133_360 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "{:pattern %s} %s" _133_361 _133_360)))
end
| FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _33_667) -> begin
(let _133_363 = (formula_to_string t1)
in (let _133_362 = (formula_to_string t2)
in (FStar_Util.format2 "%s /\\ %s" _133_363 _133_362)))
end))
and pats_to_string : FStar_Absyn_Syntax.arg Prims.list Prims.list  ->  Prims.string = (fun ps -> (let _133_367 = (FStar_All.pipe_right ps (FStar_List.map (fun e -> (let _133_366 = (FStar_All.pipe_right e (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _133_366 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _133_367 (FStar_String.concat " \\/ "))))
and kind_to_string : FStar_Absyn_Syntax.knd  ->  Prims.string = (fun x -> (match ((let _133_369 = (FStar_Absyn_Util.compress_kind x)
in _133_369.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_lam (_33_674) -> begin
(failwith "Impossible")
end
| FStar_Absyn_Syntax.Kind_delayed (_33_677) -> begin
(failwith "Impossible")
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(uvar_k_to_string' ((uv), (args)))
end
| FStar_Absyn_Syntax.Kind_type -> begin
"Type"
end
| FStar_Absyn_Syntax.Kind_effect -> begin
"Effect"
end
| FStar_Absyn_Syntax.Kind_abbrev ((n, args), k) -> begin
if (FStar_Options.print_real_names ()) then begin
(kind_to_string k)
end else begin
(let _133_371 = (sli n)
in (let _133_370 = (args_to_string args)
in (FStar_Util.format2 "%s %s" _133_371 _133_370)))
end
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(let _133_373 = (binders_to_string " -> " binders)
in (let _133_372 = (FStar_All.pipe_right k kind_to_string)
in (FStar_Util.format2 "(%s -> %s)" _133_373 _133_372)))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun uv -> (let _133_375 = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _133_374 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _133_374))
end
in (Prims.strcat "\'k_" _133_375)))
and uvar_k_to_string' : ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list)  ->  Prims.string = (fun _33_699 -> (match (_33_699) with
| (uv, args) -> begin
(

let str = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _133_377 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _133_377))
end
in (let _133_378 = (args_to_string args)
in (FStar_Util.format2 "(\'k_%s %s)" str _133_378)))
end))
and pat_to_string : FStar_Absyn_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (l, _33_704, pats) -> begin
(let _133_383 = (sli l.FStar_Absyn_Syntax.v)
in (let _133_382 = (let _133_381 = (FStar_List.map (fun _33_710 -> (match (_33_710) with
| (x, b) -> begin
(

let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _133_381 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _133_383 _133_382)))
end
| FStar_Absyn_Syntax.Pat_dot_term (x, _33_714) -> begin
(let _133_384 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".%s" _133_384))
end
| FStar_Absyn_Syntax.Pat_dot_typ (x, _33_719) -> begin
(let _133_385 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".\'%s" _133_385))
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
| FStar_Absyn_Syntax.Pat_wild (_33_729) -> begin
"_"
end
| FStar_Absyn_Syntax.Pat_twild (_33_732) -> begin
"\'_"
end
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(let _133_386 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _133_386))
end))


let subst_to_string = (fun subst -> (let _133_394 = (let _133_393 = (FStar_List.map (fun _33_16 -> (match (_33_16) with
| FStar_Util.Inl (a, t) -> begin
(let _133_390 = (strBvd a)
in (let _133_389 = (typ_to_string t)
in (FStar_Util.format2 "(%s -> %s)" _133_390 _133_389)))
end
| FStar_Util.Inr (x, e) -> begin
(let _133_392 = (strBvd x)
in (let _133_391 = (exp_to_string e)
in (FStar_Util.format2 "(%s -> %s)" _133_392 _133_391)))
end)) subst)
in (FStar_All.pipe_right _133_393 (FStar_String.concat ", ")))
in (FStar_All.pipe_left (FStar_Util.format1 "{%s}") _133_394)))


let freevars_to_string : FStar_Absyn_Syntax.freevars  ->  Prims.string = (fun fvs -> (

let f = (fun l -> (let _133_400 = (let _133_399 = (FStar_All.pipe_right l FStar_Util.set_elements)
in (FStar_All.pipe_right _133_399 (FStar_List.map (fun t -> (strBvd t.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _133_400 (FStar_String.concat ", "))))
in (let _133_402 = (f fvs.FStar_Absyn_Syntax.ftvs)
in (let _133_401 = (f fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_Util.format2 "ftvs={%s}, fxvs={%s}" _133_402 _133_401)))))


let qual_to_string : FStar_Absyn_Syntax.qualifier  ->  Prims.string = (fun _33_17 -> (match (_33_17) with
| FStar_Absyn_Syntax.Logic -> begin
"logic"
end
| FStar_Absyn_Syntax.Opaque -> begin
"opaque"
end
| FStar_Absyn_Syntax.Discriminator (_33_756) -> begin
"discriminator"
end
| FStar_Absyn_Syntax.Projector (_33_759) -> begin
"projector"
end
| FStar_Absyn_Syntax.RecordType (ids) -> begin
(let _133_407 = (let _133_406 = (FStar_All.pipe_right ids (FStar_List.map (fun lid -> lid.FStar_Ident.ident.FStar_Ident.idText)))
in (FStar_All.pipe_right _133_406 (FStar_String.concat ", ")))
in (FStar_Util.format1 "record(%s)" _133_407))
end
| _33_765 -> begin
"other"
end))


let quals_to_string : FStar_Absyn_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (let _133_410 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _133_410 (FStar_String.concat " "))))


let rec sigelt_to_string : FStar_Absyn_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.ResetOptions (None), _33_771) -> begin
"#reset-options"
end
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.ResetOptions (Some (s)), _33_778) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.SetOptions (s), _33_784) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _33_791, _33_793, quals, _33_796) -> begin
(let _133_415 = (quals_to_string quals)
in (let _133_414 = (binders_to_string " " tps)
in (let _133_413 = (kind_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _133_415 lid.FStar_Ident.str _133_414 _133_413))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, _33_804, _33_806) -> begin
(let _133_418 = (binders_to_string " " tps)
in (let _133_417 = (kind_to_string k)
in (let _133_416 = (typ_to_string t)
in (FStar_Util.format4 "type %s %s : %s = %s" lid.FStar_Ident.str _133_418 _133_417 _133_416))))
end
| FStar_Absyn_Syntax.Sig_datacon (lid, t, _33_812, _33_814, _33_816, _33_818) -> begin
(let _133_419 = (typ_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _133_419))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _33_825) -> begin
(let _133_421 = (quals_to_string quals)
in (let _133_420 = (typ_to_string t)
in (FStar_Util.format3 "%s val %s : %s" _133_421 lid.FStar_Ident.str _133_420)))
end
| FStar_Absyn_Syntax.Sig_assume (lid, f, _33_831, _33_833) -> begin
(let _133_422 = (typ_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _133_422))
end
| FStar_Absyn_Syntax.Sig_let (lbs, _33_838, _33_840, b) -> begin
(lbs_to_string lbs)
end
| FStar_Absyn_Syntax.Sig_main (e, _33_846) -> begin
(let _133_423 = (exp_to_string e)
in (FStar_Util.format1 "let _ = %s" _133_423))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _33_851, _33_853, _33_855) -> begin
(let _133_424 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _133_424 (FStar_String.concat "\n")))
end
| FStar_Absyn_Syntax.Sig_new_effect (_33_859) -> begin
"new_effect { ... }"
end
| FStar_Absyn_Syntax.Sig_sub_effect (_33_862) -> begin
"sub_effect ..."
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_33_865) -> begin
"kind ..."
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, tps, c, _33_871, _33_873) -> begin
(let _133_427 = (sli l)
in (let _133_426 = (binders_to_string " " tps)
in (let _133_425 = (comp_typ_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _133_427 _133_426 _133_425))))
end))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _133_432 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _133_432 msg)))


let rec sigelt_to_string_short : FStar_Absyn_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_let ((_33_880, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _33_884; FStar_Absyn_Syntax.lbdef = _33_882})::[]), _33_892, _33_894, _33_896) -> begin
(let _133_435 = (typ_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Ident.str _133_435))
end
| _33_900 -> begin
(let _133_438 = (let _133_437 = (FStar_Absyn_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _133_437 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _133_438 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Absyn_Syntax.modul  ->  Prims.string = (fun m -> (let _133_443 = (sli m.FStar_Absyn_Syntax.name)
in (let _133_442 = (let _133_441 = (FStar_List.map sigelt_to_string m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _133_441 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _133_443 _133_442))))




