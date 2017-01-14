
open Prims

let infix_prim_ops : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = (((FStar_Absyn_Const.op_Addition), ("+")))::(((FStar_Absyn_Const.op_Subtraction), ("-")))::(((FStar_Absyn_Const.op_Multiply), ("*")))::(((FStar_Absyn_Const.op_Division), ("/")))::(((FStar_Absyn_Const.op_Eq), ("=")))::(((FStar_Absyn_Const.op_ColonEq), (":=")))::(((FStar_Absyn_Const.op_notEq), ("<>")))::(((FStar_Absyn_Const.op_And), ("&&")))::(((FStar_Absyn_Const.op_Or), ("||")))::(((FStar_Absyn_Const.op_LTE), ("<=")))::(((FStar_Absyn_Const.op_GTE), (">=")))::(((FStar_Absyn_Const.op_LT), ("<")))::(((FStar_Absyn_Const.op_GT), (">")))::(((FStar_Absyn_Const.op_Modulus), ("mod")))::[]


let unary_prim_ops : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = (((FStar_Absyn_Const.op_Negation), ("not")))::(((FStar_Absyn_Const.op_Minus), ("-")))::[]


let infix_type_ops : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = (((FStar_Absyn_Const.and_lid), ("/\\")))::(((FStar_Absyn_Const.or_lid), ("\\/")))::(((FStar_Absyn_Const.imp_lid), ("==>")))::(((FStar_Absyn_Const.iff_lid), ("<==>")))::(((FStar_Absyn_Const.precedes_lid), ("<<")))::(((FStar_Absyn_Const.eq2_lid), ("==")))::(((FStar_Absyn_Const.eqT_lid), ("==")))::[]


let unary_type_ops : (FStar_Absyn_Syntax.lident * Prims.string) Prims.list = (((FStar_Absyn_Const.not_lid), ("~")))::[]


let is_prim_op = (fun ps f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _34_5) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _34_9 -> begin
false
end))


let is_type_op = (fun ps t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals ftv.FStar_Absyn_Syntax.v)))
end
| _34_15 -> begin
false
end))


let get_lid = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _34_19) -> begin
fv.FStar_Absyn_Syntax.v
end
| _34_23 -> begin
(failwith "get_lid")
end))


let get_type_lid = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
ftv.FStar_Absyn_Syntax.v
end
| _34_28 -> begin
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


let is_inr = (fun uu___41 -> (match (uu___41) with
| FStar_Util.Inl (_34_40) -> begin
false
end
| FStar_Util.Inr (_34_43) -> begin
true
end))


let rec reconstruct_lex : FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _135_28 = (FStar_Absyn_Util.compress_exp e)
in _135_28.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (f, args) -> begin
(

let args = (FStar_List.filter (fun a -> (match (a) with
| ((FStar_Util.Inl (_), _)) | ((FStar_Util.Inr (_), Some (FStar_Absyn_Syntax.Implicit (_)))) -> begin
false
end
| _34_66 -> begin
true
end)) args)
in (

let exps = (FStar_List.map (fun uu___42 -> (match (uu___42) with
| (FStar_Util.Inl (_34_70), _34_73) -> begin
(failwith "impossible")
end
| (FStar_Util.Inr (x), _34_78) -> begin
x
end)) args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = (Prims.parse_int "2"))) then begin
(match ((let _135_31 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex _135_31))) with
| Some (xs) -> begin
(let _135_33 = (let _135_32 = (FStar_List.nth exps (Prims.parse_int "0"))
in (_135_32)::xs)
in Some (_135_33))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _34_85 -> begin
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


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _135_47 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _135_47)))


let infix_prim_op_to_string = (fun e -> (let _135_49 = (get_lid e)
in (find_lid _135_49 infix_prim_ops)))


let unary_prim_op_to_string = (fun e -> (let _135_51 = (get_lid e)
in (find_lid _135_51 unary_prim_ops)))


let infix_type_op_to_string = (fun t -> (let _135_53 = (get_type_lid t)
in (find_lid _135_53 infix_type_ops)))


let unary_type_op_to_string = (fun t -> (let _135_55 = (get_type_lid t)
in (find_lid _135_55 unary_type_ops)))


let quant_to_string = (fun t -> (let _135_57 = (get_type_lid t)
in (find_lid _135_57 quants)))


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

let _34_108 = (let _135_62 = (FStar_Util.substring_from bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText (Prims.parse_int "1"))
in (FStar_Util.int_of_string _135_62))
in "_?")
end)
with
| _34_105 -> begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end
end else begin
bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end
end)


let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___43 -> (match (uu___43) with
| (_34_113, Some (FStar_Absyn_Syntax.Implicit (_34_115))) -> begin
false
end
| _34_120 -> begin
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
| FStar_Const.Const_string (bytes, _34_132) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_34_136) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x, _34_140) -> begin
x
end
| FStar_Const.Const_range (r) -> begin
(FStar_Range.string_of_range r)
end
| (FStar_Const.Const_reify) | (FStar_Const.Const_reflect (_)) -> begin
"unsupported constant"
end))


let rec tag_of_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_34_151) -> begin
"Typ_btvar"
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(Prims.strcat "Typ_const " v.FStar_Absyn_Syntax.v.FStar_Ident.str)
end
| FStar_Absyn_Syntax.Typ_fun (_34_156) -> begin
"Typ_fun"
end
| FStar_Absyn_Syntax.Typ_refine (_34_159) -> begin
"Typ_refine"
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let _135_103 = (tag_of_typ head)
in (let _135_102 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.format2 "Typ_app(%s, [%s args])" _135_103 _135_102)))
end
| FStar_Absyn_Syntax.Typ_lam (_34_166) -> begin
"Typ_lam"
end
| FStar_Absyn_Syntax.Typ_ascribed (_34_169) -> begin
"Typ_ascribed"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_34_172)) -> begin
"Typ_meta_pattern"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_34_176)) -> begin
"Typ_meta_named"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_34_180)) -> begin
"Typ_meta_labeled"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_34_184)) -> begin
"Typ_meta_refresh_label"
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_34_188)) -> begin
"Typ_meta_slack_formula"
end
| FStar_Absyn_Syntax.Typ_uvar (_34_192) -> begin
"Typ_uvar"
end
| FStar_Absyn_Syntax.Typ_delayed (_34_195) -> begin
"Typ_delayed"
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"Typ_unknown"
end))
and tag_of_exp = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_34_200) -> begin
"Exp_bvar"
end
| FStar_Absyn_Syntax.Exp_fvar (_34_203) -> begin
"Exp_fvar"
end
| FStar_Absyn_Syntax.Exp_constant (_34_206) -> begin
"Exp_constant"
end
| FStar_Absyn_Syntax.Exp_abs (_34_209) -> begin
"Exp_abs"
end
| FStar_Absyn_Syntax.Exp_app (_34_212) -> begin
"Exp_app"
end
| FStar_Absyn_Syntax.Exp_match (_34_215) -> begin
"Exp_match"
end
| FStar_Absyn_Syntax.Exp_ascribed (_34_218) -> begin
"Exp_ascribed"
end
| FStar_Absyn_Syntax.Exp_let (_34_221) -> begin
"Exp_let"
end
| FStar_Absyn_Syntax.Exp_uvar (_34_224) -> begin
"Exp_uvar"
end
| FStar_Absyn_Syntax.Exp_delayed (_34_227) -> begin
"Exp_delayed"
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_34_230, m)) -> begin
(let _135_107 = (meta_e_to_string m)
in (Prims.strcat "Exp_meta_desugared " _135_107))
end))
and meta_e_to_string : FStar_Absyn_Syntax.meta_source_info  ->  Prims.string = (fun uu___44 -> (match (uu___44) with
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
| FStar_Absyn_Syntax.Typ_delayed (_34_244) -> begin
(failwith "impossible")
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_34_247, l)) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Typ_meta (meta) -> begin
(let _135_113 = (FStar_All.pipe_right meta meta_to_string)
in (FStar_Util.format1 "(Meta %s)" _135_113))
end
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(strBvd btv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(sli v.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Typ_fun (binders, c) -> begin
(let _135_115 = (binders_to_string " -> " binders)
in (let _135_114 = (comp_typ_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _135_115 _135_114)))
end
| FStar_Absyn_Syntax.Typ_refine (xt, f) -> begin
(let _135_118 = (strBvd xt.FStar_Absyn_Syntax.v)
in (let _135_117 = (FStar_All.pipe_right xt.FStar_Absyn_Syntax.sort typ_to_string)
in (let _135_116 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "%s:%s{%s}" _135_118 _135_117 _135_116))))
end
| FStar_Absyn_Syntax.Typ_app (_34_267, []) -> begin
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
| _34_287 -> begin
(let _135_129 = (tag_of_typ t)
in (let _135_128 = (typ_to_string t)
in (FStar_Util.format2 "<Expected a type-lambda! got %s>%s" _135_129 _135_128)))
end))
end
| FStar_Util.Inr (e) -> begin
(let _135_130 = (exp_to_string e)
in (FStar_Util.format1 "(<Expected a type!>%s)" _135_130))
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
(let _135_140 = (let _135_135 = (FStar_List.nth args (Prims.parse_int "0"))
in (arg_to_string _135_135))
in (let _135_139 = (let _135_136 = (FStar_List.nth args (Prims.parse_int "1"))
in (arg_to_string _135_136))
in (let _135_138 = (let _135_137 = (FStar_List.nth args (Prims.parse_int "2"))
in (arg_to_string _135_137))
in (FStar_Util.format3 "if %s then %s else %s" _135_140 _135_139 _135_138))))
end else begin
if ((is_b2t t) && ((FStar_List.length args) = (Prims.parse_int "1"))) then begin
(let _135_141 = (FStar_List.nth args (Prims.parse_int "0"))
in (FStar_All.pipe_right _135_141 arg_to_string))
end else begin
if ((is_quant t) && ((FStar_List.length args) <= (Prims.parse_int "2"))) then begin
(let _135_146 = (quant_to_string t)
in (let _135_145 = (let _135_142 = (FStar_List.nth args' (Prims.parse_int "0"))
in (qbinder_to_string _135_142))
in (let _135_144 = (let _135_143 = (FStar_List.nth args' (Prims.parse_int "0"))
in (qbody_to_string _135_143))
in (FStar_Util.format3 "(%s (%s). %s)" _135_146 _135_145 _135_144))))
end else begin
if ((is_infix_type_op t) && ((FStar_List.length args') = (Prims.parse_int "2"))) then begin
(let _135_151 = (let _135_147 = (FStar_List.nth args' (Prims.parse_int "0"))
in (FStar_All.pipe_right _135_147 arg_to_string))
in (let _135_150 = (FStar_All.pipe_right t infix_type_op_to_string)
in (let _135_149 = (let _135_148 = (FStar_List.nth args' (Prims.parse_int "1"))
in (FStar_All.pipe_right _135_148 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _135_151 _135_150 _135_149))))
end else begin
if ((is_unary_type_op t) && ((FStar_List.length args') = (Prims.parse_int "1"))) then begin
(let _135_154 = (FStar_All.pipe_right t unary_type_op_to_string)
in (let _135_153 = (let _135_152 = (FStar_List.nth args' (Prims.parse_int "0"))
in (FStar_All.pipe_right _135_152 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _135_154 _135_153)))
end else begin
(let _135_156 = (FStar_All.pipe_right t typ_to_string)
in (let _135_155 = (FStar_All.pipe_right args args_to_string)
in (FStar_Util.format2 "(%s %s)" _135_156 _135_155)))
end
end
end
end
end))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(let _135_158 = (binders_to_string " " binders)
in (let _135_157 = (FStar_All.pipe_right t2 typ_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _135_158 _135_157)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
if (FStar_Options.print_real_names ()) then begin
(let _135_160 = (typ_to_string t)
in (let _135_159 = (kind_to_string k)
in (FStar_Util.format2 "(%s <: %s)" _135_160 _135_159)))
end else begin
(FStar_All.pipe_right t typ_to_string)
end
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
"<UNKNOWN>"
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(match ((FStar_Absyn_Visit.compress_typ_aux false x)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_34_317); FStar_Absyn_Syntax.tk = _34_315; FStar_Absyn_Syntax.pos = _34_313; FStar_Absyn_Syntax.fvs = _34_311; FStar_Absyn_Syntax.uvs = _34_309} -> begin
(uvar_t_to_string ((uv), (k)))
end
| t -> begin
(FStar_All.pipe_right t typ_to_string)
end)
end)))
and uvar_t_to_string : (FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd)  ->  Prims.string = (fun _34_323 -> (match (_34_323) with
| (uv, k) -> begin
if (false && (FStar_Options.print_real_names ())) then begin
(let _135_164 = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _135_162 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _135_162))
end
in (let _135_163 = (kind_to_string k)
in (FStar_Util.format2 "(U%s : %s)" _135_164 _135_163)))
end else begin
(let _135_166 = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _135_165 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _135_165))
end
in (FStar_Util.format1 "U%s" _135_166))
end
end))
and imp_to_string : Prims.string  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s uu___45 -> (match (uu___45) with
| Some (FStar_Absyn_Syntax.Implicit (_34_327)) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Absyn_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _34_333 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (match (b) with
| (FStar_Util.Inl (a), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _135_171 = (FStar_Options.print_real_names ())
in (FStar_All.pipe_right _135_171 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp a.FStar_Absyn_Syntax.v))) then begin
(kind_to_string a.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_implicits ())))) then begin
(let _135_172 = (strBvd a.FStar_Absyn_Syntax.v)
in (imp_to_string _135_172 imp))
end else begin
(let _135_176 = (let _135_175 = (strBvd a.FStar_Absyn_Syntax.v)
in (let _135_174 = (let _135_173 = (kind_to_string a.FStar_Absyn_Syntax.sort)
in (Prims.strcat ":" _135_173))
in (Prims.strcat _135_175 _135_174)))
in (imp_to_string _135_176 imp))
end
end
end
| (FStar_Util.Inr (x), imp) -> begin
if ((FStar_Absyn_Syntax.is_null_binder b) || ((let _135_177 = (FStar_Options.print_real_names ())
in (FStar_All.pipe_right _135_177 Prims.op_Negation)) && (FStar_Absyn_Syntax.is_null_pp x.FStar_Absyn_Syntax.v))) then begin
(typ_to_string x.FStar_Absyn_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_implicits ())))) then begin
(let _135_178 = (strBvd x.FStar_Absyn_Syntax.v)
in (imp_to_string _135_178 imp))
end else begin
(let _135_182 = (let _135_181 = (strBvd x.FStar_Absyn_Syntax.v)
in (let _135_180 = (let _135_179 = (typ_to_string x.FStar_Absyn_Syntax.sort)
in (Prims.strcat ":" _135_179))
in (Prims.strcat _135_181 _135_180)))
in (imp_to_string _135_182 imp))
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
(let _135_187 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _135_187 (FStar_String.concat sep)))
end else begin
(let _135_188 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _135_188 (FStar_String.concat sep)))
end))
and arg_to_string : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun uu___46 -> (match (uu___46) with
| (FStar_Util.Inl (a), imp) -> begin
(let _135_190 = (typ_to_string a)
in (imp_to_string _135_190 imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _135_191 = (exp_to_string x)
in (imp_to_string _135_191 imp))
end))
and args_to_string : FStar_Absyn_Syntax.args  ->  Prims.string = (fun args -> (

let args = if (FStar_Options.print_implicits ()) then begin
args
end else begin
(filter_imp args)
end
in (let _135_193 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _135_193 (FStar_String.concat " ")))))
and lcomp_typ_to_string : FStar_Absyn_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _135_196 = (sli lc.FStar_Absyn_Syntax.eff_name)
in (let _135_195 = (typ_to_string lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _135_196 _135_195))))
and comp_typ_to_string : FStar_Absyn_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _135_198 = (typ_to_string t)
in (FStar_Util.format1 "Tot %s" _135_198))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(

let basic = if ((FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun uu___47 -> (match (uu___47) with
| FStar_Absyn_Syntax.TOTAL -> begin
true
end
| _34_369 -> begin
false
end)))) && (not ((FStar_Options.print_effect_args ())))) then begin
(let _135_200 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _135_200))
end else begin
if ((not ((FStar_Options.print_effect_args ()))) && (FStar_Ident.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid)) then begin
(typ_to_string c.FStar_Absyn_Syntax.result_typ)
end else begin
if ((not ((FStar_Options.print_effect_args ()))) && (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun uu___48 -> (match (uu___48) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _34_373 -> begin
false
end))))) then begin
(let _135_202 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _135_202))
end else begin
if (FStar_Options.print_effect_args ()) then begin
(let _135_206 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _135_205 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (let _135_204 = (let _135_203 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.effect_args (FStar_List.map effect_arg_to_string))
in (FStar_All.pipe_right _135_203 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _135_206 _135_205 _135_204))))
end else begin
(let _135_208 = (sli c.FStar_Absyn_Syntax.effect_name)
in (let _135_207 = (typ_to_string c.FStar_Absyn_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _135_208 _135_207)))
end
end
end
end
in (

let dec = (let _135_212 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.collect (fun uu___49 -> (match (uu___49) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _135_211 = (let _135_210 = (exp_to_string e)
in (FStar_Util.format1 " (decreases %s)" _135_210))
in (_135_211)::[])
end
| _34_379 -> begin
[]
end))))
in (FStar_All.pipe_right _135_212 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and effect_arg_to_string : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun e -> (match (e) with
| (FStar_Util.Inr (e), _34_385) -> begin
(exp_to_string e)
end
| (FStar_Util.Inl (wp), _34_390) -> begin
(formula_to_string wp)
end))
and formula_to_string : FStar_Absyn_Syntax.typ  ->  Prims.string = (fun phi -> (typ_to_string phi))
and formula_to_string_old_now_unused : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun phi -> (

let const_op = (fun f _34_396 -> f)
in (

let un_op = (fun f uu___50 -> (match (uu___50) with
| ((FStar_Util.Inl (t), _34_404))::[] -> begin
(let _135_224 = (formula_to_string t)
in (FStar_Util.format2 "%s %s" f _135_224))
end
| _34_408 -> begin
(failwith "impos")
end))
in (

let bin_top = (fun f uu___51 -> (match (uu___51) with
| ((FStar_Util.Inl (t1), _34_420))::((FStar_Util.Inl (t2), _34_415))::[] -> begin
(let _135_230 = (formula_to_string t1)
in (let _135_229 = (formula_to_string t2)
in (FStar_Util.format3 "%s %s %s" _135_230 f _135_229)))
end
| _34_424 -> begin
(failwith "Impos")
end))
in (

let bin_eop = (fun f uu___52 -> (match (uu___52) with
| ((FStar_Util.Inr (e1), _34_436))::((FStar_Util.Inr (e2), _34_431))::[] -> begin
(let _135_236 = (exp_to_string e1)
in (let _135_235 = (exp_to_string e2)
in (FStar_Util.format3 "%s %s %s" _135_236 f _135_235)))
end
| _34_440 -> begin
(failwith "impos")
end))
in (

let ite = (fun uu___53 -> (match (uu___53) with
| ((FStar_Util.Inl (t1), _34_455))::((FStar_Util.Inl (t2), _34_450))::((FStar_Util.Inl (t3), _34_445))::[] -> begin
(let _135_241 = (formula_to_string t1)
in (let _135_240 = (formula_to_string t2)
in (let _135_239 = (formula_to_string t3)
in (FStar_Util.format3 "if %s then %s else %s" _135_241 _135_240 _135_239))))
end
| _34_459 -> begin
(failwith "impos")
end))
in (

let eq_op = (fun uu___54 -> (match (uu___54) with
| ((FStar_Util.Inl (t1), _34_480))::((FStar_Util.Inl (t2), _34_475))::((FStar_Util.Inr (e1), _34_470))::((FStar_Util.Inr (e2), _34_465))::[] -> begin
if (FStar_Options.print_implicits ()) then begin
(let _135_247 = (typ_to_string t1)
in (let _135_246 = (typ_to_string t2)
in (let _135_245 = (exp_to_string e1)
in (let _135_244 = (exp_to_string e2)
in (FStar_Util.format4 "Eq2 %s %s %s %s" _135_247 _135_246 _135_245 _135_244)))))
end else begin
(let _135_249 = (exp_to_string e1)
in (let _135_248 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _135_249 _135_248)))
end
end
| ((FStar_Util.Inr (e1), _34_491))::((FStar_Util.Inr (e2), _34_486))::[] -> begin
(let _135_251 = (exp_to_string e1)
in (let _135_250 = (exp_to_string e2)
in (FStar_Util.format2 "%s == %s" _135_251 _135_250)))
end
| _34_495 -> begin
(failwith "Impossible")
end))
in (

let connectives = (((FStar_Absyn_Const.and_lid), ((bin_top "/\\"))))::(((FStar_Absyn_Const.or_lid), ((bin_top "\\/"))))::(((FStar_Absyn_Const.imp_lid), ((bin_top "==>"))))::(((FStar_Absyn_Const.iff_lid), ((bin_top "<==>"))))::(((FStar_Absyn_Const.ite_lid), (ite)))::(((FStar_Absyn_Const.not_lid), ((un_op "~"))))::(((FStar_Absyn_Const.eqT_lid), ((bin_top "=="))))::(((FStar_Absyn_Const.eq2_lid), (eq_op)))::(((FStar_Absyn_Const.true_lid), ((const_op "True"))))::(((FStar_Absyn_Const.false_lid), ((const_op "False"))))::[]
in (

let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (binders, phi) -> begin
(let _135_290 = (binders_to_string " " binders)
in (let _135_289 = (formula_to_string phi)
in (FStar_Util.format2 "(fun %s => %s)" _135_290 _135_289)))
end
| _34_505 -> begin
(typ_to_string phi)
end))
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _34_515 -> (match (_34_515) with
| (l, _34_514) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_34_518, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, _34_524, body)) -> begin
(let _135_308 = (binders_to_string " " vars)
in (let _135_307 = (formula_to_string body)
in (FStar_Util.format2 "(forall %s. %s)" _135_308 _135_307)))
end
| Some (FStar_Absyn_Util.QEx (vars, _34_531, body)) -> begin
(let _135_310 = (binders_to_string " " vars)
in (let _135_309 = (formula_to_string body)
in (FStar_Util.format2 "(exists %s. %s)" _135_310 _135_309)))
end))))))))))
and exp_to_string : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun x -> (match ((let _135_312 = (FStar_Absyn_Util.compress_exp x)
in _135_312.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_delayed (_34_538) -> begin
(failwith "Impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _34_542)) -> begin
(exp_to_string e)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(uvar_e_to_string ((uv), (t)))
end
| FStar_Absyn_Syntax.Exp_bvar (bvv) -> begin
(strBvd bvv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_fvar (fv, _34_554) -> begin
(sli fv.FStar_Absyn_Syntax.v)
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(FStar_All.pipe_right c const_to_string)
end
| FStar_Absyn_Syntax.Exp_abs (binders, e) -> begin
(let _135_314 = (binders_to_string " " binders)
in (let _135_313 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _135_314 _135_313)))
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
(let _135_317 = (let _135_316 = (let _135_315 = (FStar_List.map exp_to_string es)
in (FStar_String.concat "; " _135_315))
in (Prims.strcat _135_316 "]"))
in (Prims.strcat "%[" _135_317))
end
| None -> begin
(

let args' = (let _135_319 = (filter_imp args)
in (FStar_All.pipe_right _135_319 (FStar_List.filter (fun uu___55 -> (match (uu___55) with
| (FStar_Util.Inr (_34_573), _34_576) -> begin
true
end
| _34_579 -> begin
false
end)))))
in if ((is_infix_prim_op e) && ((FStar_List.length args') = (Prims.parse_int "2"))) then begin
(let _135_324 = (let _135_320 = (FStar_List.nth args' (Prims.parse_int "0"))
in (FStar_All.pipe_right _135_320 arg_to_string))
in (let _135_323 = (FStar_All.pipe_right e infix_prim_op_to_string)
in (let _135_322 = (let _135_321 = (FStar_List.nth args' (Prims.parse_int "1"))
in (FStar_All.pipe_right _135_321 arg_to_string))
in (FStar_Util.format3 "(%s %s %s)" _135_324 _135_323 _135_322))))
end else begin
if ((is_unary_prim_op e) && ((FStar_List.length args') = (Prims.parse_int "1"))) then begin
(let _135_327 = (FStar_All.pipe_right e unary_prim_op_to_string)
in (let _135_326 = (let _135_325 = (FStar_List.nth args' (Prims.parse_int "0"))
in (FStar_All.pipe_right _135_325 arg_to_string))
in (FStar_Util.format2 "(%s %s)" _135_327 _135_326)))
end else begin
(let _135_329 = (FStar_All.pipe_right e exp_to_string)
in (let _135_328 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _135_329 _135_328)))
end
end)
end))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _135_337 = (FStar_All.pipe_right e exp_to_string)
in (let _135_336 = (let _135_335 = (FStar_All.pipe_right pats (FStar_List.map (fun _34_588 -> (match (_34_588) with
| (p, wopt, e) -> begin
(let _135_334 = (FStar_All.pipe_right p pat_to_string)
in (let _135_333 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _135_331 = (FStar_All.pipe_right w exp_to_string)
in (FStar_Util.format1 "when %s" _135_331))
end)
in (let _135_332 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format3 "%s %s -> %s" _135_334 _135_333 _135_332))))
end))))
in (FStar_Util.concat_l "\n\t" _135_335))
in (FStar_Util.format2 "(match %s with %s)" _135_337 _135_336)))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _34_595) -> begin
(let _135_339 = (FStar_All.pipe_right e exp_to_string)
in (let _135_338 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "(%s:%s)" _135_339 _135_338)))
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(let _135_341 = (lbs_to_string lbs)
in (let _135_340 = (FStar_All.pipe_right e exp_to_string)
in (FStar_Util.format2 "%s in %s" _135_341 _135_340)))
end))
and uvar_e_to_string : (FStar_Absyn_Syntax.uvar_e * FStar_Absyn_Syntax.typ)  ->  Prims.string = (fun _34_605 -> (match (_34_605) with
| (uv, _34_604) -> begin
(let _135_344 = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _135_343 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _135_343))
end
in (Prims.strcat "\'e" _135_344))
end))
and lbs_to_string : FStar_Absyn_Syntax.letbindings  ->  Prims.string = (fun lbs -> (let _135_351 = (let _135_350 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _135_349 = (lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _135_348 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbtyp typ_to_string)
in (let _135_347 = (FStar_All.pipe_right lb.FStar_Absyn_Syntax.lbdef exp_to_string)
in (FStar_Util.format3 "%s:%s = %s" _135_349 _135_348 _135_347)))))))
in (FStar_Util.concat_l "\n and " _135_350))
in (FStar_Util.format2 "let %s %s" (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _135_351)))
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
and either_l_to_string : Prims.string  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either Prims.list  ->  Prims.string = (fun delim l -> (let _135_356 = (FStar_All.pipe_right l (FStar_List.map either_to_string))
in (FStar_All.pipe_right _135_356 (FStar_Util.concat_l delim))))
and meta_to_string : FStar_Absyn_Syntax.meta_t  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Meta_refresh_label (t, _34_623, _34_625) -> begin
(let _135_358 = (typ_to_string t)
in (FStar_Util.format1 "(refresh) %s" _135_358))
end
| FStar_Absyn_Syntax.Meta_labeled (t, l, _34_631, _34_633) -> begin
(let _135_359 = (typ_to_string t)
in (FStar_Util.format2 "(labeled \"%s\") %s" l _135_359))
end
| FStar_Absyn_Syntax.Meta_named (_34_637, l) -> begin
(sli l)
end
| FStar_Absyn_Syntax.Meta_pattern (t, ps) -> begin
(let _135_361 = (pats_to_string ps)
in (let _135_360 = (FStar_All.pipe_right t typ_to_string)
in (FStar_Util.format2 "{:pattern %s} %s" _135_361 _135_360)))
end
| FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _34_648) -> begin
(let _135_363 = (formula_to_string t1)
in (let _135_362 = (formula_to_string t2)
in (FStar_Util.format2 "%s /\\ %s" _135_363 _135_362)))
end))
and pats_to_string : FStar_Absyn_Syntax.arg Prims.list Prims.list  ->  Prims.string = (fun ps -> (let _135_367 = (FStar_All.pipe_right ps (FStar_List.map (fun e -> (let _135_366 = (FStar_All.pipe_right e (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _135_366 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _135_367 (FStar_String.concat " \\/ "))))
and kind_to_string : FStar_Absyn_Syntax.knd  ->  Prims.string = (fun x -> (match ((let _135_369 = (FStar_Absyn_Util.compress_kind x)
in _135_369.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_lam (_34_655) -> begin
(failwith "Impossible")
end
| FStar_Absyn_Syntax.Kind_delayed (_34_658) -> begin
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
(let _135_371 = (sli n)
in (let _135_370 = (args_to_string args)
in (FStar_Util.format2 "%s %s" _135_371 _135_370)))
end
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(let _135_373 = (binders_to_string " -> " binders)
in (let _135_372 = (FStar_All.pipe_right k kind_to_string)
in (FStar_Util.format2 "(%s -> %s)" _135_373 _135_372)))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun uv -> (let _135_375 = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _135_374 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _135_374))
end
in (Prims.strcat "\'k_" _135_375)))
and uvar_k_to_string' : ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list)  ->  Prims.string = (fun _34_680 -> (match (_34_680) with
| (uv, args) -> begin
(

let str = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _135_377 = (FStar_Unionfind.uvar_id uv)
in (FStar_Util.string_of_int _135_377))
end
in (let _135_378 = (args_to_string args)
in (FStar_Util.format2 "(\'k_%s %s)" str _135_378)))
end))
and pat_to_string : FStar_Absyn_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (l, _34_685, pats) -> begin
(let _135_383 = (sli l.FStar_Absyn_Syntax.v)
in (let _135_382 = (let _135_381 = (FStar_List.map (fun _34_691 -> (match (_34_691) with
| (x, b) -> begin
(

let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _135_381 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _135_383 _135_382)))
end
| FStar_Absyn_Syntax.Pat_dot_term (x, _34_695) -> begin
(let _135_384 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".%s" _135_384))
end
| FStar_Absyn_Syntax.Pat_dot_typ (x, _34_700) -> begin
(let _135_385 = (strBvd x.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 ".\'%s" _135_385))
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
| FStar_Absyn_Syntax.Pat_wild (_34_710) -> begin
"_"
end
| FStar_Absyn_Syntax.Pat_twild (_34_713) -> begin
"\'_"
end
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(let _135_386 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _135_386))
end))


let subst_to_string = (fun subst -> (let _135_394 = (let _135_393 = (FStar_List.map (fun uu___56 -> (match (uu___56) with
| FStar_Util.Inl (a, t) -> begin
(let _135_390 = (strBvd a)
in (let _135_389 = (typ_to_string t)
in (FStar_Util.format2 "(%s -> %s)" _135_390 _135_389)))
end
| FStar_Util.Inr (x, e) -> begin
(let _135_392 = (strBvd x)
in (let _135_391 = (exp_to_string e)
in (FStar_Util.format2 "(%s -> %s)" _135_392 _135_391)))
end)) subst)
in (FStar_All.pipe_right _135_393 (FStar_String.concat ", ")))
in (FStar_All.pipe_left (FStar_Util.format1 "{%s}") _135_394)))


let freevars_to_string : FStar_Absyn_Syntax.freevars  ->  Prims.string = (fun fvs -> (

let f = (fun l -> (let _135_400 = (let _135_399 = (FStar_All.pipe_right l FStar_Util.set_elements)
in (FStar_All.pipe_right _135_399 (FStar_List.map (fun t -> (strBvd t.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _135_400 (FStar_String.concat ", "))))
in (let _135_402 = (f fvs.FStar_Absyn_Syntax.ftvs)
in (let _135_401 = (f fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_Util.format2 "ftvs={%s}, fxvs={%s}" _135_402 _135_401)))))


let qual_to_string : FStar_Absyn_Syntax.qualifier  ->  Prims.string = (fun uu___57 -> (match (uu___57) with
| FStar_Absyn_Syntax.Logic -> begin
"logic"
end
| FStar_Absyn_Syntax.Opaque -> begin
"opaque"
end
| FStar_Absyn_Syntax.Discriminator (_34_737) -> begin
"discriminator"
end
| FStar_Absyn_Syntax.Projector (_34_740) -> begin
"projector"
end
| FStar_Absyn_Syntax.RecordType (ids) -> begin
(let _135_407 = (let _135_406 = (FStar_All.pipe_right ids (FStar_List.map (fun lid -> lid.FStar_Ident.ident.FStar_Ident.idText)))
in (FStar_All.pipe_right _135_406 (FStar_String.concat ", ")))
in (FStar_Util.format1 "record(%s)" _135_407))
end
| _34_746 -> begin
"other"
end))


let quals_to_string : FStar_Absyn_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (let _135_410 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _135_410 (FStar_String.concat " "))))


let rec sigelt_to_string : FStar_Absyn_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.ResetOptions (None), _34_752) -> begin
"#reset-options"
end
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.ResetOptions (Some (s)), _34_759) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Absyn_Syntax.Sig_pragma (FStar_Absyn_Syntax.SetOptions (s), _34_765) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _34_772, _34_774, quals, _34_777) -> begin
(let _135_415 = (quals_to_string quals)
in (let _135_414 = (binders_to_string " " tps)
in (let _135_413 = (kind_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _135_415 lid.FStar_Ident.str _135_414 _135_413))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, _34_785, _34_787) -> begin
(let _135_418 = (binders_to_string " " tps)
in (let _135_417 = (kind_to_string k)
in (let _135_416 = (typ_to_string t)
in (FStar_Util.format4 "type %s %s : %s = %s" lid.FStar_Ident.str _135_418 _135_417 _135_416))))
end
| FStar_Absyn_Syntax.Sig_datacon (lid, t, _34_793, _34_795, _34_797, _34_799) -> begin
(let _135_419 = (typ_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _135_419))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _34_806) -> begin
(let _135_421 = (quals_to_string quals)
in (let _135_420 = (typ_to_string t)
in (FStar_Util.format3 "%s val %s : %s" _135_421 lid.FStar_Ident.str _135_420)))
end
| FStar_Absyn_Syntax.Sig_assume (lid, f, _34_812, _34_814) -> begin
(let _135_422 = (typ_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _135_422))
end
| FStar_Absyn_Syntax.Sig_let (lbs, _34_819, _34_821, b) -> begin
(lbs_to_string lbs)
end
| FStar_Absyn_Syntax.Sig_main (e, _34_827) -> begin
(let _135_423 = (exp_to_string e)
in (FStar_Util.format1 "let _ = %s" _135_423))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _34_832, _34_834, _34_836) -> begin
(let _135_424 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _135_424 (FStar_String.concat "\n")))
end
| FStar_Absyn_Syntax.Sig_new_effect (_34_840) -> begin
"new_effect { ... }"
end
| FStar_Absyn_Syntax.Sig_sub_effect (_34_843) -> begin
"sub_effect ..."
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (_34_846) -> begin
"kind ..."
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, tps, c, _34_852, _34_854) -> begin
(let _135_427 = (sli l)
in (let _135_426 = (binders_to_string " " tps)
in (let _135_425 = (comp_typ_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _135_427 _135_426 _135_425))))
end))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _135_432 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _135_432 msg)))


let rec sigelt_to_string_short : FStar_Absyn_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Absyn_Syntax.Sig_let ((_34_861, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _34_865; FStar_Absyn_Syntax.lbdef = _34_863})::[]), _34_873, _34_875, _34_877) -> begin
(let _135_435 = (typ_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Ident.str _135_435))
end
| _34_881 -> begin
(let _135_438 = (let _135_437 = (FStar_Absyn_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _135_437 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _135_438 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Absyn_Syntax.modul  ->  Prims.string = (fun m -> (let _135_443 = (sli m.FStar_Absyn_Syntax.name)
in (let _135_442 = (let _135_441 = (FStar_List.map sigelt_to_string m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _135_441 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _135_443 _135_442))))




