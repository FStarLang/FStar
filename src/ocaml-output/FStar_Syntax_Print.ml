
open Prims

let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> l.FStar_Ident.str)


let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _130_7 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "#") _130_7)))


let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> if (FStar_Options.print_real_names ()) then begin
(bv_to_string bv)
end else begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)


let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _130_12 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "!") _130_12)))


let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.op_Addition, "+"))::((FStar_Syntax_Const.op_Subtraction, "-"))::((FStar_Syntax_Const.op_Multiply, "*"))::((FStar_Syntax_Const.op_Division, "/"))::((FStar_Syntax_Const.op_Eq, "="))::((FStar_Syntax_Const.op_ColonEq, ":="))::((FStar_Syntax_Const.op_notEq, "<>"))::((FStar_Syntax_Const.op_And, "&&"))::((FStar_Syntax_Const.op_Or, "||"))::((FStar_Syntax_Const.op_LTE, "<="))::((FStar_Syntax_Const.op_GTE, ">="))::((FStar_Syntax_Const.op_LT, "<"))::((FStar_Syntax_Const.op_GT, ">"))::((FStar_Syntax_Const.op_Modulus, "mod"))::((FStar_Syntax_Const.and_lid, "/\\"))::((FStar_Syntax_Const.or_lid, "\\/"))::((FStar_Syntax_Const.imp_lid, "==>"))::((FStar_Syntax_Const.iff_lid, "<==>"))::((FStar_Syntax_Const.precedes_lid, "<<"))::((FStar_Syntax_Const.eq2_lid, "=="))::((FStar_Syntax_Const.eq3_lid, "==="))::[]


let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.op_Negation, "not"))::((FStar_Syntax_Const.op_Minus, "-"))::((FStar_Syntax_Const.not_lid, "~"))::[]


let is_prim_op = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
end
| _39_22 -> begin
false
end))


let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| _39_27 -> begin
(FStar_All.failwith "get_lid")
end))


let is_infix_prim_op : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split infix_prim_ops)) e))


let is_unary_prim_op : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split unary_prim_ops)) e))


let quants : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.forall_lid, "forall"))::((FStar_Syntax_Const.exists_lid, "exists"))::[]


type exp =
FStar_Syntax_Syntax.term


let is_b2t : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op ((FStar_Syntax_Const.b2t_lid)::[]) t))


let is_quant : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op (Prims.fst (FStar_List.split quants)) t))


let is_ite : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op ((FStar_Syntax_Const.ite_lid)::[]) t))


let is_lex_cons : exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Syntax_Const.lexcons_lid)::[]) f))


let is_lex_top : exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Syntax_Const.lextop_lid)::[]) f))


let is_inr = (fun _39_1 -> (match (_39_1) with
| FStar_Util.Inl (_39_37) -> begin
false
end
| FStar_Util.Inr (_39_40) -> begin
true
end))


let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _39_2 -> (match (_39_2) with
| (_39_45, Some (FStar_Syntax_Syntax.Implicit (_39_47))) -> begin
false
end
| _39_52 -> begin
true
end)))))


let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _130_35 = (FStar_Syntax_Subst.compress e)
in _130_35.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args = (filter_imp args)
in (

let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = 2)) then begin
(match ((let _130_36 = (FStar_List.nth exps 1)
in (reconstruct_lex _130_36))) with
| Some (xs) -> begin
(let _130_38 = (let _130_37 = (FStar_List.nth exps 0)
in (_130_37)::xs)
in Some (_130_38))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _39_64 -> begin
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
| (hd)::tl -> begin
if (f hd) then begin
hd
end else begin
(find f tl)
end
end))


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _130_52 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _130_52)))


let infix_prim_op_to_string = (fun e -> (let _130_54 = (get_lid e)
in (find_lid _130_54 infix_prim_ops)))


let unary_prim_op_to_string = (fun e -> (let _130_56 = (get_lid e)
in (find_lid _130_56 unary_prim_ops)))


let quant_to_string = (fun t -> (let _130_58 = (get_lid t)
in (find_lid _130_58 quants)))


let rec sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_Options.print_real_names ()) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)


let const_to_string : FStar_Const.sconst  ->  Prims.string = (fun x -> (match (x) with
| FStar_Const.Const_effect -> begin
"Effect"
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
| FStar_Const.Const_string (bytes, _39_88) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_39_92) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x, _39_96) -> begin
x
end
| FStar_Const.Const_char (c) -> begin
(FStar_Util.string_of_char c)
end
| FStar_Const.Const_range (r) -> begin
(FStar_Range.string_of_range r)
end))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun _39_3 -> (match (_39_3) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _130_67 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _130_67))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _130_68 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _130_68))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _130_69 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _130_69))
end
| FStar_Syntax_Syntax.Tm_uinst (_39_116) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (_39_119) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (_39_122) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (_39_125) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (_39_128) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (_39_131) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (_39_134) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (_39_137) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (_39_140) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (_39_143) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (_39_146) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (_39_149, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
"Tm_delayed"
end
| Some (_39_155) -> begin
"Tm_delayed-resolved"
end)
end
| FStar_Syntax_Syntax.Tm_meta (_39_158) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))


let uvar_to_string = (fun u -> if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _130_74 = (let _130_73 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _130_73 FStar_Util.string_of_int))
in (Prims.strcat "?" _130_74))
end)


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_unif (u) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(FStar_Util.format1 "U_name<%s>" x.FStar_Ident.idText)
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(let _130_77 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _130_77))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _130_78 = (univ_to_string u)
in (FStar_Util.format1 "(S %s)" _130_78))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _130_80 = (let _130_79 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _130_79 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _130_80))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _130_83 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _130_83 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _130_87 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _130_87 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun _39_4 -> (match (_39_4) with
| FStar_Syntax_Syntax.Assumption -> begin
"assume"
end
| FStar_Syntax_Syntax.New -> begin
"new"
end
| FStar_Syntax_Syntax.Private -> begin
"private"
end
| FStar_Syntax_Syntax.Inline -> begin
"inline"
end
| FStar_Syntax_Syntax.Unfoldable -> begin
"unfoldable"
end
| FStar_Syntax_Syntax.Irreducible -> begin
"irreducible"
end
| FStar_Syntax_Syntax.Abstract -> begin
"abstract"
end
| FStar_Syntax_Syntax.Noeq -> begin
"noeq"
end
| FStar_Syntax_Syntax.Logic -> begin
"logic"
end
| FStar_Syntax_Syntax.TotalEffect -> begin
"total"
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(let _130_90 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _130_90))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _130_91 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _130_91 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(let _130_93 = (let _130_92 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _130_92 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordType %s)" _130_93))
end
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
(let _130_95 = (let _130_94 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _130_94 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordConstructor %s)" _130_95))
end
| FStar_Syntax_Syntax.ExceptionConstructor -> begin
"ExceptionConstructor"
end
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
"HasMaskedEffect"
end
| FStar_Syntax_Syntax.Effect -> begin
"Effect"
end))


let quals_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| _39_205 -> begin
(let _130_99 = (let _130_98 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _130_98 (FStar_String.concat " ")))
in (Prims.strcat _130_99 " "))
end))


let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let x = (FStar_Syntax_Subst.compress x)
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_39_209) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_39_212, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (let _130_124 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _130_123 = (FStar_All.pipe_right args (FStar_List.map (fun _39_225 -> (match (_39_225) with
| (t, _39_224) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _130_123 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _130_124 (FStar_String.concat "\\/")))
in (let _130_125 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _130_125)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _39_229) -> begin
(term_to_string t)
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _130_126 = (db_to_string x)
in (FStar_Util.format1 "Tm_bvar:%s" _130_126))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _130_127 = (nm_to_string x)
in (FStar_Util.format1 "Tm_name:%s" _130_127))
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(let _130_128 = (fv_to_string f)
in (FStar_Util.format1 "Tm_fvar:%s" _130_128))
end
| FStar_Syntax_Syntax.Tm_uvar (u, _39_240) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_Options.print_universes ()) then begin
(let _130_129 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _130_129))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _130_131 = (binders_to_string " -> " bs)
in (let _130_130 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _130_131 _130_130)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
(let _130_135 = (binders_to_string " " bs)
in (let _130_134 = (term_to_string t2)
in (let _130_133 = (let _130_132 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _130_132))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _130_135 _130_134 _130_133))))
end
| Some (FStar_Util.Inr (l)) when (FStar_Options.print_implicits ()) -> begin
(let _130_137 = (binders_to_string " " bs)
in (let _130_136 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _130_137 _130_136 l.FStar_Ident.str)))
end
| _39_263 -> begin
(let _130_139 = (binders_to_string " " bs)
in (let _130_138 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _130_139 _130_138)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _130_142 = (bv_to_string xt)
in (let _130_141 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _130_140 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _130_142 _130_141 _130_140))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _130_144 = (term_to_string t)
in (let _130_143 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _130_144 _130_143)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _130_146 = (lbs_to_string [] lbs)
in (let _130_145 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _130_146 _130_145)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _39_280) -> begin
(let _130_148 = (term_to_string e)
in (let _130_147 = (term_to_string t)
in (FStar_Util.format2 "(%s : %s)" _130_148 _130_147)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _39_287) -> begin
(let _130_150 = (term_to_string e)
in (let _130_149 = (comp_to_string c)
in (FStar_Util.format2 "(%s : %s)" _130_150 _130_149)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _130_158 = (term_to_string head)
in (let _130_157 = (let _130_156 = (FStar_All.pipe_right branches (FStar_List.map (fun _39_297 -> (match (_39_297) with
| (p, wopt, e) -> begin
(let _130_155 = (FStar_All.pipe_right p pat_to_string)
in (let _130_154 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _130_152 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _130_152))
end)
in (let _130_153 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _130_155 _130_154 _130_153))))
end))))
in (FStar_Util.concat_l "\n\t|" _130_156))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _130_158 _130_157)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_Options.print_universes ()) then begin
(let _130_160 = (term_to_string t)
in (let _130_159 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _130_160 _130_159)))
end else begin
(term_to_string t)
end
end
| _39_306 -> begin
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _130_165 = (fv_to_string l)
in (let _130_164 = (let _130_163 = (FStar_List.map (fun _39_314 -> (match (_39_314) with
| (x, b) -> begin
(

let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _130_163 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _130_165 _130_164)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _39_318) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _130_167 = (bv_to_string x)
in (let _130_166 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" _130_167 _130_166)))
end else begin
(let _130_168 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _130_168))
end
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _130_170 = (bv_to_string x)
in (let _130_169 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" _130_170 _130_169)))
end else begin
(bv_to_string x)
end
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_Options.print_real_names ()) then begin
(let _130_171 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _130_171))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _130_172 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _130_172))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (

let lbs = if (FStar_Options.print_universes ()) then begin
(let _130_178 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _39_334 = (let _130_176 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _130_176))
in (match (_39_334) with
| (us, td) -> begin
(

let _39_352 = (match ((let _130_177 = (FStar_Syntax_Subst.compress td)
in _130_177.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_39_336, ((t, _39_343))::((d, _39_339))::[]) -> begin
(t, d)
end
| _39_349 -> begin
(FStar_All.failwith "Impossibe")
end)
in (match (_39_352) with
| (t, d) -> begin
(

let _39_353 = lb
in {FStar_Syntax_Syntax.lbname = _39_353.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_353.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in ((Prims.fst lbs), _130_178))
end else begin
lbs
end
in (let _130_188 = (quals_to_string quals)
in (let _130_187 = (let _130_186 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _130_185 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _130_184 = if (FStar_Options.print_universes ()) then begin
(let _130_181 = (let _130_180 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat "<" _130_180))
in (Prims.strcat _130_181 ">"))
end else begin
""
end
in (let _130_183 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _130_182 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _130_185 _130_184 _130_183 _130_182))))))))
in (FStar_Util.concat_l "\n and " _130_186))
in (FStar_Util.format3 "%slet %s %s" _130_188 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _130_187)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _130_191 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _130_190 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _130_191 _130_190))))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s _39_5 -> (match (_39_5) with
| Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
(Prims.strcat "#." s)
end
| Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "$" s)
end
| _39_369 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (

let _39_374 = b
in (match (_39_374) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(let _130_196 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" _130_196))
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_bound_var_types ())))) then begin
(let _130_197 = (nm_to_string a)
in (imp_to_string _130_197 imp))
end else begin
(let _130_201 = (let _130_200 = (let _130_198 = (nm_to_string a)
in (Prims.strcat _130_198 ":"))
in (let _130_199 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat _130_200 _130_199)))
in (imp_to_string _130_201 imp))
end
end
end)))
and binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (

let bs = if (FStar_Options.print_implicits ()) then begin
bs
end else begin
(filter_imp bs)
end
in if (sep = " -> ") then begin
(let _130_206 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _130_206 (FStar_String.concat sep)))
end else begin
(let _130_207 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _130_207 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _39_6 -> (match (_39_6) with
| (a, imp) -> begin
(let _130_209 = (term_to_string a)
in (imp_to_string _130_209 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args = if (FStar_Options.print_implicits ()) then begin
args
end else begin
(filter_imp args)
end
in (let _130_211 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _130_211 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(match ((let _130_213 = (FStar_Syntax_Subst.compress t)
in _130_213.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_390) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_393 -> begin
(let _130_214 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _130_214))
end)
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(match ((let _130_215 = (FStar_Syntax_Subst.compress t)
in _130_215.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_397) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_400 -> begin
(let _130_216 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _130_216))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let basic = if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_7 -> (match (_39_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _39_406 -> begin
false
end)))) && (not ((FStar_Options.print_effect_args ())))) then begin
(let _130_218 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _130_218))
end else begin
if (((not ((FStar_Options.print_effect_args ()))) && (not ((FStar_Options.print_implicits ())))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_Options.print_effect_args ()))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_8 -> (match (_39_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _39_410 -> begin
false
end))))) then begin
(let _130_220 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _130_220))
end else begin
if (FStar_Options.print_effect_args ()) then begin
(let _130_224 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _130_223 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _130_222 = (let _130_221 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _130_221 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _130_224 _130_223 _130_222))))
end else begin
(let _130_226 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _130_225 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _130_226 _130_225)))
end
end
end
end
in (

let dec = (let _130_230 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _39_9 -> (match (_39_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _130_229 = (let _130_228 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _130_228))
in (_130_229)::[])
end
| _39_416 -> begin
[]
end))))
in (FStar_All.pipe_right _130_230 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))


let tscheme_to_string : (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  Prims.string = (fun _39_421 -> (match (_39_421) with
| (us, t) -> begin
(let _130_235 = (univ_names_to_string us)
in (let _130_234 = (term_to_string t)
in (FStar_Util.format2 "<%s> %s" _130_235 _130_234)))
end))


let eff_decl_to_string : FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun ed -> (let _130_265 = (let _130_264 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _130_263 = (let _130_262 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (let _130_261 = (let _130_260 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _130_259 = (let _130_258 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _130_257 = (let _130_256 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret)
in (let _130_255 = (let _130_254 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _130_253 = (let _130_252 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _130_251 = (let _130_250 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _130_249 = (let _130_248 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (let _130_247 = (let _130_246 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _130_245 = (let _130_244 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _130_243 = (let _130_242 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _130_241 = (let _130_240 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _130_239 = (let _130_238 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (_130_238)::[])
in (_130_240)::_130_239))
in (_130_242)::_130_241))
in (_130_244)::_130_243))
in (_130_246)::_130_245))
in (_130_248)::_130_247))
in (_130_250)::_130_249))
in (_130_252)::_130_251))
in (_130_254)::_130_253))
in (_130_256)::_130_255))
in (_130_258)::_130_257))
in (_130_260)::_130_259))
in (_130_262)::_130_261))
in (_130_264)::_130_263))
in (FStar_Util.format "new_effect { %s<%s> %s : %s \n\tret         = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s}\n" _130_265)))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None), _39_427) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s)), _39_434) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _39_440) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _39_448, _39_450, quals, _39_453) -> begin
(let _130_271 = (quals_to_string quals)
in (let _130_270 = (univ_names_to_string univs)
in (let _130_269 = (binders_to_string " " tps)
in (let _130_268 = (term_to_string k)
in (FStar_Util.format5 "%s type %s<%s> %s : %s" _130_271 lid.FStar_Ident.str _130_270 _130_269 _130_268)))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _39_460, _39_462, _39_464, _39_466, _39_468) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_473 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_473) with
| (univs, t) -> begin
(let _130_273 = (univ_names_to_string univs)
in (let _130_272 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _130_273 lid.FStar_Ident.str _130_272)))
end))
end else begin
(let _130_274 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _130_274))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _39_479) -> begin
(

let _39_484 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_484) with
| (univs, t) -> begin
(let _130_278 = (quals_to_string quals)
in (let _130_277 = if (FStar_Options.print_universes ()) then begin
(let _130_275 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _130_275))
end else begin
""
end
in (let _130_276 = (term_to_string t)
in (FStar_Util.format4 "%s val %s %s : %s" _130_278 lid.FStar_Ident.str _130_277 _130_276))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _39_488, _39_490) -> begin
(let _130_279 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _130_279))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _39_495, _39_497, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _39_503) -> begin
(let _130_280 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _130_280))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _39_508, _39_510, _39_512) -> begin
(let _130_281 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _130_281 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _39_517) -> begin
(eff_decl_to_string ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(

let _39_526 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst se.FStar_Syntax_Syntax.lift) (Prims.snd se.FStar_Syntax_Syntax.lift))
in (match (_39_526) with
| (us, t) -> begin
(let _130_285 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _130_284 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _130_283 = (univ_names_to_string us)
in (let _130_282 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _130_285 _130_284 _130_283 _130_282)))))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _39_532, _39_534) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_539 = (let _130_286 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _130_286))
in (match (_39_539) with
| (univs, t) -> begin
(

let _39_548 = (match ((let _130_287 = (FStar_Syntax_Subst.compress t)
in _130_287.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(bs, c)
end
| _39_545 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_39_548) with
| (tps, c) -> begin
(let _130_291 = (sli l)
in (let _130_290 = (univ_names_to_string univs)
in (let _130_289 = (binders_to_string " " tps)
in (let _130_288 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _130_291 _130_290 _130_289 _130_288)))))
end))
end))
end else begin
(let _130_294 = (sli l)
in (let _130_293 = (binders_to_string " " tps)
in (let _130_292 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _130_294 _130_293 _130_292))))
end
end))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _130_299 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _130_299 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_39_553, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = _39_560; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_557; FStar_Syntax_Syntax.lbdef = _39_555})::[]), _39_566, _39_568, _39_570) -> begin
(let _130_303 = (lbname_to_string lb)
in (let _130_302 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _130_303 _130_302)))
end
| _39_574 -> begin
(let _130_306 = (let _130_305 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _130_305 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _130_306 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _130_311 = (sli m.FStar_Syntax_Syntax.name)
in (let _130_310 = (let _130_309 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _130_309 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _130_311 _130_310))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _39_10 -> (match (_39_10) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(let _130_315 = (FStar_Util.string_of_int i)
in (let _130_314 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _130_315 _130_314)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _130_317 = (bv_to_string x)
in (let _130_316 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _130_317 _130_316)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _130_319 = (bv_to_string x)
in (let _130_318 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _130_319 _130_318)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _130_321 = (FStar_Util.string_of_int i)
in (let _130_320 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _130_321 _130_320)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _130_322 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _130_322))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _130_325 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _130_325 (FStar_String.concat "; "))))




