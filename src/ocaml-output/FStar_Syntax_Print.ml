
open Prims
let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> l.FStar_Ident.str)

let fv_to_string = (fun fv -> (lid_to_string (Prims.fst fv).FStar_Syntax_Syntax.v))

let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _144_6 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "#") _144_6)))

let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> if (FStar_ST.read FStar_Options.print_real_names) then begin
(bv_to_string bv)
end else begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)

let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _144_11 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "@") _144_11)))

let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.op_Addition, "+"))::((FStar_Syntax_Const.op_Subtraction, "-"))::((FStar_Syntax_Const.op_Multiply, "*"))::((FStar_Syntax_Const.op_Division, "/"))::((FStar_Syntax_Const.op_Eq, "="))::((FStar_Syntax_Const.op_ColonEq, ":="))::((FStar_Syntax_Const.op_notEq, "<>"))::((FStar_Syntax_Const.op_And, "&&"))::((FStar_Syntax_Const.op_Or, "||"))::((FStar_Syntax_Const.op_LTE, "<="))::((FStar_Syntax_Const.op_GTE, ">="))::((FStar_Syntax_Const.op_LT, "<"))::((FStar_Syntax_Const.op_GT, ">"))::((FStar_Syntax_Const.op_Modulus, "mod"))::((FStar_Syntax_Const.and_lid, "/\\"))::((FStar_Syntax_Const.or_lid, "\\/"))::((FStar_Syntax_Const.imp_lid, "==>"))::((FStar_Syntax_Const.iff_lid, "<==>"))::((FStar_Syntax_Const.precedes_lid, "<<"))::((FStar_Syntax_Const.eq2_lid, "=="))::[]

let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.op_Negation, "not"))::((FStar_Syntax_Const.op_Minus, "-"))::((FStar_Syntax_Const.not_lid, "~"))::[]

let is_prim_op = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _42_20) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v)))
end
| _42_24 -> begin
false
end))

let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _42_28) -> begin
fv.FStar_Syntax_Syntax.v
end
| _42_32 -> begin
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

let is_inr = (fun _42_1 -> (match (_42_1) with
| FStar_Util.Inl (_42_42) -> begin
false
end
| FStar_Util.Inr (_42_45) -> begin
true
end))

let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _144_32 = (FStar_Syntax_Subst.compress e)
in _144_32.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(let args = (FStar_List.filter (fun a -> ((Prims.snd a) <> Some (FStar_Syntax_Syntax.Implicit))) args)
in (let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = 2)) then begin
(match ((let _144_34 = (FStar_List.nth exps 1)
in (reconstruct_lex _144_34))) with
| Some (xs) -> begin
(let _144_36 = (let _144_35 = (FStar_List.nth exps 0)
in (_144_35)::xs)
in Some (_144_36))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _42_59 -> begin
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

let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _144_50 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _144_50)))

let infix_prim_op_to_string = (fun e -> (let _144_52 = (get_lid e)
in (find_lid _144_52 infix_prim_ops)))

let unary_prim_op_to_string = (fun e -> (let _144_54 = (get_lid e)
in (find_lid _144_54 unary_prim_ops)))

let quant_to_string = (fun t -> (let _144_56 = (get_lid t)
in (find_lid _144_56 quants)))

let rec sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_ST.read FStar_Options.print_real_names) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)

let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _42_2 -> (match (_42_2) with
| (_42_77, Some (FStar_Syntax_Syntax.Implicit)) -> begin
false
end
| _42_82 -> begin
true
end)))))

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
| FStar_Const.Const_int32 (x) -> begin
(FStar_Util.string_of_int32 x)
end
| FStar_Const.Const_float (x) -> begin
(FStar_Util.string_of_float x)
end
| FStar_Const.Const_char (x) -> begin
(Prims.strcat (Prims.strcat "\'" (FStar_Util.string_of_char x)) "\'")
end
| FStar_Const.Const_string (bytes, _42_96) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_42_100) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x) -> begin
x
end
| FStar_Const.Const_int64 (_42_105) -> begin
"<int64>"
end
| FStar_Const.Const_uint8 (_42_108) -> begin
"<uint8>"
end))

let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun _42_3 -> (match (_42_3) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l)
end))

let tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _144_67 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _144_67))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _144_68 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _144_68))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _144_69 = (lid_to_string (Prims.fst x).FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _144_69))
end
| FStar_Syntax_Syntax.Tm_uinst (_42_123) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (_42_126) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (_42_129) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (_42_132) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (_42_135) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (_42_138) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (_42_141) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (_42_144) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (_42_147) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (_42_150) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (_42_153) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (_42_156, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
"Tm_delayed"
end
| Some (_42_162) -> begin
"Tm_delayed-resolved"
end)
end
| FStar_Syntax_Syntax.Tm_meta (_42_165) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))

let uvar_to_string = (fun u -> if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _144_74 = (let _144_73 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _144_73 FStar_Util.string_of_int))
in (Prims.strcat "?" _144_74))
end)

let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_unif (u) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(let _144_77 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _144_77))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _144_78 = (univ_to_string u)
in (FStar_Util.format1 "(S %s)" _144_78))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _144_80 = (let _144_79 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _144_79 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _144_80))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))

let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _144_83 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _144_83 (FStar_String.concat ", "))))

let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _144_87 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _144_87 (FStar_String.concat ", "))))

let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun _42_4 -> (match (_42_4) with
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
| FStar_Syntax_Syntax.Logic -> begin
"logic"
end
| FStar_Syntax_Syntax.TotalEffect -> begin
"total"
end
| FStar_Syntax_Syntax.DefaultEffect (None) -> begin
"no default"
end
| FStar_Syntax_Syntax.DefaultEffect (Some (l)) -> begin
(let _144_90 = (lid_to_string l)
in (FStar_Util.format1 "default %s" _144_90))
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(let _144_91 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _144_91))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _144_92 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _144_92 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(let _144_94 = (let _144_93 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _144_93 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordType %s)" _144_94))
end
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
(let _144_96 = (let _144_95 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _144_95 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordConstructor %s)" _144_96))
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
| _42_216 -> begin
(let _144_100 = (let _144_99 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _144_99 (FStar_String.concat " ")))
in (Prims.strcat _144_100 " "))
end))

let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (let x = (FStar_Syntax_Subst.compress x)
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_42_220) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_42_223, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, _42_229) -> begin
(term_to_string t)
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(db_to_string x)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(nm_to_string x)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(fv_to_string f)
end
| FStar_Syntax_Syntax.Tm_uvar (u, _42_240) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _144_122 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _144_122))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _144_124 = (binders_to_string " -> " bs)
in (let _144_123 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _144_124 _144_123)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (l) when (FStar_ST.read FStar_Options.print_implicits) -> begin
(let _144_128 = (binders_to_string " " bs)
in (let _144_127 = (term_to_string t2)
in (let _144_126 = (let _144_125 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _144_125))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _144_128 _144_127 _144_126))))
end
| _42_259 -> begin
(let _144_130 = (binders_to_string " " bs)
in (let _144_129 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _144_130 _144_129)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _144_133 = (bv_to_string xt)
in (let _144_132 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _144_131 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _144_133 _144_132 _144_131))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _144_135 = (term_to_string t)
in (let _144_134 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _144_135 _144_134)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _144_137 = (lbs_to_string [] lbs)
in (let _144_136 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _144_137 _144_136)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _42_275) -> begin
(let _144_139 = (term_to_string e)
in (let _144_138 = (term_to_string t)
in (FStar_Util.format2 "(%s : %s)" _144_139 _144_138)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _144_147 = (term_to_string head)
in (let _144_146 = (let _144_145 = (FStar_All.pipe_right branches (FStar_List.map (fun _42_285 -> (match (_42_285) with
| (p, wopt, e) -> begin
(let _144_144 = (FStar_All.pipe_right p pat_to_string)
in (let _144_143 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _144_141 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _144_141))
end)
in (let _144_142 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _144_144 _144_143 _144_142))))
end))))
in (FStar_Util.concat_l "\n\t|" _144_145))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _144_147 _144_146)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _144_149 = (term_to_string t)
in (let _144_148 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _144_149 _144_148)))
end else begin
(term_to_string t)
end
end
| _42_294 -> begin
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _144_154 = (fv_to_string l)
in (let _144_153 = (let _144_152 = (FStar_List.map (fun _42_302 -> (match (_42_302) with
| (x, b) -> begin
(let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _144_152 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _144_154 _144_153)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _42_306) -> begin
(let _144_155 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _144_155))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(bv_to_string x)
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _144_156 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _144_156))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _144_157 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _144_157))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (let _144_169 = (quals_to_string quals)
in (let _144_168 = (let _144_167 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _144_166 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _144_165 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _144_162 = (let _144_161 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat "<" _144_161))
in (Prims.strcat _144_162 ">"))
end else begin
""
end
in (let _144_164 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _144_163 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _144_166 _144_165 _144_164 _144_163))))))))
in (FStar_Util.concat_l "\n and " _144_167))
in (FStar_Util.format3 "%slet %s %s" _144_169 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _144_168))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _144_172 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _144_171 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _144_172 _144_171))))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s _42_5 -> (match (_42_5) with
| Some (FStar_Syntax_Syntax.Implicit) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _42_328 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (let _42_333 = b
in (match (_42_333) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(term_to_string a.FStar_Syntax_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_bound_var_types)))) then begin
(let _144_177 = (nm_to_string a)
in (imp_to_string _144_177 imp))
end else begin
(let _144_181 = (let _144_180 = (let _144_178 = (nm_to_string a)
in (Prims.strcat _144_178 ":"))
in (let _144_179 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat _144_180 _144_179)))
in (imp_to_string _144_181 imp))
end
end
end)))
and binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (let bs = if (FStar_ST.read FStar_Options.print_implicits) then begin
bs
end else begin
(filter_imp bs)
end
in if (sep = " -> ") then begin
(let _144_186 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _144_186 (FStar_String.concat sep)))
end else begin
(let _144_187 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _144_187 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _42_6 -> (match (_42_6) with
| (a, imp) -> begin
(let _144_189 = (term_to_string a)
in (imp_to_string _144_189 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _144_191 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _144_191 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(match ((let _144_193 = (FStar_Syntax_Subst.compress t)
in _144_193.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_42_349) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _42_352 -> begin
(let _144_194 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _144_194))
end)
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(match ((let _144_195 = (FStar_Syntax_Subst.compress t)
in _144_195.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_42_356) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _42_359 -> begin
(let _144_196 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _144_196))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(let basic = if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _42_7 -> (match (_42_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _42_365 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args)))) then begin
(let _144_198 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _144_198))
end else begin
if (((not ((FStar_ST.read FStar_Options.print_effect_args))) && (not ((FStar_ST.read FStar_Options.print_implicits)))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _42_8 -> (match (_42_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _42_369 -> begin
false
end))))) then begin
(let _144_200 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _144_200))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _144_204 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _144_203 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _144_202 = (let _144_201 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _144_201 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _144_204 _144_203 _144_202))))
end else begin
(let _144_206 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _144_205 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _144_206 _144_205)))
end
end
end
end
in (let dec = (let _144_210 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _42_9 -> (match (_42_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _144_209 = (let _144_208 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _144_208))
in (_144_209)::[])
end
| _42_375 -> begin
[]
end))))
in (FStar_All.pipe_right _144_210 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))

let tscheme_to_string : (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  Prims.string = (fun _42_380 -> (match (_42_380) with
| (us, t) -> begin
(let _144_215 = (univ_names_to_string us)
in (let _144_214 = (term_to_string t)
in (FStar_Util.format2 "<%s> %s" _144_215 _144_214)))
end))

let eff_decl_to_string : FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun ed -> (let _144_251 = (let _144_250 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _144_249 = (let _144_248 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (let _144_247 = (let _144_246 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _144_245 = (let _144_244 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _144_243 = (let _144_242 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret)
in (let _144_241 = (let _144_240 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _144_239 = (let _144_238 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wlp)
in (let _144_237 = (let _144_236 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _144_235 = (let _144_234 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _144_233 = (let _144_232 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wlp)
in (let _144_231 = (let _144_230 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_binop)
in (let _144_229 = (let _144_228 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_as_type)
in (let _144_227 = (let _144_226 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _144_225 = (let _144_224 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _144_223 = (let _144_222 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _144_221 = (let _144_220 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _144_219 = (let _144_218 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (_144_218)::[])
in (_144_220)::_144_219))
in (_144_222)::_144_221))
in (_144_224)::_144_223))
in (_144_226)::_144_225))
in (_144_228)::_144_227))
in (_144_230)::_144_229))
in (_144_232)::_144_231))
in (_144_234)::_144_233))
in (_144_236)::_144_235))
in (_144_238)::_144_237))
in (_144_240)::_144_239))
in (_144_242)::_144_241))
in (_144_244)::_144_243))
in (_144_246)::_144_245))
in (_144_248)::_144_247))
in (_144_250)::_144_249))
in (FStar_Util.format "new_effect { %s<%s> %s : %s \n\tret         = %s\n; bind_wp     = %s\n; bind_wlp    = %s\n; if_then_else= %s\n; ite_wp      = %s\n; ite_wlp     = %s\n; wp_binop    = %s\n; wp_as_type  = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s}\n" _144_251)))

let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions, _42_385) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _42_391) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _42_399, _42_401, quals, _42_404) -> begin
(let _144_256 = (quals_to_string quals)
in (let _144_255 = (binders_to_string " " tps)
in (let _144_254 = (term_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _144_256 lid.FStar_Ident.str _144_255 _144_254))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _42_411, _42_413, _42_415, _42_417, _42_419) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _42_424 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_42_424) with
| (univs, t) -> begin
(let _144_258 = (univ_names_to_string univs)
in (let _144_257 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _144_258 lid.FStar_Ident.str _144_257)))
end))
end else begin
(let _144_259 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _144_259))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _42_430) -> begin
(let _42_435 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_42_435) with
| (univs, t) -> begin
(let _144_263 = (quals_to_string quals)
in (let _144_262 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _144_260 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _144_260))
end else begin
""
end
in (let _144_261 = (term_to_string t)
in (FStar_Util.format4 "%s val %s %s : %s" _144_263 lid.FStar_Ident.str _144_262 _144_261))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _42_439, _42_441) -> begin
(let _144_264 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _144_264))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _42_446, _42_448, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _42_454) -> begin
(let _144_265 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _144_265))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _42_459, _42_461, _42_463) -> begin
(let _144_266 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _144_266 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _42_468) -> begin
(eff_decl_to_string ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(let _42_477 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst se.FStar_Syntax_Syntax.lift) (Prims.snd se.FStar_Syntax_Syntax.lift))
in (match (_42_477) with
| (us, t) -> begin
(let _144_270 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _144_269 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _144_268 = (univ_names_to_string us)
in (let _144_267 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _144_270 _144_269 _144_268 _144_267)))))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, _42_480, tps, c, _42_484, _42_486) -> begin
(let _144_273 = (sli l)
in (let _144_272 = (binders_to_string " " tps)
in (let _144_271 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _144_273 _144_272 _144_271))))
end))

let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _144_278 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _144_278 msg)))

let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_42_493, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (l); FStar_Syntax_Syntax.lbunivs = _42_500; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _42_497; FStar_Syntax_Syntax.lbdef = _42_495}::[]), _42_507, _42_509, _42_511) -> begin
(let _144_281 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Ident.str _144_281))
end
| _42_515 -> begin
(let _144_284 = (let _144_283 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _144_283 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _144_284 (FStar_String.concat ", ")))
end))

let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _144_289 = (sli m.FStar_Syntax_Syntax.name)
in (let _144_288 = (let _144_287 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _144_287 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _144_289 _144_288))))

let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _42_10 -> (match (_42_10) with
| FStar_Syntax_Syntax.DB (i, t) -> begin
(let _144_293 = (FStar_Util.string_of_int i)
in (let _144_292 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _144_293 _144_292)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _144_295 = (bv_to_string x)
in (let _144_294 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _144_295 _144_294)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _144_297 = (bv_to_string x)
in (let _144_296 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _144_297 _144_296)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _144_299 = (FStar_Util.string_of_int i)
in (let _144_298 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _144_299 _144_298)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _144_300 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _144_300))
end))

let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _144_303 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _144_303 (FStar_String.concat "; "))))




