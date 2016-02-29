
open Prims
# 44 "FStar.Syntax.Print.fst"
let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> l.FStar_Ident.str)

# 46 "FStar.Syntax.Print.fst"
let fv_to_string = (fun fv -> (lid_to_string (Prims.fst fv).FStar_Syntax_Syntax.v))

# 48 "FStar.Syntax.Print.fst"
let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _116_6 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "#") _116_6)))

# 50 "FStar.Syntax.Print.fst"
let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> if (FStar_ST.read FStar_Options.print_real_names) then begin
(bv_to_string bv)
end else begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)

# 55 "FStar.Syntax.Print.fst"
let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _116_11 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "@") _116_11)))

# 57 "FStar.Syntax.Print.fst"
let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.op_Addition, "+"))::((FStar_Syntax_Const.op_Subtraction, "-"))::((FStar_Syntax_Const.op_Multiply, "*"))::((FStar_Syntax_Const.op_Division, "/"))::((FStar_Syntax_Const.op_Eq, "="))::((FStar_Syntax_Const.op_ColonEq, ":="))::((FStar_Syntax_Const.op_notEq, "<>"))::((FStar_Syntax_Const.op_And, "&&"))::((FStar_Syntax_Const.op_Or, "||"))::((FStar_Syntax_Const.op_LTE, "<="))::((FStar_Syntax_Const.op_GTE, ">="))::((FStar_Syntax_Const.op_LT, "<"))::((FStar_Syntax_Const.op_GT, ">"))::((FStar_Syntax_Const.op_Modulus, "mod"))::((FStar_Syntax_Const.and_lid, "/\\"))::((FStar_Syntax_Const.or_lid, "\\/"))::((FStar_Syntax_Const.imp_lid, "==>"))::((FStar_Syntax_Const.iff_lid, "<==>"))::((FStar_Syntax_Const.precedes_lid, "<<"))::((FStar_Syntax_Const.eq2_lid, "=="))::[]

# 81 "FStar.Syntax.Print.fst"
let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.op_Negation, "not"))::((FStar_Syntax_Const.op_Minus, "-"))::((FStar_Syntax_Const.not_lid, "~"))::[]

# 87 "FStar.Syntax.Print.fst"
let is_prim_op = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _35_21) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v)))
end
| _35_25 -> begin
false
end))

# 91 "FStar.Syntax.Print.fst"
let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _35_29) -> begin
fv.FStar_Syntax_Syntax.v
end
| _35_33 -> begin
(FStar_All.failwith "get_lid")
end))

# 95 "FStar.Syntax.Print.fst"
let is_infix_prim_op : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split infix_prim_ops)) e))

# 97 "FStar.Syntax.Print.fst"
let is_unary_prim_op : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split unary_prim_ops)) e))

# 98 "FStar.Syntax.Print.fst"
let quants : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.forall_lid, "forall"))::((FStar_Syntax_Const.exists_lid, "exists"))::[]

# 103 "FStar.Syntax.Print.fst"
type exp =
FStar_Syntax_Syntax.term

# 104 "FStar.Syntax.Print.fst"
let is_b2t : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op ((FStar_Syntax_Const.b2t_lid)::[]) t))

# 106 "FStar.Syntax.Print.fst"
let is_quant : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op (Prims.fst (FStar_List.split quants)) t))

# 107 "FStar.Syntax.Print.fst"
let is_ite : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op ((FStar_Syntax_Const.ite_lid)::[]) t))

# 108 "FStar.Syntax.Print.fst"
let is_lex_cons : exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Syntax_Const.lexcons_lid)::[]) f))

# 110 "FStar.Syntax.Print.fst"
let is_lex_top : exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Syntax_Const.lextop_lid)::[]) f))

# 111 "FStar.Syntax.Print.fst"
let is_inr = (fun _35_1 -> (match (_35_1) with
| FStar_Util.Inl (_35_43) -> begin
false
end
| FStar_Util.Inr (_35_46) -> begin
true
end))

# 112 "FStar.Syntax.Print.fst"
let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _35_2 -> (match (_35_2) with
| (_35_51, Some (FStar_Syntax_Syntax.Implicit (_35_53))) -> begin
false
end
| _35_58 -> begin
true
end)))))

# 113 "FStar.Syntax.Print.fst"
let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _116_34 = (FStar_Syntax_Subst.compress e)
in _116_34.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(
# 117 "FStar.Syntax.Print.fst"
let args = (filter_imp args)
in (
# 118 "FStar.Syntax.Print.fst"
let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = 2)) then begin
(match ((let _116_35 = (FStar_List.nth exps 1)
in (reconstruct_lex _116_35))) with
| Some (xs) -> begin
(let _116_37 = (let _116_36 = (FStar_List.nth exps 0)
in (_116_36)::xs)
in Some (_116_37))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _35_70 -> begin
if (is_lex_top e) then begin
Some ([])
end else begin
None
end
end))

# 124 "FStar.Syntax.Print.fst"
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

# 129 "FStar.Syntax.Print.fst"
let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _116_51 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _116_51)))

# 132 "FStar.Syntax.Print.fst"
let infix_prim_op_to_string = (fun e -> (let _116_53 = (get_lid e)
in (find_lid _116_53 infix_prim_ops)))

# 134 "FStar.Syntax.Print.fst"
let unary_prim_op_to_string = (fun e -> (let _116_55 = (get_lid e)
in (find_lid _116_55 unary_prim_ops)))

# 135 "FStar.Syntax.Print.fst"
let quant_to_string = (fun t -> (let _116_57 = (get_lid t)
in (find_lid _116_57 quants)))

# 136 "FStar.Syntax.Print.fst"
let rec sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_ST.read FStar_Options.print_real_names) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)

# 141 "FStar.Syntax.Print.fst"
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
| FStar_Const.Const_string (bytes, _35_98) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_35_102) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x) -> begin
x
end
| FStar_Const.Const_int64 (_35_107) -> begin
"<int64>"
end
| FStar_Const.Const_uint8 (_35_110) -> begin
"<uint8>"
end
| FStar_Const.Const_range (r) -> begin
(FStar_Range.string_of_range r)
end))

# 156 "FStar.Syntax.Print.fst"
let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun _35_3 -> (match (_35_3) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l)
end))

# 160 "FStar.Syntax.Print.fst"
let tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _116_66 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _116_66))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _116_67 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _116_67))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _116_68 = (lid_to_string (Prims.fst x).FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _116_68))
end
| FStar_Syntax_Syntax.Tm_uinst (_35_127) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (_35_130) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (_35_133) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (_35_136) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (_35_139) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (_35_142) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (_35_145) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (_35_148) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (_35_151) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (_35_154) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (_35_157) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (_35_160, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
"Tm_delayed"
end
| Some (_35_166) -> begin
"Tm_delayed-resolved"
end)
end
| FStar_Syntax_Syntax.Tm_meta (_35_169) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))

# 183 "FStar.Syntax.Print.fst"
let uvar_to_string = (fun u -> if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _116_73 = (let _116_72 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _116_72 FStar_Util.string_of_int))
in (Prims.strcat "?" _116_73))
end)

# 185 "FStar.Syntax.Print.fst"
let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_unif (u) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(let _116_76 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _116_76))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _116_77 = (univ_to_string u)
in (FStar_Util.format1 "(S %s)" _116_77))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _116_79 = (let _116_78 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _116_78 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _116_79))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))

# 194 "FStar.Syntax.Print.fst"
let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _116_82 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _116_82 (FStar_String.concat ", "))))

# 196 "FStar.Syntax.Print.fst"
let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _116_86 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _116_86 (FStar_String.concat ", "))))

# 198 "FStar.Syntax.Print.fst"
let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun _35_4 -> (match (_35_4) with
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
(let _116_89 = (lid_to_string l)
in (FStar_Util.format1 "default %s" _116_89))
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(let _116_90 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _116_90))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _116_91 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _116_91 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(let _116_93 = (let _116_92 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _116_92 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordType %s)" _116_93))
end
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
(let _116_95 = (let _116_94 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _116_94 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordConstructor %s)" _116_95))
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

# 218 "FStar.Syntax.Print.fst"
let quals_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| _35_220 -> begin
(let _116_99 = (let _116_98 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _116_98 (FStar_String.concat " ")))
in (Prims.strcat _116_99 " "))
end))

# 221 "FStar.Syntax.Print.fst"
let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (
# 229 "FStar.Syntax.Print.fst"
let x = (FStar_Syntax_Subst.compress x)
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_35_224) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_35_227, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(
# 235 "FStar.Syntax.Print.fst"
let pats = (let _116_124 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _116_123 = (FStar_All.pipe_right args (FStar_List.map (fun _35_240 -> (match (_35_240) with
| (t, _35_239) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _116_123 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _116_124 (FStar_String.concat "\\/")))
in (let _116_125 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _116_125)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _35_244) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, _35_255) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _116_126 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _116_126))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _116_128 = (binders_to_string " -> " bs)
in (let _116_127 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _116_128 _116_127)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (l) when (FStar_ST.read FStar_Options.print_implicits) -> begin
(let _116_132 = (binders_to_string " " bs)
in (let _116_131 = (term_to_string t2)
in (let _116_130 = (let _116_129 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _116_129))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _116_132 _116_131 _116_130))))
end
| _35_274 -> begin
(let _116_134 = (binders_to_string " " bs)
in (let _116_133 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _116_134 _116_133)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _116_137 = (bv_to_string xt)
in (let _116_136 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _116_135 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _116_137 _116_136 _116_135))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _116_139 = (term_to_string t)
in (let _116_138 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _116_139 _116_138)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _116_141 = (lbs_to_string [] lbs)
in (let _116_140 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _116_141 _116_140)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _35_290) -> begin
(let _116_143 = (term_to_string e)
in (let _116_142 = (term_to_string t)
in (FStar_Util.format2 "(%s : %s)" _116_143 _116_142)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _116_151 = (term_to_string head)
in (let _116_150 = (let _116_149 = (FStar_All.pipe_right branches (FStar_List.map (fun _35_300 -> (match (_35_300) with
| (p, wopt, e) -> begin
(let _116_148 = (FStar_All.pipe_right p pat_to_string)
in (let _116_147 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _116_145 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _116_145))
end)
in (let _116_146 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _116_148 _116_147 _116_146))))
end))))
in (FStar_Util.concat_l "\n\t|" _116_149))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _116_151 _116_150)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _116_153 = (term_to_string t)
in (let _116_152 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _116_153 _116_152)))
end else begin
(term_to_string t)
end
end
| _35_309 -> begin
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _116_158 = (fv_to_string l)
in (let _116_157 = (let _116_156 = (FStar_List.map (fun _35_317 -> (match (_35_317) with
| (x, b) -> begin
(
# 273 "FStar.Syntax.Print.fst"
let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _116_156 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _116_158 _116_157)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _35_321) -> begin
(let _116_159 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _116_159))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(bv_to_string x)
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _116_160 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _116_160))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _116_161 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _116_161))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (
# 282 "FStar.Syntax.Print.fst"
let lbs = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _116_167 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 284 "FStar.Syntax.Print.fst"
let _35_337 = (let _116_165 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _116_165))
in (match (_35_337) with
| (us, td) -> begin
(
# 285 "FStar.Syntax.Print.fst"
let _35_355 = (match ((let _116_166 = (FStar_Syntax_Subst.compress td)
in _116_166.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_35_339, (t, _35_346)::(d, _35_342)::[]) -> begin
(t, d)
end
| _35_352 -> begin
(FStar_All.failwith "Impossibe")
end)
in (match (_35_355) with
| (t, d) -> begin
(
# 288 "FStar.Syntax.Print.fst"
let _35_356 = lb
in {FStar_Syntax_Syntax.lbname = _35_356.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _35_356.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in ((Prims.fst lbs), _116_167))
end else begin
lbs
end
in (let _116_177 = (quals_to_string quals)
in (let _116_176 = (let _116_175 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _116_174 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _116_173 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _116_170 = (let _116_169 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat "<" _116_169))
in (Prims.strcat _116_170 ">"))
end else begin
""
end
in (let _116_172 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _116_171 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _116_174 _116_173 _116_172 _116_171))))))))
in (FStar_Util.concat_l "\n and " _116_175))
in (FStar_Util.format3 "%slet %s %s" _116_177 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _116_176)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _116_180 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _116_179 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _116_180 _116_179))))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s _35_5 -> (match (_35_5) with
| Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
(Prims.strcat "#." s)
end
| Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _35_372 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (
# 320 "FStar.Syntax.Print.fst"
let _35_377 = b
in (match (_35_377) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(term_to_string a.FStar_Syntax_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_bound_var_types)))) then begin
(let _116_185 = (nm_to_string a)
in (imp_to_string _116_185 imp))
end else begin
(let _116_189 = (let _116_188 = (let _116_186 = (nm_to_string a)
in (Prims.strcat _116_186 ":"))
in (let _116_187 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat _116_188 _116_187)))
in (imp_to_string _116_189 imp))
end
end
end)))
and binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (
# 331 "FStar.Syntax.Print.fst"
let bs = if (FStar_ST.read FStar_Options.print_implicits) then begin
bs
end else begin
(filter_imp bs)
end
in if (sep = " -> ") then begin
(let _116_194 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _116_194 (FStar_String.concat sep)))
end else begin
(let _116_195 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _116_195 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _35_6 -> (match (_35_6) with
| (a, imp) -> begin
(let _116_197 = (term_to_string a)
in (imp_to_string _116_197 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (
# 340 "FStar.Syntax.Print.fst"
let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _116_199 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _116_199 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(match ((let _116_201 = (FStar_Syntax_Subst.compress t)
in _116_201.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_35_393) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _35_396 -> begin
(let _116_202 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _116_202))
end)
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(match ((let _116_203 = (FStar_Syntax_Subst.compress t)
in _116_203.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_35_400) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _35_403 -> begin
(let _116_204 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _116_204))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 356 "FStar.Syntax.Print.fst"
let basic = if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _35_7 -> (match (_35_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _35_409 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args)))) then begin
(let _116_206 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _116_206))
end else begin
if (((not ((FStar_ST.read FStar_Options.print_effect_args))) && (not ((FStar_ST.read FStar_Options.print_implicits)))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _35_8 -> (match (_35_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _35_413 -> begin
false
end))))) then begin
(let _116_208 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _116_208))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _116_212 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _116_211 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _116_210 = (let _116_209 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _116_209 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _116_212 _116_211 _116_210))))
end else begin
(let _116_214 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _116_213 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _116_214 _116_213)))
end
end
end
end
in (
# 369 "FStar.Syntax.Print.fst"
let dec = (let _116_218 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _35_9 -> (match (_35_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _116_217 = (let _116_216 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _116_216))
in (_116_217)::[])
end
| _35_419 -> begin
[]
end))))
in (FStar_All.pipe_right _116_218 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))

# 374 "FStar.Syntax.Print.fst"
let tscheme_to_string : (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  Prims.string = (fun _35_424 -> (match (_35_424) with
| (us, t) -> begin
(let _116_223 = (univ_names_to_string us)
in (let _116_222 = (term_to_string t)
in (FStar_Util.format2 "<%s> %s" _116_223 _116_222)))
end))

# 388 "FStar.Syntax.Print.fst"
let eff_decl_to_string : FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun ed -> (let _116_259 = (let _116_258 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _116_257 = (let _116_256 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (let _116_255 = (let _116_254 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _116_253 = (let _116_252 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _116_251 = (let _116_250 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret)
in (let _116_249 = (let _116_248 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _116_247 = (let _116_246 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wlp)
in (let _116_245 = (let _116_244 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _116_243 = (let _116_242 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _116_241 = (let _116_240 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wlp)
in (let _116_239 = (let _116_238 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_binop)
in (let _116_237 = (let _116_236 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_as_type)
in (let _116_235 = (let _116_234 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _116_233 = (let _116_232 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _116_231 = (let _116_230 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _116_229 = (let _116_228 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _116_227 = (let _116_226 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (_116_226)::[])
in (_116_228)::_116_227))
in (_116_230)::_116_229))
in (_116_232)::_116_231))
in (_116_234)::_116_233))
in (_116_236)::_116_235))
in (_116_238)::_116_237))
in (_116_240)::_116_239))
in (_116_242)::_116_241))
in (_116_244)::_116_243))
in (_116_246)::_116_245))
in (_116_248)::_116_247))
in (_116_250)::_116_249))
in (_116_252)::_116_251))
in (_116_254)::_116_253))
in (_116_256)::_116_255))
in (_116_258)::_116_257))
in (FStar_Util.format "new_effect { %s<%s> %s : %s \n\tret         = %s\n; bind_wp     = %s\n; bind_wlp    = %s\n; if_then_else= %s\n; ite_wp      = %s\n; ite_wlp     = %s\n; wp_binop    = %s\n; wp_as_type  = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s}\n" _116_259)))

# 421 "FStar.Syntax.Print.fst"
let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions, _35_429) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _35_435) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _35_443, _35_445, quals, _35_448) -> begin
(let _116_264 = (quals_to_string quals)
in (let _116_263 = (binders_to_string " " tps)
in (let _116_262 = (term_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _116_264 lid.FStar_Ident.str _116_263 _116_262))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _35_455, _35_457, _35_459, _35_461, _35_463) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(
# 434 "FStar.Syntax.Print.fst"
let _35_468 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_35_468) with
| (univs, t) -> begin
(let _116_266 = (univ_names_to_string univs)
in (let _116_265 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _116_266 lid.FStar_Ident.str _116_265)))
end))
end else begin
(let _116_267 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _116_267))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _35_474) -> begin
(
# 438 "FStar.Syntax.Print.fst"
let _35_479 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_35_479) with
| (univs, t) -> begin
(let _116_271 = (quals_to_string quals)
in (let _116_270 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _116_268 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _116_268))
end else begin
""
end
in (let _116_269 = (term_to_string t)
in (FStar_Util.format4 "%s val %s %s : %s" _116_271 lid.FStar_Ident.str _116_270 _116_269))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _35_483, _35_485) -> begin
(let _116_272 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _116_272))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _35_490, _35_492, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _35_498) -> begin
(let _116_273 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _116_273))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _35_503, _35_505, _35_507) -> begin
(let _116_274 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _116_274 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _35_512) -> begin
(eff_decl_to_string ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(
# 450 "FStar.Syntax.Print.fst"
let _35_521 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst se.FStar_Syntax_Syntax.lift) (Prims.snd se.FStar_Syntax_Syntax.lift))
in (match (_35_521) with
| (us, t) -> begin
(let _116_278 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _116_277 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _116_276 = (univ_names_to_string us)
in (let _116_275 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _116_278 _116_277 _116_276 _116_275)))))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _35_527, _35_529) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(
# 456 "FStar.Syntax.Print.fst"
let _35_534 = (let _116_279 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _116_279))
in (match (_35_534) with
| (univs, t) -> begin
(
# 457 "FStar.Syntax.Print.fst"
let _35_543 = (match ((let _116_280 = (FStar_Syntax_Subst.compress t)
in _116_280.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(bs, c)
end
| _35_540 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_35_543) with
| (tps, c) -> begin
(let _116_284 = (sli l)
in (let _116_283 = (univ_names_to_string univs)
in (let _116_282 = (binders_to_string " " tps)
in (let _116_281 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _116_284 _116_283 _116_282 _116_281)))))
end))
end))
end else begin
(let _116_287 = (sli l)
in (let _116_286 = (binders_to_string " " tps)
in (let _116_285 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _116_287 _116_286 _116_285))))
end
end))

# 461 "FStar.Syntax.Print.fst"
let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _116_292 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _116_292 msg)))

# 463 "FStar.Syntax.Print.fst"
let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_35_548, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (l); FStar_Syntax_Syntax.lbunivs = _35_555; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _35_552; FStar_Syntax_Syntax.lbdef = _35_550}::[]), _35_562, _35_564, _35_566) -> begin
(let _116_295 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Ident.str _116_295))
end
| _35_570 -> begin
(let _116_298 = (let _116_297 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _116_297 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _116_298 (FStar_String.concat ", ")))
end))

# 467 "FStar.Syntax.Print.fst"
let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _116_303 = (sli m.FStar_Syntax_Syntax.name)
in (let _116_302 = (let _116_301 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _116_301 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _116_303 _116_302))))

# 470 "FStar.Syntax.Print.fst"
let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _35_10 -> (match (_35_10) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(let _116_307 = (FStar_Util.string_of_int i)
in (let _116_306 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _116_307 _116_306)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _116_309 = (bv_to_string x)
in (let _116_308 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _116_309 _116_308)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _116_311 = (bv_to_string x)
in (let _116_310 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _116_311 _116_310)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _116_313 = (FStar_Util.string_of_int i)
in (let _116_312 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _116_313 _116_312)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _116_314 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _116_314))
end))

# 477 "FStar.Syntax.Print.fst"
let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _116_317 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _116_317 (FStar_String.concat "; "))))




