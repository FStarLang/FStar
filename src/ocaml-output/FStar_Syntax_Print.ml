
open Prims
# 46 "FStar.Syntax.Print.fst"
let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> l.FStar_Ident.str)

# 48 "FStar.Syntax.Print.fst"
let fv_to_string = (fun fv -> (lid_to_string (Prims.fst fv).FStar_Syntax_Syntax.v))

# 50 "FStar.Syntax.Print.fst"
let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _117_6 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "#") _117_6)))

# 52 "FStar.Syntax.Print.fst"
let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> if (FStar_ST.read FStar_Options.print_real_names) then begin
(bv_to_string bv)
end else begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)

# 57 "FStar.Syntax.Print.fst"
let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _117_11 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "@") _117_11)))

# 60 "FStar.Syntax.Print.fst"
let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.op_Addition, "+"))::((FStar_Syntax_Const.op_Subtraction, "-"))::((FStar_Syntax_Const.op_Multiply, "*"))::((FStar_Syntax_Const.op_Division, "/"))::((FStar_Syntax_Const.op_Eq, "="))::((FStar_Syntax_Const.op_ColonEq, ":="))::((FStar_Syntax_Const.op_notEq, "<>"))::((FStar_Syntax_Const.op_And, "&&"))::((FStar_Syntax_Const.op_Or, "||"))::((FStar_Syntax_Const.op_LTE, "<="))::((FStar_Syntax_Const.op_GTE, ">="))::((FStar_Syntax_Const.op_LT, "<"))::((FStar_Syntax_Const.op_GT, ">"))::((FStar_Syntax_Const.op_Modulus, "mod"))::((FStar_Syntax_Const.and_lid, "/\\"))::((FStar_Syntax_Const.or_lid, "\\/"))::((FStar_Syntax_Const.imp_lid, "==>"))::((FStar_Syntax_Const.iff_lid, "<==>"))::((FStar_Syntax_Const.precedes_lid, "<<"))::((FStar_Syntax_Const.eq2_lid, "=="))::[]

# 83 "FStar.Syntax.Print.fst"
let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.op_Negation, "not"))::((FStar_Syntax_Const.op_Minus, "-"))::((FStar_Syntax_Const.not_lid, "~"))::[]

# 89 "FStar.Syntax.Print.fst"
let is_prim_op = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _35_21) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v)))
end
| _35_25 -> begin
false
end))

# 93 "FStar.Syntax.Print.fst"
let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _35_29) -> begin
fv.FStar_Syntax_Syntax.v
end
| _35_33 -> begin
(FStar_All.failwith "get_lid")
end))

# 97 "FStar.Syntax.Print.fst"
let is_infix_prim_op : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split infix_prim_ops)) e))

# 98 "FStar.Syntax.Print.fst"
let is_unary_prim_op : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split unary_prim_ops)) e))

# 100 "FStar.Syntax.Print.fst"
let quants : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.forall_lid, "forall"))::((FStar_Syntax_Const.exists_lid, "exists"))::[]

# 104 "FStar.Syntax.Print.fst"
type exp =
FStar_Syntax_Syntax.term

# 106 "FStar.Syntax.Print.fst"
let is_b2t : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op ((FStar_Syntax_Const.b2t_lid)::[]) t))

# 107 "FStar.Syntax.Print.fst"
let is_quant : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op (Prims.fst (FStar_List.split quants)) t))

# 108 "FStar.Syntax.Print.fst"
let is_ite : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op ((FStar_Syntax_Const.ite_lid)::[]) t))

# 110 "FStar.Syntax.Print.fst"
let is_lex_cons : exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Syntax_Const.lexcons_lid)::[]) f))

# 111 "FStar.Syntax.Print.fst"
let is_lex_top : exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Syntax_Const.lextop_lid)::[]) f))

# 112 "FStar.Syntax.Print.fst"
let is_inr = (fun _35_1 -> (match (_35_1) with
| FStar_Util.Inl (_35_43) -> begin
false
end
| FStar_Util.Inr (_35_46) -> begin
true
end))

# 113 "FStar.Syntax.Print.fst"
let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _35_2 -> (match (_35_2) with
| (_35_51, Some (FStar_Syntax_Syntax.Implicit (_35_53))) -> begin
false
end
| _35_58 -> begin
true
end)))))

# 114 "FStar.Syntax.Print.fst"
let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _117_34 = (FStar_Syntax_Subst.compress e)
in _117_34.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(
# 117 "FStar.Syntax.Print.fst"
let args = (filter_imp args)
in (
# 118 "FStar.Syntax.Print.fst"
let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = 2)) then begin
(match ((let _117_35 = (FStar_List.nth exps 1)
in (reconstruct_lex _117_35))) with
| Some (xs) -> begin
(let _117_37 = (let _117_36 = (FStar_List.nth exps 0)
in (_117_36)::xs)
in Some (_117_37))
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

# 127 "FStar.Syntax.Print.fst"
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

# 131 "FStar.Syntax.Print.fst"
let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _117_51 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _117_51)))

# 134 "FStar.Syntax.Print.fst"
let infix_prim_op_to_string = (fun e -> (let _117_53 = (get_lid e)
in (find_lid _117_53 infix_prim_ops)))

# 135 "FStar.Syntax.Print.fst"
let unary_prim_op_to_string = (fun e -> (let _117_55 = (get_lid e)
in (find_lid _117_55 unary_prim_ops)))

# 136 "FStar.Syntax.Print.fst"
let quant_to_string = (fun t -> (let _117_57 = (get_lid t)
in (find_lid _117_57 quants)))

# 138 "FStar.Syntax.Print.fst"
let rec sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_ST.read FStar_Options.print_real_names) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)

# 144 "FStar.Syntax.Print.fst"
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
end))

# 157 "FStar.Syntax.Print.fst"
let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun _35_3 -> (match (_35_3) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l)
end))

# 161 "FStar.Syntax.Print.fst"
let tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _117_66 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _117_66))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _117_67 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _117_67))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _117_68 = (lid_to_string (Prims.fst x).FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _117_68))
end
| FStar_Syntax_Syntax.Tm_uinst (_35_125) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (_35_128) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (_35_131) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (_35_134) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (_35_137) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (_35_140) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (_35_143) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (_35_146) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (_35_149) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (_35_152) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (_35_155) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (_35_158, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
"Tm_delayed"
end
| Some (_35_164) -> begin
"Tm_delayed-resolved"
end)
end
| FStar_Syntax_Syntax.Tm_meta (_35_167) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))

# 184 "FStar.Syntax.Print.fst"
let uvar_to_string = (fun u -> if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _117_73 = (let _117_72 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _117_72 FStar_Util.string_of_int))
in (Prims.strcat "?" _117_73))
end)

# 186 "FStar.Syntax.Print.fst"
let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_unif (u) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(let _117_76 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _117_76))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _117_77 = (univ_to_string u)
in (FStar_Util.format1 "(S %s)" _117_77))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _117_79 = (let _117_78 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _117_78 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _117_79))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))

# 195 "FStar.Syntax.Print.fst"
let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _117_82 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _117_82 (FStar_String.concat ", "))))

# 197 "FStar.Syntax.Print.fst"
let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _117_86 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _117_86 (FStar_String.concat ", "))))

# 199 "FStar.Syntax.Print.fst"
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
(let _117_89 = (lid_to_string l)
in (FStar_Util.format1 "default %s" _117_89))
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(let _117_90 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _117_90))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _117_91 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _117_91 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(let _117_93 = (let _117_92 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _117_92 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordType %s)" _117_93))
end
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
(let _117_95 = (let _117_94 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _117_94 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordConstructor %s)" _117_95))
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
| _35_218 -> begin
(let _117_99 = (let _117_98 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _117_98 (FStar_String.concat " ")))
in (Prims.strcat _117_99 " "))
end))

# 227 "FStar.Syntax.Print.fst"
let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (
# 228 "FStar.Syntax.Print.fst"
let x = (FStar_Syntax_Subst.compress x)
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_35_222) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_35_225, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(
# 234 "FStar.Syntax.Print.fst"
let pats = (let _117_124 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _117_123 = (FStar_All.pipe_right args (FStar_List.map (fun _35_238 -> (match (_35_238) with
| (t, _35_237) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _117_123 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _117_124 (FStar_String.concat "\\/")))
in (let _117_125 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _117_125)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _35_242) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, _35_253) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _117_126 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _117_126))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _117_128 = (binders_to_string " -> " bs)
in (let _117_127 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _117_128 _117_127)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (l) when (FStar_ST.read FStar_Options.print_implicits) -> begin
(let _117_132 = (binders_to_string " " bs)
in (let _117_131 = (term_to_string t2)
in (let _117_130 = (let _117_129 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _117_129))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _117_132 _117_131 _117_130))))
end
| _35_272 -> begin
(let _117_134 = (binders_to_string " " bs)
in (let _117_133 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _117_134 _117_133)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _117_137 = (bv_to_string xt)
in (let _117_136 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _117_135 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _117_137 _117_136 _117_135))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _117_139 = (term_to_string t)
in (let _117_138 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _117_139 _117_138)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _117_141 = (lbs_to_string [] lbs)
in (let _117_140 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _117_141 _117_140)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _35_288) -> begin
(let _117_143 = (term_to_string e)
in (let _117_142 = (term_to_string t)
in (FStar_Util.format2 "(%s : %s)" _117_143 _117_142)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _117_151 = (term_to_string head)
in (let _117_150 = (let _117_149 = (FStar_All.pipe_right branches (FStar_List.map (fun _35_298 -> (match (_35_298) with
| (p, wopt, e) -> begin
(let _117_148 = (FStar_All.pipe_right p pat_to_string)
in (let _117_147 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _117_145 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _117_145))
end)
in (let _117_146 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _117_148 _117_147 _117_146))))
end))))
in (FStar_Util.concat_l "\n\t|" _117_149))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _117_151 _117_150)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _117_153 = (term_to_string t)
in (let _117_152 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _117_153 _117_152)))
end else begin
(term_to_string t)
end
end
| _35_307 -> begin
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _117_158 = (fv_to_string l)
in (let _117_157 = (let _117_156 = (FStar_List.map (fun _35_315 -> (match (_35_315) with
| (x, b) -> begin
(
# 272 "FStar.Syntax.Print.fst"
let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _117_156 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _117_158 _117_157)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _35_319) -> begin
(let _117_159 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _117_159))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(bv_to_string x)
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _117_160 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _117_160))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _117_161 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _117_161))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (
# 281 "FStar.Syntax.Print.fst"
let lbs = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _117_167 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 283 "FStar.Syntax.Print.fst"
let _35_335 = (let _117_165 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _117_165))
in (match (_35_335) with
| (us, td) -> begin
(
# 284 "FStar.Syntax.Print.fst"
let _35_353 = (match ((let _117_166 = (FStar_Syntax_Subst.compress td)
in _117_166.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_35_337, (t, _35_344)::(d, _35_340)::[]) -> begin
(t, d)
end
| _35_350 -> begin
(FStar_All.failwith "Impossibe")
end)
in (match (_35_353) with
| (t, d) -> begin
(
# 287 "FStar.Syntax.Print.fst"
let _35_354 = lb
in {FStar_Syntax_Syntax.lbname = _35_354.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _35_354.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in ((Prims.fst lbs), _117_167))
end else begin
lbs
end
in (let _117_177 = (quals_to_string quals)
in (let _117_176 = (let _117_175 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _117_174 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _117_173 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _117_170 = (let _117_169 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat "<" _117_169))
in (Prims.strcat _117_170 ">"))
end else begin
""
end
in (let _117_172 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _117_171 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _117_174 _117_173 _117_172 _117_171))))))))
in (FStar_Util.concat_l "\n and " _117_175))
in (FStar_Util.format3 "%slet %s %s" _117_177 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _117_176)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _117_180 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _117_179 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _117_180 _117_179))))
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
| _35_370 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (
# 319 "FStar.Syntax.Print.fst"
let _35_375 = b
in (match (_35_375) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(term_to_string a.FStar_Syntax_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_bound_var_types)))) then begin
(let _117_185 = (nm_to_string a)
in (imp_to_string _117_185 imp))
end else begin
(let _117_189 = (let _117_188 = (let _117_186 = (nm_to_string a)
in (Prims.strcat _117_186 ":"))
in (let _117_187 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat _117_188 _117_187)))
in (imp_to_string _117_189 imp))
end
end
end)))
and binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (
# 330 "FStar.Syntax.Print.fst"
let bs = if (FStar_ST.read FStar_Options.print_implicits) then begin
bs
end else begin
(filter_imp bs)
end
in if (sep = " -> ") then begin
(let _117_194 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _117_194 (FStar_String.concat sep)))
end else begin
(let _117_195 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _117_195 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _35_6 -> (match (_35_6) with
| (a, imp) -> begin
(let _117_197 = (term_to_string a)
in (imp_to_string _117_197 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (
# 339 "FStar.Syntax.Print.fst"
let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _117_199 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _117_199 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(match ((let _117_201 = (FStar_Syntax_Subst.compress t)
in _117_201.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_35_391) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _35_394 -> begin
(let _117_202 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _117_202))
end)
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(match ((let _117_203 = (FStar_Syntax_Subst.compress t)
in _117_203.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_35_398) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _35_401 -> begin
(let _117_204 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _117_204))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 355 "FStar.Syntax.Print.fst"
let basic = if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _35_7 -> (match (_35_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _35_407 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args)))) then begin
(let _117_206 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _117_206))
end else begin
if (((not ((FStar_ST.read FStar_Options.print_effect_args))) && (not ((FStar_ST.read FStar_Options.print_implicits)))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _35_8 -> (match (_35_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _35_411 -> begin
false
end))))) then begin
(let _117_208 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _117_208))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _117_212 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _117_211 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _117_210 = (let _117_209 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _117_209 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _117_212 _117_211 _117_210))))
end else begin
(let _117_214 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _117_213 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _117_214 _117_213)))
end
end
end
end
in (
# 368 "FStar.Syntax.Print.fst"
let dec = (let _117_218 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _35_9 -> (match (_35_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _117_217 = (let _117_216 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _117_216))
in (_117_217)::[])
end
| _35_417 -> begin
[]
end))))
in (FStar_All.pipe_right _117_218 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))

# 387 "FStar.Syntax.Print.fst"
let tscheme_to_string : (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  Prims.string = (fun _35_422 -> (match (_35_422) with
| (us, t) -> begin
(let _117_223 = (univ_names_to_string us)
in (let _117_222 = (term_to_string t)
in (FStar_Util.format2 "<%s> %s" _117_223 _117_222)))
end))

# 389 "FStar.Syntax.Print.fst"
let eff_decl_to_string : FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun ed -> (let _117_259 = (let _117_258 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _117_257 = (let _117_256 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (let _117_255 = (let _117_254 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _117_253 = (let _117_252 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _117_251 = (let _117_250 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret)
in (let _117_249 = (let _117_248 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _117_247 = (let _117_246 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wlp)
in (let _117_245 = (let _117_244 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _117_243 = (let _117_242 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _117_241 = (let _117_240 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wlp)
in (let _117_239 = (let _117_238 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_binop)
in (let _117_237 = (let _117_236 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_as_type)
in (let _117_235 = (let _117_234 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _117_233 = (let _117_232 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _117_231 = (let _117_230 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _117_229 = (let _117_228 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _117_227 = (let _117_226 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (_117_226)::[])
in (_117_228)::_117_227))
in (_117_230)::_117_229))
in (_117_232)::_117_231))
in (_117_234)::_117_233))
in (_117_236)::_117_235))
in (_117_238)::_117_237))
in (_117_240)::_117_239))
in (_117_242)::_117_241))
in (_117_244)::_117_243))
in (_117_246)::_117_245))
in (_117_248)::_117_247))
in (_117_250)::_117_249))
in (_117_252)::_117_251))
in (_117_254)::_117_253))
in (_117_256)::_117_255))
in (_117_258)::_117_257))
in (FStar_Util.format "new_effect { %s<%s> %s : %s \n\tret         = %s\n; bind_wp     = %s\n; bind_wlp    = %s\n; if_then_else= %s\n; ite_wp      = %s\n; ite_wlp     = %s\n; wp_binop    = %s\n; wp_as_type  = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s}\n" _117_259)))

# 422 "FStar.Syntax.Print.fst"
let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions, _35_427) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _35_433) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _35_441, _35_443, quals, _35_446) -> begin
(let _117_264 = (quals_to_string quals)
in (let _117_263 = (binders_to_string " " tps)
in (let _117_262 = (term_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _117_264 lid.FStar_Ident.str _117_263 _117_262))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _35_453, _35_455, _35_457, _35_459, _35_461) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(
# 433 "FStar.Syntax.Print.fst"
let _35_466 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_35_466) with
| (univs, t) -> begin
(let _117_266 = (univ_names_to_string univs)
in (let _117_265 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _117_266 lid.FStar_Ident.str _117_265)))
end))
end else begin
(let _117_267 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _117_267))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _35_472) -> begin
(
# 437 "FStar.Syntax.Print.fst"
let _35_477 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_35_477) with
| (univs, t) -> begin
(let _117_271 = (quals_to_string quals)
in (let _117_270 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _117_268 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _117_268))
end else begin
""
end
in (let _117_269 = (term_to_string t)
in (FStar_Util.format4 "%s val %s %s : %s" _117_271 lid.FStar_Ident.str _117_270 _117_269))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _35_481, _35_483) -> begin
(let _117_272 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _117_272))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _35_488, _35_490, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _35_496) -> begin
(let _117_273 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _117_273))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _35_501, _35_503, _35_505) -> begin
(let _117_274 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _117_274 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _35_510) -> begin
(eff_decl_to_string ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(
# 449 "FStar.Syntax.Print.fst"
let _35_519 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst se.FStar_Syntax_Syntax.lift) (Prims.snd se.FStar_Syntax_Syntax.lift))
in (match (_35_519) with
| (us, t) -> begin
(let _117_278 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _117_277 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _117_276 = (univ_names_to_string us)
in (let _117_275 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _117_278 _117_277 _117_276 _117_275)))))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _35_525, _35_527) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(
# 455 "FStar.Syntax.Print.fst"
let _35_532 = (let _117_279 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _117_279))
in (match (_35_532) with
| (univs, t) -> begin
(
# 456 "FStar.Syntax.Print.fst"
let _35_541 = (match ((let _117_280 = (FStar_Syntax_Subst.compress t)
in _117_280.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(bs, c)
end
| _35_538 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_35_541) with
| (tps, c) -> begin
(let _117_284 = (sli l)
in (let _117_283 = (univ_names_to_string univs)
in (let _117_282 = (binders_to_string " " tps)
in (let _117_281 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _117_284 _117_283 _117_282 _117_281)))))
end))
end))
end else begin
(let _117_287 = (sli l)
in (let _117_286 = (binders_to_string " " tps)
in (let _117_285 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _117_287 _117_286 _117_285))))
end
end))

# 462 "FStar.Syntax.Print.fst"
let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _117_292 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _117_292 msg)))

# 464 "FStar.Syntax.Print.fst"
let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_35_546, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (l); FStar_Syntax_Syntax.lbunivs = _35_553; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _35_550; FStar_Syntax_Syntax.lbdef = _35_548}::[]), _35_560, _35_562, _35_564) -> begin
(let _117_295 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Ident.str _117_295))
end
| _35_568 -> begin
(let _117_298 = (let _117_297 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _117_297 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _117_298 (FStar_String.concat ", ")))
end))

# 468 "FStar.Syntax.Print.fst"
let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _117_303 = (sli m.FStar_Syntax_Syntax.name)
in (let _117_302 = (let _117_301 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _117_301 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _117_303 _117_302))))

# 471 "FStar.Syntax.Print.fst"
let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _35_10 -> (match (_35_10) with
| FStar_Syntax_Syntax.DB (i, t) -> begin
(let _117_307 = (FStar_Util.string_of_int i)
in (let _117_306 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _117_307 _117_306)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _117_309 = (bv_to_string x)
in (let _117_308 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _117_309 _117_308)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _117_311 = (bv_to_string x)
in (let _117_310 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _117_311 _117_310)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _117_313 = (FStar_Util.string_of_int i)
in (let _117_312 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _117_313 _117_312)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _117_314 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _117_314))
end))

# 478 "FStar.Syntax.Print.fst"
let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _117_317 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _117_317 (FStar_String.concat "; "))))




