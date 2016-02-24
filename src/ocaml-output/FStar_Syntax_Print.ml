
open Prims
# 46 "FStar.Syntax.Print.fst"
let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> l.FStar_Ident.str)

# 48 "FStar.Syntax.Print.fst"
let fv_to_string = (fun fv -> (lid_to_string (Prims.fst fv).FStar_Syntax_Syntax.v))

# 50 "FStar.Syntax.Print.fst"
let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _115_6 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "#") _115_6)))

# 52 "FStar.Syntax.Print.fst"
let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> if (FStar_ST.read FStar_Options.print_real_names) then begin
(bv_to_string bv)
end else begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)

# 57 "FStar.Syntax.Print.fst"
let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _115_11 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "@") _115_11)))

# 60 "FStar.Syntax.Print.fst"
let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.op_Addition, "+"))::((FStar_Syntax_Const.op_Subtraction, "-"))::((FStar_Syntax_Const.op_Multiply, "*"))::((FStar_Syntax_Const.op_Division, "/"))::((FStar_Syntax_Const.op_Eq, "="))::((FStar_Syntax_Const.op_ColonEq, ":="))::((FStar_Syntax_Const.op_notEq, "<>"))::((FStar_Syntax_Const.op_And, "&&"))::((FStar_Syntax_Const.op_Or, "||"))::((FStar_Syntax_Const.op_LTE, "<="))::((FStar_Syntax_Const.op_GTE, ">="))::((FStar_Syntax_Const.op_LT, "<"))::((FStar_Syntax_Const.op_GT, ">"))::((FStar_Syntax_Const.op_Modulus, "mod"))::((FStar_Syntax_Const.and_lid, "/\\"))::((FStar_Syntax_Const.or_lid, "\\/"))::((FStar_Syntax_Const.imp_lid, "==>"))::((FStar_Syntax_Const.iff_lid, "<==>"))::((FStar_Syntax_Const.precedes_lid, "<<"))::((FStar_Syntax_Const.eq2_lid, "=="))::[]

# 83 "FStar.Syntax.Print.fst"
let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.op_Negation, "not"))::((FStar_Syntax_Const.op_Minus, "-"))::((FStar_Syntax_Const.not_lid, "~"))::[]

# 89 "FStar.Syntax.Print.fst"
let is_prim_op = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _36_21) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v)))
end
| _36_25 -> begin
false
end))

# 93 "FStar.Syntax.Print.fst"
let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _36_29) -> begin
fv.FStar_Syntax_Syntax.v
end
| _36_33 -> begin
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
let is_inr = (fun _36_1 -> (match (_36_1) with
| FStar_Util.Inl (_36_43) -> begin
false
end
| FStar_Util.Inr (_36_46) -> begin
true
end))

# 113 "FStar.Syntax.Print.fst"
let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _36_2 -> (match (_36_2) with
| (_36_51, Some (FStar_Syntax_Syntax.Implicit (_36_53))) -> begin
false
end
| _36_58 -> begin
true
end)))))

# 114 "FStar.Syntax.Print.fst"
let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _115_34 = (FStar_Syntax_Subst.compress e)
in _115_34.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(
# 117 "FStar.Syntax.Print.fst"
let args = (filter_imp args)
in (
# 118 "FStar.Syntax.Print.fst"
let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = 2)) then begin
(match ((let _115_35 = (FStar_List.nth exps 1)
in (reconstruct_lex _115_35))) with
| Some (xs) -> begin
(let _115_37 = (let _115_36 = (FStar_List.nth exps 0)
in (_115_36)::xs)
in Some (_115_37))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _36_70 -> begin
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
let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _115_51 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _115_51)))

# 134 "FStar.Syntax.Print.fst"
let infix_prim_op_to_string = (fun e -> (let _115_53 = (get_lid e)
in (find_lid _115_53 infix_prim_ops)))

# 135 "FStar.Syntax.Print.fst"
let unary_prim_op_to_string = (fun e -> (let _115_55 = (get_lid e)
in (find_lid _115_55 unary_prim_ops)))

# 136 "FStar.Syntax.Print.fst"
let quant_to_string = (fun t -> (let _115_57 = (get_lid t)
in (find_lid _115_57 quants)))

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
| FStar_Const.Const_string (bytes, _36_98) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_36_102) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x) -> begin
x
end
| FStar_Const.Const_int64 (_36_107) -> begin
"<int64>"
end
| FStar_Const.Const_uint8 (_36_110) -> begin
"<uint8>"
end))

# 157 "FStar.Syntax.Print.fst"
let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun _36_3 -> (match (_36_3) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l)
end))

# 161 "FStar.Syntax.Print.fst"
let tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _115_66 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _115_66))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _115_67 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _115_67))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _115_68 = (lid_to_string (Prims.fst x).FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _115_68))
end
| FStar_Syntax_Syntax.Tm_uinst (_36_125) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (_36_128) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (_36_131) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (_36_134) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (_36_137) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (_36_140) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (_36_143) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (_36_146) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (_36_149) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (_36_152) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (_36_155) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (_36_158, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
"Tm_delayed"
end
| Some (_36_164) -> begin
"Tm_delayed-resolved"
end)
end
| FStar_Syntax_Syntax.Tm_meta (_36_167) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))

# 184 "FStar.Syntax.Print.fst"
let uvar_to_string = (fun u -> if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _115_73 = (let _115_72 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _115_72 FStar_Util.string_of_int))
in (Prims.strcat "?" _115_73))
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
(let _115_76 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _115_76))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _115_77 = (univ_to_string u)
in (FStar_Util.format1 "(S %s)" _115_77))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _115_79 = (let _115_78 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _115_78 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _115_79))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))

# 195 "FStar.Syntax.Print.fst"
let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _115_82 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _115_82 (FStar_String.concat ", "))))

# 197 "FStar.Syntax.Print.fst"
let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _115_86 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _115_86 (FStar_String.concat ", "))))

# 199 "FStar.Syntax.Print.fst"
let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun _36_4 -> (match (_36_4) with
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
(let _115_89 = (lid_to_string l)
in (FStar_Util.format1 "default %s" _115_89))
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(let _115_90 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _115_90))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _115_91 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _115_91 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(let _115_93 = (let _115_92 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _115_92 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordType %s)" _115_93))
end
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
(let _115_95 = (let _115_94 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _115_94 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordConstructor %s)" _115_95))
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
| _36_218 -> begin
(let _115_99 = (let _115_98 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _115_98 (FStar_String.concat " ")))
in (Prims.strcat _115_99 " "))
end))

# 227 "FStar.Syntax.Print.fst"
let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (
# 228 "FStar.Syntax.Print.fst"
let x = (FStar_Syntax_Subst.compress x)
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_36_222) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_36_225, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(
# 234 "FStar.Syntax.Print.fst"
let pats = (let _115_124 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _115_123 = (FStar_All.pipe_right args (FStar_List.map (fun _36_238 -> (match (_36_238) with
| (t, _36_237) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _115_123 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _115_124 (FStar_String.concat "\\/")))
in (let _115_125 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _115_125)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _36_242) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, _36_253) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _115_126 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _115_126))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _115_128 = (binders_to_string " -> " bs)
in (let _115_127 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _115_128 _115_127)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (l) when (FStar_ST.read FStar_Options.print_implicits) -> begin
(let _115_132 = (binders_to_string " " bs)
in (let _115_131 = (term_to_string t2)
in (let _115_130 = (let _115_129 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _115_129))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _115_132 _115_131 _115_130))))
end
| _36_272 -> begin
(let _115_134 = (binders_to_string " " bs)
in (let _115_133 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _115_134 _115_133)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _115_137 = (bv_to_string xt)
in (let _115_136 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _115_135 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _115_137 _115_136 _115_135))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _115_139 = (term_to_string t)
in (let _115_138 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _115_139 _115_138)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _115_141 = (lbs_to_string [] lbs)
in (let _115_140 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _115_141 _115_140)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _36_288) -> begin
(let _115_143 = (term_to_string e)
in (let _115_142 = (term_to_string t)
in (FStar_Util.format2 "(%s : %s)" _115_143 _115_142)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _115_151 = (term_to_string head)
in (let _115_150 = (let _115_149 = (FStar_All.pipe_right branches (FStar_List.map (fun _36_298 -> (match (_36_298) with
| (p, wopt, e) -> begin
(let _115_148 = (FStar_All.pipe_right p pat_to_string)
in (let _115_147 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _115_145 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _115_145))
end)
in (let _115_146 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _115_148 _115_147 _115_146))))
end))))
in (FStar_Util.concat_l "\n\t|" _115_149))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _115_151 _115_150)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _115_153 = (term_to_string t)
in (let _115_152 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _115_153 _115_152)))
end else begin
(term_to_string t)
end
end
| _36_307 -> begin
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _115_158 = (fv_to_string l)
in (let _115_157 = (let _115_156 = (FStar_List.map (fun _36_315 -> (match (_36_315) with
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
in (FStar_All.pipe_right _115_156 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _115_158 _115_157)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _36_319) -> begin
(let _115_159 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _115_159))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(bv_to_string x)
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _115_160 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _115_160))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _115_161 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _115_161))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (
# 281 "FStar.Syntax.Print.fst"
let lbs = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _115_167 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 283 "FStar.Syntax.Print.fst"
let _36_335 = (let _115_165 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _115_165))
in (match (_36_335) with
| (us, td) -> begin
(
# 284 "FStar.Syntax.Print.fst"
let _36_353 = (match ((let _115_166 = (FStar_Syntax_Subst.compress td)
in _115_166.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_36_337, (t, _36_344)::(d, _36_340)::[]) -> begin
(t, d)
end
| _36_350 -> begin
(FStar_All.failwith "Impossibe")
end)
in (match (_36_353) with
| (t, d) -> begin
(
# 287 "FStar.Syntax.Print.fst"
let _36_354 = lb
in {FStar_Syntax_Syntax.lbname = _36_354.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _36_354.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in ((Prims.fst lbs), _115_167))
end else begin
lbs
end
in (let _115_177 = (quals_to_string quals)
in (let _115_176 = (let _115_175 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _115_174 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _115_173 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _115_170 = (let _115_169 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat "<" _115_169))
in (Prims.strcat _115_170 ">"))
end else begin
""
end
in (let _115_172 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _115_171 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _115_174 _115_173 _115_172 _115_171))))))))
in (FStar_Util.concat_l "\n and " _115_175))
in (FStar_Util.format3 "%slet %s %s" _115_177 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _115_176)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _115_180 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _115_179 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _115_180 _115_179))))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s _36_5 -> (match (_36_5) with
| Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
(Prims.strcat "#." s)
end
| Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _36_370 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (
# 319 "FStar.Syntax.Print.fst"
let _36_375 = b
in (match (_36_375) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(term_to_string a.FStar_Syntax_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_bound_var_types)))) then begin
(let _115_185 = (nm_to_string a)
in (imp_to_string _115_185 imp))
end else begin
(let _115_189 = (let _115_188 = (let _115_186 = (nm_to_string a)
in (Prims.strcat _115_186 ":"))
in (let _115_187 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat _115_188 _115_187)))
in (imp_to_string _115_189 imp))
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
(let _115_194 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _115_194 (FStar_String.concat sep)))
end else begin
(let _115_195 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _115_195 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _36_6 -> (match (_36_6) with
| (a, imp) -> begin
(let _115_197 = (term_to_string a)
in (imp_to_string _115_197 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (
# 339 "FStar.Syntax.Print.fst"
let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _115_199 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _115_199 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(match ((let _115_201 = (FStar_Syntax_Subst.compress t)
in _115_201.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_36_391) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _36_394 -> begin
(let _115_202 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _115_202))
end)
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(match ((let _115_203 = (FStar_Syntax_Subst.compress t)
in _115_203.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_36_398) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _36_401 -> begin
(let _115_204 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _115_204))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 355 "FStar.Syntax.Print.fst"
let basic = if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _36_7 -> (match (_36_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _36_407 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args)))) then begin
(let _115_206 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _115_206))
end else begin
if (((not ((FStar_ST.read FStar_Options.print_effect_args))) && (not ((FStar_ST.read FStar_Options.print_implicits)))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _36_8 -> (match (_36_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _36_411 -> begin
false
end))))) then begin
(let _115_208 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _115_208))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _115_212 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _115_211 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _115_210 = (let _115_209 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _115_209 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _115_212 _115_211 _115_210))))
end else begin
(let _115_214 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _115_213 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _115_214 _115_213)))
end
end
end
end
in (
# 368 "FStar.Syntax.Print.fst"
let dec = (let _115_218 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _36_9 -> (match (_36_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _115_217 = (let _115_216 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _115_216))
in (_115_217)::[])
end
| _36_417 -> begin
[]
end))))
in (FStar_All.pipe_right _115_218 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))

# 387 "FStar.Syntax.Print.fst"
let tscheme_to_string : (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  Prims.string = (fun _36_422 -> (match (_36_422) with
| (us, t) -> begin
(let _115_223 = (univ_names_to_string us)
in (let _115_222 = (term_to_string t)
in (FStar_Util.format2 "<%s> %s" _115_223 _115_222)))
end))

# 389 "FStar.Syntax.Print.fst"
let eff_decl_to_string : FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun ed -> (let _115_259 = (let _115_258 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _115_257 = (let _115_256 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (let _115_255 = (let _115_254 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _115_253 = (let _115_252 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _115_251 = (let _115_250 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret)
in (let _115_249 = (let _115_248 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _115_247 = (let _115_246 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wlp)
in (let _115_245 = (let _115_244 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _115_243 = (let _115_242 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _115_241 = (let _115_240 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wlp)
in (let _115_239 = (let _115_238 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_binop)
in (let _115_237 = (let _115_236 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_as_type)
in (let _115_235 = (let _115_234 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _115_233 = (let _115_232 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _115_231 = (let _115_230 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _115_229 = (let _115_228 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _115_227 = (let _115_226 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (_115_226)::[])
in (_115_228)::_115_227))
in (_115_230)::_115_229))
in (_115_232)::_115_231))
in (_115_234)::_115_233))
in (_115_236)::_115_235))
in (_115_238)::_115_237))
in (_115_240)::_115_239))
in (_115_242)::_115_241))
in (_115_244)::_115_243))
in (_115_246)::_115_245))
in (_115_248)::_115_247))
in (_115_250)::_115_249))
in (_115_252)::_115_251))
in (_115_254)::_115_253))
in (_115_256)::_115_255))
in (_115_258)::_115_257))
in (FStar_Util.format "new_effect { %s<%s> %s : %s \n\tret         = %s\n; bind_wp     = %s\n; bind_wlp    = %s\n; if_then_else= %s\n; ite_wp      = %s\n; ite_wlp     = %s\n; wp_binop    = %s\n; wp_as_type  = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s}\n" _115_259)))

# 422 "FStar.Syntax.Print.fst"
let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions, _36_427) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _36_433) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _36_441, _36_443, quals, _36_446) -> begin
(let _115_264 = (quals_to_string quals)
in (let _115_263 = (binders_to_string " " tps)
in (let _115_262 = (term_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _115_264 lid.FStar_Ident.str _115_263 _115_262))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _36_453, _36_455, _36_457, _36_459, _36_461) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(
# 433 "FStar.Syntax.Print.fst"
let _36_466 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_36_466) with
| (univs, t) -> begin
(let _115_266 = (univ_names_to_string univs)
in (let _115_265 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _115_266 lid.FStar_Ident.str _115_265)))
end))
end else begin
(let _115_267 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _115_267))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _36_472) -> begin
(
# 437 "FStar.Syntax.Print.fst"
let _36_477 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_36_477) with
| (univs, t) -> begin
(let _115_271 = (quals_to_string quals)
in (let _115_270 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _115_268 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _115_268))
end else begin
""
end
in (let _115_269 = (term_to_string t)
in (FStar_Util.format4 "%s val %s %s : %s" _115_271 lid.FStar_Ident.str _115_270 _115_269))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _36_481, _36_483) -> begin
(let _115_272 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _115_272))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _36_488, _36_490, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _36_496) -> begin
(let _115_273 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _115_273))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _36_501, _36_503, _36_505) -> begin
(let _115_274 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _115_274 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _36_510) -> begin
(eff_decl_to_string ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(
# 449 "FStar.Syntax.Print.fst"
let _36_519 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst se.FStar_Syntax_Syntax.lift) (Prims.snd se.FStar_Syntax_Syntax.lift))
in (match (_36_519) with
| (us, t) -> begin
(let _115_278 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _115_277 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _115_276 = (univ_names_to_string us)
in (let _115_275 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _115_278 _115_277 _115_276 _115_275)))))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _36_525, _36_527) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(
# 455 "FStar.Syntax.Print.fst"
let _36_532 = (let _115_279 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _115_279))
in (match (_36_532) with
| (univs, t) -> begin
(
# 456 "FStar.Syntax.Print.fst"
let _36_541 = (match ((let _115_280 = (FStar_Syntax_Subst.compress t)
in _115_280.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(bs, c)
end
| _36_538 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_36_541) with
| (tps, c) -> begin
(let _115_284 = (sli l)
in (let _115_283 = (univ_names_to_string univs)
in (let _115_282 = (binders_to_string " " tps)
in (let _115_281 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _115_284 _115_283 _115_282 _115_281)))))
end))
end))
end else begin
(let _115_287 = (sli l)
in (let _115_286 = (binders_to_string " " tps)
in (let _115_285 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _115_287 _115_286 _115_285))))
end
end))

# 462 "FStar.Syntax.Print.fst"
let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _115_292 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _115_292 msg)))

# 464 "FStar.Syntax.Print.fst"
let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_36_546, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (l); FStar_Syntax_Syntax.lbunivs = _36_553; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _36_550; FStar_Syntax_Syntax.lbdef = _36_548}::[]), _36_560, _36_562, _36_564) -> begin
(let _115_295 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Ident.str _115_295))
end
| _36_568 -> begin
(let _115_298 = (let _115_297 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _115_297 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _115_298 (FStar_String.concat ", ")))
end))

# 468 "FStar.Syntax.Print.fst"
let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _115_303 = (sli m.FStar_Syntax_Syntax.name)
in (let _115_302 = (let _115_301 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _115_301 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _115_303 _115_302))))

# 471 "FStar.Syntax.Print.fst"
let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _36_10 -> (match (_36_10) with
| FStar_Syntax_Syntax.DB (i, t) -> begin
(let _115_307 = (FStar_Util.string_of_int i)
in (let _115_306 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _115_307 _115_306)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _115_309 = (bv_to_string x)
in (let _115_308 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _115_309 _115_308)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _115_311 = (bv_to_string x)
in (let _115_310 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _115_311 _115_310)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _115_313 = (FStar_Util.string_of_int i)
in (let _115_312 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _115_313 _115_312)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _115_314 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _115_314))
end))

# 478 "FStar.Syntax.Print.fst"
let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _115_317 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _115_317 (FStar_String.concat "; "))))




