
open Prims
# 49 "FStar.Syntax.Print.fst"
let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> l.FStar_Ident.str)

# 52 "FStar.Syntax.Print.fst"
let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))

# 54 "FStar.Syntax.Print.fst"
let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _120_7 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "#") _120_7)))

# 56 "FStar.Syntax.Print.fst"
let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> if (FStar_ST.read FStar_Options.print_real_names) then begin
(bv_to_string bv)
end else begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)

# 61 "FStar.Syntax.Print.fst"
let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _120_12 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "@") _120_12)))

# 64 "FStar.Syntax.Print.fst"
let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.op_Addition, "+"))::((FStar_Syntax_Const.op_Subtraction, "-"))::((FStar_Syntax_Const.op_Multiply, "*"))::((FStar_Syntax_Const.op_Division, "/"))::((FStar_Syntax_Const.op_Eq, "="))::((FStar_Syntax_Const.op_ColonEq, ":="))::((FStar_Syntax_Const.op_notEq, "<>"))::((FStar_Syntax_Const.op_And, "&&"))::((FStar_Syntax_Const.op_Or, "||"))::((FStar_Syntax_Const.op_LTE, "<="))::((FStar_Syntax_Const.op_GTE, ">="))::((FStar_Syntax_Const.op_LT, "<"))::((FStar_Syntax_Const.op_GT, ">"))::((FStar_Syntax_Const.op_Modulus, "mod"))::((FStar_Syntax_Const.and_lid, "/\\"))::((FStar_Syntax_Const.or_lid, "\\/"))::((FStar_Syntax_Const.imp_lid, "==>"))::((FStar_Syntax_Const.iff_lid, "<==>"))::((FStar_Syntax_Const.precedes_lid, "<<"))::((FStar_Syntax_Const.eq2_lid, "=="))::[]

# 87 "FStar.Syntax.Print.fst"
let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.op_Negation, "not"))::((FStar_Syntax_Const.op_Minus, "-"))::((FStar_Syntax_Const.not_lid, "~"))::[]

# 93 "FStar.Syntax.Print.fst"
let is_prim_op = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
end
| _35_22 -> begin
false
end))

# 97 "FStar.Syntax.Print.fst"
let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| _35_27 -> begin
(FStar_All.failwith "get_lid")
end))

# 101 "FStar.Syntax.Print.fst"
let is_infix_prim_op : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split infix_prim_ops)) e))

# 102 "FStar.Syntax.Print.fst"
let is_unary_prim_op : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split unary_prim_ops)) e))

# 104 "FStar.Syntax.Print.fst"
let quants : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.forall_lid, "forall"))::((FStar_Syntax_Const.exists_lid, "exists"))::[]

# 108 "FStar.Syntax.Print.fst"
type exp =
FStar_Syntax_Syntax.term

# 110 "FStar.Syntax.Print.fst"
let is_b2t : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op ((FStar_Syntax_Const.b2t_lid)::[]) t))

# 111 "FStar.Syntax.Print.fst"
let is_quant : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op (Prims.fst (FStar_List.split quants)) t))

# 112 "FStar.Syntax.Print.fst"
let is_ite : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op ((FStar_Syntax_Const.ite_lid)::[]) t))

# 114 "FStar.Syntax.Print.fst"
let is_lex_cons : exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Syntax_Const.lexcons_lid)::[]) f))

# 115 "FStar.Syntax.Print.fst"
let is_lex_top : exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Syntax_Const.lextop_lid)::[]) f))

# 116 "FStar.Syntax.Print.fst"
let is_inr = (fun _35_1 -> (match (_35_1) with
| FStar_Util.Inl (_35_37) -> begin
false
end
| FStar_Util.Inr (_35_40) -> begin
true
end))

# 117 "FStar.Syntax.Print.fst"
let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _35_2 -> (match (_35_2) with
| (_35_45, Some (FStar_Syntax_Syntax.Implicit (_35_47))) -> begin
false
end
| _35_52 -> begin
true
end)))))

# 118 "FStar.Syntax.Print.fst"
let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _120_35 = (FStar_Syntax_Subst.compress e)
in _120_35.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(
# 121 "FStar.Syntax.Print.fst"
let args = (filter_imp args)
in (
# 122 "FStar.Syntax.Print.fst"
let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = 2)) then begin
(match ((let _120_36 = (FStar_List.nth exps 1)
in (reconstruct_lex _120_36))) with
| Some (xs) -> begin
(let _120_38 = (let _120_37 = (FStar_List.nth exps 0)
in (_120_37)::xs)
in Some (_120_38))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _35_64 -> begin
if (is_lex_top e) then begin
Some ([])
end else begin
None
end
end))

# 131 "FStar.Syntax.Print.fst"
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

# 135 "FStar.Syntax.Print.fst"
let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _120_52 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _120_52)))

# 138 "FStar.Syntax.Print.fst"
let infix_prim_op_to_string = (fun e -> (let _120_54 = (get_lid e)
in (find_lid _120_54 infix_prim_ops)))

# 139 "FStar.Syntax.Print.fst"
let unary_prim_op_to_string = (fun e -> (let _120_56 = (get_lid e)
in (find_lid _120_56 unary_prim_ops)))

# 140 "FStar.Syntax.Print.fst"
let quant_to_string = (fun t -> (let _120_58 = (get_lid t)
in (find_lid _120_58 quants)))

# 142 "FStar.Syntax.Print.fst"
let rec sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_ST.read FStar_Options.print_real_names) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)

# 148 "FStar.Syntax.Print.fst"
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
| FStar_Const.Const_string (bytes, _35_92) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_35_96) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x) -> begin
x
end
| FStar_Const.Const_int64 (_35_101) -> begin
"<int64>"
end
| FStar_Const.Const_uint8 (_35_104) -> begin
"<uint8>"
end
| FStar_Const.Const_range (r) -> begin
(FStar_Range.string_of_range r)
end))

# 162 "FStar.Syntax.Print.fst"
let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun _35_3 -> (match (_35_3) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))

# 166 "FStar.Syntax.Print.fst"
let tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _120_67 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _120_67))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _120_68 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _120_68))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _120_69 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _120_69))
end
| FStar_Syntax_Syntax.Tm_uinst (_35_121) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (_35_124) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (_35_127) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (_35_130) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (_35_133) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (_35_136) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (_35_139) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (_35_142) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (_35_145) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (_35_148) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (_35_151) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (_35_154, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
"Tm_delayed"
end
| Some (_35_160) -> begin
"Tm_delayed-resolved"
end)
end
| FStar_Syntax_Syntax.Tm_meta (_35_163) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))

# 189 "FStar.Syntax.Print.fst"
let uvar_to_string = (fun u -> if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _120_74 = (let _120_73 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _120_73 FStar_Util.string_of_int))
in (Prims.strcat "?" _120_74))
end)

# 191 "FStar.Syntax.Print.fst"
let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_unif (u) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(let _120_77 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _120_77))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _120_78 = (univ_to_string u)
in (FStar_Util.format1 "(S %s)" _120_78))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _120_80 = (let _120_79 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _120_79 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _120_80))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))

# 200 "FStar.Syntax.Print.fst"
let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _120_83 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _120_83 (FStar_String.concat ", "))))

# 202 "FStar.Syntax.Print.fst"
let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _120_87 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _120_87 (FStar_String.concat ", "))))

# 204 "FStar.Syntax.Print.fst"
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
(let _120_90 = (lid_to_string l)
in (FStar_Util.format1 "default %s" _120_90))
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(let _120_91 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _120_91))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _120_92 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _120_92 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(let _120_94 = (let _120_93 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _120_93 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordType %s)" _120_94))
end
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
(let _120_96 = (let _120_95 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _120_95 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordConstructor %s)" _120_96))
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

# 223 "FStar.Syntax.Print.fst"
let quals_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| _35_214 -> begin
(let _120_100 = (let _120_99 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _120_99 (FStar_String.concat " ")))
in (Prims.strcat _120_100 " "))
end))

# 232 "FStar.Syntax.Print.fst"
let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (
# 233 "FStar.Syntax.Print.fst"
let x = (FStar_Syntax_Subst.compress x)
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_35_218) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_35_221, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(
# 239 "FStar.Syntax.Print.fst"
let pats = (let _120_125 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _120_124 = (FStar_All.pipe_right args (FStar_List.map (fun _35_234 -> (match (_35_234) with
| (t, _35_233) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _120_124 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _120_125 (FStar_String.concat "\\/")))
in (let _120_126 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _120_126)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _35_238) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, _35_249) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _120_127 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _120_127))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _120_129 = (binders_to_string " -> " bs)
in (let _120_128 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _120_129 _120_128)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (l) when (FStar_ST.read FStar_Options.print_implicits) -> begin
(let _120_133 = (binders_to_string " " bs)
in (let _120_132 = (term_to_string t2)
in (let _120_131 = (let _120_130 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _120_130))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _120_133 _120_132 _120_131))))
end
| _35_268 -> begin
(let _120_135 = (binders_to_string " " bs)
in (let _120_134 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _120_135 _120_134)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _120_138 = (bv_to_string xt)
in (let _120_137 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _120_136 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _120_138 _120_137 _120_136))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _120_140 = (term_to_string t)
in (let _120_139 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _120_140 _120_139)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _120_142 = (lbs_to_string [] lbs)
in (let _120_141 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _120_142 _120_141)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _35_285) -> begin
(let _120_144 = (term_to_string e)
in (let _120_143 = (term_to_string t)
in (FStar_Util.format2 "(%s : %s)" _120_144 _120_143)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _35_292) -> begin
(let _120_146 = (term_to_string e)
in (let _120_145 = (comp_to_string c)
in (FStar_Util.format2 "(%s : %s)" _120_146 _120_145)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _120_154 = (term_to_string head)
in (let _120_153 = (let _120_152 = (FStar_All.pipe_right branches (FStar_List.map (fun _35_302 -> (match (_35_302) with
| (p, wopt, e) -> begin
(let _120_151 = (FStar_All.pipe_right p pat_to_string)
in (let _120_150 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _120_148 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _120_148))
end)
in (let _120_149 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _120_151 _120_150 _120_149))))
end))))
in (FStar_Util.concat_l "\n\t|" _120_152))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _120_154 _120_153)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _120_156 = (term_to_string t)
in (let _120_155 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _120_156 _120_155)))
end else begin
(term_to_string t)
end
end
| _35_311 -> begin
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _120_161 = (fv_to_string l)
in (let _120_160 = (let _120_159 = (FStar_List.map (fun _35_319 -> (match (_35_319) with
| (x, b) -> begin
(
# 279 "FStar.Syntax.Print.fst"
let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _120_159 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _120_161 _120_160)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _35_323) -> begin
(let _120_162 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _120_162))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(bv_to_string x)
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _120_163 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _120_163))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _120_164 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _120_164))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (
# 288 "FStar.Syntax.Print.fst"
let lbs = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _120_170 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 290 "FStar.Syntax.Print.fst"
let _35_339 = (let _120_168 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _120_168))
in (match (_35_339) with
| (us, td) -> begin
(
# 291 "FStar.Syntax.Print.fst"
let _35_357 = (match ((let _120_169 = (FStar_Syntax_Subst.compress td)
in _120_169.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_35_341, (t, _35_348)::(d, _35_344)::[]) -> begin
(t, d)
end
| _35_354 -> begin
(FStar_All.failwith "Impossibe")
end)
in (match (_35_357) with
| (t, d) -> begin
(
# 294 "FStar.Syntax.Print.fst"
let _35_358 = lb
in {FStar_Syntax_Syntax.lbname = _35_358.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _35_358.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in ((Prims.fst lbs), _120_170))
end else begin
lbs
end
in (let _120_180 = (quals_to_string quals)
in (let _120_179 = (let _120_178 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _120_177 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _120_176 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _120_173 = (let _120_172 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat "<" _120_172))
in (Prims.strcat _120_173 ">"))
end else begin
""
end
in (let _120_175 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _120_174 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _120_177 _120_176 _120_175 _120_174))))))))
in (FStar_Util.concat_l "\n and " _120_178))
in (FStar_Util.format3 "%slet %s %s" _120_180 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _120_179)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _120_183 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _120_182 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _120_183 _120_182))))
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
| _35_374 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (
# 326 "FStar.Syntax.Print.fst"
let _35_379 = b
in (match (_35_379) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(term_to_string a.FStar_Syntax_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_bound_var_types)))) then begin
(let _120_188 = (nm_to_string a)
in (imp_to_string _120_188 imp))
end else begin
(let _120_192 = (let _120_191 = (let _120_189 = (nm_to_string a)
in (Prims.strcat _120_189 ":"))
in (let _120_190 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat _120_191 _120_190)))
in (imp_to_string _120_192 imp))
end
end
end)))
and binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (
# 337 "FStar.Syntax.Print.fst"
let bs = if (FStar_ST.read FStar_Options.print_implicits) then begin
bs
end else begin
(filter_imp bs)
end
in if (sep = " -> ") then begin
(let _120_197 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _120_197 (FStar_String.concat sep)))
end else begin
(let _120_198 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _120_198 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _35_6 -> (match (_35_6) with
| (a, imp) -> begin
(let _120_200 = (term_to_string a)
in (imp_to_string _120_200 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (
# 346 "FStar.Syntax.Print.fst"
let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _120_202 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _120_202 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(match ((let _120_204 = (FStar_Syntax_Subst.compress t)
in _120_204.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_35_395) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _35_398 -> begin
(let _120_205 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _120_205))
end)
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(match ((let _120_206 = (FStar_Syntax_Subst.compress t)
in _120_206.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_35_402) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _35_405 -> begin
(let _120_207 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _120_207))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 362 "FStar.Syntax.Print.fst"
let basic = if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _35_7 -> (match (_35_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _35_411 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args)))) then begin
(let _120_209 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _120_209))
end else begin
if (((not ((FStar_ST.read FStar_Options.print_effect_args))) && (not ((FStar_ST.read FStar_Options.print_implicits)))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _35_8 -> (match (_35_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _35_415 -> begin
false
end))))) then begin
(let _120_211 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _120_211))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _120_215 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _120_214 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _120_213 = (let _120_212 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _120_212 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _120_215 _120_214 _120_213))))
end else begin
(let _120_217 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _120_216 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _120_217 _120_216)))
end
end
end
end
in (
# 375 "FStar.Syntax.Print.fst"
let dec = (let _120_221 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _35_9 -> (match (_35_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _120_220 = (let _120_219 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _120_219))
in (_120_220)::[])
end
| _35_421 -> begin
[]
end))))
in (FStar_All.pipe_right _120_221 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))

# 394 "FStar.Syntax.Print.fst"
let tscheme_to_string : (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  Prims.string = (fun _35_426 -> (match (_35_426) with
| (us, t) -> begin
(let _120_226 = (univ_names_to_string us)
in (let _120_225 = (term_to_string t)
in (FStar_Util.format2 "<%s> %s" _120_226 _120_225)))
end))

# 396 "FStar.Syntax.Print.fst"
let eff_decl_to_string : FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun ed -> (let _120_262 = (let _120_261 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _120_260 = (let _120_259 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (let _120_258 = (let _120_257 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _120_256 = (let _120_255 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _120_254 = (let _120_253 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret)
in (let _120_252 = (let _120_251 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _120_250 = (let _120_249 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wlp)
in (let _120_248 = (let _120_247 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _120_246 = (let _120_245 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _120_244 = (let _120_243 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wlp)
in (let _120_242 = (let _120_241 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_binop)
in (let _120_240 = (let _120_239 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_as_type)
in (let _120_238 = (let _120_237 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _120_236 = (let _120_235 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _120_234 = (let _120_233 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _120_232 = (let _120_231 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _120_230 = (let _120_229 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (_120_229)::[])
in (_120_231)::_120_230))
in (_120_233)::_120_232))
in (_120_235)::_120_234))
in (_120_237)::_120_236))
in (_120_239)::_120_238))
in (_120_241)::_120_240))
in (_120_243)::_120_242))
in (_120_245)::_120_244))
in (_120_247)::_120_246))
in (_120_249)::_120_248))
in (_120_251)::_120_250))
in (_120_253)::_120_252))
in (_120_255)::_120_254))
in (_120_257)::_120_256))
in (_120_259)::_120_258))
in (_120_261)::_120_260))
in (FStar_Util.format "new_effect { %s<%s> %s : %s \n\tret         = %s\n; bind_wp     = %s\n; bind_wlp    = %s\n; if_then_else= %s\n; ite_wp      = %s\n; ite_wlp     = %s\n; wp_binop    = %s\n; wp_as_type  = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s}\n" _120_262)))

# 429 "FStar.Syntax.Print.fst"
let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None), _35_432) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s)), _35_439) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _35_445) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _35_453, _35_455, quals, _35_458) -> begin
(let _120_267 = (quals_to_string quals)
in (let _120_266 = (binders_to_string " " tps)
in (let _120_265 = (term_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _120_267 lid.FStar_Ident.str _120_266 _120_265))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _35_465, _35_467, _35_469, _35_471, _35_473) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(
# 441 "FStar.Syntax.Print.fst"
let _35_478 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_35_478) with
| (univs, t) -> begin
(let _120_269 = (univ_names_to_string univs)
in (let _120_268 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _120_269 lid.FStar_Ident.str _120_268)))
end))
end else begin
(let _120_270 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _120_270))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _35_484) -> begin
(
# 445 "FStar.Syntax.Print.fst"
let _35_489 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_35_489) with
| (univs, t) -> begin
(let _120_274 = (quals_to_string quals)
in (let _120_273 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _120_271 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _120_271))
end else begin
""
end
in (let _120_272 = (term_to_string t)
in (FStar_Util.format4 "%s val %s %s : %s" _120_274 lid.FStar_Ident.str _120_273 _120_272))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _35_493, _35_495) -> begin
(let _120_275 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _120_275))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _35_500, _35_502, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _35_508) -> begin
(let _120_276 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _120_276))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _35_513, _35_515, _35_517) -> begin
(let _120_277 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _120_277 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _35_522) -> begin
(eff_decl_to_string ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(
# 457 "FStar.Syntax.Print.fst"
let _35_531 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst se.FStar_Syntax_Syntax.lift) (Prims.snd se.FStar_Syntax_Syntax.lift))
in (match (_35_531) with
| (us, t) -> begin
(let _120_281 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _120_280 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _120_279 = (univ_names_to_string us)
in (let _120_278 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _120_281 _120_280 _120_279 _120_278)))))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _35_537, _35_539) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(
# 463 "FStar.Syntax.Print.fst"
let _35_544 = (let _120_282 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _120_282))
in (match (_35_544) with
| (univs, t) -> begin
(
# 464 "FStar.Syntax.Print.fst"
let _35_553 = (match ((let _120_283 = (FStar_Syntax_Subst.compress t)
in _120_283.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(bs, c)
end
| _35_550 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_35_553) with
| (tps, c) -> begin
(let _120_287 = (sli l)
in (let _120_286 = (univ_names_to_string univs)
in (let _120_285 = (binders_to_string " " tps)
in (let _120_284 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _120_287 _120_286 _120_285 _120_284)))))
end))
end))
end else begin
(let _120_290 = (sli l)
in (let _120_289 = (binders_to_string " " tps)
in (let _120_288 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _120_290 _120_289 _120_288))))
end
end))

# 470 "FStar.Syntax.Print.fst"
let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _120_295 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _120_295 msg)))

# 472 "FStar.Syntax.Print.fst"
let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_35_558, {FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = _35_565; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _35_562; FStar_Syntax_Syntax.lbdef = _35_560}::[]), _35_571, _35_573, _35_575) -> begin
(let _120_299 = (lbname_to_string lb)
in (let _120_298 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _120_299 _120_298)))
end
| _35_579 -> begin
(let _120_302 = (let _120_301 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _120_301 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _120_302 (FStar_String.concat ", ")))
end))

# 476 "FStar.Syntax.Print.fst"
let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _120_307 = (sli m.FStar_Syntax_Syntax.name)
in (let _120_306 = (let _120_305 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _120_305 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _120_307 _120_306))))

# 479 "FStar.Syntax.Print.fst"
let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _35_10 -> (match (_35_10) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(let _120_311 = (FStar_Util.string_of_int i)
in (let _120_310 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _120_311 _120_310)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _120_313 = (bv_to_string x)
in (let _120_312 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _120_313 _120_312)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _120_315 = (bv_to_string x)
in (let _120_314 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _120_315 _120_314)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _120_317 = (FStar_Util.string_of_int i)
in (let _120_316 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _120_317 _120_316)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _120_318 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _120_318))
end))

# 486 "FStar.Syntax.Print.fst"
let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _120_321 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _120_321 (FStar_String.concat "; "))))




