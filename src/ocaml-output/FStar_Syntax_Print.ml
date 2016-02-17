
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
let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _115_32 = (FStar_Syntax_Subst.compress e)
in _115_32.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(
# 116 "FStar.Syntax.Print.fst"
let args = (FStar_List.filter (fun a -> ((Prims.snd a) <> Some (FStar_Syntax_Syntax.Implicit))) args)
in (
# 117 "FStar.Syntax.Print.fst"
let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = 2)) then begin
(match ((let _115_34 = (FStar_List.nth exps 1)
in (reconstruct_lex _115_34))) with
| Some (xs) -> begin
(let _115_36 = (let _115_35 = (FStar_List.nth exps 0)
in (_115_35)::xs)
in Some (_115_36))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _36_60 -> begin
if (is_lex_top e) then begin
Some ([])
end else begin
None
end
end))

# 126 "FStar.Syntax.Print.fst"
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

# 130 "FStar.Syntax.Print.fst"
let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _115_50 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _115_50)))

# 133 "FStar.Syntax.Print.fst"
let infix_prim_op_to_string = (fun e -> (let _115_52 = (get_lid e)
in (find_lid _115_52 infix_prim_ops)))

# 134 "FStar.Syntax.Print.fst"
let unary_prim_op_to_string = (fun e -> (let _115_54 = (get_lid e)
in (find_lid _115_54 unary_prim_ops)))

# 135 "FStar.Syntax.Print.fst"
let quant_to_string = (fun t -> (let _115_56 = (get_lid t)
in (find_lid _115_56 quants)))

# 137 "FStar.Syntax.Print.fst"
let rec sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_ST.read FStar_Options.print_real_names) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)

# 143 "FStar.Syntax.Print.fst"
let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _36_2 -> (match (_36_2) with
| (_36_78, Some (FStar_Syntax_Syntax.Implicit)) -> begin
false
end
| _36_83 -> begin
true
end)))))

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
| FStar_Const.Const_string (bytes, _36_97) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_36_101) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x) -> begin
x
end
| FStar_Const.Const_int64 (_36_106) -> begin
"<int64>"
end
| FStar_Const.Const_uint8 (_36_109) -> begin
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
(let _115_67 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _115_67))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _115_68 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _115_68))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _115_69 = (lid_to_string (Prims.fst x).FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _115_69))
end
| FStar_Syntax_Syntax.Tm_uinst (_36_124) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (_36_127) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (_36_130) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (_36_133) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (_36_136) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (_36_139) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (_36_142) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (_36_145) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (_36_148) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (_36_151) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (_36_154) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (_36_157, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
"Tm_delayed"
end
| Some (_36_163) -> begin
"Tm_delayed-resolved"
end)
end
| FStar_Syntax_Syntax.Tm_meta (_36_166) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))

# 184 "FStar.Syntax.Print.fst"
let uvar_to_string = (fun u -> if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _115_74 = (let _115_73 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _115_73 FStar_Util.string_of_int))
in (Prims.strcat "?" _115_74))
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
(let _115_77 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _115_77))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _115_78 = (univ_to_string u)
in (FStar_Util.format1 "(S %s)" _115_78))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _115_80 = (let _115_79 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _115_79 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _115_80))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))

# 195 "FStar.Syntax.Print.fst"
let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _115_83 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _115_83 (FStar_String.concat ", "))))

# 197 "FStar.Syntax.Print.fst"
let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _115_87 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _115_87 (FStar_String.concat ", "))))

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
(let _115_90 = (lid_to_string l)
in (FStar_Util.format1 "default %s" _115_90))
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(let _115_91 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _115_91))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _115_92 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _115_92 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(let _115_94 = (let _115_93 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _115_93 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordType %s)" _115_94))
end
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
(let _115_96 = (let _115_95 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _115_95 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordConstructor %s)" _115_96))
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
| _36_217 -> begin
(let _115_100 = (let _115_99 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _115_99 (FStar_String.concat " ")))
in (Prims.strcat _115_100 " "))
end))

# 227 "FStar.Syntax.Print.fst"
let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (
# 228 "FStar.Syntax.Print.fst"
let x = (FStar_Syntax_Subst.compress x)
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_36_221) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_36_224, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, _36_230) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, _36_241) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _115_122 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _115_122))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _115_124 = (binders_to_string " -> " bs)
in (let _115_123 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _115_124 _115_123)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (l) when (FStar_ST.read FStar_Options.print_implicits) -> begin
(let _115_128 = (binders_to_string " " bs)
in (let _115_127 = (term_to_string t2)
in (let _115_126 = (let _115_125 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _115_125))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _115_128 _115_127 _115_126))))
end
| _36_260 -> begin
(let _115_130 = (binders_to_string " " bs)
in (let _115_129 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _115_130 _115_129)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _115_133 = (bv_to_string xt)
in (let _115_132 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _115_131 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _115_133 _115_132 _115_131))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _115_135 = (term_to_string t)
in (let _115_134 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _115_135 _115_134)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _115_137 = (lbs_to_string [] lbs)
in (let _115_136 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _115_137 _115_136)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _36_276) -> begin
(let _115_139 = (term_to_string e)
in (let _115_138 = (term_to_string t)
in (FStar_Util.format2 "(%s : %s)" _115_139 _115_138)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _115_147 = (term_to_string head)
in (let _115_146 = (let _115_145 = (FStar_All.pipe_right branches (FStar_List.map (fun _36_286 -> (match (_36_286) with
| (p, wopt, e) -> begin
(let _115_144 = (FStar_All.pipe_right p pat_to_string)
in (let _115_143 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _115_141 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _115_141))
end)
in (let _115_142 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _115_144 _115_143 _115_142))))
end))))
in (FStar_Util.concat_l "\n\t|" _115_145))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _115_147 _115_146)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _115_149 = (term_to_string t)
in (let _115_148 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _115_149 _115_148)))
end else begin
(term_to_string t)
end
end
| _36_295 -> begin
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _115_154 = (fv_to_string l)
in (let _115_153 = (let _115_152 = (FStar_List.map (fun _36_303 -> (match (_36_303) with
| (x, b) -> begin
(
# 268 "FStar.Syntax.Print.fst"
let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _115_152 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _115_154 _115_153)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _36_307) -> begin
(let _115_155 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _115_155))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(bv_to_string x)
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _115_156 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _115_156))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _115_157 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _115_157))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (let _115_169 = (quals_to_string quals)
in (let _115_168 = (let _115_167 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _115_166 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _115_165 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _115_162 = (let _115_161 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat "<" _115_161))
in (Prims.strcat _115_162 ">"))
end else begin
""
end
in (let _115_164 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _115_163 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _115_166 _115_165 _115_164 _115_163))))))))
in (FStar_Util.concat_l "\n and " _115_167))
in (FStar_Util.format3 "%slet %s %s" _115_169 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _115_168))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _115_172 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _115_171 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _115_172 _115_171))))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s _36_5 -> (match (_36_5) with
| Some (FStar_Syntax_Syntax.Implicit) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _36_329 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (
# 306 "FStar.Syntax.Print.fst"
let _36_334 = b
in (match (_36_334) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(term_to_string a.FStar_Syntax_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_bound_var_types)))) then begin
(let _115_177 = (nm_to_string a)
in (imp_to_string _115_177 imp))
end else begin
(let _115_181 = (let _115_180 = (let _115_178 = (nm_to_string a)
in (Prims.strcat _115_178 ":"))
in (let _115_179 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat _115_180 _115_179)))
in (imp_to_string _115_181 imp))
end
end
end)))
and binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (
# 317 "FStar.Syntax.Print.fst"
let bs = if (FStar_ST.read FStar_Options.print_implicits) then begin
bs
end else begin
(filter_imp bs)
end
in if (sep = " -> ") then begin
(let _115_186 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _115_186 (FStar_String.concat sep)))
end else begin
(let _115_187 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _115_187 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _36_6 -> (match (_36_6) with
| (a, imp) -> begin
(let _115_189 = (term_to_string a)
in (imp_to_string _115_189 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (
# 326 "FStar.Syntax.Print.fst"
let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _115_191 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _115_191 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(match ((let _115_193 = (FStar_Syntax_Subst.compress t)
in _115_193.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_36_350) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _36_353 -> begin
(let _115_194 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _115_194))
end)
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(match ((let _115_195 = (FStar_Syntax_Subst.compress t)
in _115_195.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_36_357) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _36_360 -> begin
(let _115_196 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _115_196))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 342 "FStar.Syntax.Print.fst"
let basic = if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _36_7 -> (match (_36_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _36_366 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args)))) then begin
(let _115_198 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _115_198))
end else begin
if (((not ((FStar_ST.read FStar_Options.print_effect_args))) && (not ((FStar_ST.read FStar_Options.print_implicits)))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _36_8 -> (match (_36_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _36_370 -> begin
false
end))))) then begin
(let _115_200 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _115_200))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _115_204 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _115_203 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _115_202 = (let _115_201 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _115_201 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _115_204 _115_203 _115_202))))
end else begin
(let _115_206 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _115_205 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _115_206 _115_205)))
end
end
end
end
in (
# 355 "FStar.Syntax.Print.fst"
let dec = (let _115_210 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _36_9 -> (match (_36_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _115_209 = (let _115_208 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _115_208))
in (_115_209)::[])
end
| _36_376 -> begin
[]
end))))
in (FStar_All.pipe_right _115_210 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))

# 374 "FStar.Syntax.Print.fst"
let tscheme_to_string : (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  Prims.string = (fun _36_381 -> (match (_36_381) with
| (us, t) -> begin
(let _115_215 = (univ_names_to_string us)
in (let _115_214 = (term_to_string t)
in (FStar_Util.format2 "<%s> %s" _115_215 _115_214)))
end))

# 376 "FStar.Syntax.Print.fst"
let eff_decl_to_string : FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun ed -> (let _115_251 = (let _115_250 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _115_249 = (let _115_248 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (let _115_247 = (let _115_246 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _115_245 = (let _115_244 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _115_243 = (let _115_242 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret)
in (let _115_241 = (let _115_240 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _115_239 = (let _115_238 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wlp)
in (let _115_237 = (let _115_236 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _115_235 = (let _115_234 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _115_233 = (let _115_232 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wlp)
in (let _115_231 = (let _115_230 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_binop)
in (let _115_229 = (let _115_228 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_as_type)
in (let _115_227 = (let _115_226 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _115_225 = (let _115_224 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _115_223 = (let _115_222 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _115_221 = (let _115_220 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _115_219 = (let _115_218 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (_115_218)::[])
in (_115_220)::_115_219))
in (_115_222)::_115_221))
in (_115_224)::_115_223))
in (_115_226)::_115_225))
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
in (FStar_Util.format "new_effect { %s<%s> %s : %s \n\tret         = %s\n; bind_wp     = %s\n; bind_wlp    = %s\n; if_then_else= %s\n; ite_wp      = %s\n; ite_wlp     = %s\n; wp_binop    = %s\n; wp_as_type  = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s}\n" _115_251)))

# 409 "FStar.Syntax.Print.fst"
let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions, _36_386) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _36_392) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _36_400, _36_402, quals, _36_405) -> begin
(let _115_256 = (quals_to_string quals)
in (let _115_255 = (binders_to_string " " tps)
in (let _115_254 = (term_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _115_256 lid.FStar_Ident.str _115_255 _115_254))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _36_412, _36_414, _36_416, _36_418, _36_420) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(
# 420 "FStar.Syntax.Print.fst"
let _36_425 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_36_425) with
| (univs, t) -> begin
(let _115_258 = (univ_names_to_string univs)
in (let _115_257 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _115_258 lid.FStar_Ident.str _115_257)))
end))
end else begin
(let _115_259 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _115_259))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _36_431) -> begin
(
# 424 "FStar.Syntax.Print.fst"
let _36_436 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_36_436) with
| (univs, t) -> begin
(let _115_263 = (quals_to_string quals)
in (let _115_262 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _115_260 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _115_260))
end else begin
""
end
in (let _115_261 = (term_to_string t)
in (FStar_Util.format4 "%s val %s %s : %s" _115_263 lid.FStar_Ident.str _115_262 _115_261))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _36_440, _36_442) -> begin
(let _115_264 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _115_264))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _36_447, _36_449, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _36_455) -> begin
(let _115_265 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _115_265))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _36_460, _36_462, _36_464) -> begin
(let _115_266 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _115_266 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _36_469) -> begin
(eff_decl_to_string ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(
# 436 "FStar.Syntax.Print.fst"
let _36_478 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst se.FStar_Syntax_Syntax.lift) (Prims.snd se.FStar_Syntax_Syntax.lift))
in (match (_36_478) with
| (us, t) -> begin
(let _115_270 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _115_269 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _115_268 = (univ_names_to_string us)
in (let _115_267 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _115_270 _115_269 _115_268 _115_267)))))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, _36_481, tps, c, _36_485, _36_487) -> begin
(let _115_273 = (sli l)
in (let _115_272 = (binders_to_string " " tps)
in (let _115_271 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _115_273 _115_272 _115_271))))
end))

# 442 "FStar.Syntax.Print.fst"
let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _115_278 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _115_278 msg)))

# 444 "FStar.Syntax.Print.fst"
let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_36_494, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (l); FStar_Syntax_Syntax.lbunivs = _36_501; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _36_498; FStar_Syntax_Syntax.lbdef = _36_496}::[]), _36_508, _36_510, _36_512) -> begin
(let _115_281 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Ident.str _115_281))
end
| _36_516 -> begin
(let _115_284 = (let _115_283 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _115_283 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _115_284 (FStar_String.concat ", ")))
end))

# 448 "FStar.Syntax.Print.fst"
let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _115_289 = (sli m.FStar_Syntax_Syntax.name)
in (let _115_288 = (let _115_287 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _115_287 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _115_289 _115_288))))

# 451 "FStar.Syntax.Print.fst"
let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _36_10 -> (match (_36_10) with
| FStar_Syntax_Syntax.DB (i, t) -> begin
(let _115_293 = (FStar_Util.string_of_int i)
in (let _115_292 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _115_293 _115_292)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _115_295 = (bv_to_string x)
in (let _115_294 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _115_295 _115_294)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _115_297 = (bv_to_string x)
in (let _115_296 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _115_297 _115_296)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _115_299 = (FStar_Util.string_of_int i)
in (let _115_298 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _115_299 _115_298)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _115_300 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _115_300))
end))

# 458 "FStar.Syntax.Print.fst"
let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _115_303 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _115_303 (FStar_String.concat "; "))))




