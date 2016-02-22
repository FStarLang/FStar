
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
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(
# 234 "FStar.Syntax.Print.fst"
let pats = (let _115_125 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _115_124 = (FStar_All.pipe_right args (FStar_List.map (fun _36_237 -> (match (_36_237) with
| (t, _36_236) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _115_124 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _115_125 (FStar_String.concat "\\/")))
in (let _115_126 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _115_126)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _36_241) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, _36_252) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _115_127 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _115_127))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _115_129 = (binders_to_string " -> " bs)
in (let _115_128 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _115_129 _115_128)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (l) when (FStar_ST.read FStar_Options.print_implicits) -> begin
(let _115_133 = (binders_to_string " " bs)
in (let _115_132 = (term_to_string t2)
in (let _115_131 = (let _115_130 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _115_130))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _115_133 _115_132 _115_131))))
end
| _36_271 -> begin
(let _115_135 = (binders_to_string " " bs)
in (let _115_134 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _115_135 _115_134)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _115_138 = (bv_to_string xt)
in (let _115_137 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _115_136 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _115_138 _115_137 _115_136))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _115_140 = (term_to_string t)
in (let _115_139 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _115_140 _115_139)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _115_142 = (lbs_to_string [] lbs)
in (let _115_141 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _115_142 _115_141)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _36_287) -> begin
(let _115_144 = (term_to_string e)
in (let _115_143 = (term_to_string t)
in (FStar_Util.format2 "(%s : %s)" _115_144 _115_143)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _115_152 = (term_to_string head)
in (let _115_151 = (let _115_150 = (FStar_All.pipe_right branches (FStar_List.map (fun _36_297 -> (match (_36_297) with
| (p, wopt, e) -> begin
(let _115_149 = (FStar_All.pipe_right p pat_to_string)
in (let _115_148 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _115_146 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _115_146))
end)
in (let _115_147 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _115_149 _115_148 _115_147))))
end))))
in (FStar_Util.concat_l "\n\t|" _115_150))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _115_152 _115_151)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _115_154 = (term_to_string t)
in (let _115_153 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _115_154 _115_153)))
end else begin
(term_to_string t)
end
end
| _36_306 -> begin
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _115_159 = (fv_to_string l)
in (let _115_158 = (let _115_157 = (FStar_List.map (fun _36_314 -> (match (_36_314) with
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
in (FStar_All.pipe_right _115_157 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _115_159 _115_158)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _36_318) -> begin
(let _115_160 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _115_160))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(bv_to_string x)
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _115_161 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _115_161))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _115_162 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _115_162))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (
# 281 "FStar.Syntax.Print.fst"
let lbs = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _115_168 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 283 "FStar.Syntax.Print.fst"
let _36_334 = (let _115_166 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _115_166))
in (match (_36_334) with
| (us, td) -> begin
(
# 284 "FStar.Syntax.Print.fst"
let _36_352 = (match ((let _115_167 = (FStar_Syntax_Subst.compress td)
in _115_167.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_36_336, (t, _36_343)::(d, _36_339)::[]) -> begin
(t, d)
end
| _36_349 -> begin
(FStar_All.failwith "Impossibe")
end)
in (match (_36_352) with
| (t, d) -> begin
(
# 287 "FStar.Syntax.Print.fst"
let _36_353 = lb
in {FStar_Syntax_Syntax.lbname = _36_353.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _36_353.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in ((Prims.fst lbs), _115_168))
end else begin
lbs
end
in (let _115_178 = (quals_to_string quals)
in (let _115_177 = (let _115_176 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _115_175 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _115_174 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _115_171 = (let _115_170 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat "<" _115_170))
in (Prims.strcat _115_171 ">"))
end else begin
""
end
in (let _115_173 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _115_172 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _115_175 _115_174 _115_173 _115_172))))))))
in (FStar_Util.concat_l "\n and " _115_176))
in (FStar_Util.format3 "%slet %s %s" _115_178 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _115_177)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _115_181 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _115_180 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _115_181 _115_180))))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s _36_5 -> (match (_36_5) with
| Some (FStar_Syntax_Syntax.Implicit) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _36_365 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (
# 318 "FStar.Syntax.Print.fst"
let _36_370 = b
in (match (_36_370) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(term_to_string a.FStar_Syntax_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_bound_var_types)))) then begin
(let _115_186 = (nm_to_string a)
in (imp_to_string _115_186 imp))
end else begin
(let _115_190 = (let _115_189 = (let _115_187 = (nm_to_string a)
in (Prims.strcat _115_187 ":"))
in (let _115_188 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat _115_189 _115_188)))
in (imp_to_string _115_190 imp))
end
end
end)))
and binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (
# 329 "FStar.Syntax.Print.fst"
let bs = if (FStar_ST.read FStar_Options.print_implicits) then begin
bs
end else begin
(filter_imp bs)
end
in if (sep = " -> ") then begin
(let _115_195 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _115_195 (FStar_String.concat sep)))
end else begin
(let _115_196 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _115_196 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _36_6 -> (match (_36_6) with
| (a, imp) -> begin
(let _115_198 = (term_to_string a)
in (imp_to_string _115_198 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (
# 338 "FStar.Syntax.Print.fst"
let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _115_200 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _115_200 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(match ((let _115_202 = (FStar_Syntax_Subst.compress t)
in _115_202.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_36_386) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _36_389 -> begin
(let _115_203 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _115_203))
end)
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(match ((let _115_204 = (FStar_Syntax_Subst.compress t)
in _115_204.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_36_393) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _36_396 -> begin
(let _115_205 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _115_205))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 354 "FStar.Syntax.Print.fst"
let basic = if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _36_7 -> (match (_36_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _36_402 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args)))) then begin
(let _115_207 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _115_207))
end else begin
if (((not ((FStar_ST.read FStar_Options.print_effect_args))) && (not ((FStar_ST.read FStar_Options.print_implicits)))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _36_8 -> (match (_36_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _36_406 -> begin
false
end))))) then begin
(let _115_209 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _115_209))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _115_213 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _115_212 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _115_211 = (let _115_210 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _115_210 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _115_213 _115_212 _115_211))))
end else begin
(let _115_215 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _115_214 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _115_215 _115_214)))
end
end
end
end
in (
# 367 "FStar.Syntax.Print.fst"
let dec = (let _115_219 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _36_9 -> (match (_36_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _115_218 = (let _115_217 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _115_217))
in (_115_218)::[])
end
| _36_412 -> begin
[]
end))))
in (FStar_All.pipe_right _115_219 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))

# 386 "FStar.Syntax.Print.fst"
let tscheme_to_string : (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  Prims.string = (fun _36_417 -> (match (_36_417) with
| (us, t) -> begin
(let _115_224 = (univ_names_to_string us)
in (let _115_223 = (term_to_string t)
in (FStar_Util.format2 "<%s> %s" _115_224 _115_223)))
end))

# 388 "FStar.Syntax.Print.fst"
let eff_decl_to_string : FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun ed -> (let _115_260 = (let _115_259 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _115_258 = (let _115_257 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (let _115_256 = (let _115_255 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _115_254 = (let _115_253 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _115_252 = (let _115_251 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret)
in (let _115_250 = (let _115_249 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _115_248 = (let _115_247 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wlp)
in (let _115_246 = (let _115_245 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _115_244 = (let _115_243 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _115_242 = (let _115_241 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wlp)
in (let _115_240 = (let _115_239 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_binop)
in (let _115_238 = (let _115_237 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_as_type)
in (let _115_236 = (let _115_235 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _115_234 = (let _115_233 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _115_232 = (let _115_231 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _115_230 = (let _115_229 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _115_228 = (let _115_227 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (_115_227)::[])
in (_115_229)::_115_228))
in (_115_231)::_115_230))
in (_115_233)::_115_232))
in (_115_235)::_115_234))
in (_115_237)::_115_236))
in (_115_239)::_115_238))
in (_115_241)::_115_240))
in (_115_243)::_115_242))
in (_115_245)::_115_244))
in (_115_247)::_115_246))
in (_115_249)::_115_248))
in (_115_251)::_115_250))
in (_115_253)::_115_252))
in (_115_255)::_115_254))
in (_115_257)::_115_256))
in (_115_259)::_115_258))
in (FStar_Util.format "new_effect { %s<%s> %s : %s \n\tret         = %s\n; bind_wp     = %s\n; bind_wlp    = %s\n; if_then_else= %s\n; ite_wp      = %s\n; ite_wlp     = %s\n; wp_binop    = %s\n; wp_as_type  = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s}\n" _115_260)))

# 421 "FStar.Syntax.Print.fst"
let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions, _36_422) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _36_428) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _36_436, _36_438, quals, _36_441) -> begin
(let _115_265 = (quals_to_string quals)
in (let _115_264 = (binders_to_string " " tps)
in (let _115_263 = (term_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _115_265 lid.FStar_Ident.str _115_264 _115_263))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _36_448, _36_450, _36_452, _36_454, _36_456) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(
# 432 "FStar.Syntax.Print.fst"
let _36_461 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_36_461) with
| (univs, t) -> begin
(let _115_267 = (univ_names_to_string univs)
in (let _115_266 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _115_267 lid.FStar_Ident.str _115_266)))
end))
end else begin
(let _115_268 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _115_268))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _36_467) -> begin
(
# 436 "FStar.Syntax.Print.fst"
let _36_472 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_36_472) with
| (univs, t) -> begin
(let _115_272 = (quals_to_string quals)
in (let _115_271 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _115_269 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _115_269))
end else begin
""
end
in (let _115_270 = (term_to_string t)
in (FStar_Util.format4 "%s val %s %s : %s" _115_272 lid.FStar_Ident.str _115_271 _115_270))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _36_476, _36_478) -> begin
(let _115_273 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _115_273))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _36_483, _36_485, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _36_491) -> begin
(let _115_274 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _115_274))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _36_496, _36_498, _36_500) -> begin
(let _115_275 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _115_275 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _36_505) -> begin
(eff_decl_to_string ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(
# 448 "FStar.Syntax.Print.fst"
let _36_514 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst se.FStar_Syntax_Syntax.lift) (Prims.snd se.FStar_Syntax_Syntax.lift))
in (match (_36_514) with
| (us, t) -> begin
(let _115_279 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _115_278 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _115_277 = (univ_names_to_string us)
in (let _115_276 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _115_279 _115_278 _115_277 _115_276)))))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _36_520, _36_522) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(
# 454 "FStar.Syntax.Print.fst"
let _36_527 = (let _115_280 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _115_280))
in (match (_36_527) with
| (univs, t) -> begin
(
# 455 "FStar.Syntax.Print.fst"
let _36_536 = (match ((let _115_281 = (FStar_Syntax_Subst.compress t)
in _115_281.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(bs, c)
end
| _36_533 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_36_536) with
| (tps, c) -> begin
(let _115_285 = (sli l)
in (let _115_284 = (univ_names_to_string univs)
in (let _115_283 = (binders_to_string " " tps)
in (let _115_282 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _115_285 _115_284 _115_283 _115_282)))))
end))
end))
end else begin
(let _115_288 = (sli l)
in (let _115_287 = (binders_to_string " " tps)
in (let _115_286 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _115_288 _115_287 _115_286))))
end
end))

# 461 "FStar.Syntax.Print.fst"
let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _115_293 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _115_293 msg)))

# 463 "FStar.Syntax.Print.fst"
let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_36_541, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (l); FStar_Syntax_Syntax.lbunivs = _36_548; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _36_545; FStar_Syntax_Syntax.lbdef = _36_543}::[]), _36_555, _36_557, _36_559) -> begin
(let _115_296 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Ident.str _115_296))
end
| _36_563 -> begin
(let _115_299 = (let _115_298 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _115_298 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _115_299 (FStar_String.concat ", ")))
end))

# 467 "FStar.Syntax.Print.fst"
let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _115_304 = (sli m.FStar_Syntax_Syntax.name)
in (let _115_303 = (let _115_302 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _115_302 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _115_304 _115_303))))

# 470 "FStar.Syntax.Print.fst"
let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _36_10 -> (match (_36_10) with
| FStar_Syntax_Syntax.DB (i, t) -> begin
(let _115_308 = (FStar_Util.string_of_int i)
in (let _115_307 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _115_308 _115_307)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _115_310 = (bv_to_string x)
in (let _115_309 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _115_310 _115_309)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _115_312 = (bv_to_string x)
in (let _115_311 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _115_312 _115_311)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _115_314 = (FStar_Util.string_of_int i)
in (let _115_313 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _115_314 _115_313)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _115_315 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _115_315))
end))

# 477 "FStar.Syntax.Print.fst"
let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _115_318 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _115_318 (FStar_String.concat "; "))))




