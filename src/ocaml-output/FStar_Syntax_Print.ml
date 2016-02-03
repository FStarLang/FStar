
open Prims
let lid_to_string = (fun l -> l.FStar_Ident.str)

let fv_to_string = (fun fv -> (lid_to_string (Prims.fst fv).FStar_Syntax_Syntax.v))

let bv_to_string = (fun bv -> (let _134_6 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "#") _134_6)))

let nm_to_string = (fun bv -> if (FStar_ST.read FStar_Options.print_real_names) then begin
(bv_to_string bv)
end else begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)

let db_to_string = (fun bv -> (let _134_11 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "@") _134_11)))

let infix_prim_ops = ((FStar_Syntax_Const.op_Addition, "+"))::((FStar_Syntax_Const.op_Subtraction, "-"))::((FStar_Syntax_Const.op_Multiply, "*"))::((FStar_Syntax_Const.op_Division, "/"))::((FStar_Syntax_Const.op_Eq, "="))::((FStar_Syntax_Const.op_ColonEq, ":="))::((FStar_Syntax_Const.op_notEq, "<>"))::((FStar_Syntax_Const.op_And, "&&"))::((FStar_Syntax_Const.op_Or, "||"))::((FStar_Syntax_Const.op_LTE, "<="))::((FStar_Syntax_Const.op_GTE, ">="))::((FStar_Syntax_Const.op_LT, "<"))::((FStar_Syntax_Const.op_GT, ">"))::((FStar_Syntax_Const.op_Modulus, "mod"))::((FStar_Syntax_Const.and_lid, "/\\"))::((FStar_Syntax_Const.or_lid, "\\/"))::((FStar_Syntax_Const.imp_lid, "==>"))::((FStar_Syntax_Const.iff_lid, "<==>"))::((FStar_Syntax_Const.precedes_lid, "<<"))::((FStar_Syntax_Const.eq2_lid, "=="))::[]

let unary_prim_ops = ((FStar_Syntax_Const.op_Negation, "not"))::((FStar_Syntax_Const.op_Minus, "-"))::((FStar_Syntax_Const.not_lid, "~"))::[]

let is_prim_op = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _43_20) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v)))
end
| _43_24 -> begin
false
end))

let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _43_28) -> begin
fv.FStar_Syntax_Syntax.v
end
| _43_32 -> begin
(FStar_All.failwith "get_lid")
end))

let is_infix_prim_op = (fun e -> (is_prim_op (Prims.fst (FStar_List.split infix_prim_ops)) e))

let is_unary_prim_op = (fun e -> (is_prim_op (Prims.fst (FStar_List.split unary_prim_ops)) e))

let quants = ((FStar_Syntax_Const.forall_lid, "forall"))::((FStar_Syntax_Const.exists_lid, "exists"))::[]

type exp =
FStar_Syntax_Syntax.term

let is_b2t = (fun t -> (is_prim_op ((FStar_Syntax_Const.b2t_lid)::[]) t))

let is_quant = (fun t -> (is_prim_op (Prims.fst (FStar_List.split quants)) t))

let is_ite = (fun t -> (is_prim_op ((FStar_Syntax_Const.ite_lid)::[]) t))

let is_lex_cons = (fun f -> (is_prim_op ((FStar_Syntax_Const.lexcons_lid)::[]) f))

let is_lex_top = (fun f -> (is_prim_op ((FStar_Syntax_Const.lextop_lid)::[]) f))

let is_inr = (fun _43_1 -> (match (_43_1) with
| FStar_Util.Inl (_43_42) -> begin
false
end
| FStar_Util.Inr (_43_45) -> begin
true
end))

let rec reconstruct_lex = (fun e -> (match ((let _134_32 = (FStar_Syntax_Subst.compress e)
in _134_32.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(let args = (FStar_List.filter (fun a -> ((Prims.snd a) <> Some (FStar_Syntax_Syntax.Implicit))) args)
in (let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = 2)) then begin
(match ((let _134_34 = (FStar_List.nth exps 1)
in (reconstruct_lex _134_34))) with
| Some (xs) -> begin
(let _134_36 = (let _134_35 = (FStar_List.nth exps 0)
in (_134_35)::xs)
in Some (_134_36))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _43_59 -> begin
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

let find_lid = (fun x xs -> (let _134_50 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _134_50)))

let infix_prim_op_to_string = (fun e -> (let _134_52 = (get_lid e)
in (find_lid _134_52 infix_prim_ops)))

let unary_prim_op_to_string = (fun e -> (let _134_54 = (get_lid e)
in (find_lid _134_54 unary_prim_ops)))

let quant_to_string = (fun t -> (let _134_56 = (get_lid t)
in (find_lid _134_56 quants)))

let rec sli = (fun l -> if (FStar_ST.read FStar_Options.print_real_names) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)

let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _43_2 -> (match (_43_2) with
| (_43_77, Some (FStar_Syntax_Syntax.Implicit)) -> begin
false
end
| _43_82 -> begin
true
end)))))

let const_to_string = (fun x -> (match (x) with
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
| FStar_Const.Const_string (bytes, _43_96) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_43_100) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x) -> begin
x
end
| FStar_Const.Const_int64 (_43_105) -> begin
"<int64>"
end
| FStar_Const.Const_uint8 (_43_108) -> begin
"<uint8>"
end))

let lbname_to_string = (fun _43_3 -> (match (_43_3) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l)
end))

let tag_of_term = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _134_67 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _134_67))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _134_68 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _134_68))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _134_69 = (lid_to_string (Prims.fst x).FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _134_69))
end
| FStar_Syntax_Syntax.Tm_uinst (_43_123) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (_43_126) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (_43_129) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (_43_132) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (_43_135) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (_43_138) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (_43_141) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (_43_144) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (_43_147) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (_43_150) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (_43_153) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (_43_156, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
"Tm_delayed"
end
| Some (_43_162) -> begin
"Tm_delayed-resolved"
end)
end
| FStar_Syntax_Syntax.Tm_meta (_43_165) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))

let uvar_to_string = (fun u -> if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _134_74 = (let _134_73 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _134_73 FStar_Util.string_of_int))
in (Prims.strcat "?" _134_74))
end)

let rec univ_to_string = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_unif (u) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(let _134_77 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _134_77))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _134_78 = (univ_to_string u)
in (FStar_Util.format1 "(S %s)" _134_78))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _134_80 = (let _134_79 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _134_79 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _134_80))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))

let univs_to_string = (fun us -> (let _134_83 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _134_83 (FStar_String.concat ", "))))

let univ_names_to_string = (fun us -> (let _134_87 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _134_87 (FStar_String.concat ", "))))

let qual_to_string = (fun _43_4 -> (match (_43_4) with
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
(let _134_90 = (lid_to_string l)
in (FStar_Util.format1 "default %s" _134_90))
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(let _134_91 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _134_91))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _134_92 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _134_92 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(let _134_94 = (let _134_93 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _134_93 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordType %s)" _134_94))
end
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
(let _134_96 = (let _134_95 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _134_95 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordConstructor %s)" _134_96))
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

let quals_to_string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| _43_216 -> begin
(let _134_100 = (let _134_99 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _134_99 (FStar_String.concat " ")))
in (Prims.strcat _134_100 " "))
end))

let rec term_to_string = (fun x -> (let x = (FStar_Syntax_Subst.compress x)
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_43_220) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_43_223, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, _43_229) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, _43_240) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _134_122 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _134_122))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _134_124 = (binders_to_string " -> " bs)
in (let _134_123 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _134_124 _134_123)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (l) when (FStar_ST.read FStar_Options.print_implicits) -> begin
(let _134_128 = (binders_to_string " " bs)
in (let _134_127 = (term_to_string t2)
in (let _134_126 = (let _134_125 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _134_125))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _134_128 _134_127 _134_126))))
end
| _43_259 -> begin
(let _134_130 = (binders_to_string " " bs)
in (let _134_129 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _134_130 _134_129)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _134_133 = (bv_to_string xt)
in (let _134_132 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _134_131 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _134_133 _134_132 _134_131))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _134_135 = (term_to_string t)
in (let _134_134 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _134_135 _134_134)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _134_137 = (lbs_to_string [] lbs)
in (let _134_136 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _134_137 _134_136)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _43_275) -> begin
(let _134_139 = (term_to_string e)
in (let _134_138 = (term_to_string t)
in (FStar_Util.format2 "(%s : %s)" _134_139 _134_138)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _134_147 = (term_to_string head)
in (let _134_146 = (let _134_145 = (FStar_All.pipe_right branches (FStar_List.map (fun _43_285 -> (match (_43_285) with
| (p, wopt, e) -> begin
(let _134_144 = (FStar_All.pipe_right p pat_to_string)
in (let _134_143 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _134_141 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _134_141))
end)
in (let _134_142 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _134_144 _134_143 _134_142))))
end))))
in (FStar_Util.concat_l "\n\t|" _134_145))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _134_147 _134_146)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _134_149 = (term_to_string t)
in (let _134_148 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _134_149 _134_148)))
end else begin
(term_to_string t)
end
end
| _43_294 -> begin
(tag_of_term x)
end)))
and pat_to_string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _134_154 = (fv_to_string l)
in (let _134_153 = (let _134_152 = (FStar_List.map (fun _43_302 -> (match (_43_302) with
| (x, b) -> begin
(let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _134_152 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _134_154 _134_153)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _43_306) -> begin
(let _134_155 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _134_155))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(bv_to_string x)
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _134_156 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _134_156))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _134_157 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _134_157))
end))
and lbs_to_string = (fun quals lbs -> (let _134_169 = (quals_to_string quals)
in (let _134_168 = (let _134_167 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _134_166 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _134_165 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _134_162 = (let _134_161 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat "<" _134_161))
in (Prims.strcat _134_162 ">"))
end else begin
""
end
in (let _134_164 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _134_163 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _134_166 _134_165 _134_164 _134_163))))))))
in (FStar_Util.concat_l "\n and " _134_167))
in (FStar_Util.format3 "%slet %s %s" _134_169 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _134_168))))
and lcomp_to_string = (fun lc -> (let _134_172 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _134_171 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _134_172 _134_171))))
and imp_to_string = (fun s _43_5 -> (match (_43_5) with
| Some (FStar_Syntax_Syntax.Implicit) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _43_328 -> begin
s
end))
and binder_to_string' = (fun is_arrow b -> (let _43_333 = b
in (match (_43_333) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(term_to_string a.FStar_Syntax_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_bound_var_types)))) then begin
(let _134_177 = (nm_to_string a)
in (imp_to_string _134_177 imp))
end else begin
(let _134_181 = (let _134_180 = (let _134_178 = (nm_to_string a)
in (Prims.strcat _134_178 ":"))
in (let _134_179 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat _134_180 _134_179)))
in (imp_to_string _134_181 imp))
end
end
end)))
and binder_to_string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string = (fun b -> (binder_to_string' true b))
and binders_to_string = (fun sep bs -> (let bs = if (FStar_ST.read FStar_Options.print_implicits) then begin
bs
end else begin
(filter_imp bs)
end
in if (sep = " -> ") then begin
(let _134_186 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _134_186 (FStar_String.concat sep)))
end else begin
(let _134_187 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _134_187 (FStar_String.concat sep)))
end))
and arg_to_string = (fun _43_6 -> (match (_43_6) with
| (a, imp) -> begin
(let _134_189 = (term_to_string a)
in (imp_to_string _134_189 imp))
end))
and args_to_string = (fun args -> (let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _134_191 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _134_191 (FStar_String.concat " ")))))
and comp_to_string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(match ((let _134_193 = (FStar_Syntax_Subst.compress t)
in _134_193.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_43_349) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _43_352 -> begin
(let _134_194 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _134_194))
end)
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(match ((let _134_195 = (FStar_Syntax_Subst.compress t)
in _134_195.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_43_356) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _43_359 -> begin
(let _134_196 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _134_196))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(let basic = if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _43_7 -> (match (_43_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _43_365 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args)))) then begin
(let _134_198 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _134_198))
end else begin
if (((not ((FStar_ST.read FStar_Options.print_effect_args))) && (not ((FStar_ST.read FStar_Options.print_implicits)))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _43_8 -> (match (_43_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _43_369 -> begin
false
end))))) then begin
(let _134_200 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _134_200))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _134_204 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _134_203 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _134_202 = (let _134_201 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _134_201 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _134_204 _134_203 _134_202))))
end else begin
(let _134_206 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _134_205 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _134_206 _134_205)))
end
end
end
end
in (let dec = (let _134_210 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _43_9 -> (match (_43_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _134_209 = (let _134_208 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _134_208))
in (_134_209)::[])
end
| _43_375 -> begin
[]
end))))
in (FStar_All.pipe_right _134_210 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and formula_to_string = (fun phi -> (term_to_string phi))

let tscheme_to_string = (fun _43_380 -> (match (_43_380) with
| (us, t) -> begin
(let _134_215 = (univ_names_to_string us)
in (let _134_214 = (term_to_string t)
in (FStar_Util.format2 "<%s> %s" _134_215 _134_214)))
end))

let eff_decl_to_string = (fun ed -> (let _134_251 = (let _134_250 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _134_249 = (let _134_248 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (let _134_247 = (let _134_246 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _134_245 = (let _134_244 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _134_243 = (let _134_242 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret)
in (let _134_241 = (let _134_240 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _134_239 = (let _134_238 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wlp)
in (let _134_237 = (let _134_236 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _134_235 = (let _134_234 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _134_233 = (let _134_232 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wlp)
in (let _134_231 = (let _134_230 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_binop)
in (let _134_229 = (let _134_228 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_as_type)
in (let _134_227 = (let _134_226 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _134_225 = (let _134_224 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _134_223 = (let _134_222 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _134_221 = (let _134_220 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _134_219 = (let _134_218 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (_134_218)::[])
in (_134_220)::_134_219))
in (_134_222)::_134_221))
in (_134_224)::_134_223))
in (_134_226)::_134_225))
in (_134_228)::_134_227))
in (_134_230)::_134_229))
in (_134_232)::_134_231))
in (_134_234)::_134_233))
in (_134_236)::_134_235))
in (_134_238)::_134_237))
in (_134_240)::_134_239))
in (_134_242)::_134_241))
in (_134_244)::_134_243))
in (_134_246)::_134_245))
in (_134_248)::_134_247))
in (_134_250)::_134_249))
in (FStar_Util.format "new_effect { %s<%s> %s : %s \n\tret         = %s\n; bind_wp     = %s\n; bind_wlp    = %s\n; if_then_else= %s\n; ite_wp      = %s\n; ite_wlp     = %s\n; wp_binop    = %s\n; wp_as_type  = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s}\n" _134_251)))

let rec sigelt_to_string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions, _43_385) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _43_391) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (lid, univs, tps, k, _43_399, _43_401, quals, _43_404)) -> begin
(let _134_256 = (quals_to_string quals)
in (let _134_255 = (binders_to_string " " tps)
in (let _134_254 = (term_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _134_256 lid.FStar_Ident.str _134_255 _134_254))))
end
| FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (lid, univs, t, _43_411, _43_413, _43_415, _43_417, _43_419)) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _43_424 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_43_424) with
| (univs, t) -> begin
(let _134_258 = (univ_names_to_string univs)
in (let _134_257 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _134_258 lid.FStar_Ident.str _134_257)))
end))
end else begin
(let _134_259 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _134_259))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _43_430) -> begin
(let _43_435 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_43_435) with
| (univs, t) -> begin
(let _134_263 = (quals_to_string quals)
in (let _134_262 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _134_260 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _134_260))
end else begin
""
end
in (let _134_261 = (term_to_string t)
in (FStar_Util.format4 "%s val %s %s : %s" _134_263 lid.FStar_Ident.str _134_262 _134_261))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _43_439, _43_441) -> begin
(let _134_264 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _134_264))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _43_446, _43_448, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _43_454) -> begin
(let _134_265 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _134_265))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _43_459, _43_461, _43_463) -> begin
(let _134_266 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _134_266 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _43_468) -> begin
(eff_decl_to_string ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(let _43_477 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst se.FStar_Syntax_Syntax.lift) (Prims.snd se.FStar_Syntax_Syntax.lift))
in (match (_43_477) with
| (us, t) -> begin
(let _134_270 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _134_269 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _134_268 = (univ_names_to_string us)
in (let _134_267 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _134_270 _134_269 _134_268 _134_267)))))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, _43_480, tps, c, _43_484, _43_486) -> begin
(let _134_273 = (sli l)
in (let _134_272 = (binders_to_string " " tps)
in (let _134_271 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _134_273 _134_272 _134_271))))
end))

let format_error = (fun r msg -> (let _134_278 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _134_278 msg)))

let rec sigelt_to_string_short = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_43_493, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (l); FStar_Syntax_Syntax.lbunivs = _43_500; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _43_497; FStar_Syntax_Syntax.lbdef = _43_495}::[]), _43_507, _43_509, _43_511) -> begin
(let _134_281 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Ident.str _134_281))
end
| _43_515 -> begin
(let _134_284 = (let _134_283 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _134_283 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _134_284 (FStar_String.concat ", ")))
end))

let rec modul_to_string = (fun m -> (let _134_289 = (sli m.FStar_Syntax_Syntax.name)
in (let _134_288 = (let _134_287 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _134_287 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _134_289 _134_288))))

let subst_elt_to_string = (fun _43_10 -> (match (_43_10) with
| FStar_Syntax_Syntax.DB (i, t) -> begin
(let _134_293 = (FStar_Util.string_of_int i)
in (let _134_292 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _134_293 _134_292)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _134_295 = (bv_to_string x)
in (let _134_294 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _134_295 _134_294)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _134_297 = (bv_to_string x)
in (let _134_296 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _134_297 _134_296)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _134_299 = (FStar_Util.string_of_int i)
in (let _134_298 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _134_299 _134_298)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _134_300 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _134_300))
end))

let subst_to_string = (fun s -> (let _134_303 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _134_303 (FStar_String.concat "; "))))




