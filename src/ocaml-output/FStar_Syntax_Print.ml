
open Prims
let lid_to_string = (fun l -> l.FStar_Ident.str)

let fv_to_string = (fun fv -> (lid_to_string (Prims.fst fv).FStar_Syntax_Syntax.v))

let bv_to_string = (fun bv -> (let _94_6 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "#") _94_6)))

let nm_to_string = (fun bv -> if (FStar_ST.read FStar_Options.print_real_names) then begin
(bv_to_string bv)
end else begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)

let db_to_string = (fun bv -> (let _94_11 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "@") _94_11)))

let infix_prim_ops = ((FStar_Syntax_Const.op_Addition, "+"))::((FStar_Syntax_Const.op_Subtraction, "-"))::((FStar_Syntax_Const.op_Multiply, "*"))::((FStar_Syntax_Const.op_Division, "/"))::((FStar_Syntax_Const.op_Eq, "="))::((FStar_Syntax_Const.op_ColonEq, ":="))::((FStar_Syntax_Const.op_notEq, "<>"))::((FStar_Syntax_Const.op_And, "&&"))::((FStar_Syntax_Const.op_Or, "||"))::((FStar_Syntax_Const.op_LTE, "<="))::((FStar_Syntax_Const.op_GTE, ">="))::((FStar_Syntax_Const.op_LT, "<"))::((FStar_Syntax_Const.op_GT, ">"))::((FStar_Syntax_Const.op_Modulus, "mod"))::((FStar_Syntax_Const.and_lid, "/\\"))::((FStar_Syntax_Const.or_lid, "\\/"))::((FStar_Syntax_Const.imp_lid, "==>"))::((FStar_Syntax_Const.iff_lid, "<==>"))::((FStar_Syntax_Const.precedes_lid, "<<"))::((FStar_Syntax_Const.eq2_lid, "=="))::[]

let unary_prim_ops = ((FStar_Syntax_Const.op_Negation, "not"))::((FStar_Syntax_Const.op_Minus, "-"))::((FStar_Syntax_Const.not_lid, "~"))::[]

let is_prim_op = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _41_20) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v)))
end
| _41_24 -> begin
false
end))

let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _41_28) -> begin
fv.FStar_Syntax_Syntax.v
end
| _41_32 -> begin
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

let is_inr = (fun _41_1 -> (match (_41_1) with
| FStar_Util.Inl (_41_42) -> begin
false
end
| FStar_Util.Inr (_41_45) -> begin
true
end))

let rec reconstruct_lex = (fun e -> (match ((let _94_32 = (FStar_Syntax_Subst.compress e)
in _94_32.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(let args = (FStar_List.filter (fun a -> ((Prims.snd a) <> Some (FStar_Syntax_Syntax.Implicit))) args)
in (let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = 2)) then begin
(match ((let _94_34 = (FStar_List.nth exps 1)
in (reconstruct_lex _94_34))) with
| Some (xs) -> begin
(let _94_36 = (let _94_35 = (FStar_List.nth exps 0)
in (_94_35)::xs)
in Some (_94_36))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _41_59 -> begin
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

let find_lid = (fun x xs -> (let _94_50 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _94_50)))

let infix_prim_op_to_string = (fun e -> (let _94_52 = (get_lid e)
in (find_lid _94_52 infix_prim_ops)))

let unary_prim_op_to_string = (fun e -> (let _94_54 = (get_lid e)
in (find_lid _94_54 unary_prim_ops)))

let quant_to_string = (fun t -> (let _94_56 = (get_lid t)
in (find_lid _94_56 quants)))

let rec sli = (fun l -> if (FStar_ST.read FStar_Options.print_real_names) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)

let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _41_2 -> (match (_41_2) with
| (_41_77, Some (FStar_Syntax_Syntax.Implicit)) -> begin
false
end
| _41_82 -> begin
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
| FStar_Const.Const_string (bytes, _41_96) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_41_100) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x) -> begin
x
end
| FStar_Const.Const_int64 (_41_105) -> begin
"<int64>"
end
| FStar_Const.Const_uint8 (_41_108) -> begin
"<uint8>"
end))

let lbname_to_string = (fun _41_3 -> (match (_41_3) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l)
end))

let tag_of_term = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _94_67 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _94_67))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _94_68 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _94_68))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _94_69 = (lid_to_string (Prims.fst x).FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _94_69))
end
| FStar_Syntax_Syntax.Tm_uinst (_41_123) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (_41_126) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (_41_129) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (_41_132) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (_41_135) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (_41_138) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (_41_141) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (_41_144) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (_41_147) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (_41_150) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (_41_153) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (_41_156, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
"Tm_delayed"
end
| Some (_41_162) -> begin
"Tm_delayed-resolved"
end)
end
| FStar_Syntax_Syntax.Tm_meta (_41_165) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))

let uvar_to_string = (fun u -> if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _94_74 = (let _94_73 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _94_73 FStar_Util.string_of_int))
in (Prims.strcat "?" _94_74))
end)

let rec univ_to_string = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_unif (u) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(let _94_77 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _94_77))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _94_78 = (univ_to_string u)
in (FStar_Util.format1 "(S %s)" _94_78))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _94_80 = (let _94_79 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _94_79 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _94_80))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))

let univs_to_string = (fun us -> (let _94_83 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _94_83 (FStar_String.concat ", "))))

let univ_names_to_string = (fun us -> (let _94_87 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _94_87 (FStar_String.concat ", "))))

let qual_to_string = (fun _41_4 -> (match (_41_4) with
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
(let _94_90 = (lid_to_string l)
in (FStar_Util.format1 "default %s" _94_90))
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(let _94_91 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _94_91))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _94_92 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _94_92 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(let _94_94 = (let _94_93 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _94_93 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordType %s)" _94_94))
end
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
(let _94_96 = (let _94_95 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _94_95 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordConstructor %s)" _94_96))
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
| _41_216 -> begin
(let _94_100 = (let _94_99 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _94_99 (FStar_String.concat " ")))
in (Prims.strcat _94_100 " "))
end))

let rec term_to_string = (fun x -> (let x = (FStar_Syntax_Subst.compress x)
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_41_220) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_41_223, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, _41_229) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, _41_240) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _94_122 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _94_122))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _94_124 = (binders_to_string " -> " bs)
in (let _94_123 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _94_124 _94_123)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (l) when (FStar_ST.read FStar_Options.print_implicits) -> begin
(let _94_128 = (binders_to_string " " bs)
in (let _94_127 = (term_to_string t2)
in (let _94_126 = (let _94_125 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _94_125))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _94_128 _94_127 _94_126))))
end
| _41_259 -> begin
(let _94_130 = (binders_to_string " " bs)
in (let _94_129 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _94_130 _94_129)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _94_133 = (bv_to_string xt)
in (let _94_132 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _94_131 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _94_133 _94_132 _94_131))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _94_135 = (term_to_string t)
in (let _94_134 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _94_135 _94_134)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _94_137 = (lbs_to_string [] lbs)
in (let _94_136 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _94_137 _94_136)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _41_275) -> begin
(let _94_139 = (term_to_string e)
in (let _94_138 = (term_to_string t)
in (FStar_Util.format2 "(%s : %s)" _94_139 _94_138)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _94_147 = (term_to_string head)
in (let _94_146 = (let _94_145 = (FStar_All.pipe_right branches (FStar_List.map (fun _41_285 -> (match (_41_285) with
| (p, wopt, e) -> begin
(let _94_144 = (FStar_All.pipe_right p pat_to_string)
in (let _94_143 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _94_141 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _94_141))
end)
in (let _94_142 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _94_144 _94_143 _94_142))))
end))))
in (FStar_Util.concat_l "\n\t|" _94_145))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _94_147 _94_146)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _94_149 = (term_to_string t)
in (let _94_148 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _94_149 _94_148)))
end else begin
(term_to_string t)
end
end
| _41_294 -> begin
(tag_of_term x)
end)))
and pat_to_string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _94_154 = (fv_to_string l)
in (let _94_153 = (let _94_152 = (FStar_List.map (fun _41_302 -> (match (_41_302) with
| (x, b) -> begin
(let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _94_152 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _94_154 _94_153)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _41_306) -> begin
(let _94_155 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _94_155))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(bv_to_string x)
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _94_156 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _94_156))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _94_157 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _94_157))
end))
and lbs_to_string = (fun quals lbs -> (let _94_169 = (quals_to_string quals)
in (let _94_168 = (let _94_167 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _94_166 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _94_165 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _94_162 = (let _94_161 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat "<" _94_161))
in (Prims.strcat _94_162 ">"))
end else begin
""
end
in (let _94_164 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _94_163 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _94_166 _94_165 _94_164 _94_163))))))))
in (FStar_Util.concat_l "\n and " _94_167))
in (FStar_Util.format3 "%slet %s %s" _94_169 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _94_168))))
and lcomp_to_string = (fun lc -> (let _94_172 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _94_171 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _94_172 _94_171))))
and imp_to_string = (fun s _41_5 -> (match (_41_5) with
| Some (FStar_Syntax_Syntax.Implicit) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _41_328 -> begin
s
end))
and binder_to_string' = (fun is_arrow b -> (let _41_333 = b
in (match (_41_333) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(term_to_string a.FStar_Syntax_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_bound_var_types)))) then begin
(let _94_177 = (nm_to_string a)
in (imp_to_string _94_177 imp))
end else begin
(let _94_181 = (let _94_180 = (let _94_178 = (nm_to_string a)
in (Prims.strcat _94_178 ":"))
in (let _94_179 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat _94_180 _94_179)))
in (imp_to_string _94_181 imp))
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
(let _94_186 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _94_186 (FStar_String.concat sep)))
end else begin
(let _94_187 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _94_187 (FStar_String.concat sep)))
end))
and arg_to_string = (fun _41_6 -> (match (_41_6) with
| (a, imp) -> begin
(let _94_189 = (term_to_string a)
in (imp_to_string _94_189 imp))
end))
and args_to_string = (fun args -> (let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _94_191 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _94_191 (FStar_String.concat " ")))))
and comp_to_string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(match ((let _94_193 = (FStar_Syntax_Subst.compress t)
in _94_193.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_41_349) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _41_352 -> begin
(let _94_194 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _94_194))
end)
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(match ((let _94_195 = (FStar_Syntax_Subst.compress t)
in _94_195.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_41_356) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _41_359 -> begin
(let _94_196 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _94_196))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(let basic = if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _41_7 -> (match (_41_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _41_365 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args)))) then begin
(let _94_198 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _94_198))
end else begin
if (((not ((FStar_ST.read FStar_Options.print_effect_args))) && (not ((FStar_ST.read FStar_Options.print_implicits)))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _41_8 -> (match (_41_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _41_369 -> begin
false
end))))) then begin
(let _94_200 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _94_200))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _94_204 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _94_203 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _94_202 = (let _94_201 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _94_201 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _94_204 _94_203 _94_202))))
end else begin
(let _94_206 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _94_205 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _94_206 _94_205)))
end
end
end
end
in (let dec = (let _94_210 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _41_9 -> (match (_41_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _94_209 = (let _94_208 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _94_208))
in (_94_209)::[])
end
| _41_375 -> begin
[]
end))))
in (FStar_All.pipe_right _94_210 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and formula_to_string = (fun phi -> (term_to_string phi))

let tscheme_to_string = (fun _41_380 -> (match (_41_380) with
| (us, t) -> begin
(let _94_215 = (univ_names_to_string us)
in (let _94_214 = (term_to_string t)
in (FStar_Util.format2 "<%s> %s" _94_215 _94_214)))
end))

let eff_decl_to_string = (fun ed -> (let _94_251 = (let _94_250 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _94_249 = (let _94_248 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (let _94_247 = (let _94_246 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _94_245 = (let _94_244 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _94_243 = (let _94_242 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret)
in (let _94_241 = (let _94_240 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _94_239 = (let _94_238 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wlp)
in (let _94_237 = (let _94_236 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _94_235 = (let _94_234 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _94_233 = (let _94_232 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wlp)
in (let _94_231 = (let _94_230 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_binop)
in (let _94_229 = (let _94_228 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_as_type)
in (let _94_227 = (let _94_226 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _94_225 = (let _94_224 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _94_223 = (let _94_222 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _94_221 = (let _94_220 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _94_219 = (let _94_218 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (_94_218)::[])
in (_94_220)::_94_219))
in (_94_222)::_94_221))
in (_94_224)::_94_223))
in (_94_226)::_94_225))
in (_94_228)::_94_227))
in (_94_230)::_94_229))
in (_94_232)::_94_231))
in (_94_234)::_94_233))
in (_94_236)::_94_235))
in (_94_238)::_94_237))
in (_94_240)::_94_239))
in (_94_242)::_94_241))
in (_94_244)::_94_243))
in (_94_246)::_94_245))
in (_94_248)::_94_247))
in (_94_250)::_94_249))
in (FStar_Util.format "new_effect { %s<%s> %s : %s \n\tret         = %s\n; bind_wp     = %s\n; bind_wlp    = %s\n; if_then_else= %s\n; ite_wp      = %s\n; ite_wlp     = %s\n; wp_binop    = %s\n; wp_as_type  = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s}\n" _94_251)))

let rec sigelt_to_string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions, _41_385) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _41_391) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (lid, univs, tps, k, _41_399, _41_401, quals, _41_404)) -> begin
(let _94_256 = (quals_to_string quals)
in (let _94_255 = (binders_to_string " " tps)
in (let _94_254 = (term_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _94_256 lid.FStar_Ident.str _94_255 _94_254))))
end
| FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (lid, univs, t, _41_411, _41_413, _41_415, _41_417, _41_419)) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _41_424 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_41_424) with
| (univs, t) -> begin
(let _94_258 = (univ_names_to_string univs)
in (let _94_257 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _94_258 lid.FStar_Ident.str _94_257)))
end))
end else begin
(let _94_259 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _94_259))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _41_430) -> begin
(let _41_435 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_41_435) with
| (univs, t) -> begin
(let _94_263 = (quals_to_string quals)
in (let _94_262 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _94_260 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _94_260))
end else begin
""
end
in (let _94_261 = (term_to_string t)
in (FStar_Util.format4 "%s val %s %s : %s" _94_263 lid.FStar_Ident.str _94_262 _94_261))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _41_439, _41_441) -> begin
(let _94_264 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _94_264))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _41_446, _41_448, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _41_454) -> begin
(let _94_265 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _94_265))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _41_459, _41_461, _41_463) -> begin
(let _94_266 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _94_266 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _41_468) -> begin
(eff_decl_to_string ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(let _41_477 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst se.FStar_Syntax_Syntax.lift) (Prims.snd se.FStar_Syntax_Syntax.lift))
in (match (_41_477) with
| (us, t) -> begin
(let _94_270 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _94_269 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _94_268 = (univ_names_to_string us)
in (let _94_267 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _94_270 _94_269 _94_268 _94_267)))))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, _41_480, tps, c, _41_484, _41_486) -> begin
(let _94_273 = (sli l)
in (let _94_272 = (binders_to_string " " tps)
in (let _94_271 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _94_273 _94_272 _94_271))))
end))

let format_error = (fun r msg -> (let _94_278 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _94_278 msg)))

let rec sigelt_to_string_short = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_41_493, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (l); FStar_Syntax_Syntax.lbunivs = _41_500; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _41_497; FStar_Syntax_Syntax.lbdef = _41_495}::[]), _41_507, _41_509, _41_511) -> begin
(let _94_281 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" l.FStar_Ident.str _94_281))
end
| _41_515 -> begin
(let _94_284 = (let _94_283 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _94_283 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _94_284 (FStar_String.concat ", ")))
end))

let rec modul_to_string = (fun m -> (let _94_289 = (sli m.FStar_Syntax_Syntax.name)
in (let _94_288 = (let _94_287 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _94_287 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _94_289 _94_288))))

let subst_elt_to_string = (fun _41_10 -> (match (_41_10) with
| FStar_Syntax_Syntax.DB (i, t) -> begin
(let _94_293 = (FStar_Util.string_of_int i)
in (let _94_292 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _94_293 _94_292)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _94_295 = (bv_to_string x)
in (let _94_294 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _94_295 _94_294)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _94_297 = (bv_to_string x)
in (let _94_296 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _94_297 _94_296)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _94_299 = (FStar_Util.string_of_int i)
in (let _94_298 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _94_299 _94_298)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _94_300 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _94_300))
end))

let subst_to_string = (fun s -> (let _94_303 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _94_303 (FStar_String.concat "; "))))




