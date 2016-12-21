
open Prims

let sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_Options.print_real_names ()) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)


let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> (sli l))


let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _138_10 = (let _138_9 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "#" _138_9))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _138_10)))


let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> if (FStar_Options.print_real_names ()) then begin
(bv_to_string bv)
end else begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)


let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _138_16 = (let _138_15 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "@" _138_15))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _138_16)))


let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Syntax_Const.op_Addition), ("+")))::(((FStar_Syntax_Const.op_Subtraction), ("-")))::(((FStar_Syntax_Const.op_Multiply), ("*")))::(((FStar_Syntax_Const.op_Division), ("/")))::(((FStar_Syntax_Const.op_Eq), ("=")))::(((FStar_Syntax_Const.op_ColonEq), (":=")))::(((FStar_Syntax_Const.op_notEq), ("<>")))::(((FStar_Syntax_Const.op_And), ("&&")))::(((FStar_Syntax_Const.op_Or), ("||")))::(((FStar_Syntax_Const.op_LTE), ("<=")))::(((FStar_Syntax_Const.op_GTE), (">=")))::(((FStar_Syntax_Const.op_LT), ("<")))::(((FStar_Syntax_Const.op_GT), (">")))::(((FStar_Syntax_Const.op_Modulus), ("mod")))::(((FStar_Syntax_Const.and_lid), ("/\\")))::(((FStar_Syntax_Const.or_lid), ("\\/")))::(((FStar_Syntax_Const.imp_lid), ("==>")))::(((FStar_Syntax_Const.iff_lid), ("<==>")))::(((FStar_Syntax_Const.precedes_lid), ("<<")))::(((FStar_Syntax_Const.eq2_lid), ("==")))::(((FStar_Syntax_Const.eq3_lid), ("===")))::[]


let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Syntax_Const.op_Negation), ("not")))::(((FStar_Syntax_Const.op_Minus), ("-")))::(((FStar_Syntax_Const.not_lid), ("~")))::[]


let is_prim_op = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
end
| _40_25 -> begin
false
end))


let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| _40_30 -> begin
(FStar_All.failwith "get_lid")
end))


let is_infix_prim_op : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split infix_prim_ops)) e))


let is_unary_prim_op : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split unary_prim_ops)) e))


let quants : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Syntax_Const.forall_lid), ("forall")))::(((FStar_Syntax_Const.exists_lid), ("exists")))::[]


type exp =
FStar_Syntax_Syntax.term


let is_b2t : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op ((FStar_Syntax_Const.b2t_lid)::[]) t))


let is_quant : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op (Prims.fst (FStar_List.split quants)) t))


let is_ite : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op ((FStar_Syntax_Const.ite_lid)::[]) t))


let is_lex_cons : exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Syntax_Const.lexcons_lid)::[]) f))


let is_lex_top : exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Syntax_Const.lextop_lid)::[]) f))


let is_inr = (fun _40_1 -> (match (_40_1) with
| FStar_Util.Inl (_40_40) -> begin
false
end
| FStar_Util.Inr (_40_43) -> begin
true
end))


let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _40_2 -> (match (_40_2) with
| (_40_48, Some (FStar_Syntax_Syntax.Implicit (_40_50))) -> begin
false
end
| _40_55 -> begin
true
end)))))


let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _138_39 = (FStar_Syntax_Subst.compress e)
in _138_39.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args = (filter_imp args)
in (

let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = (Prims.parse_int "2"))) then begin
(match ((let _138_40 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex _138_40))) with
| Some (xs) -> begin
(let _138_42 = (let _138_41 = (FStar_List.nth exps (Prims.parse_int "0"))
in (_138_41)::xs)
in Some (_138_42))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _40_67 -> begin
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


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _138_56 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _138_56)))


let infix_prim_op_to_string = (fun e -> (let _138_58 = (get_lid e)
in (find_lid _138_58 infix_prim_ops)))


let unary_prim_op_to_string = (fun e -> (let _138_60 = (get_lid e)
in (find_lid _138_60 unary_prim_ops)))


let quant_to_string = (fun t -> (let _138_62 = (get_lid t)
in (find_lid _138_62 quants)))


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
| FStar_Const.Const_string (bytes, _40_90) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_40_94) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x, _40_98) -> begin
x
end
| FStar_Const.Const_char (c) -> begin
(Prims.strcat "\'" (Prims.strcat (FStar_Util.string_of_char c) "\'"))
end
| FStar_Const.Const_range (r) -> begin
(FStar_Range.string_of_range r)
end
| FStar_Const.Const_reify -> begin
"reify"
end
| FStar_Const.Const_reflect (l) -> begin
(let _138_65 = (sli l)
in (FStar_Util.format1 "[[%s.reflect]]" _138_65))
end))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun _40_3 -> (match (_40_3) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _138_70 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _138_70))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _138_71 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _138_71))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _138_72 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _138_72))
end
| FStar_Syntax_Syntax.Tm_uinst (_40_121) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (_40_124) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (_40_127) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (_40_130) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (_40_133) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (_40_136) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (_40_139) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (_40_142) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (_40_145) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (_40_148) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (_40_151) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (_40_154, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
"Tm_delayed"
end
| Some (_40_160) -> begin
"Tm_delayed-resolved"
end)
end
| FStar_Syntax_Syntax.Tm_meta (_40_163) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))


let uvar_to_string = (fun u -> if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _138_77 = (let _138_76 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _138_76 FStar_Util.string_of_int))
in (Prims.strcat "?" _138_77))
end)


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_unif (u) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(Prims.strcat "n" x.FStar_Ident.idText)
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(let _138_80 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _138_80))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _138_81 = (univ_to_string u)
in (FStar_Util.format1 "(S %s)" _138_81))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _138_83 = (let _138_82 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _138_82 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _138_83))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _138_86 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _138_86 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _138_90 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _138_90 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun _40_4 -> (match (_40_4) with
| FStar_Syntax_Syntax.Assumption -> begin
"assume"
end
| FStar_Syntax_Syntax.New -> begin
"new"
end
| FStar_Syntax_Syntax.Private -> begin
"private"
end
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
"unfold"
end
| FStar_Syntax_Syntax.Inline_for_extraction -> begin
"inline"
end
| FStar_Syntax_Syntax.NoExtract -> begin
"noextract"
end
| FStar_Syntax_Syntax.Visible_default -> begin
"visible"
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
| FStar_Syntax_Syntax.Unopteq -> begin
"unopteq"
end
| FStar_Syntax_Syntax.Logic -> begin
"logic"
end
| FStar_Syntax_Syntax.TotalEffect -> begin
"total"
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(let _138_93 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _138_93))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _138_94 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _138_94 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(let _138_98 = (let _138_95 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path _138_95))
in (let _138_97 = (let _138_96 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right _138_96 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" _138_98 _138_97)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(let _138_102 = (let _138_99 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path _138_99))
in (let _138_101 = (let _138_100 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right _138_100 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" _138_102 _138_101)))
end
| FStar_Syntax_Syntax.ExceptionConstructor -> begin
"ExceptionConstructor"
end
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
"HasMaskedEffect"
end
| FStar_Syntax_Syntax.Effect -> begin
"Effect"
end
| FStar_Syntax_Syntax.Reifiable -> begin
"reify"
end
| FStar_Syntax_Syntax.Reflectable (l) -> begin
(FStar_Util.format1 "(reflect %s)" l.FStar_Ident.str)
end))


let quals_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| _40_220 -> begin
(let _138_105 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _138_105 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| _40_224 -> begin
(let _138_108 = (quals_to_string quals)
in (Prims.strcat _138_108 " "))
end))


let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let x = (FStar_Syntax_Subst.compress x)
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_40_228) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_40_231, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (let _138_134 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _138_133 = (FStar_All.pipe_right args (FStar_List.map (fun _40_244 -> (match (_40_244) with
| (t, _40_243) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _138_133 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _138_134 (FStar_String.concat "\\/")))
in (let _138_135 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _138_135)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _138_139 = (tag_of_term t)
in (let _138_138 = (sli m)
in (let _138_137 = (term_to_string t')
in (let _138_136 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s )" _138_139 _138_138 _138_137 _138_136)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1)) -> begin
(let _138_143 = (tag_of_term t)
in (let _138_142 = (term_to_string t)
in (let _138_141 = (sli m0)
in (let _138_140 = (sli m1)
in (FStar_Util.format4 "(MonadicLift-%s{%s} %s -> %s)" _138_143 _138_142 _138_141 _138_140)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(let _138_145 = (FStar_Range.string_of_range r)
in (let _138_144 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l _138_145 _138_144)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _40_270) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, _40_281) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_Options.print_universes ()) then begin
(let _138_146 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _138_146))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _138_148 = (binders_to_string " -> " bs)
in (let _138_147 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _138_148 _138_147)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
(let _138_152 = (binders_to_string " " bs)
in (let _138_151 = (term_to_string t2)
in (let _138_150 = (let _138_149 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _138_149))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _138_152 _138_151 _138_150))))
end
| Some (FStar_Util.Inr (l, flags)) when (FStar_Options.print_implicits ()) -> begin
(let _138_154 = (binders_to_string " " bs)
in (let _138_153 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))" _138_154 _138_153 l.FStar_Ident.str)))
end
| _40_306 -> begin
(let _138_156 = (binders_to_string " " bs)
in (let _138_155 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _138_156 _138_155)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _138_159 = (bv_to_string xt)
in (let _138_158 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _138_157 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _138_159 _138_158 _138_157))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _138_161 = (term_to_string t)
in (let _138_160 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _138_161 _138_160)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _138_163 = (lbs_to_string [] lbs)
in (let _138_162 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _138_163 _138_162)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), eff_name) -> begin
(let _138_167 = (term_to_string e)
in (let _138_166 = (let _138_164 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right _138_164 (FStar_Util.dflt "default")))
in (let _138_165 = (term_to_string t)
in (FStar_Util.format3 "(%s <: [%s] %s)" _138_167 _138_166 _138_165))))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _40_329) -> begin
(let _138_169 = (term_to_string e)
in (let _138_168 = (comp_to_string c)
in (FStar_Util.format2 "(%s <: %s)" _138_169 _138_168)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _138_177 = (term_to_string head)
in (let _138_176 = (let _138_175 = (FStar_All.pipe_right branches (FStar_List.map (fun _40_339 -> (match (_40_339) with
| (p, wopt, e) -> begin
(let _138_174 = (FStar_All.pipe_right p pat_to_string)
in (let _138_173 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _138_171 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _138_171))
end)
in (let _138_172 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _138_174 _138_173 _138_172))))
end))))
in (FStar_Util.concat_l "\n\t|" _138_175))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _138_177 _138_176)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_Options.print_universes ()) then begin
(let _138_179 = (term_to_string t)
in (let _138_178 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _138_179 _138_178)))
end else begin
(term_to_string t)
end
end
| _40_348 -> begin
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _138_184 = (fv_to_string l)
in (let _138_183 = (let _138_182 = (FStar_List.map (fun _40_356 -> (match (_40_356) with
| (x, b) -> begin
(

let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _138_182 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _138_184 _138_183)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _40_360) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _138_186 = (bv_to_string x)
in (let _138_185 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" _138_186 _138_185)))
end else begin
(let _138_187 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _138_187))
end
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _138_189 = (bv_to_string x)
in (let _138_188 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" _138_189 _138_188)))
end else begin
(bv_to_string x)
end
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_Options.print_real_names ()) then begin
(let _138_190 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _138_190))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _138_191 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _138_191))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (

let lbs = if (FStar_Options.print_universes ()) then begin
(let _138_197 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _40_376 = (let _138_195 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _138_195))
in (match (_40_376) with
| (us, td) -> begin
(

let _40_394 = (match ((let _138_196 = (FStar_Syntax_Subst.compress td)
in _138_196.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_40_378, ((t, _40_385))::((d, _40_381))::[]) -> begin
((t), (d))
end
| _40_391 -> begin
(FStar_All.failwith "Impossibe")
end)
in (match (_40_394) with
| (t, d) -> begin
(

let _40_395 = lb
in {FStar_Syntax_Syntax.lbname = _40_395.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _40_395.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((Prims.fst lbs)), (_138_197)))
end else begin
lbs
end
in (let _138_207 = (quals_to_string' quals)
in (let _138_206 = (let _138_205 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _138_204 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _138_203 = if (FStar_Options.print_universes ()) then begin
(let _138_200 = (let _138_199 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat _138_199 ">"))
in (Prims.strcat "<" _138_200))
end else begin
""
end
in (let _138_202 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _138_201 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _138_204 _138_203 _138_202 _138_201))))))))
in (FStar_Util.concat_l "\n and " _138_205))
in (FStar_Util.format3 "%slet %s %s" _138_207 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _138_206)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> if (FStar_Options.print_effect_args ()) then begin
(let _138_209 = (lc.FStar_Syntax_Syntax.comp ())
in (comp_to_string _138_209))
end else begin
(let _138_211 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _138_210 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _138_211 _138_210)))
end)
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s _40_5 -> (match (_40_5) with
| Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
(Prims.strcat "#." s)
end
| Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "$" s)
end
| _40_411 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (

let _40_416 = b
in (match (_40_416) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(let _138_216 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" _138_216))
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_bound_var_types ())))) then begin
(let _138_217 = (nm_to_string a)
in (imp_to_string _138_217 imp))
end else begin
(let _138_221 = (let _138_220 = (nm_to_string a)
in (let _138_219 = (let _138_218 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" _138_218))
in (Prims.strcat _138_220 _138_219)))
in (imp_to_string _138_221 imp))
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
(let _138_226 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _138_226 (FStar_String.concat sep)))
end else begin
(let _138_227 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _138_227 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _40_6 -> (match (_40_6) with
| (a, imp) -> begin
(let _138_229 = (term_to_string a)
in (imp_to_string _138_229 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args = if (FStar_Options.print_implicits ()) then begin
args
end else begin
(filter_imp args)
end
in (let _138_231 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _138_231 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _40_431) -> begin
(match ((let _138_233 = (FStar_Syntax_Subst.compress t)
in _138_233.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_40_435) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _40_438 -> begin
(let _138_234 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _138_234))
end)
end
| FStar_Syntax_Syntax.GTotal (t, _40_441) -> begin
(match ((let _138_235 = (FStar_Syntax_Subst.compress t)
in _138_235.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_40_445) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _40_448 -> begin
(let _138_236 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _138_236))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let basic = if (FStar_Options.print_effect_args ()) then begin
(let _138_242 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _138_241 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _138_240 = (let _138_237 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _138_237 (FStar_String.concat ", ")))
in (let _138_239 = (let _138_238 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right _138_238 (FStar_String.concat " ")))
in (FStar_Util.format4 "%s (%s) %s (attributes %s)" _138_242 _138_241 _138_240 _138_239)))))
end else begin
if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _40_7 -> (match (_40_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _40_454 -> begin
false
end)))) && (not ((FStar_Options.print_effect_args ())))) then begin
(let _138_244 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _138_244))
end else begin
if (((not ((FStar_Options.print_effect_args ()))) && (not ((FStar_Options.print_implicits ())))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_Options.print_effect_args ()))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _40_8 -> (match (_40_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _40_458 -> begin
false
end))))) then begin
(let _138_246 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _138_246))
end else begin
(let _138_248 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _138_247 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _138_248 _138_247)))
end
end
end
end
in (

let dec = (let _138_252 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _40_9 -> (match (_40_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _138_251 = (let _138_250 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _138_250))
in (_138_251)::[])
end
| _40_464 -> begin
[]
end))))
in (FStar_All.pipe_right _138_252 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and cflags_to_string : FStar_Syntax_Syntax.cflags  ->  Prims.string = (fun c -> (match (c) with
| FStar_Syntax_Syntax.TOTAL -> begin
"total"
end
| FStar_Syntax_Syntax.MLEFFECT -> begin
"ml"
end
| FStar_Syntax_Syntax.RETURN -> begin
"return"
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
"partial_return"
end
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
"sometrivial"
end
| FStar_Syntax_Syntax.LEMMA -> begin
"lemma"
end
| FStar_Syntax_Syntax.CPS -> begin
"cps"
end
| FStar_Syntax_Syntax.DECREASES (_40_475) -> begin
""
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> if (FStar_Options.print_universes ()) then begin
(Prims.strcat "<" (Prims.strcat s ">"))
end else begin
""
end)


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun _40_481 -> (match (_40_481) with
| (us, t) -> begin
(let _138_261 = (let _138_259 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes _138_259))
in (let _138_260 = (term_to_string t)
in (FStar_Util.format2 "%s%s" _138_261 _138_260)))
end))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (

let actions_to_string = (fun actions -> (let _138_274 = (FStar_All.pipe_right actions (FStar_List.map (fun a -> (let _138_273 = (sli a.FStar_Syntax_Syntax.action_name)
in (let _138_272 = (let _138_269 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes _138_269))
in (let _138_271 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (let _138_270 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format4 "%s%s : %s = %s" _138_273 _138_272 _138_271 _138_270))))))))
in (FStar_All.pipe_right _138_274 (FStar_String.concat ",\n\t"))))
in (let _138_312 = (let _138_311 = (let _138_310 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _138_309 = (let _138_308 = (let _138_275 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes _138_275))
in (let _138_307 = (let _138_306 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _138_305 = (let _138_304 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _138_303 = (let _138_302 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (let _138_301 = (let _138_300 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _138_299 = (let _138_298 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _138_297 = (let _138_296 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _138_295 = (let _138_294 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (let _138_293 = (let _138_292 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _138_291 = (let _138_290 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _138_289 = (let _138_288 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _138_287 = (let _138_286 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _138_285 = (let _138_284 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (let _138_283 = (let _138_282 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _138_281 = (let _138_280 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (let _138_279 = (let _138_278 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (let _138_277 = (let _138_276 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (_138_276)::[])
in (_138_278)::_138_277))
in (_138_280)::_138_279))
in (_138_282)::_138_281))
in (_138_284)::_138_283))
in (_138_286)::_138_285))
in (_138_288)::_138_287))
in (_138_290)::_138_289))
in (_138_292)::_138_291))
in (_138_294)::_138_293))
in (_138_296)::_138_295))
in (_138_298)::_138_297))
in (_138_300)::_138_299))
in (_138_302)::_138_301))
in (_138_304)::_138_303))
in (_138_306)::_138_305))
in (_138_308)::_138_307))
in (_138_310)::_138_309))
in (if for_free then begin
"_for_free "
end else begin
""
end)::_138_311)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" _138_312))))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None), _40_491) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s)), _40_498) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _40_504) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _40_512, _40_514, quals, _40_517) -> begin
(let _138_317 = (quals_to_string' quals)
in (let _138_316 = (binders_to_string " " tps)
in (let _138_315 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" _138_317 lid.FStar_Ident.str _138_316 _138_315))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _40_524, _40_526, _40_528, _40_530, _40_532) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _40_537 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_40_537) with
| (univs, t) -> begin
(let _138_319 = (univ_names_to_string univs)
in (let _138_318 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _138_319 lid.FStar_Ident.str _138_318)))
end))
end else begin
(let _138_320 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _138_320))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _40_543) -> begin
(

let _40_548 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_40_548) with
| (univs, t) -> begin
(let _138_324 = (quals_to_string' quals)
in (let _138_323 = if (FStar_Options.print_universes ()) then begin
(let _138_321 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _138_321))
end else begin
""
end
in (let _138_322 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" _138_324 lid.FStar_Ident.str _138_323 _138_322))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _40_552, _40_554) -> begin
(let _138_325 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _138_325))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _40_559, _40_561, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _40_567) -> begin
(let _138_326 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _138_326))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _40_572, _40_574, _40_576) -> begin
(let _138_327 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _138_327 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _40_581) -> begin
(eff_decl_to_string false ed)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed, _40_586) -> begin
(eff_decl_to_string true ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(

let lift_wp = (match (((se.FStar_Syntax_Syntax.lift_wp), (se.FStar_Syntax_Syntax.lift))) with
| (None, None) -> begin
(FStar_All.failwith "impossible")
end
| (Some (lift_wp), _40_599) -> begin
lift_wp
end
| (_40_602, Some (lift)) -> begin
lift
end)
in (

let _40_609 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp) (Prims.snd lift_wp))
in (match (_40_609) with
| (us, t) -> begin
(let _138_331 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _138_330 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _138_329 = (univ_names_to_string us)
in (let _138_328 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _138_331 _138_330 _138_329 _138_328)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _40_615, flags, _40_618) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _40_623 = (let _138_332 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _138_332))
in (match (_40_623) with
| (univs, t) -> begin
(

let _40_632 = (match ((let _138_333 = (FStar_Syntax_Subst.compress t)
in _138_333.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((bs), (c))
end
| _40_629 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_40_632) with
| (tps, c) -> begin
(let _138_337 = (sli l)
in (let _138_336 = (univ_names_to_string univs)
in (let _138_335 = (binders_to_string " " tps)
in (let _138_334 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _138_337 _138_336 _138_335 _138_334)))))
end))
end))
end else begin
(let _138_340 = (sli l)
in (let _138_339 = (binders_to_string " " tps)
in (let _138_338 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _138_340 _138_339 _138_338))))
end
end))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _138_345 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _138_345 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_40_637, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = _40_644; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _40_641; FStar_Syntax_Syntax.lbdef = _40_639})::[]), _40_650, _40_652, _40_654) -> begin
(let _138_349 = (lbname_to_string lb)
in (let _138_348 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _138_349 _138_348)))
end
| _40_658 -> begin
(let _138_352 = (let _138_351 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _138_351 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _138_352 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _138_357 = (sli m.FStar_Syntax_Syntax.name)
in (let _138_356 = (let _138_355 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _138_355 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _138_357 _138_356))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _40_10 -> (match (_40_10) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(let _138_361 = (FStar_Util.string_of_int i)
in (let _138_360 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _138_361 _138_360)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _138_363 = (bv_to_string x)
in (let _138_362 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _138_363 _138_362)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _138_365 = (bv_to_string x)
in (let _138_364 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _138_365 _138_364)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _138_367 = (FStar_Util.string_of_int i)
in (let _138_366 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _138_367 _138_366)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _138_368 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _138_368))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _138_371 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _138_371 (FStar_String.concat "; "))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in (

let _40_696 = (match (ascription) with
| None -> begin
(FStar_Util.string_builder_append strb "None")
end
| Some (FStar_Util.Inl (lc)) -> begin
(

let _40_689 = (FStar_Util.string_builder_append strb "Some Inr ")
in (FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name)))
end
| Some (FStar_Util.Inr (lid)) -> begin
(

let _40_694 = (FStar_Util.string_builder_append strb "Some Inr ")
in (FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lid)))
end)
in (FStar_Util.string_of_string_builder strb))))


let set_to_string = (fun f s -> (

let elts = (FStar_Util.set_elements s)
in (match (elts) with
| [] -> begin
"{}"
end
| (x)::xs -> begin
(

let strb = (FStar_Util.new_string_builder ())
in (

let _40_706 = (FStar_Util.string_builder_append strb "{")
in (

let _40_708 = (let _138_379 = (f x)
in (FStar_Util.string_builder_append strb _138_379))
in (

let _40_713 = (FStar_List.iter (fun x -> (

let _40_711 = (FStar_Util.string_builder_append strb ", ")
in (let _138_381 = (f x)
in (FStar_Util.string_builder_append strb _138_381)))) xs)
in (

let _40_715 = (FStar_Util.string_builder_append strb "}")
in (FStar_Util.string_of_string_builder strb))))))
end)))


let list_to_string = (fun f elts -> (match (elts) with
| [] -> begin
"[]"
end
| (x)::xs -> begin
(

let strb = (FStar_Util.new_string_builder ())
in (

let _40_724 = (FStar_Util.string_builder_append strb "[")
in (

let _40_726 = (let _138_387 = (f x)
in (FStar_Util.string_builder_append strb _138_387))
in (

let _40_731 = (FStar_List.iter (fun x -> (

let _40_729 = (FStar_Util.string_builder_append strb "; ")
in (let _138_389 = (f x)
in (FStar_Util.string_builder_append strb _138_389)))) xs)
in (

let _40_733 = (FStar_Util.string_builder_append strb "]")
in (FStar_Util.string_of_string_builder strb))))))
end))




