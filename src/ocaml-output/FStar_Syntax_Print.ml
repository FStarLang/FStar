
open Prims

let sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_Options.print_real_names ()) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)


let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> (sli l))


let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _137_10 = (let _137_9 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "#" _137_9))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _137_10)))


let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> if (FStar_Options.print_real_names ()) then begin
(bv_to_string bv)
end else begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)


let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _137_16 = (let _137_15 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "@" _137_15))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _137_16)))


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


let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _137_39 = (FStar_Syntax_Subst.compress e)
in _137_39.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args = (filter_imp args)
in (

let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = (Prims.parse_int "2"))) then begin
(match ((let _137_40 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex _137_40))) with
| Some (xs) -> begin
(let _137_42 = (let _137_41 = (FStar_List.nth exps (Prims.parse_int "0"))
in (_137_41)::xs)
in Some (_137_42))
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


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _137_56 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _137_56)))


let infix_prim_op_to_string = (fun e -> (let _137_58 = (get_lid e)
in (find_lid _137_58 infix_prim_ops)))


let unary_prim_op_to_string = (fun e -> (let _137_60 = (get_lid e)
in (find_lid _137_60 unary_prim_ops)))


let quant_to_string = (fun t -> (let _137_62 = (get_lid t)
in (find_lid _137_62 quants)))


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
(let _137_65 = (sli l)
in (FStar_Util.format1 "[[%s.reflect]]" _137_65))
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
(let _137_70 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _137_70))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _137_71 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _137_71))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _137_72 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _137_72))
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
(let _137_77 = (let _137_76 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _137_76 FStar_Util.string_of_int))
in (Prims.strcat "?" _137_77))
end)


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_unif (u) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(Prims.strcat "n" x.FStar_Ident.idText)
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(let _137_80 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _137_80))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _137_81 = (univ_to_string u)
in (FStar_Util.format1 "(S %s)" _137_81))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _137_83 = (let _137_82 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _137_82 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _137_83))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _137_86 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _137_86 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _137_90 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _137_90 (FStar_String.concat ", "))))


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
(let _137_93 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _137_93))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _137_94 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _137_94 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(let _137_98 = (let _137_95 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path _137_95))
in (let _137_97 = (let _137_96 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right _137_96 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" _137_98 _137_97)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(let _137_102 = (let _137_99 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path _137_99))
in (let _137_101 = (let _137_100 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right _137_100 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" _137_102 _137_101)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(let _137_103 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" _137_103))
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
| _40_222 -> begin
(let _137_106 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _137_106 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| _40_226 -> begin
(let _137_109 = (quals_to_string quals)
in (Prims.strcat _137_109 " "))
end))


let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let x = (FStar_Syntax_Subst.compress x)
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_40_230) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_40_233, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (let _137_135 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _137_134 = (FStar_All.pipe_right args (FStar_List.map (fun _40_246 -> (match (_40_246) with
| (t, _40_245) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _137_134 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _137_135 (FStar_String.concat "\\/")))
in (let _137_136 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _137_136)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _137_140 = (tag_of_term t)
in (let _137_139 = (sli m)
in (let _137_138 = (term_to_string t')
in (let _137_137 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" _137_140 _137_139 _137_138 _137_137)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(let _137_145 = (tag_of_term t)
in (let _137_144 = (term_to_string t')
in (let _137_143 = (sli m0)
in (let _137_142 = (sli m1)
in (let _137_141 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" _137_145 _137_144 _137_143 _137_142 _137_141))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(let _137_147 = (FStar_Range.string_of_range r)
in (let _137_146 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l _137_147 _137_146)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _40_273) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, _40_284) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_Options.print_universes ()) then begin
(let _137_148 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _137_148))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _137_150 = (binders_to_string " -> " bs)
in (let _137_149 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _137_150 _137_149)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
(let _137_154 = (binders_to_string " " bs)
in (let _137_153 = (term_to_string t2)
in (let _137_152 = (let _137_151 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _137_151))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _137_154 _137_153 _137_152))))
end
| Some (FStar_Util.Inr (l, flags)) when (FStar_Options.print_implicits ()) -> begin
(let _137_156 = (binders_to_string " " bs)
in (let _137_155 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))" _137_156 _137_155 l.FStar_Ident.str)))
end
| _40_309 -> begin
(let _137_158 = (binders_to_string " " bs)
in (let _137_157 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _137_158 _137_157)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _137_161 = (bv_to_string xt)
in (let _137_160 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _137_159 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _137_161 _137_160 _137_159))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _137_163 = (term_to_string t)
in (let _137_162 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _137_163 _137_162)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _137_165 = (lbs_to_string [] lbs)
in (let _137_164 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _137_165 _137_164)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), eff_name) -> begin
(let _137_169 = (term_to_string e)
in (let _137_168 = (let _137_166 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right _137_166 (FStar_Util.dflt "default")))
in (let _137_167 = (term_to_string t)
in (FStar_Util.format3 "(%s <: [%s] %s)" _137_169 _137_168 _137_167))))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _40_332) -> begin
(let _137_171 = (term_to_string e)
in (let _137_170 = (comp_to_string c)
in (FStar_Util.format2 "(%s <: %s)" _137_171 _137_170)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _137_179 = (term_to_string head)
in (let _137_178 = (let _137_177 = (FStar_All.pipe_right branches (FStar_List.map (fun _40_342 -> (match (_40_342) with
| (p, wopt, e) -> begin
(let _137_176 = (FStar_All.pipe_right p pat_to_string)
in (let _137_175 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _137_173 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _137_173))
end)
in (let _137_174 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _137_176 _137_175 _137_174))))
end))))
in (FStar_Util.concat_l "\n\t|" _137_177))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _137_179 _137_178)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_Options.print_universes ()) then begin
(let _137_181 = (term_to_string t)
in (let _137_180 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _137_181 _137_180)))
end else begin
(term_to_string t)
end
end
| _40_351 -> begin
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _137_186 = (fv_to_string l)
in (let _137_185 = (let _137_184 = (FStar_List.map (fun _40_359 -> (match (_40_359) with
| (x, b) -> begin
(

let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _137_184 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _137_186 _137_185)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _40_363) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _137_188 = (bv_to_string x)
in (let _137_187 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" _137_188 _137_187)))
end else begin
(let _137_189 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _137_189))
end
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _137_191 = (bv_to_string x)
in (let _137_190 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" _137_191 _137_190)))
end else begin
(bv_to_string x)
end
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_Options.print_real_names ()) then begin
(let _137_192 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _137_192))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _137_193 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _137_193))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (

let lbs = if (FStar_Options.print_universes ()) then begin
(let _137_199 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _40_379 = (let _137_197 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _137_197))
in (match (_40_379) with
| (us, td) -> begin
(

let _40_397 = (match ((let _137_198 = (FStar_Syntax_Subst.compress td)
in _137_198.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_40_381, ((t, _40_388))::((d, _40_384))::[]) -> begin
((t), (d))
end
| _40_394 -> begin
(FStar_All.failwith "Impossibe")
end)
in (match (_40_397) with
| (t, d) -> begin
(

let _40_398 = lb
in {FStar_Syntax_Syntax.lbname = _40_398.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _40_398.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((Prims.fst lbs)), (_137_199)))
end else begin
lbs
end
in (let _137_209 = (quals_to_string' quals)
in (let _137_208 = (let _137_207 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _137_206 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _137_205 = if (FStar_Options.print_universes ()) then begin
(let _137_202 = (let _137_201 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat _137_201 ">"))
in (Prims.strcat "<" _137_202))
end else begin
""
end
in (let _137_204 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _137_203 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _137_206 _137_205 _137_204 _137_203))))))))
in (FStar_Util.concat_l "\n and " _137_207))
in (FStar_Util.format3 "%slet %s %s" _137_209 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _137_208)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> if (FStar_Options.print_effect_args ()) then begin
(let _137_211 = (lc.FStar_Syntax_Syntax.comp ())
in (comp_to_string _137_211))
end else begin
(let _137_213 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _137_212 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _137_213 _137_212)))
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
| _40_414 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (

let _40_419 = b
in (match (_40_419) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(let _137_218 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" _137_218))
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_bound_var_types ())))) then begin
(let _137_219 = (nm_to_string a)
in (imp_to_string _137_219 imp))
end else begin
(let _137_223 = (let _137_222 = (nm_to_string a)
in (let _137_221 = (let _137_220 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" _137_220))
in (Prims.strcat _137_222 _137_221)))
in (imp_to_string _137_223 imp))
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
(let _137_228 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _137_228 (FStar_String.concat sep)))
end else begin
(let _137_229 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _137_229 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _40_6 -> (match (_40_6) with
| (a, imp) -> begin
(let _137_231 = (term_to_string a)
in (imp_to_string _137_231 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args = if (FStar_Options.print_implicits ()) then begin
args
end else begin
(filter_imp args)
end
in (let _137_233 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _137_233 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _40_434) -> begin
(match ((let _137_235 = (FStar_Syntax_Subst.compress t)
in _137_235.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_40_438) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _40_441 -> begin
(let _137_236 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _137_236))
end)
end
| FStar_Syntax_Syntax.GTotal (t, _40_444) -> begin
(match ((let _137_237 = (FStar_Syntax_Subst.compress t)
in _137_237.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_40_448) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _40_451 -> begin
(let _137_238 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _137_238))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let basic = if (FStar_Options.print_effect_args ()) then begin
(let _137_244 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _137_243 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _137_242 = (let _137_239 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _137_239 (FStar_String.concat ", ")))
in (let _137_241 = (let _137_240 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right _137_240 (FStar_String.concat " ")))
in (FStar_Util.format4 "%s (%s) %s (attributes %s)" _137_244 _137_243 _137_242 _137_241)))))
end else begin
if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _40_7 -> (match (_40_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _40_457 -> begin
false
end)))) && (not ((FStar_Options.print_effect_args ())))) then begin
(let _137_246 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _137_246))
end else begin
if (((not ((FStar_Options.print_effect_args ()))) && (not ((FStar_Options.print_implicits ())))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_Options.print_effect_args ()))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _40_8 -> (match (_40_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _40_461 -> begin
false
end))))) then begin
(let _137_248 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _137_248))
end else begin
(let _137_250 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _137_249 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _137_250 _137_249)))
end
end
end
end
in (

let dec = (let _137_254 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _40_9 -> (match (_40_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _137_253 = (let _137_252 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _137_252))
in (_137_253)::[])
end
| _40_467 -> begin
[]
end))))
in (FStar_All.pipe_right _137_254 (FStar_String.concat " ")))
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
| FStar_Syntax_Syntax.DECREASES (_40_478) -> begin
""
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> if (FStar_Options.print_universes ()) then begin
(Prims.strcat "<" (Prims.strcat s ">"))
end else begin
""
end)


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun _40_484 -> (match (_40_484) with
| (us, t) -> begin
(let _137_263 = (let _137_261 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes _137_261))
in (let _137_262 = (term_to_string t)
in (FStar_Util.format2 "%s%s" _137_263 _137_262)))
end))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (

let actions_to_string = (fun actions -> (let _137_276 = (FStar_All.pipe_right actions (FStar_List.map (fun a -> (let _137_275 = (sli a.FStar_Syntax_Syntax.action_name)
in (let _137_274 = (let _137_271 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes _137_271))
in (let _137_273 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (let _137_272 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format4 "%s%s : %s = %s" _137_275 _137_274 _137_273 _137_272))))))))
in (FStar_All.pipe_right _137_276 (FStar_String.concat ",\n\t"))))
in (let _137_314 = (let _137_313 = (let _137_312 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _137_311 = (let _137_310 = (let _137_277 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes _137_277))
in (let _137_309 = (let _137_308 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _137_307 = (let _137_306 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _137_305 = (let _137_304 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (let _137_303 = (let _137_302 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _137_301 = (let _137_300 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _137_299 = (let _137_298 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _137_297 = (let _137_296 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (let _137_295 = (let _137_294 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _137_293 = (let _137_292 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _137_291 = (let _137_290 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _137_289 = (let _137_288 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _137_287 = (let _137_286 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (let _137_285 = (let _137_284 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _137_283 = (let _137_282 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (let _137_281 = (let _137_280 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (let _137_279 = (let _137_278 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (_137_278)::[])
in (_137_280)::_137_279))
in (_137_282)::_137_281))
in (_137_284)::_137_283))
in (_137_286)::_137_285))
in (_137_288)::_137_287))
in (_137_290)::_137_289))
in (_137_292)::_137_291))
in (_137_294)::_137_293))
in (_137_296)::_137_295))
in (_137_298)::_137_297))
in (_137_300)::_137_299))
in (_137_302)::_137_301))
in (_137_304)::_137_303))
in (_137_306)::_137_305))
in (_137_308)::_137_307))
in (_137_310)::_137_309))
in (_137_312)::_137_311))
in (if for_free then begin
"_for_free "
end else begin
""
end)::_137_313)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" _137_314))))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None), _40_494) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s)), _40_501) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _40_507) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _40_515, _40_517, quals, _40_520) -> begin
(let _137_319 = (quals_to_string' quals)
in (let _137_318 = (binders_to_string " " tps)
in (let _137_317 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" _137_319 lid.FStar_Ident.str _137_318 _137_317))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _40_527, _40_529, _40_531, _40_533, _40_535) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _40_540 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_40_540) with
| (univs, t) -> begin
(let _137_321 = (univ_names_to_string univs)
in (let _137_320 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _137_321 lid.FStar_Ident.str _137_320)))
end))
end else begin
(let _137_322 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _137_322))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _40_546) -> begin
(

let _40_551 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_40_551) with
| (univs, t) -> begin
(let _137_326 = (quals_to_string' quals)
in (let _137_325 = if (FStar_Options.print_universes ()) then begin
(let _137_323 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _137_323))
end else begin
""
end
in (let _137_324 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" _137_326 lid.FStar_Ident.str _137_325 _137_324))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _40_555, _40_557) -> begin
(let _137_327 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _137_327))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _40_562, _40_564, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _40_570) -> begin
(let _137_328 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _137_328))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _40_575, _40_577, _40_579) -> begin
(let _137_329 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _137_329 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _40_584) -> begin
(eff_decl_to_string false ed)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed, _40_589) -> begin
(eff_decl_to_string true ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(

let lift_wp = (match (((se.FStar_Syntax_Syntax.lift_wp), (se.FStar_Syntax_Syntax.lift))) with
| (None, None) -> begin
(FStar_All.failwith "impossible")
end
| (Some (lift_wp), _40_602) -> begin
lift_wp
end
| (_40_605, Some (lift)) -> begin
lift
end)
in (

let _40_612 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp) (Prims.snd lift_wp))
in (match (_40_612) with
| (us, t) -> begin
(let _137_333 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _137_332 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _137_331 = (univ_names_to_string us)
in (let _137_330 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _137_333 _137_332 _137_331 _137_330)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _40_618, flags, _40_621) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _40_626 = (let _137_334 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _137_334))
in (match (_40_626) with
| (univs, t) -> begin
(

let _40_635 = (match ((let _137_335 = (FStar_Syntax_Subst.compress t)
in _137_335.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((bs), (c))
end
| _40_632 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_40_635) with
| (tps, c) -> begin
(let _137_339 = (sli l)
in (let _137_338 = (univ_names_to_string univs)
in (let _137_337 = (binders_to_string " " tps)
in (let _137_336 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _137_339 _137_338 _137_337 _137_336)))))
end))
end))
end else begin
(let _137_342 = (sli l)
in (let _137_341 = (binders_to_string " " tps)
in (let _137_340 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _137_342 _137_341 _137_340))))
end
end))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _137_347 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _137_347 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_40_640, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = _40_647; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _40_644; FStar_Syntax_Syntax.lbdef = _40_642})::[]), _40_653, _40_655, _40_657) -> begin
(let _137_351 = (lbname_to_string lb)
in (let _137_350 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _137_351 _137_350)))
end
| _40_661 -> begin
(let _137_354 = (let _137_353 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _137_353 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _137_354 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _137_359 = (sli m.FStar_Syntax_Syntax.name)
in (let _137_358 = (let _137_357 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _137_357 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _137_359 _137_358))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _40_10 -> (match (_40_10) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(let _137_363 = (FStar_Util.string_of_int i)
in (let _137_362 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _137_363 _137_362)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _137_365 = (bv_to_string x)
in (let _137_364 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _137_365 _137_364)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _137_367 = (bv_to_string x)
in (let _137_366 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _137_367 _137_366)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _137_369 = (FStar_Util.string_of_int i)
in (let _137_368 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _137_369 _137_368)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _137_370 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _137_370))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _137_373 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _137_373 (FStar_String.concat "; "))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in (

let _40_699 = (match (ascription) with
| None -> begin
(FStar_Util.string_builder_append strb "None")
end
| Some (FStar_Util.Inl (lc)) -> begin
(

let _40_692 = (FStar_Util.string_builder_append strb "Some Inr ")
in (FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name)))
end
| Some (FStar_Util.Inr (lid)) -> begin
(

let _40_697 = (FStar_Util.string_builder_append strb "Some Inr ")
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

let _40_709 = (FStar_Util.string_builder_append strb "{")
in (

let _40_711 = (let _137_381 = (f x)
in (FStar_Util.string_builder_append strb _137_381))
in (

let _40_716 = (FStar_List.iter (fun x -> (

let _40_714 = (FStar_Util.string_builder_append strb ", ")
in (let _137_383 = (f x)
in (FStar_Util.string_builder_append strb _137_383)))) xs)
in (

let _40_718 = (FStar_Util.string_builder_append strb "}")
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

let _40_727 = (FStar_Util.string_builder_append strb "[")
in (

let _40_729 = (let _137_389 = (f x)
in (FStar_Util.string_builder_append strb _137_389))
in (

let _40_734 = (FStar_List.iter (fun x -> (

let _40_732 = (FStar_Util.string_builder_append strb "; ")
in (let _137_391 = (f x)
in (FStar_Util.string_builder_append strb _137_391)))) xs)
in (

let _40_736 = (FStar_Util.string_builder_append strb "]")
in (FStar_Util.string_of_string_builder strb))))))
end))




