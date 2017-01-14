
open Prims

let sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_Options.print_real_names ()) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)


let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> (sli l))


let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _142_10 = (let _142_9 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "#" _142_9))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _142_10)))


let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> if (FStar_Options.print_real_names ()) then begin
(bv_to_string bv)
end else begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)


let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _142_16 = (let _142_15 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "@" _142_15))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _142_16)))


let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Syntax_Const.op_Addition), ("+")))::(((FStar_Syntax_Const.op_Subtraction), ("-")))::(((FStar_Syntax_Const.op_Multiply), ("*")))::(((FStar_Syntax_Const.op_Division), ("/")))::(((FStar_Syntax_Const.op_Eq), ("=")))::(((FStar_Syntax_Const.op_ColonEq), (":=")))::(((FStar_Syntax_Const.op_notEq), ("<>")))::(((FStar_Syntax_Const.op_And), ("&&")))::(((FStar_Syntax_Const.op_Or), ("||")))::(((FStar_Syntax_Const.op_LTE), ("<=")))::(((FStar_Syntax_Const.op_GTE), (">=")))::(((FStar_Syntax_Const.op_LT), ("<")))::(((FStar_Syntax_Const.op_GT), (">")))::(((FStar_Syntax_Const.op_Modulus), ("mod")))::(((FStar_Syntax_Const.and_lid), ("/\\")))::(((FStar_Syntax_Const.or_lid), ("\\/")))::(((FStar_Syntax_Const.imp_lid), ("==>")))::(((FStar_Syntax_Const.iff_lid), ("<==>")))::(((FStar_Syntax_Const.precedes_lid), ("<<")))::(((FStar_Syntax_Const.eq2_lid), ("==")))::(((FStar_Syntax_Const.eq3_lid), ("===")))::[]


let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Syntax_Const.op_Negation), ("not")))::(((FStar_Syntax_Const.op_Minus), ("-")))::(((FStar_Syntax_Const.not_lid), ("~")))::[]


let is_prim_op = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
end
| _41_15 -> begin
false
end))


let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| _41_20 -> begin
(failwith "get_lid")
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


let is_inr = (fun uu___87 -> (match (uu___87) with
| FStar_Util.Inl (_41_30) -> begin
false
end
| FStar_Util.Inr (_41_33) -> begin
true
end))


let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___88 -> (match (uu___88) with
| (_41_38, Some (FStar_Syntax_Syntax.Implicit (_41_40))) -> begin
false
end
| _41_45 -> begin
true
end)))))


let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _142_39 = (FStar_Syntax_Subst.compress e)
in _142_39.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args = (filter_imp args)
in (

let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = (Prims.parse_int "2"))) then begin
(match ((let _142_40 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex _142_40))) with
| Some (xs) -> begin
(let _142_42 = (let _142_41 = (FStar_List.nth exps (Prims.parse_int "0"))
in (_142_41)::xs)
in Some (_142_42))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _41_57 -> begin
if (is_lex_top e) then begin
Some ([])
end else begin
None
end
end))


let rec find = (fun f l -> (match (l) with
| [] -> begin
(failwith "blah")
end
| (hd)::tl -> begin
if (f hd) then begin
hd
end else begin
(find f tl)
end
end))


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _142_56 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _142_56)))


let infix_prim_op_to_string = (fun e -> (let _142_58 = (get_lid e)
in (find_lid _142_58 infix_prim_ops)))


let unary_prim_op_to_string = (fun e -> (let _142_60 = (get_lid e)
in (find_lid _142_60 unary_prim_ops)))


let quant_to_string = (fun t -> (let _142_62 = (get_lid t)
in (find_lid _142_62 quants)))


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
| FStar_Const.Const_string (bytes, _41_80) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_41_84) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x, _41_88) -> begin
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
(let _142_65 = (sli l)
in (FStar_Util.format1 "[[%s.reflect]]" _142_65))
end))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun uu___89 -> (match (uu___89) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _142_70 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _142_70))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _142_71 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _142_71))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _142_72 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _142_72))
end
| FStar_Syntax_Syntax.Tm_uinst (_41_111) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (_41_114) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (_41_117) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (_41_120) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (_41_123) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (_41_126) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (_41_129) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (_41_132) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (_41_135) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (_41_138) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (_41_141) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (_41_144, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
"Tm_delayed"
end
| Some (_41_150) -> begin
"Tm_delayed-resolved"
end)
end
| FStar_Syntax_Syntax.Tm_meta (_41_153) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))


let uvar_to_string = (fun u -> if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _142_77 = (let _142_76 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _142_76 FStar_Util.string_of_int))
in (Prims.strcat "?" _142_77))
end)


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe Prims.option) = (fun n u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_zero -> begin
((n), (None))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(int_of_univ (n + (Prims.parse_int "1")) u)
end
| _41_163 -> begin
((n), (Some (u)))
end))


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_unif (u) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(let _142_84 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _142_84))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(match ((int_of_univ (Prims.parse_int "1") u)) with
| (n, None) -> begin
(FStar_Util.string_of_int n)
end
| (n, Some (u)) -> begin
(let _142_86 = (univ_to_string u)
in (let _142_85 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 "(%s + %s)" _142_86 _142_85)))
end)
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _142_88 = (let _142_87 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _142_87 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _142_88))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _142_91 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _142_91 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _142_95 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _142_95 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun uu___90 -> (match (uu___90) with
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
(let _142_98 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _142_98))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _142_99 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _142_99 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(let _142_103 = (let _142_100 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path _142_100))
in (let _142_102 = (let _142_101 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right _142_101 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" _142_103 _142_102)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(let _142_107 = (let _142_104 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path _142_104))
in (let _142_106 = (let _142_105 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right _142_105 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" _142_107 _142_106)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(let _142_108 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" _142_108))
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
end
| FStar_Syntax_Syntax.OnlyName -> begin
"OnlyName"
end))


let quals_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| _41_227 -> begin
(let _142_111 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _142_111 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| _41_231 -> begin
(let _142_114 = (quals_to_string quals)
in (Prims.strcat _142_114 " "))
end))


let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let x = (FStar_Syntax_Subst.compress x)
in (

let x = if (FStar_Options.print_implicits ()) then begin
x
end else begin
(FStar_Syntax_Util.unmeta x)
end
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_41_236) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_41_239, []) -> begin
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (let _142_140 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _142_139 = (FStar_All.pipe_right args (FStar_List.map (fun _41_252 -> (match (_41_252) with
| (t, _41_251) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _142_139 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _142_140 (FStar_String.concat "\\/")))
in (let _142_141 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _142_141)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _142_145 = (tag_of_term t)
in (let _142_144 = (sli m)
in (let _142_143 = (term_to_string t')
in (let _142_142 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" _142_145 _142_144 _142_143 _142_142)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(let _142_150 = (tag_of_term t)
in (let _142_149 = (term_to_string t')
in (let _142_148 = (sli m0)
in (let _142_147 = (sli m1)
in (let _142_146 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" _142_150 _142_149 _142_148 _142_147 _142_146))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(let _142_152 = (FStar_Range.string_of_range r)
in (let _142_151 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l _142_152 _142_151)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _41_279) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, _41_290) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_Options.print_universes ()) then begin
(let _142_153 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _142_153))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _142_155 = (binders_to_string " -> " bs)
in (let _142_154 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _142_155 _142_154)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
(let _142_159 = (binders_to_string " " bs)
in (let _142_158 = (term_to_string t2)
in (let _142_157 = (let _142_156 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _142_156))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _142_159 _142_158 _142_157))))
end
| Some (FStar_Util.Inr (l, flags)) when (FStar_Options.print_implicits ()) -> begin
(let _142_161 = (binders_to_string " " bs)
in (let _142_160 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))" _142_161 _142_160 l.FStar_Ident.str)))
end
| _41_315 -> begin
(let _142_163 = (binders_to_string " " bs)
in (let _142_162 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _142_163 _142_162)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _142_166 = (bv_to_string xt)
in (let _142_165 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _142_164 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _142_166 _142_165 _142_164))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _142_168 = (term_to_string t)
in (let _142_167 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _142_168 _142_167)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _142_170 = (lbs_to_string [] lbs)
in (let _142_169 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _142_170 _142_169)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), eff_name) -> begin
(let _142_174 = (term_to_string e)
in (let _142_173 = (let _142_171 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right _142_171 (FStar_Util.dflt "default")))
in (let _142_172 = (term_to_string t)
in (FStar_Util.format3 "(%s <: [%s] %s)" _142_174 _142_173 _142_172))))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _41_338) -> begin
(let _142_176 = (term_to_string e)
in (let _142_175 = (comp_to_string c)
in (FStar_Util.format2 "(%s <: %s)" _142_176 _142_175)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _142_184 = (term_to_string head)
in (let _142_183 = (let _142_182 = (FStar_All.pipe_right branches (FStar_List.map (fun _41_348 -> (match (_41_348) with
| (p, wopt, e) -> begin
(let _142_181 = (FStar_All.pipe_right p pat_to_string)
in (let _142_180 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _142_178 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _142_178))
end)
in (let _142_179 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _142_181 _142_180 _142_179))))
end))))
in (FStar_Util.concat_l "\n\t|" _142_182))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _142_184 _142_183)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_Options.print_universes ()) then begin
(let _142_186 = (term_to_string t)
in (let _142_185 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _142_186 _142_185)))
end else begin
(term_to_string t)
end
end
| _41_357 -> begin
(tag_of_term x)
end))))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _142_191 = (fv_to_string l)
in (let _142_190 = (let _142_189 = (FStar_List.map (fun _41_365 -> (match (_41_365) with
| (x, b) -> begin
(

let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _142_189 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _142_191 _142_190)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _41_369) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _142_193 = (bv_to_string x)
in (let _142_192 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" _142_193 _142_192)))
end else begin
(let _142_194 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _142_194))
end
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _142_196 = (bv_to_string x)
in (let _142_195 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" _142_196 _142_195)))
end else begin
(bv_to_string x)
end
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_Options.print_real_names ()) then begin
(let _142_197 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _142_197))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _142_198 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _142_198))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (

let lbs = if (FStar_Options.print_universes ()) then begin
(let _142_204 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _41_385 = (let _142_202 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _142_202))
in (match (_41_385) with
| (us, td) -> begin
(

let _41_403 = (match ((let _142_203 = (FStar_Syntax_Subst.compress td)
in _142_203.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_41_387, ((t, _41_394))::((d, _41_390))::[]) -> begin
((t), (d))
end
| _41_400 -> begin
(failwith "Impossibe")
end)
in (match (_41_403) with
| (t, d) -> begin
(

let _41_404 = lb
in {FStar_Syntax_Syntax.lbname = _41_404.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _41_404.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((Prims.fst lbs)), (_142_204)))
end else begin
lbs
end
in (let _142_214 = (quals_to_string' quals)
in (let _142_213 = (let _142_212 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _142_211 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _142_210 = if (FStar_Options.print_universes ()) then begin
(let _142_207 = (let _142_206 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat _142_206 ">"))
in (Prims.strcat "<" _142_207))
end else begin
""
end
in (let _142_209 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _142_208 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _142_211 _142_210 _142_209 _142_208))))))))
in (FStar_Util.concat_l "\n and " _142_212))
in (FStar_Util.format3 "%slet %s %s" _142_214 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _142_213)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> if (FStar_Options.print_effect_args ()) then begin
(let _142_216 = (lc.FStar_Syntax_Syntax.comp ())
in (comp_to_string _142_216))
end else begin
(let _142_218 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _142_217 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _142_218 _142_217)))
end)
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s uu___91 -> (match (uu___91) with
| Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
(Prims.strcat "#." s)
end
| Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "$" s)
end
| _41_420 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (

let _41_425 = b
in (match (_41_425) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(let _142_223 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" _142_223))
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_bound_var_types ())))) then begin
(let _142_224 = (nm_to_string a)
in (imp_to_string _142_224 imp))
end else begin
(let _142_228 = (let _142_227 = (nm_to_string a)
in (let _142_226 = (let _142_225 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" _142_225))
in (Prims.strcat _142_227 _142_226)))
in (imp_to_string _142_228 imp))
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
(let _142_233 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _142_233 (FStar_String.concat sep)))
end else begin
(let _142_234 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _142_234 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun uu___92 -> (match (uu___92) with
| (a, imp) -> begin
(let _142_236 = (term_to_string a)
in (imp_to_string _142_236 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args = if (FStar_Options.print_implicits ()) then begin
args
end else begin
(filter_imp args)
end
in (let _142_238 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _142_238 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _41_440) -> begin
(match ((let _142_240 = (FStar_Syntax_Subst.compress t)
in _142_240.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_41_444) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _41_447 -> begin
(let _142_241 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _142_241))
end)
end
| FStar_Syntax_Syntax.GTotal (t, _41_450) -> begin
(match ((let _142_242 = (FStar_Syntax_Subst.compress t)
in _142_242.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_41_454) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _41_457 -> begin
(let _142_243 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _142_243))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let basic = if (FStar_Options.print_effect_args ()) then begin
(let _142_249 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _142_248 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _142_247 = (let _142_244 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _142_244 (FStar_String.concat ", ")))
in (let _142_246 = (let _142_245 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right _142_245 (FStar_String.concat " ")))
in (FStar_Util.format4 "%s (%s) %s (attributes %s)" _142_249 _142_248 _142_247 _142_246)))))
end else begin
if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___93 -> (match (uu___93) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _41_463 -> begin
false
end)))) && (not ((FStar_Options.print_effect_args ())))) then begin
(let _142_251 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _142_251))
end else begin
if (((not ((FStar_Options.print_effect_args ()))) && (not ((FStar_Options.print_implicits ())))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_Options.print_effect_args ()))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___94 -> (match (uu___94) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _41_467 -> begin
false
end))))) then begin
(let _142_253 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _142_253))
end else begin
(let _142_255 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _142_254 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _142_255 _142_254)))
end
end
end
end
in (

let dec = (let _142_259 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun uu___95 -> (match (uu___95) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _142_258 = (let _142_257 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _142_257))
in (_142_258)::[])
end
| _41_473 -> begin
[]
end))))
in (FStar_All.pipe_right _142_259 (FStar_String.concat " ")))
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
| FStar_Syntax_Syntax.DECREASES (_41_484) -> begin
""
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> if (FStar_Options.print_universes ()) then begin
(Prims.strcat "<" (Prims.strcat s ">"))
end else begin
""
end)


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun _41_490 -> (match (_41_490) with
| (us, t) -> begin
(let _142_268 = (let _142_266 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes _142_266))
in (let _142_267 = (term_to_string t)
in (FStar_Util.format2 "%s%s" _142_268 _142_267)))
end))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (

let actions_to_string = (fun actions -> (let _142_281 = (FStar_All.pipe_right actions (FStar_List.map (fun a -> (let _142_280 = (sli a.FStar_Syntax_Syntax.action_name)
in (let _142_279 = (let _142_276 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes _142_276))
in (let _142_278 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (let _142_277 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format4 "%s%s : %s = %s" _142_280 _142_279 _142_278 _142_277))))))))
in (FStar_All.pipe_right _142_281 (FStar_String.concat ",\n\t"))))
in (let _142_319 = (let _142_318 = (let _142_317 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _142_316 = (let _142_315 = (let _142_282 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes _142_282))
in (let _142_314 = (let _142_313 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _142_312 = (let _142_311 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _142_310 = (let _142_309 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (let _142_308 = (let _142_307 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _142_306 = (let _142_305 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _142_304 = (let _142_303 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _142_302 = (let _142_301 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (let _142_300 = (let _142_299 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _142_298 = (let _142_297 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _142_296 = (let _142_295 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _142_294 = (let _142_293 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _142_292 = (let _142_291 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (let _142_290 = (let _142_289 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _142_288 = (let _142_287 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (let _142_286 = (let _142_285 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (let _142_284 = (let _142_283 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (_142_283)::[])
in (_142_285)::_142_284))
in (_142_287)::_142_286))
in (_142_289)::_142_288))
in (_142_291)::_142_290))
in (_142_293)::_142_292))
in (_142_295)::_142_294))
in (_142_297)::_142_296))
in (_142_299)::_142_298))
in (_142_301)::_142_300))
in (_142_303)::_142_302))
in (_142_305)::_142_304))
in (_142_307)::_142_306))
in (_142_309)::_142_308))
in (_142_311)::_142_310))
in (_142_313)::_142_312))
in (_142_315)::_142_314))
in (_142_317)::_142_316))
in (if for_free then begin
"_for_free "
end else begin
""
end)::_142_318)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" _142_319))))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None), _41_500) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s)), _41_507) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _41_513) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _41_521, _41_523, quals, _41_526) -> begin
(let _142_324 = (quals_to_string' quals)
in (let _142_323 = (binders_to_string " " tps)
in (let _142_322 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" _142_324 lid.FStar_Ident.str _142_323 _142_322))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _41_533, _41_535, _41_537, _41_539, _41_541) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _41_546 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_41_546) with
| (univs, t) -> begin
(let _142_326 = (univ_names_to_string univs)
in (let _142_325 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _142_326 lid.FStar_Ident.str _142_325)))
end))
end else begin
(let _142_327 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _142_327))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _41_552) -> begin
(

let _41_557 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_41_557) with
| (univs, t) -> begin
(let _142_331 = (quals_to_string' quals)
in (let _142_330 = if (FStar_Options.print_universes ()) then begin
(let _142_328 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _142_328))
end else begin
""
end
in (let _142_329 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" _142_331 lid.FStar_Ident.str _142_330 _142_329))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _41_561, _41_563) -> begin
(let _142_332 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _142_332))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _41_568, _41_570, qs, _41_573) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _41_578) -> begin
(let _142_333 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _142_333))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _41_583, _41_585, _41_587) -> begin
(let _142_334 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _142_334 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _41_592) -> begin
(eff_decl_to_string false ed)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed, _41_597) -> begin
(eff_decl_to_string true ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(

let lift_wp = (match (((se.FStar_Syntax_Syntax.lift_wp), (se.FStar_Syntax_Syntax.lift))) with
| (None, None) -> begin
(failwith "impossible")
end
| (Some (lift_wp), _41_610) -> begin
lift_wp
end
| (_41_613, Some (lift)) -> begin
lift
end)
in (

let _41_620 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp) (Prims.snd lift_wp))
in (match (_41_620) with
| (us, t) -> begin
(let _142_338 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _142_337 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _142_336 = (univ_names_to_string us)
in (let _142_335 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _142_338 _142_337 _142_336 _142_335)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _41_626, flags, _41_629) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _41_634 = (let _142_339 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _142_339))
in (match (_41_634) with
| (univs, t) -> begin
(

let _41_643 = (match ((let _142_340 = (FStar_Syntax_Subst.compress t)
in _142_340.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((bs), (c))
end
| _41_640 -> begin
(failwith "impossible")
end)
in (match (_41_643) with
| (tps, c) -> begin
(let _142_344 = (sli l)
in (let _142_343 = (univ_names_to_string univs)
in (let _142_342 = (binders_to_string " " tps)
in (let _142_341 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _142_344 _142_343 _142_342 _142_341)))))
end))
end))
end else begin
(let _142_347 = (sli l)
in (let _142_346 = (binders_to_string " " tps)
in (let _142_345 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _142_347 _142_346 _142_345))))
end
end))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _142_352 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _142_352 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_41_648, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = _41_655; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _41_652; FStar_Syntax_Syntax.lbdef = _41_650})::[]), _41_661, _41_663, _41_665, _41_667) -> begin
(let _142_356 = (lbname_to_string lb)
in (let _142_355 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _142_356 _142_355)))
end
| _41_671 -> begin
(let _142_358 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right _142_358 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _142_363 = (sli m.FStar_Syntax_Syntax.name)
in (let _142_362 = (let _142_361 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _142_361 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _142_363 _142_362))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun uu___96 -> (match (uu___96) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(let _142_367 = (FStar_Util.string_of_int i)
in (let _142_366 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _142_367 _142_366)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _142_369 = (bv_to_string x)
in (let _142_368 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _142_369 _142_368)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _142_371 = (bv_to_string x)
in (let _142_370 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _142_371 _142_370)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _142_373 = (FStar_Util.string_of_int i)
in (let _142_372 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _142_373 _142_372)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _142_374 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _142_374))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _142_377 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _142_377 (FStar_String.concat "; "))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in (

let _41_709 = (match (ascription) with
| None -> begin
(FStar_Util.string_builder_append strb "None")
end
| Some (FStar_Util.Inl (lc)) -> begin
(

let _41_702 = (FStar_Util.string_builder_append strb "Some Inr ")
in (FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name)))
end
| Some (FStar_Util.Inr (lid)) -> begin
(

let _41_707 = (FStar_Util.string_builder_append strb "Some Inr ")
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

let _41_719 = (FStar_Util.string_builder_append strb "{")
in (

let _41_721 = (let _142_385 = (f x)
in (FStar_Util.string_builder_append strb _142_385))
in (

let _41_726 = (FStar_List.iter (fun x -> (

let _41_724 = (FStar_Util.string_builder_append strb ", ")
in (let _142_387 = (f x)
in (FStar_Util.string_builder_append strb _142_387)))) xs)
in (

let _41_728 = (FStar_Util.string_builder_append strb "}")
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

let _41_737 = (FStar_Util.string_builder_append strb "[")
in (

let _41_739 = (let _142_393 = (f x)
in (FStar_Util.string_builder_append strb _142_393))
in (

let _41_744 = (FStar_List.iter (fun x -> (

let _41_742 = (FStar_Util.string_builder_append strb "; ")
in (let _142_395 = (f x)
in (FStar_Util.string_builder_append strb _142_395)))) xs)
in (

let _41_746 = (FStar_Util.string_builder_append strb "]")
in (FStar_Util.string_of_string_builder strb))))))
end))




