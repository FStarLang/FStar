
open Prims

let sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_Options.print_real_names ()) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)


let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> (sli l))


let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _139_10 = (let _139_9 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "#" _139_9))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _139_10)))


let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> if (FStar_Options.print_real_names ()) then begin
(bv_to_string bv)
end else begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)


let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _139_16 = (let _139_15 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "@" _139_15))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _139_16)))


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


let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _139_39 = (FStar_Syntax_Subst.compress e)
in _139_39.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args = (filter_imp args)
in (

let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = (Prims.parse_int "2"))) then begin
(match ((let _139_40 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex _139_40))) with
| Some (xs) -> begin
(let _139_42 = (let _139_41 = (FStar_List.nth exps (Prims.parse_int "0"))
in (_139_41)::xs)
in Some (_139_42))
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
(failwith "blah")
end
| (hd)::tl -> begin
if (f hd) then begin
hd
end else begin
(find f tl)
end
end))


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _139_56 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _139_56)))


let infix_prim_op_to_string = (fun e -> (let _139_58 = (get_lid e)
in (find_lid _139_58 infix_prim_ops)))


let unary_prim_op_to_string = (fun e -> (let _139_60 = (get_lid e)
in (find_lid _139_60 unary_prim_ops)))


let quant_to_string = (fun t -> (let _139_62 = (get_lid t)
in (find_lid _139_62 quants)))


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
(let _139_65 = (sli l)
in (FStar_Util.format1 "[[%s.reflect]]" _139_65))
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
(let _139_70 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _139_70))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _139_71 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _139_71))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _139_72 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _139_72))
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
(let _139_77 = (let _139_76 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _139_76 FStar_Util.string_of_int))
in (Prims.strcat "?" _139_77))
end)


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe Prims.option) = (fun n u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_zero -> begin
((n), (None))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(int_of_univ (n + (Prims.parse_int "1")) u)
end
| _40_173 -> begin
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
(let _139_84 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _139_84))
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
(let _139_86 = (univ_to_string u)
in (let _139_85 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 "(%s + %s)" _139_86 _139_85)))
end)
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _139_88 = (let _139_87 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _139_87 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _139_88))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _139_91 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _139_91 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _139_95 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _139_95 (FStar_String.concat ", "))))


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
(let _139_98 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _139_98))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _139_99 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _139_99 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(let _139_103 = (let _139_100 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path _139_100))
in (let _139_102 = (let _139_101 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right _139_101 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" _139_103 _139_102)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(let _139_107 = (let _139_104 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path _139_104))
in (let _139_106 = (let _139_105 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right _139_105 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" _139_107 _139_106)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(let _139_108 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" _139_108))
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
| _40_237 -> begin
(let _139_111 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _139_111 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| _40_241 -> begin
(let _139_114 = (quals_to_string quals)
in (Prims.strcat _139_114 " "))
end))


let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let x = (FStar_Syntax_Subst.compress x)
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_40_245) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_40_248, []) -> begin
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (let _139_140 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _139_139 = (FStar_All.pipe_right args (FStar_List.map (fun _40_261 -> (match (_40_261) with
| (t, _40_260) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _139_139 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _139_140 (FStar_String.concat "\\/")))
in (let _139_141 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _139_141)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _139_145 = (tag_of_term t)
in (let _139_144 = (sli m)
in (let _139_143 = (term_to_string t')
in (let _139_142 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" _139_145 _139_144 _139_143 _139_142)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(let _139_150 = (tag_of_term t)
in (let _139_149 = (term_to_string t')
in (let _139_148 = (sli m0)
in (let _139_147 = (sli m1)
in (let _139_146 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" _139_150 _139_149 _139_148 _139_147 _139_146))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(let _139_152 = (FStar_Range.string_of_range r)
in (let _139_151 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l _139_152 _139_151)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _40_288) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, _40_299) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_Options.print_universes ()) then begin
(let _139_153 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _139_153))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _139_155 = (binders_to_string " -> " bs)
in (let _139_154 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _139_155 _139_154)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
(let _139_159 = (binders_to_string " " bs)
in (let _139_158 = (term_to_string t2)
in (let _139_157 = (let _139_156 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _139_156))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _139_159 _139_158 _139_157))))
end
| Some (FStar_Util.Inr (l, flags)) when (FStar_Options.print_implicits ()) -> begin
(let _139_161 = (binders_to_string " " bs)
in (let _139_160 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))" _139_161 _139_160 l.FStar_Ident.str)))
end
| _40_324 -> begin
(let _139_163 = (binders_to_string " " bs)
in (let _139_162 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _139_163 _139_162)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _139_166 = (bv_to_string xt)
in (let _139_165 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _139_164 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _139_166 _139_165 _139_164))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _139_168 = (term_to_string t)
in (let _139_167 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _139_168 _139_167)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _139_170 = (lbs_to_string [] lbs)
in (let _139_169 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _139_170 _139_169)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), eff_name) -> begin
(let _139_174 = (term_to_string e)
in (let _139_173 = (let _139_171 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right _139_171 (FStar_Util.dflt "default")))
in (let _139_172 = (term_to_string t)
in (FStar_Util.format3 "(%s <: [%s] %s)" _139_174 _139_173 _139_172))))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _40_347) -> begin
(let _139_176 = (term_to_string e)
in (let _139_175 = (comp_to_string c)
in (FStar_Util.format2 "(%s <: %s)" _139_176 _139_175)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _139_184 = (term_to_string head)
in (let _139_183 = (let _139_182 = (FStar_All.pipe_right branches (FStar_List.map (fun _40_357 -> (match (_40_357) with
| (p, wopt, e) -> begin
(let _139_181 = (FStar_All.pipe_right p pat_to_string)
in (let _139_180 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _139_178 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _139_178))
end)
in (let _139_179 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _139_181 _139_180 _139_179))))
end))))
in (FStar_Util.concat_l "\n\t|" _139_182))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _139_184 _139_183)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_Options.print_universes ()) then begin
(let _139_186 = (term_to_string t)
in (let _139_185 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _139_186 _139_185)))
end else begin
(term_to_string t)
end
end
| _40_366 -> begin
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _139_191 = (fv_to_string l)
in (let _139_190 = (let _139_189 = (FStar_List.map (fun _40_374 -> (match (_40_374) with
| (x, b) -> begin
(

let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _139_189 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _139_191 _139_190)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _40_378) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _139_193 = (bv_to_string x)
in (let _139_192 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" _139_193 _139_192)))
end else begin
(let _139_194 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _139_194))
end
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _139_196 = (bv_to_string x)
in (let _139_195 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" _139_196 _139_195)))
end else begin
(bv_to_string x)
end
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_Options.print_real_names ()) then begin
(let _139_197 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _139_197))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _139_198 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _139_198))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (

let lbs = if (FStar_Options.print_universes ()) then begin
(let _139_204 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _40_394 = (let _139_202 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _139_202))
in (match (_40_394) with
| (us, td) -> begin
(

let _40_412 = (match ((let _139_203 = (FStar_Syntax_Subst.compress td)
in _139_203.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_40_396, ((t, _40_403))::((d, _40_399))::[]) -> begin
((t), (d))
end
| _40_409 -> begin
(failwith "Impossibe")
end)
in (match (_40_412) with
| (t, d) -> begin
(

let _40_413 = lb
in {FStar_Syntax_Syntax.lbname = _40_413.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _40_413.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((Prims.fst lbs)), (_139_204)))
end else begin
lbs
end
in (let _139_214 = (quals_to_string' quals)
in (let _139_213 = (let _139_212 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _139_211 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _139_210 = if (FStar_Options.print_universes ()) then begin
(let _139_207 = (let _139_206 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat _139_206 ">"))
in (Prims.strcat "<" _139_207))
end else begin
""
end
in (let _139_209 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _139_208 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _139_211 _139_210 _139_209 _139_208))))))))
in (FStar_Util.concat_l "\n and " _139_212))
in (FStar_Util.format3 "%slet %s %s" _139_214 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _139_213)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> if (FStar_Options.print_effect_args ()) then begin
(let _139_216 = (lc.FStar_Syntax_Syntax.comp ())
in (comp_to_string _139_216))
end else begin
(let _139_218 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _139_217 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _139_218 _139_217)))
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
| _40_429 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (

let _40_434 = b
in (match (_40_434) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(let _139_223 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" _139_223))
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_bound_var_types ())))) then begin
(let _139_224 = (nm_to_string a)
in (imp_to_string _139_224 imp))
end else begin
(let _139_228 = (let _139_227 = (nm_to_string a)
in (let _139_226 = (let _139_225 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" _139_225))
in (Prims.strcat _139_227 _139_226)))
in (imp_to_string _139_228 imp))
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
(let _139_233 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _139_233 (FStar_String.concat sep)))
end else begin
(let _139_234 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _139_234 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _40_6 -> (match (_40_6) with
| (a, imp) -> begin
(let _139_236 = (term_to_string a)
in (imp_to_string _139_236 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args = if (FStar_Options.print_implicits ()) then begin
args
end else begin
(filter_imp args)
end
in (let _139_238 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _139_238 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _40_449) -> begin
(match ((let _139_240 = (FStar_Syntax_Subst.compress t)
in _139_240.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_40_453) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _40_456 -> begin
(let _139_241 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _139_241))
end)
end
| FStar_Syntax_Syntax.GTotal (t, _40_459) -> begin
(match ((let _139_242 = (FStar_Syntax_Subst.compress t)
in _139_242.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_40_463) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _40_466 -> begin
(let _139_243 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _139_243))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let basic = if (FStar_Options.print_effect_args ()) then begin
(let _139_249 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _139_248 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _139_247 = (let _139_244 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _139_244 (FStar_String.concat ", ")))
in (let _139_246 = (let _139_245 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right _139_245 (FStar_String.concat " ")))
in (FStar_Util.format4 "%s (%s) %s (attributes %s)" _139_249 _139_248 _139_247 _139_246)))))
end else begin
if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _40_7 -> (match (_40_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _40_472 -> begin
false
end)))) && (not ((FStar_Options.print_effect_args ())))) then begin
(let _139_251 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _139_251))
end else begin
if (((not ((FStar_Options.print_effect_args ()))) && (not ((FStar_Options.print_implicits ())))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_Options.print_effect_args ()))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _40_8 -> (match (_40_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _40_476 -> begin
false
end))))) then begin
(let _139_253 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _139_253))
end else begin
(let _139_255 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _139_254 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _139_255 _139_254)))
end
end
end
end
in (

let dec = (let _139_259 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _40_9 -> (match (_40_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _139_258 = (let _139_257 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _139_257))
in (_139_258)::[])
end
| _40_482 -> begin
[]
end))))
in (FStar_All.pipe_right _139_259 (FStar_String.concat " ")))
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
| FStar_Syntax_Syntax.DECREASES (_40_493) -> begin
""
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> if (FStar_Options.print_universes ()) then begin
(Prims.strcat "<" (Prims.strcat s ">"))
end else begin
""
end)


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun _40_499 -> (match (_40_499) with
| (us, t) -> begin
(let _139_268 = (let _139_266 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes _139_266))
in (let _139_267 = (term_to_string t)
in (FStar_Util.format2 "%s%s" _139_268 _139_267)))
end))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (

let actions_to_string = (fun actions -> (let _139_281 = (FStar_All.pipe_right actions (FStar_List.map (fun a -> (let _139_280 = (sli a.FStar_Syntax_Syntax.action_name)
in (let _139_279 = (let _139_276 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes _139_276))
in (let _139_278 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (let _139_277 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format4 "%s%s : %s = %s" _139_280 _139_279 _139_278 _139_277))))))))
in (FStar_All.pipe_right _139_281 (FStar_String.concat ",\n\t"))))
in (let _139_319 = (let _139_318 = (let _139_317 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _139_316 = (let _139_315 = (let _139_282 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes _139_282))
in (let _139_314 = (let _139_313 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _139_312 = (let _139_311 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _139_310 = (let _139_309 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (let _139_308 = (let _139_307 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _139_306 = (let _139_305 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _139_304 = (let _139_303 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _139_302 = (let _139_301 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (let _139_300 = (let _139_299 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _139_298 = (let _139_297 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _139_296 = (let _139_295 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _139_294 = (let _139_293 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _139_292 = (let _139_291 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (let _139_290 = (let _139_289 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _139_288 = (let _139_287 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (let _139_286 = (let _139_285 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (let _139_284 = (let _139_283 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (_139_283)::[])
in (_139_285)::_139_284))
in (_139_287)::_139_286))
in (_139_289)::_139_288))
in (_139_291)::_139_290))
in (_139_293)::_139_292))
in (_139_295)::_139_294))
in (_139_297)::_139_296))
in (_139_299)::_139_298))
in (_139_301)::_139_300))
in (_139_303)::_139_302))
in (_139_305)::_139_304))
in (_139_307)::_139_306))
in (_139_309)::_139_308))
in (_139_311)::_139_310))
in (_139_313)::_139_312))
in (_139_315)::_139_314))
in (_139_317)::_139_316))
in (if for_free then begin
"_for_free "
end else begin
""
end)::_139_318)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" _139_319))))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None), _40_509) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s)), _40_516) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _40_522) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _40_530, _40_532, quals, _40_535) -> begin
(let _139_324 = (quals_to_string' quals)
in (let _139_323 = (binders_to_string " " tps)
in (let _139_322 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" _139_324 lid.FStar_Ident.str _139_323 _139_322))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _40_542, _40_544, _40_546, _40_548, _40_550) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _40_555 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_40_555) with
| (univs, t) -> begin
(let _139_326 = (univ_names_to_string univs)
in (let _139_325 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _139_326 lid.FStar_Ident.str _139_325)))
end))
end else begin
(let _139_327 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _139_327))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _40_561) -> begin
(

let _40_566 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_40_566) with
| (univs, t) -> begin
(let _139_331 = (quals_to_string' quals)
in (let _139_330 = if (FStar_Options.print_universes ()) then begin
(let _139_328 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _139_328))
end else begin
""
end
in (let _139_329 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" _139_331 lid.FStar_Ident.str _139_330 _139_329))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _40_570, _40_572) -> begin
(let _139_332 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _139_332))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _40_577, _40_579, qs, _40_582) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _40_587) -> begin
(let _139_333 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _139_333))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _40_592, _40_594, _40_596) -> begin
(let _139_334 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _139_334 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _40_601) -> begin
(eff_decl_to_string false ed)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed, _40_606) -> begin
(eff_decl_to_string true ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(

let lift_wp = (match (((se.FStar_Syntax_Syntax.lift_wp), (se.FStar_Syntax_Syntax.lift))) with
| (None, None) -> begin
(failwith "impossible")
end
| (Some (lift_wp), _40_619) -> begin
lift_wp
end
| (_40_622, Some (lift)) -> begin
lift
end)
in (

let _40_629 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp) (Prims.snd lift_wp))
in (match (_40_629) with
| (us, t) -> begin
(let _139_338 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _139_337 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _139_336 = (univ_names_to_string us)
in (let _139_335 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _139_338 _139_337 _139_336 _139_335)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _40_635, flags, _40_638) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _40_643 = (let _139_339 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _139_339))
in (match (_40_643) with
| (univs, t) -> begin
(

let _40_652 = (match ((let _139_340 = (FStar_Syntax_Subst.compress t)
in _139_340.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((bs), (c))
end
| _40_649 -> begin
(failwith "impossible")
end)
in (match (_40_652) with
| (tps, c) -> begin
(let _139_344 = (sli l)
in (let _139_343 = (univ_names_to_string univs)
in (let _139_342 = (binders_to_string " " tps)
in (let _139_341 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _139_344 _139_343 _139_342 _139_341)))))
end))
end))
end else begin
(let _139_347 = (sli l)
in (let _139_346 = (binders_to_string " " tps)
in (let _139_345 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _139_347 _139_346 _139_345))))
end
end))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _139_352 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _139_352 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_40_657, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = _40_664; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _40_661; FStar_Syntax_Syntax.lbdef = _40_659})::[]), _40_670, _40_672, _40_674, _40_676) -> begin
(let _139_356 = (lbname_to_string lb)
in (let _139_355 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _139_356 _139_355)))
end
| _40_680 -> begin
(let _139_358 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right _139_358 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _139_363 = (sli m.FStar_Syntax_Syntax.name)
in (let _139_362 = (let _139_361 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _139_361 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _139_363 _139_362))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _40_10 -> (match (_40_10) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(let _139_367 = (FStar_Util.string_of_int i)
in (let _139_366 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _139_367 _139_366)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _139_369 = (bv_to_string x)
in (let _139_368 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _139_369 _139_368)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _139_371 = (bv_to_string x)
in (let _139_370 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _139_371 _139_370)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _139_373 = (FStar_Util.string_of_int i)
in (let _139_372 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _139_373 _139_372)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _139_374 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _139_374))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _139_377 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _139_377 (FStar_String.concat "; "))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in (

let _40_718 = (match (ascription) with
| None -> begin
(FStar_Util.string_builder_append strb "None")
end
| Some (FStar_Util.Inl (lc)) -> begin
(

let _40_711 = (FStar_Util.string_builder_append strb "Some Inr ")
in (FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name)))
end
| Some (FStar_Util.Inr (lid)) -> begin
(

let _40_716 = (FStar_Util.string_builder_append strb "Some Inr ")
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

let _40_728 = (FStar_Util.string_builder_append strb "{")
in (

let _40_730 = (let _139_385 = (f x)
in (FStar_Util.string_builder_append strb _139_385))
in (

let _40_735 = (FStar_List.iter (fun x -> (

let _40_733 = (FStar_Util.string_builder_append strb ", ")
in (let _139_387 = (f x)
in (FStar_Util.string_builder_append strb _139_387)))) xs)
in (

let _40_737 = (FStar_Util.string_builder_append strb "}")
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

let _40_746 = (FStar_Util.string_builder_append strb "[")
in (

let _40_748 = (let _139_393 = (f x)
in (FStar_Util.string_builder_append strb _139_393))
in (

let _40_753 = (FStar_List.iter (fun x -> (

let _40_751 = (FStar_Util.string_builder_append strb "; ")
in (let _139_395 = (f x)
in (FStar_Util.string_builder_append strb _139_395)))) xs)
in (

let _40_755 = (FStar_Util.string_builder_append strb "]")
in (FStar_Util.string_of_string_builder strb))))))
end))




