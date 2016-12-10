
open Prims

let sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_Options.print_real_names ()) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)


let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> (sli l))


let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _134_10 = (let _134_9 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "#" _134_9))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _134_10)))


let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> if (FStar_Options.print_real_names ()) then begin
(bv_to_string bv)
end else begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)


let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _134_16 = (let _134_15 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "@" _134_15))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _134_16)))


let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Syntax_Const.op_Addition), ("+")))::(((FStar_Syntax_Const.op_Subtraction), ("-")))::(((FStar_Syntax_Const.op_Multiply), ("*")))::(((FStar_Syntax_Const.op_Division), ("/")))::(((FStar_Syntax_Const.op_Eq), ("=")))::(((FStar_Syntax_Const.op_ColonEq), (":=")))::(((FStar_Syntax_Const.op_notEq), ("<>")))::(((FStar_Syntax_Const.op_And), ("&&")))::(((FStar_Syntax_Const.op_Or), ("||")))::(((FStar_Syntax_Const.op_LTE), ("<=")))::(((FStar_Syntax_Const.op_GTE), (">=")))::(((FStar_Syntax_Const.op_LT), ("<")))::(((FStar_Syntax_Const.op_GT), (">")))::(((FStar_Syntax_Const.op_Modulus), ("mod")))::(((FStar_Syntax_Const.and_lid), ("/\\")))::(((FStar_Syntax_Const.or_lid), ("\\/")))::(((FStar_Syntax_Const.imp_lid), ("==>")))::(((FStar_Syntax_Const.iff_lid), ("<==>")))::(((FStar_Syntax_Const.precedes_lid), ("<<")))::(((FStar_Syntax_Const.eq2_lid), ("==")))::(((FStar_Syntax_Const.eq3_lid), ("===")))::[]


let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Syntax_Const.op_Negation), ("not")))::(((FStar_Syntax_Const.op_Minus), ("-")))::(((FStar_Syntax_Const.not_lid), ("~")))::[]


let is_prim_op = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
end
| _39_25 -> begin
false
end))


let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| _39_30 -> begin
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


let is_inr = (fun _39_1 -> (match (_39_1) with
| FStar_Util.Inl (_39_40) -> begin
false
end
| FStar_Util.Inr (_39_43) -> begin
true
end))


let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _39_2 -> (match (_39_2) with
| (_39_48, Some (FStar_Syntax_Syntax.Implicit (_39_50))) -> begin
false
end
| _39_55 -> begin
true
end)))))


let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _134_39 = (FStar_Syntax_Subst.compress e)
in _134_39.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args = (filter_imp args)
in (

let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = (Prims.parse_int "2"))) then begin
(match ((let _134_40 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex _134_40))) with
| Some (xs) -> begin
(let _134_42 = (let _134_41 = (FStar_List.nth exps (Prims.parse_int "0"))
in (_134_41)::xs)
in Some (_134_42))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _39_67 -> begin
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


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _134_56 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _134_56)))


let infix_prim_op_to_string = (fun e -> (let _134_58 = (get_lid e)
in (find_lid _134_58 infix_prim_ops)))


let unary_prim_op_to_string = (fun e -> (let _134_60 = (get_lid e)
in (find_lid _134_60 unary_prim_ops)))


let quant_to_string = (fun t -> (let _134_62 = (get_lid t)
in (find_lid _134_62 quants)))


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
| FStar_Const.Const_string (bytes, _39_90) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_39_94) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x, _39_98) -> begin
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
(let _134_65 = (sli l)
in (FStar_Util.format1 "[[%s.reflect]]" _134_65))
end))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun _39_3 -> (match (_39_3) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _134_70 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _134_70))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _134_71 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _134_71))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _134_72 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _134_72))
end
| FStar_Syntax_Syntax.Tm_uinst (_39_121) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (_39_124) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (_39_127) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (_39_130) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (_39_133) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (_39_136) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (_39_139) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (_39_142) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (_39_145) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (_39_148) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (_39_151) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (_39_154, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
"Tm_delayed"
end
| Some (_39_160) -> begin
"Tm_delayed-resolved"
end)
end
| FStar_Syntax_Syntax.Tm_meta (_39_163) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))


let uvar_to_string = (fun u -> if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _134_77 = (let _134_76 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _134_76 FStar_Util.string_of_int))
in (Prims.strcat "?" _134_77))
end)


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe Prims.option) = (fun n u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_zero -> begin
((n), (None))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(int_of_univ (n + (Prims.parse_int "1")) u)
end
| _39_173 -> begin
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
(let _134_84 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _134_84))
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
(let _134_86 = (univ_to_string u)
in (let _134_85 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 "(%s + %s)" _134_86 _134_85)))
end)
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _134_88 = (let _134_87 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _134_87 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _134_88))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _134_91 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _134_91 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _134_95 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _134_95 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun _39_4 -> (match (_39_4) with
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
(let _134_98 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _134_98))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _134_99 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _134_99 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(let _134_103 = (let _134_100 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path _134_100))
in (let _134_102 = (let _134_101 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right _134_101 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" _134_103 _134_102)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(let _134_107 = (let _134_104 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path _134_104))
in (let _134_106 = (let _134_105 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right _134_105 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" _134_107 _134_106)))
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
| _39_235 -> begin
(let _134_110 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _134_110 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| _39_239 -> begin
(let _134_113 = (quals_to_string quals)
in (Prims.strcat _134_113 " "))
end))


let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let x = (FStar_Syntax_Subst.compress x)
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_39_243) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_39_246, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (let _134_139 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _134_138 = (FStar_All.pipe_right args (FStar_List.map (fun _39_259 -> (match (_39_259) with
| (t, _39_258) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _134_138 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _134_139 (FStar_String.concat "\\/")))
in (let _134_140 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _134_140)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _134_144 = (tag_of_term t)
in (let _134_143 = (sli m)
in (let _134_142 = (term_to_string t')
in (let _134_141 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s )" _134_144 _134_143 _134_142 _134_141)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1)) -> begin
(let _134_148 = (tag_of_term t)
in (let _134_147 = (term_to_string t)
in (let _134_146 = (sli m0)
in (let _134_145 = (sli m1)
in (FStar_Util.format4 "(MonadicLift-%s{%s} %s -> %s)" _134_148 _134_147 _134_146 _134_145)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(let _134_150 = (FStar_Range.string_of_range r)
in (let _134_149 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l _134_150 _134_149)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _39_285) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, _39_296) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_Options.print_universes ()) then begin
(let _134_151 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _134_151))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _134_153 = (binders_to_string " -> " bs)
in (let _134_152 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _134_153 _134_152)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
(let _134_157 = (binders_to_string " " bs)
in (let _134_156 = (term_to_string t2)
in (let _134_155 = (let _134_154 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _134_154))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _134_157 _134_156 _134_155))))
end
| Some (FStar_Util.Inr (l, flags)) when (FStar_Options.print_implicits ()) -> begin
(let _134_159 = (binders_to_string " " bs)
in (let _134_158 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))" _134_159 _134_158 l.FStar_Ident.str)))
end
| _39_321 -> begin
(let _134_161 = (binders_to_string " " bs)
in (let _134_160 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _134_161 _134_160)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _134_164 = (bv_to_string xt)
in (let _134_163 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _134_162 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _134_164 _134_163 _134_162))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _134_166 = (term_to_string t)
in (let _134_165 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _134_166 _134_165)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _134_168 = (lbs_to_string [] lbs)
in (let _134_167 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _134_168 _134_167)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), eff_name) -> begin
(let _134_172 = (term_to_string e)
in (let _134_171 = (let _134_169 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right _134_169 (FStar_Util.dflt "default")))
in (let _134_170 = (term_to_string t)
in (FStar_Util.format3 "(%s <: [%s] %s)" _134_172 _134_171 _134_170))))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _39_344) -> begin
(let _134_174 = (term_to_string e)
in (let _134_173 = (comp_to_string c)
in (FStar_Util.format2 "(%s <: %s)" _134_174 _134_173)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _134_182 = (term_to_string head)
in (let _134_181 = (let _134_180 = (FStar_All.pipe_right branches (FStar_List.map (fun _39_354 -> (match (_39_354) with
| (p, wopt, e) -> begin
(let _134_179 = (FStar_All.pipe_right p pat_to_string)
in (let _134_178 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _134_176 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _134_176))
end)
in (let _134_177 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _134_179 _134_178 _134_177))))
end))))
in (FStar_Util.concat_l "\n\t|" _134_180))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _134_182 _134_181)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_Options.print_universes ()) then begin
(let _134_184 = (term_to_string t)
in (let _134_183 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _134_184 _134_183)))
end else begin
(term_to_string t)
end
end
| _39_363 -> begin
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _134_189 = (fv_to_string l)
in (let _134_188 = (let _134_187 = (FStar_List.map (fun _39_371 -> (match (_39_371) with
| (x, b) -> begin
(

let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _134_187 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _134_189 _134_188)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _39_375) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _134_191 = (bv_to_string x)
in (let _134_190 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" _134_191 _134_190)))
end else begin
(let _134_192 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _134_192))
end
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _134_194 = (bv_to_string x)
in (let _134_193 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" _134_194 _134_193)))
end else begin
(bv_to_string x)
end
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_Options.print_real_names ()) then begin
(let _134_195 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _134_195))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _134_196 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _134_196))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (

let lbs = if (FStar_Options.print_universes ()) then begin
(let _134_202 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _39_391 = (let _134_200 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _134_200))
in (match (_39_391) with
| (us, td) -> begin
(

let _39_409 = (match ((let _134_201 = (FStar_Syntax_Subst.compress td)
in _134_201.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_39_393, ((t, _39_400))::((d, _39_396))::[]) -> begin
((t), (d))
end
| _39_406 -> begin
(FStar_All.failwith "Impossibe")
end)
in (match (_39_409) with
| (t, d) -> begin
(

let _39_410 = lb
in {FStar_Syntax_Syntax.lbname = _39_410.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_410.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((Prims.fst lbs)), (_134_202)))
end else begin
lbs
end
in (let _134_212 = (quals_to_string' quals)
in (let _134_211 = (let _134_210 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _134_209 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _134_208 = if (FStar_Options.print_universes ()) then begin
(let _134_205 = (let _134_204 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat _134_204 ">"))
in (Prims.strcat "<" _134_205))
end else begin
""
end
in (let _134_207 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _134_206 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _134_209 _134_208 _134_207 _134_206))))))))
in (FStar_Util.concat_l "\n and " _134_210))
in (FStar_Util.format3 "%slet %s %s" _134_212 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _134_211)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> if (FStar_Options.print_effect_args ()) then begin
(let _134_214 = (lc.FStar_Syntax_Syntax.comp ())
in (comp_to_string _134_214))
end else begin
(let _134_216 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _134_215 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _134_216 _134_215)))
end)
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s _39_5 -> (match (_39_5) with
| Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
(Prims.strcat "#." s)
end
| Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "$" s)
end
| _39_426 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (

let _39_431 = b
in (match (_39_431) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(let _134_221 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" _134_221))
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_bound_var_types ())))) then begin
(let _134_222 = (nm_to_string a)
in (imp_to_string _134_222 imp))
end else begin
(let _134_226 = (let _134_225 = (nm_to_string a)
in (let _134_224 = (let _134_223 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" _134_223))
in (Prims.strcat _134_225 _134_224)))
in (imp_to_string _134_226 imp))
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
(let _134_231 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _134_231 (FStar_String.concat sep)))
end else begin
(let _134_232 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _134_232 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _39_6 -> (match (_39_6) with
| (a, imp) -> begin
(let _134_234 = (term_to_string a)
in (imp_to_string _134_234 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args = if (FStar_Options.print_implicits ()) then begin
args
end else begin
(filter_imp args)
end
in (let _134_236 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _134_236 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _39_446) -> begin
(match ((let _134_238 = (FStar_Syntax_Subst.compress t)
in _134_238.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_450) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_453 -> begin
(let _134_239 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _134_239))
end)
end
| FStar_Syntax_Syntax.GTotal (t, _39_456) -> begin
(match ((let _134_240 = (FStar_Syntax_Subst.compress t)
in _134_240.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_460) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_463 -> begin
(let _134_241 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _134_241))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let basic = if (FStar_Options.print_effect_args ()) then begin
(let _134_247 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _134_246 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _134_245 = (let _134_242 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _134_242 (FStar_String.concat ", ")))
in (let _134_244 = (let _134_243 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right _134_243 (FStar_String.concat " ")))
in (FStar_Util.format4 "%s (%s) %s (attributes %s)" _134_247 _134_246 _134_245 _134_244)))))
end else begin
if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_7 -> (match (_39_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _39_469 -> begin
false
end)))) && (not ((FStar_Options.print_effect_args ())))) then begin
(let _134_249 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _134_249))
end else begin
if (((not ((FStar_Options.print_effect_args ()))) && (not ((FStar_Options.print_implicits ())))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_Options.print_effect_args ()))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_8 -> (match (_39_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _39_473 -> begin
false
end))))) then begin
(let _134_251 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _134_251))
end else begin
(let _134_253 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _134_252 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _134_253 _134_252)))
end
end
end
end
in (

let dec = (let _134_257 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _39_9 -> (match (_39_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _134_256 = (let _134_255 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _134_255))
in (_134_256)::[])
end
| _39_479 -> begin
[]
end))))
in (FStar_All.pipe_right _134_257 (FStar_String.concat " ")))
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
| FStar_Syntax_Syntax.DECREASES (_39_490) -> begin
""
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> if (FStar_Options.print_universes ()) then begin
(Prims.strcat "<" (Prims.strcat s ">"))
end else begin
""
end)


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun _39_496 -> (match (_39_496) with
| (us, t) -> begin
(let _134_266 = (let _134_264 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes _134_264))
in (let _134_265 = (term_to_string t)
in (FStar_Util.format2 "%s%s" _134_266 _134_265)))
end))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (

let actions_to_string = (fun actions -> (let _134_279 = (FStar_All.pipe_right actions (FStar_List.map (fun a -> (let _134_278 = (sli a.FStar_Syntax_Syntax.action_name)
in (let _134_277 = (let _134_274 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes _134_274))
in (let _134_276 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (let _134_275 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format4 "%s%s : %s = %s" _134_278 _134_277 _134_276 _134_275))))))))
in (FStar_All.pipe_right _134_279 (FStar_String.concat ",\n\t"))))
in (let _134_317 = (let _134_316 = (let _134_315 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _134_314 = (let _134_313 = (let _134_280 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes _134_280))
in (let _134_312 = (let _134_311 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _134_310 = (let _134_309 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _134_308 = (let _134_307 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (let _134_306 = (let _134_305 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _134_304 = (let _134_303 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _134_302 = (let _134_301 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _134_300 = (let _134_299 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (let _134_298 = (let _134_297 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _134_296 = (let _134_295 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _134_294 = (let _134_293 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _134_292 = (let _134_291 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _134_290 = (let _134_289 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (let _134_288 = (let _134_287 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _134_286 = (let _134_285 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (let _134_284 = (let _134_283 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (let _134_282 = (let _134_281 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (_134_281)::[])
in (_134_283)::_134_282))
in (_134_285)::_134_284))
in (_134_287)::_134_286))
in (_134_289)::_134_288))
in (_134_291)::_134_290))
in (_134_293)::_134_292))
in (_134_295)::_134_294))
in (_134_297)::_134_296))
in (_134_299)::_134_298))
in (_134_301)::_134_300))
in (_134_303)::_134_302))
in (_134_305)::_134_304))
in (_134_307)::_134_306))
in (_134_309)::_134_308))
in (_134_311)::_134_310))
in (_134_313)::_134_312))
in (_134_315)::_134_314))
in (if for_free then begin
"_for_free "
end else begin
""
end)::_134_316)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" _134_317))))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None), _39_506) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s)), _39_513) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _39_519) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _39_527, _39_529, quals, _39_532) -> begin
(let _134_322 = (quals_to_string' quals)
in (let _134_321 = (binders_to_string " " tps)
in (let _134_320 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" _134_322 lid.FStar_Ident.str _134_321 _134_320))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _39_539, _39_541, _39_543, _39_545, _39_547) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_552 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_552) with
| (univs, t) -> begin
(let _134_324 = (univ_names_to_string univs)
in (let _134_323 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _134_324 lid.FStar_Ident.str _134_323)))
end))
end else begin
(let _134_325 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _134_325))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _39_558) -> begin
(

let _39_563 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_563) with
| (univs, t) -> begin
(let _134_329 = (quals_to_string' quals)
in (let _134_328 = if (FStar_Options.print_universes ()) then begin
(let _134_326 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _134_326))
end else begin
""
end
in (let _134_327 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" _134_329 lid.FStar_Ident.str _134_328 _134_327))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _39_567, _39_569) -> begin
(let _134_330 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _134_330))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _39_574, _39_576, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _39_582) -> begin
(let _134_331 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _134_331))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _39_587, _39_589, _39_591) -> begin
(let _134_332 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _134_332 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _39_596) -> begin
(eff_decl_to_string false ed)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed, _39_601) -> begin
(eff_decl_to_string true ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(

let lift_wp = (match (((se.FStar_Syntax_Syntax.lift_wp), (se.FStar_Syntax_Syntax.lift))) with
| (None, None) -> begin
(FStar_All.failwith "impossible")
end
| (Some (lift_wp), _39_614) -> begin
lift_wp
end
| (_39_617, Some (lift)) -> begin
lift
end)
in (

let _39_624 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp) (Prims.snd lift_wp))
in (match (_39_624) with
| (us, t) -> begin
(let _134_336 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _134_335 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _134_334 = (univ_names_to_string us)
in (let _134_333 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _134_336 _134_335 _134_334 _134_333)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _39_630, flags, _39_633) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_638 = (let _134_337 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _134_337))
in (match (_39_638) with
| (univs, t) -> begin
(

let _39_647 = (match ((let _134_338 = (FStar_Syntax_Subst.compress t)
in _134_338.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((bs), (c))
end
| _39_644 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_39_647) with
| (tps, c) -> begin
(let _134_342 = (sli l)
in (let _134_341 = (univ_names_to_string univs)
in (let _134_340 = (binders_to_string " " tps)
in (let _134_339 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _134_342 _134_341 _134_340 _134_339)))))
end))
end))
end else begin
(let _134_345 = (sli l)
in (let _134_344 = (binders_to_string " " tps)
in (let _134_343 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _134_345 _134_344 _134_343))))
end
end))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _134_350 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _134_350 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_39_652, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = _39_659; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_656; FStar_Syntax_Syntax.lbdef = _39_654})::[]), _39_665, _39_667, _39_669) -> begin
(let _134_354 = (lbname_to_string lb)
in (let _134_353 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _134_354 _134_353)))
end
| _39_673 -> begin
(let _134_357 = (let _134_356 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _134_356 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _134_357 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _134_362 = (sli m.FStar_Syntax_Syntax.name)
in (let _134_361 = (let _134_360 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _134_360 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _134_362 _134_361))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _39_10 -> (match (_39_10) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(let _134_366 = (FStar_Util.string_of_int i)
in (let _134_365 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _134_366 _134_365)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _134_368 = (bv_to_string x)
in (let _134_367 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _134_368 _134_367)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _134_370 = (bv_to_string x)
in (let _134_369 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _134_370 _134_369)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _134_372 = (FStar_Util.string_of_int i)
in (let _134_371 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _134_372 _134_371)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _134_373 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _134_373))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _134_376 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _134_376 (FStar_String.concat "; "))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in (

let _39_711 = (match (ascription) with
| None -> begin
(FStar_Util.string_builder_append strb "None")
end
| Some (FStar_Util.Inl (lc)) -> begin
(

let _39_704 = (FStar_Util.string_builder_append strb "Some Inr ")
in (FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name)))
end
| Some (FStar_Util.Inr (lid)) -> begin
(

let _39_709 = (FStar_Util.string_builder_append strb "Some Inr ")
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

let _39_721 = (FStar_Util.string_builder_append strb "{")
in (

let _39_723 = (let _134_384 = (f x)
in (FStar_Util.string_builder_append strb _134_384))
in (

let _39_728 = (FStar_List.iter (fun x -> (

let _39_726 = (FStar_Util.string_builder_append strb ", ")
in (let _134_386 = (f x)
in (FStar_Util.string_builder_append strb _134_386)))) xs)
in (

let _39_730 = (FStar_Util.string_builder_append strb "}")
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

let _39_739 = (FStar_Util.string_builder_append strb "[")
in (

let _39_741 = (let _134_392 = (f x)
in (FStar_Util.string_builder_append strb _134_392))
in (

let _39_746 = (FStar_List.iter (fun x -> (

let _39_744 = (FStar_Util.string_builder_append strb "; ")
in (let _134_394 = (f x)
in (FStar_Util.string_builder_append strb _134_394)))) xs)
in (

let _39_748 = (FStar_Util.string_builder_append strb "]")
in (FStar_Util.string_of_string_builder strb))))))
end))




