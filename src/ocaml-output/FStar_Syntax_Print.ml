
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


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_unif (u) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(Prims.strcat "n" x.FStar_Ident.idText)
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(let _134_80 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _134_80))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _134_81 = (univ_to_string u)
in (FStar_Util.format1 "(S %s)" _134_81))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _134_83 = (let _134_82 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _134_82 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _134_83))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _134_86 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _134_86 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _134_90 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _134_90 (FStar_String.concat ", "))))


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
(let _134_93 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _134_93))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _134_94 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _134_94 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(let _134_98 = (let _134_95 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path _134_95))
in (let _134_97 = (let _134_96 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right _134_96 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" _134_98 _134_97)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(let _134_102 = (let _134_99 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path _134_99))
in (let _134_101 = (let _134_100 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right _134_100 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" _134_102 _134_101)))
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
| _39_220 -> begin
(let _134_105 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _134_105 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| _39_224 -> begin
(let _134_108 = (quals_to_string quals)
in (Prims.strcat _134_108 " "))
end))


let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let x = (FStar_Syntax_Subst.compress x)
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_39_228) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_39_231, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (let _134_133 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _134_132 = (FStar_All.pipe_right args (FStar_List.map (fun _39_244 -> (match (_39_244) with
| (t, _39_243) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _134_132 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _134_133 (FStar_String.concat "\\/")))
in (let _134_134 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _134_134)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _134_138 = (tag_of_term t)
in (let _134_137 = (sli m)
in (let _134_136 = (term_to_string t')
in (let _134_135 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s )" _134_138 _134_137 _134_136 _134_135)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1)) -> begin
(let _134_142 = (tag_of_term t)
in (let _134_141 = (term_to_string t)
in (let _134_140 = (sli m0)
in (let _134_139 = (sli m1)
in (FStar_Util.format4 "(MonadicLift-%s{%s} %s -> %s)" _134_142 _134_141 _134_140 _134_139)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(let _134_144 = (FStar_Range.string_of_range r)
in (let _134_143 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l _134_144 _134_143)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _39_270) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, _39_281) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_Options.print_universes ()) then begin
(let _134_145 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _134_145))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _134_147 = (binders_to_string " -> " bs)
in (let _134_146 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _134_147 _134_146)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
(let _134_151 = (binders_to_string " " bs)
in (let _134_150 = (term_to_string t2)
in (let _134_149 = (let _134_148 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _134_148))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _134_151 _134_150 _134_149))))
end
| Some (FStar_Util.Inr (l)) when (FStar_Options.print_implicits ()) -> begin
(let _134_153 = (binders_to_string " " bs)
in (let _134_152 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))" _134_153 _134_152 l.FStar_Ident.str)))
end
| _39_304 -> begin
(let _134_155 = (binders_to_string " " bs)
in (let _134_154 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _134_155 _134_154)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _134_158 = (bv_to_string xt)
in (let _134_157 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _134_156 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _134_158 _134_157 _134_156))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _134_160 = (term_to_string t)
in (let _134_159 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _134_160 _134_159)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _134_162 = (lbs_to_string [] lbs)
in (let _134_161 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _134_162 _134_161)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _39_321) -> begin
(let _134_164 = (term_to_string e)
in (let _134_163 = (term_to_string t)
in (FStar_Util.format2 "(%s <: %s)" _134_164 _134_163)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _39_328) -> begin
(let _134_166 = (term_to_string e)
in (let _134_165 = (comp_to_string c)
in (FStar_Util.format2 "(%s <: %s)" _134_166 _134_165)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _134_174 = (term_to_string head)
in (let _134_173 = (let _134_172 = (FStar_All.pipe_right branches (FStar_List.map (fun _39_338 -> (match (_39_338) with
| (p, wopt, e) -> begin
(let _134_171 = (FStar_All.pipe_right p pat_to_string)
in (let _134_170 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _134_168 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _134_168))
end)
in (let _134_169 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _134_171 _134_170 _134_169))))
end))))
in (FStar_Util.concat_l "\n\t|" _134_172))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _134_174 _134_173)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_Options.print_universes ()) then begin
(let _134_176 = (term_to_string t)
in (let _134_175 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _134_176 _134_175)))
end else begin
(term_to_string t)
end
end
| _39_347 -> begin
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _134_181 = (fv_to_string l)
in (let _134_180 = (let _134_179 = (FStar_List.map (fun _39_355 -> (match (_39_355) with
| (x, b) -> begin
(

let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _134_179 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _134_181 _134_180)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _39_359) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _134_183 = (bv_to_string x)
in (let _134_182 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" _134_183 _134_182)))
end else begin
(let _134_184 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _134_184))
end
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _134_186 = (bv_to_string x)
in (let _134_185 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" _134_186 _134_185)))
end else begin
(bv_to_string x)
end
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_Options.print_real_names ()) then begin
(let _134_187 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _134_187))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _134_188 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _134_188))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (

let lbs = if (FStar_Options.print_universes ()) then begin
(let _134_194 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _39_375 = (let _134_192 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _134_192))
in (match (_39_375) with
| (us, td) -> begin
(

let _39_393 = (match ((let _134_193 = (FStar_Syntax_Subst.compress td)
in _134_193.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_39_377, ((t, _39_384))::((d, _39_380))::[]) -> begin
((t), (d))
end
| _39_390 -> begin
(FStar_All.failwith "Impossibe")
end)
in (match (_39_393) with
| (t, d) -> begin
(

let _39_394 = lb
in {FStar_Syntax_Syntax.lbname = _39_394.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_394.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((Prims.fst lbs)), (_134_194)))
end else begin
lbs
end
in (let _134_204 = (quals_to_string' quals)
in (let _134_203 = (let _134_202 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _134_201 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _134_200 = if (FStar_Options.print_universes ()) then begin
(let _134_197 = (let _134_196 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat _134_196 ">"))
in (Prims.strcat "<" _134_197))
end else begin
""
end
in (let _134_199 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _134_198 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _134_201 _134_200 _134_199 _134_198))))))))
in (FStar_Util.concat_l "\n and " _134_202))
in (FStar_Util.format3 "%slet %s %s" _134_204 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _134_203)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> if (FStar_Options.print_effect_args ()) then begin
(let _134_206 = (lc.FStar_Syntax_Syntax.comp ())
in (comp_to_string _134_206))
end else begin
(let _134_208 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _134_207 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _134_208 _134_207)))
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
| _39_410 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (

let _39_415 = b
in (match (_39_415) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(let _134_213 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" _134_213))
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_bound_var_types ())))) then begin
(let _134_214 = (nm_to_string a)
in (imp_to_string _134_214 imp))
end else begin
(let _134_218 = (let _134_217 = (nm_to_string a)
in (let _134_216 = (let _134_215 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" _134_215))
in (Prims.strcat _134_217 _134_216)))
in (imp_to_string _134_218 imp))
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
(let _134_223 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _134_223 (FStar_String.concat sep)))
end else begin
(let _134_224 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _134_224 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _39_6 -> (match (_39_6) with
| (a, imp) -> begin
(let _134_226 = (term_to_string a)
in (imp_to_string _134_226 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args = if (FStar_Options.print_implicits ()) then begin
args
end else begin
(filter_imp args)
end
in (let _134_228 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _134_228 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _39_430) -> begin
(match ((let _134_230 = (FStar_Syntax_Subst.compress t)
in _134_230.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_434) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_437 -> begin
(let _134_231 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _134_231))
end)
end
| FStar_Syntax_Syntax.GTotal (t, _39_440) -> begin
(match ((let _134_232 = (FStar_Syntax_Subst.compress t)
in _134_232.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_444) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_447 -> begin
(let _134_233 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _134_233))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let basic = if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_7 -> (match (_39_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _39_453 -> begin
false
end)))) && (not ((FStar_Options.print_effect_args ())))) then begin
(let _134_235 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _134_235))
end else begin
if (((not ((FStar_Options.print_effect_args ()))) && (not ((FStar_Options.print_implicits ())))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_Options.print_effect_args ()))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_8 -> (match (_39_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _39_457 -> begin
false
end))))) then begin
(let _134_237 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _134_237))
end else begin
if (FStar_Options.print_effect_args ()) then begin
(let _134_241 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _134_240 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _134_239 = (let _134_238 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _134_238 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _134_241 _134_240 _134_239))))
end else begin
(let _134_243 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _134_242 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _134_243 _134_242)))
end
end
end
end
in (

let dec = (let _134_247 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _39_9 -> (match (_39_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _134_246 = (let _134_245 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _134_245))
in (_134_246)::[])
end
| _39_463 -> begin
[]
end))))
in (FStar_All.pipe_right _134_247 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> if (FStar_Options.print_universes ()) then begin
(Prims.strcat "<" (Prims.strcat s ">"))
end else begin
""
end)


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun _39_469 -> (match (_39_469) with
| (us, t) -> begin
(let _134_255 = (let _134_253 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes _134_253))
in (let _134_254 = (term_to_string t)
in (FStar_Util.format2 "%s%s" _134_255 _134_254)))
end))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (

let actions_to_string = (fun actions -> (let _134_268 = (FStar_All.pipe_right actions (FStar_List.map (fun a -> (let _134_267 = (sli a.FStar_Syntax_Syntax.action_name)
in (let _134_266 = (let _134_263 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes _134_263))
in (let _134_265 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (let _134_264 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format4 "%s%s : %s = %s" _134_267 _134_266 _134_265 _134_264))))))))
in (FStar_All.pipe_right _134_268 (FStar_String.concat ",\n\t"))))
in (let _134_306 = (let _134_305 = (let _134_304 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _134_303 = (let _134_302 = (let _134_269 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes _134_269))
in (let _134_301 = (let _134_300 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _134_299 = (let _134_298 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _134_297 = (let _134_296 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (let _134_295 = (let _134_294 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _134_293 = (let _134_292 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _134_291 = (let _134_290 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _134_289 = (let _134_288 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (let _134_287 = (let _134_286 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _134_285 = (let _134_284 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _134_283 = (let _134_282 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _134_281 = (let _134_280 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _134_279 = (let _134_278 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (let _134_277 = (let _134_276 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _134_275 = (let _134_274 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (let _134_273 = (let _134_272 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (let _134_271 = (let _134_270 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (_134_270)::[])
in (_134_272)::_134_271))
in (_134_274)::_134_273))
in (_134_276)::_134_275))
in (_134_278)::_134_277))
in (_134_280)::_134_279))
in (_134_282)::_134_281))
in (_134_284)::_134_283))
in (_134_286)::_134_285))
in (_134_288)::_134_287))
in (_134_290)::_134_289))
in (_134_292)::_134_291))
in (_134_294)::_134_293))
in (_134_296)::_134_295))
in (_134_298)::_134_297))
in (_134_300)::_134_299))
in (_134_302)::_134_301))
in (_134_304)::_134_303))
in (if for_free then begin
"_for_free "
end else begin
""
end)::_134_305)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" _134_306))))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None), _39_479) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s)), _39_486) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _39_492) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _39_500, _39_502, quals, _39_505) -> begin
(let _134_311 = (quals_to_string' quals)
in (let _134_310 = (binders_to_string " " tps)
in (let _134_309 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" _134_311 lid.FStar_Ident.str _134_310 _134_309))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _39_512, _39_514, _39_516, _39_518, _39_520) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_525 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_525) with
| (univs, t) -> begin
(let _134_313 = (univ_names_to_string univs)
in (let _134_312 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _134_313 lid.FStar_Ident.str _134_312)))
end))
end else begin
(let _134_314 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _134_314))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _39_531) -> begin
(

let _39_536 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_536) with
| (univs, t) -> begin
(let _134_318 = (quals_to_string' quals)
in (let _134_317 = if (FStar_Options.print_universes ()) then begin
(let _134_315 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _134_315))
end else begin
""
end
in (let _134_316 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" _134_318 lid.FStar_Ident.str _134_317 _134_316))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _39_540, _39_542) -> begin
(let _134_319 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _134_319))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _39_547, _39_549, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _39_555) -> begin
(let _134_320 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _134_320))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _39_560, _39_562, _39_564) -> begin
(let _134_321 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _134_321 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _39_569) -> begin
(eff_decl_to_string false ed)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed, _39_574) -> begin
(eff_decl_to_string true ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(

let lift_wp = (match (((se.FStar_Syntax_Syntax.lift_wp), (se.FStar_Syntax_Syntax.lift))) with
| (None, None) -> begin
(FStar_All.failwith "impossible")
end
| (Some (lift_wp), _39_587) -> begin
lift_wp
end
| (_39_590, Some (lift)) -> begin
lift
end)
in (

let _39_597 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp) (Prims.snd lift_wp))
in (match (_39_597) with
| (us, t) -> begin
(let _134_325 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _134_324 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _134_323 = (univ_names_to_string us)
in (let _134_322 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _134_325 _134_324 _134_323 _134_322)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _39_603, _39_605) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_610 = (let _134_326 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _134_326))
in (match (_39_610) with
| (univs, t) -> begin
(

let _39_619 = (match ((let _134_327 = (FStar_Syntax_Subst.compress t)
in _134_327.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((bs), (c))
end
| _39_616 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_39_619) with
| (tps, c) -> begin
(let _134_331 = (sli l)
in (let _134_330 = (univ_names_to_string univs)
in (let _134_329 = (binders_to_string " " tps)
in (let _134_328 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _134_331 _134_330 _134_329 _134_328)))))
end))
end))
end else begin
(let _134_334 = (sli l)
in (let _134_333 = (binders_to_string " " tps)
in (let _134_332 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _134_334 _134_333 _134_332))))
end
end))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _134_339 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _134_339 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_39_624, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = _39_631; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_628; FStar_Syntax_Syntax.lbdef = _39_626})::[]), _39_637, _39_639, _39_641) -> begin
(let _134_343 = (lbname_to_string lb)
in (let _134_342 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _134_343 _134_342)))
end
| _39_645 -> begin
(let _134_346 = (let _134_345 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _134_345 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _134_346 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _134_351 = (sli m.FStar_Syntax_Syntax.name)
in (let _134_350 = (let _134_349 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _134_349 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _134_351 _134_350))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _39_10 -> (match (_39_10) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(let _134_355 = (FStar_Util.string_of_int i)
in (let _134_354 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _134_355 _134_354)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _134_357 = (bv_to_string x)
in (let _134_356 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _134_357 _134_356)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _134_359 = (bv_to_string x)
in (let _134_358 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _134_359 _134_358)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _134_361 = (FStar_Util.string_of_int i)
in (let _134_360 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _134_361 _134_360)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _134_362 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _134_362))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _134_365 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _134_365 (FStar_String.concat "; "))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in (

let _39_683 = (match (ascription) with
| None -> begin
(FStar_Util.string_builder_append strb "None")
end
| Some (FStar_Util.Inl (lc)) -> begin
(

let _39_676 = (FStar_Util.string_builder_append strb "Some Inr ")
in (FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name)))
end
| Some (FStar_Util.Inr (lid)) -> begin
(

let _39_681 = (FStar_Util.string_builder_append strb "Some Inr ")
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

let _39_693 = (FStar_Util.string_builder_append strb "{")
in (

let _39_695 = (let _134_373 = (f x)
in (FStar_Util.string_builder_append strb _134_373))
in (

let _39_700 = (FStar_List.iter (fun x -> (

let _39_698 = (FStar_Util.string_builder_append strb ", ")
in (let _134_375 = (f x)
in (FStar_Util.string_builder_append strb _134_375)))) xs)
in (

let _39_702 = (FStar_Util.string_builder_append strb "}")
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

let _39_711 = (FStar_Util.string_builder_append strb "[")
in (

let _39_713 = (let _134_381 = (f x)
in (FStar_Util.string_builder_append strb _134_381))
in (

let _39_718 = (FStar_List.iter (fun x -> (

let _39_716 = (FStar_Util.string_builder_append strb "; ")
in (let _134_383 = (f x)
in (FStar_Util.string_builder_append strb _134_383)))) xs)
in (

let _39_720 = (FStar_Util.string_builder_append strb "]")
in (FStar_Util.string_of_string_builder strb))))))
end))




