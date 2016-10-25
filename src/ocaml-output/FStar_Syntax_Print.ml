
open Prims

let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> l.FStar_Ident.str)


let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _136_8 = (let _136_7 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "#" _136_7))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _136_8)))


let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> if (FStar_Options.print_real_names ()) then begin
(bv_to_string bv)
end else begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)


let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _136_14 = (let _136_13 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "@" _136_13))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _136_14)))


let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Syntax_Const.op_Addition), ("+")))::(((FStar_Syntax_Const.op_Subtraction), ("-")))::(((FStar_Syntax_Const.op_Multiply), ("*")))::(((FStar_Syntax_Const.op_Division), ("/")))::(((FStar_Syntax_Const.op_Eq), ("=")))::(((FStar_Syntax_Const.op_ColonEq), (":=")))::(((FStar_Syntax_Const.op_notEq), ("<>")))::(((FStar_Syntax_Const.op_And), ("&&")))::(((FStar_Syntax_Const.op_Or), ("||")))::(((FStar_Syntax_Const.op_LTE), ("<=")))::(((FStar_Syntax_Const.op_GTE), (">=")))::(((FStar_Syntax_Const.op_LT), ("<")))::(((FStar_Syntax_Const.op_GT), (">")))::(((FStar_Syntax_Const.op_Modulus), ("mod")))::(((FStar_Syntax_Const.and_lid), ("/\\")))::(((FStar_Syntax_Const.or_lid), ("\\/")))::(((FStar_Syntax_Const.imp_lid), ("==>")))::(((FStar_Syntax_Const.iff_lid), ("<==>")))::(((FStar_Syntax_Const.precedes_lid), ("<<")))::(((FStar_Syntax_Const.eq2_lid), ("==")))::(((FStar_Syntax_Const.eq3_lid), ("===")))::[]


let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Syntax_Const.op_Negation), ("not")))::(((FStar_Syntax_Const.op_Minus), ("-")))::(((FStar_Syntax_Const.not_lid), ("~")))::[]


let is_prim_op = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
end
| _39_22 -> begin
false
end))


let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| _39_27 -> begin
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
| FStar_Util.Inl (_39_37) -> begin
false
end
| FStar_Util.Inr (_39_40) -> begin
true
end))


let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _39_2 -> (match (_39_2) with
| (_39_45, Some (FStar_Syntax_Syntax.Implicit (_39_47))) -> begin
false
end
| _39_52 -> begin
true
end)))))


let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _136_37 = (FStar_Syntax_Subst.compress e)
in _136_37.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args = (filter_imp args)
in (

let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = (Prims.parse_int "2"))) then begin
(match ((let _136_38 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex _136_38))) with
| Some (xs) -> begin
(let _136_40 = (let _136_39 = (FStar_List.nth exps (Prims.parse_int "0"))
in (_136_39)::xs)
in Some (_136_40))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _39_64 -> begin
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


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _136_54 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _136_54)))


let infix_prim_op_to_string = (fun e -> (let _136_56 = (get_lid e)
in (find_lid _136_56 infix_prim_ops)))


let unary_prim_op_to_string = (fun e -> (let _136_58 = (get_lid e)
in (find_lid _136_58 unary_prim_ops)))


let quant_to_string = (fun t -> (let _136_60 = (get_lid t)
in (find_lid _136_60 quants)))


let rec sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_Options.print_real_names ()) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)


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
| FStar_Const.Const_string (bytes, _39_88) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_39_92) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x, _39_96) -> begin
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
(let _136_65 = (sli l)
in (FStar_Util.format1 "[[%s.reflect]]" _136_65))
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
(let _136_70 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _136_70))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _136_71 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _136_71))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _136_72 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _136_72))
end
| FStar_Syntax_Syntax.Tm_uinst (_39_119) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (_39_122) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (_39_125) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (_39_128) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (_39_131) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (_39_134) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (_39_137) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (_39_140) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (_39_143) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (_39_146) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (_39_149) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (_39_152, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
"Tm_delayed"
end
| Some (_39_158) -> begin
"Tm_delayed-resolved"
end)
end
| FStar_Syntax_Syntax.Tm_meta (_39_161) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))


let uvar_to_string = (fun u -> if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _136_77 = (let _136_76 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _136_76 FStar_Util.string_of_int))
in (Prims.strcat "?" _136_77))
end)


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_unif (u) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(Prims.strcat "n" x.FStar_Ident.idText)
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(let _136_80 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _136_80))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _136_81 = (univ_to_string u)
in (FStar_Util.format1 "(S %s)" _136_81))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _136_83 = (let _136_82 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _136_82 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _136_83))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _136_86 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _136_86 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _136_90 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _136_90 (FStar_String.concat ", "))))


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
(let _136_93 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _136_93))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _136_94 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _136_94 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(let _136_96 = (let _136_95 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _136_95 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordType %s)" _136_96))
end
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
(let _136_98 = (let _136_97 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _136_97 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordConstructor %s)" _136_98))
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
| FStar_Syntax_Syntax.Reflectable -> begin
"reflect"
end))


let quals_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| _39_212 -> begin
(let _136_101 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _136_101 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| _39_216 -> begin
(let _136_104 = (quals_to_string quals)
in (Prims.strcat _136_104 " "))
end))


let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let x = (FStar_Syntax_Subst.compress x)
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_39_220) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_39_223, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (let _136_129 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _136_128 = (FStar_All.pipe_right args (FStar_List.map (fun _39_236 -> (match (_39_236) with
| (t, _39_235) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _136_128 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _136_129 (FStar_String.concat "\\/")))
in (let _136_130 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _136_130)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _136_134 = (tag_of_term t)
in (let _136_133 = (sli m)
in (let _136_132 = (term_to_string t')
in (let _136_131 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s )" _136_134 _136_133 _136_132 _136_131)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1)) -> begin
(let _136_138 = (tag_of_term t)
in (let _136_137 = (term_to_string t)
in (let _136_136 = (sli m0)
in (let _136_135 = (sli m1)
in (FStar_Util.format4 "(MonadicLift-%s{%s} %s -> %s)" _136_138 _136_137 _136_136 _136_135)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(let _136_140 = (FStar_Range.string_of_range r)
in (let _136_139 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l _136_140 _136_139)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _39_262) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, _39_273) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_Options.print_universes ()) then begin
(let _136_141 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _136_141))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _136_143 = (binders_to_string " -> " bs)
in (let _136_142 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _136_143 _136_142)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
(let _136_147 = (binders_to_string " " bs)
in (let _136_146 = (term_to_string t2)
in (let _136_145 = (let _136_144 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _136_144))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _136_147 _136_146 _136_145))))
end
| Some (FStar_Util.Inr (l)) when (FStar_Options.print_implicits ()) -> begin
(let _136_149 = (binders_to_string " " bs)
in (let _136_148 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))" _136_149 _136_148 l.FStar_Ident.str)))
end
| _39_296 -> begin
(let _136_151 = (binders_to_string " " bs)
in (let _136_150 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _136_151 _136_150)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _136_154 = (bv_to_string xt)
in (let _136_153 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _136_152 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _136_154 _136_153 _136_152))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _136_156 = (term_to_string t)
in (let _136_155 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _136_156 _136_155)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _136_158 = (lbs_to_string [] lbs)
in (let _136_157 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _136_158 _136_157)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _39_313) -> begin
(let _136_160 = (term_to_string e)
in (let _136_159 = (term_to_string t)
in (FStar_Util.format2 "(%s : %s)" _136_160 _136_159)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _39_320) -> begin
(let _136_162 = (term_to_string e)
in (let _136_161 = (comp_to_string c)
in (FStar_Util.format2 "(%s : %s)" _136_162 _136_161)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _136_170 = (term_to_string head)
in (let _136_169 = (let _136_168 = (FStar_All.pipe_right branches (FStar_List.map (fun _39_330 -> (match (_39_330) with
| (p, wopt, e) -> begin
(let _136_167 = (FStar_All.pipe_right p pat_to_string)
in (let _136_166 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _136_164 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _136_164))
end)
in (let _136_165 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _136_167 _136_166 _136_165))))
end))))
in (FStar_Util.concat_l "\n\t|" _136_168))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _136_170 _136_169)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_Options.print_universes ()) then begin
(let _136_172 = (term_to_string t)
in (let _136_171 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _136_172 _136_171)))
end else begin
(term_to_string t)
end
end
| _39_339 -> begin
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _136_177 = (fv_to_string l)
in (let _136_176 = (let _136_175 = (FStar_List.map (fun _39_347 -> (match (_39_347) with
| (x, b) -> begin
(

let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _136_175 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _136_177 _136_176)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _39_351) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _136_179 = (bv_to_string x)
in (let _136_178 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" _136_179 _136_178)))
end else begin
(let _136_180 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _136_180))
end
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _136_182 = (bv_to_string x)
in (let _136_181 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" _136_182 _136_181)))
end else begin
(bv_to_string x)
end
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_Options.print_real_names ()) then begin
(let _136_183 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _136_183))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _136_184 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _136_184))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (

let lbs = if (FStar_Options.print_universes ()) then begin
(let _136_190 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _39_367 = (let _136_188 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _136_188))
in (match (_39_367) with
| (us, td) -> begin
(

let _39_385 = (match ((let _136_189 = (FStar_Syntax_Subst.compress td)
in _136_189.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_39_369, ((t, _39_376))::((d, _39_372))::[]) -> begin
((t), (d))
end
| _39_382 -> begin
(FStar_All.failwith "Impossibe")
end)
in (match (_39_385) with
| (t, d) -> begin
(

let _39_386 = lb
in {FStar_Syntax_Syntax.lbname = _39_386.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_386.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((Prims.fst lbs)), (_136_190)))
end else begin
lbs
end
in (let _136_200 = (quals_to_string' quals)
in (let _136_199 = (let _136_198 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _136_197 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _136_196 = if (FStar_Options.print_universes ()) then begin
(let _136_193 = (let _136_192 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat _136_192 ">"))
in (Prims.strcat "<" _136_193))
end else begin
""
end
in (let _136_195 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _136_194 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _136_197 _136_196 _136_195 _136_194))))))))
in (FStar_Util.concat_l "\n and " _136_198))
in (FStar_Util.format3 "%slet %s %s" _136_200 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _136_199)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _136_203 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _136_202 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _136_203 _136_202))))
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
| _39_402 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (

let _39_407 = b
in (match (_39_407) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(let _136_208 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" _136_208))
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_bound_var_types ())))) then begin
(let _136_209 = (nm_to_string a)
in (imp_to_string _136_209 imp))
end else begin
(let _136_213 = (let _136_212 = (nm_to_string a)
in (let _136_211 = (let _136_210 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" _136_210))
in (Prims.strcat _136_212 _136_211)))
in (imp_to_string _136_213 imp))
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
(let _136_218 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _136_218 (FStar_String.concat sep)))
end else begin
(let _136_219 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _136_219 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _39_6 -> (match (_39_6) with
| (a, imp) -> begin
(let _136_221 = (term_to_string a)
in (imp_to_string _136_221 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args = if (FStar_Options.print_implicits ()) then begin
args
end else begin
(filter_imp args)
end
in (let _136_223 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _136_223 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _39_422) -> begin
(match ((let _136_225 = (FStar_Syntax_Subst.compress t)
in _136_225.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_426) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_429 -> begin
(let _136_226 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _136_226))
end)
end
| FStar_Syntax_Syntax.GTotal (t, _39_432) -> begin
(match ((let _136_227 = (FStar_Syntax_Subst.compress t)
in _136_227.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_436) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_439 -> begin
(let _136_228 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _136_228))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let basic = if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_7 -> (match (_39_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _39_445 -> begin
false
end)))) && (not ((FStar_Options.print_effect_args ())))) then begin
(let _136_230 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _136_230))
end else begin
if (((not ((FStar_Options.print_effect_args ()))) && (not ((FStar_Options.print_implicits ())))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_Options.print_effect_args ()))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_8 -> (match (_39_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _39_449 -> begin
false
end))))) then begin
(let _136_232 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _136_232))
end else begin
if (FStar_Options.print_effect_args ()) then begin
(let _136_236 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _136_235 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _136_234 = (let _136_233 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _136_233 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _136_236 _136_235 _136_234))))
end else begin
(let _136_238 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _136_237 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _136_238 _136_237)))
end
end
end
end
in (

let dec = (let _136_242 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _39_9 -> (match (_39_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _136_241 = (let _136_240 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _136_240))
in (_136_241)::[])
end
| _39_455 -> begin
[]
end))))
in (FStar_All.pipe_right _136_242 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun _39_460 -> (match (_39_460) with
| (us, t) -> begin
(let _136_247 = (univ_names_to_string us)
in (let _136_246 = (term_to_string t)
in (FStar_Util.format2 "<%s> %s" _136_247 _136_246)))
end))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (

let actions_to_string = (fun actions -> (let _136_259 = (FStar_All.pipe_right actions (FStar_List.map (fun a -> (let _136_258 = (sli a.FStar_Syntax_Syntax.action_name)
in (let _136_257 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (let _136_256 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (let _136_255 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format4 "%s<%s> : %s = %s" _136_258 _136_257 _136_256 _136_255))))))))
in (FStar_All.pipe_right _136_259 (FStar_String.concat ",\n\t"))))
in (let _136_296 = (let _136_295 = (let _136_294 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _136_293 = (let _136_292 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (let _136_291 = (let _136_290 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _136_289 = (let _136_288 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _136_287 = (let _136_286 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (let _136_285 = (let _136_284 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _136_283 = (let _136_282 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _136_281 = (let _136_280 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _136_279 = (let _136_278 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (let _136_277 = (let _136_276 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _136_275 = (let _136_274 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _136_273 = (let _136_272 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _136_271 = (let _136_270 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _136_269 = (let _136_268 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (let _136_267 = (let _136_266 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _136_265 = (let _136_264 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (let _136_263 = (let _136_262 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (let _136_261 = (let _136_260 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (_136_260)::[])
in (_136_262)::_136_261))
in (_136_264)::_136_263))
in (_136_266)::_136_265))
in (_136_268)::_136_267))
in (_136_270)::_136_269))
in (_136_272)::_136_271))
in (_136_274)::_136_273))
in (_136_276)::_136_275))
in (_136_278)::_136_277))
in (_136_280)::_136_279))
in (_136_282)::_136_281))
in (_136_284)::_136_283))
in (_136_286)::_136_285))
in (_136_288)::_136_287))
in (_136_290)::_136_289))
in (_136_292)::_136_291))
in (_136_294)::_136_293))
in (if for_free then begin
"for free "
end else begin
""
end)::_136_295)
in (FStar_Util.format "new_effect %s{ %s<%s> %s : %s \n  ret         = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\n; actions     = \n\t%s\n}\n" _136_296))))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None), _39_470) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s)), _39_477) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _39_483) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _39_491, _39_493, quals, _39_496) -> begin
(let _136_301 = (quals_to_string' quals)
in (let _136_300 = (binders_to_string " " tps)
in (let _136_299 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" _136_301 lid.FStar_Ident.str _136_300 _136_299))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _39_503, _39_505, _39_507, _39_509, _39_511) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_516 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_516) with
| (univs, t) -> begin
(let _136_303 = (univ_names_to_string univs)
in (let _136_302 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _136_303 lid.FStar_Ident.str _136_302)))
end))
end else begin
(let _136_304 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _136_304))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _39_522) -> begin
(

let _39_527 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_527) with
| (univs, t) -> begin
(let _136_308 = (quals_to_string' quals)
in (let _136_307 = if (FStar_Options.print_universes ()) then begin
(let _136_305 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _136_305))
end else begin
""
end
in (let _136_306 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" _136_308 lid.FStar_Ident.str _136_307 _136_306))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _39_531, _39_533) -> begin
(let _136_309 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _136_309))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _39_538, _39_540, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _39_546) -> begin
(let _136_310 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _136_310))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _39_551, _39_553, _39_555) -> begin
(let _136_311 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _136_311 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _39_560) -> begin
(eff_decl_to_string false ed)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed, _39_565) -> begin
(eff_decl_to_string true ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(

let lift_wp = (match (((se.FStar_Syntax_Syntax.lift_wp), (se.FStar_Syntax_Syntax.lift))) with
| (None, None) -> begin
(FStar_All.failwith "impossible")
end
| (Some (lift_wp), _39_578) -> begin
lift_wp
end
| (_39_581, Some (lift)) -> begin
lift
end)
in (

let _39_588 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp) (Prims.snd lift_wp))
in (match (_39_588) with
| (us, t) -> begin
(let _136_315 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _136_314 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _136_313 = (univ_names_to_string us)
in (let _136_312 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _136_315 _136_314 _136_313 _136_312)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _39_594, _39_596) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_601 = (let _136_316 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _136_316))
in (match (_39_601) with
| (univs, t) -> begin
(

let _39_610 = (match ((let _136_317 = (FStar_Syntax_Subst.compress t)
in _136_317.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((bs), (c))
end
| _39_607 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_39_610) with
| (tps, c) -> begin
(let _136_321 = (sli l)
in (let _136_320 = (univ_names_to_string univs)
in (let _136_319 = (binders_to_string " " tps)
in (let _136_318 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _136_321 _136_320 _136_319 _136_318)))))
end))
end))
end else begin
(let _136_324 = (sli l)
in (let _136_323 = (binders_to_string " " tps)
in (let _136_322 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _136_324 _136_323 _136_322))))
end
end))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _136_329 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _136_329 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_39_615, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = _39_622; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_619; FStar_Syntax_Syntax.lbdef = _39_617})::[]), _39_628, _39_630, _39_632) -> begin
(let _136_333 = (lbname_to_string lb)
in (let _136_332 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _136_333 _136_332)))
end
| _39_636 -> begin
(let _136_336 = (let _136_335 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _136_335 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _136_336 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _136_341 = (sli m.FStar_Syntax_Syntax.name)
in (let _136_340 = (let _136_339 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _136_339 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _136_341 _136_340))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _39_10 -> (match (_39_10) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(let _136_345 = (FStar_Util.string_of_int i)
in (let _136_344 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _136_345 _136_344)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _136_347 = (bv_to_string x)
in (let _136_346 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _136_347 _136_346)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _136_349 = (bv_to_string x)
in (let _136_348 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _136_349 _136_348)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _136_351 = (FStar_Util.string_of_int i)
in (let _136_350 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _136_351 _136_350)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _136_352 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _136_352))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _136_355 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _136_355 (FStar_String.concat "; "))))




