
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
| _40_23 -> begin
false
end))


let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| _40_28 -> begin
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
| FStar_Util.Inl (_40_38) -> begin
false
end
| FStar_Util.Inr (_40_41) -> begin
true
end))


let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _40_2 -> (match (_40_2) with
| (_40_46, Some (FStar_Syntax_Syntax.Implicit (_40_48))) -> begin
false
end
| _40_53 -> begin
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
| _40_65 -> begin
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
| FStar_Const.Const_string (bytes, _40_88) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_40_92) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x, _40_96) -> begin
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
| FStar_Syntax_Syntax.Tm_uinst (_40_119) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (_40_122) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (_40_125) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (_40_128) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (_40_131) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (_40_134) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (_40_137) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (_40_140) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (_40_143) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (_40_146) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (_40_149) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (_40_152, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
"Tm_delayed"
end
| Some (_40_158) -> begin
"Tm_delayed-resolved"
end)
end
| FStar_Syntax_Syntax.Tm_meta (_40_161) -> begin
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
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(let _137_96 = (let _137_95 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _137_95 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordType %s)" _137_96))
end
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
(let _137_98 = (let _137_97 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _137_97 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordConstructor %s)" _137_98))
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
| _40_212 -> begin
(let _137_101 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _137_101 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| _40_216 -> begin
(let _137_104 = (quals_to_string quals)
in (Prims.strcat _137_104 " "))
end))


let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let x = (FStar_Syntax_Subst.compress x)
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_40_220) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_40_223, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (let _137_129 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _137_128 = (FStar_All.pipe_right args (FStar_List.map (fun _40_236 -> (match (_40_236) with
| (t, _40_235) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _137_128 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _137_129 (FStar_String.concat "\\/")))
in (let _137_130 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _137_130)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _137_134 = (tag_of_term t)
in (let _137_133 = (sli m)
in (let _137_132 = (term_to_string t')
in (let _137_131 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s )" _137_134 _137_133 _137_132 _137_131)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1)) -> begin
(let _137_138 = (tag_of_term t)
in (let _137_137 = (term_to_string t)
in (let _137_136 = (sli m0)
in (let _137_135 = (sli m1)
in (FStar_Util.format4 "(MonadicLift-%s{%s} %s -> %s)" _137_138 _137_137 _137_136 _137_135)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(let _137_140 = (FStar_Range.string_of_range r)
in (let _137_139 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l _137_140 _137_139)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _40_262) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, _40_273) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_Options.print_universes ()) then begin
(let _137_141 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _137_141))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _137_143 = (binders_to_string " -> " bs)
in (let _137_142 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _137_143 _137_142)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
(let _137_147 = (binders_to_string " " bs)
in (let _137_146 = (term_to_string t2)
in (let _137_145 = (let _137_144 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _137_144))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _137_147 _137_146 _137_145))))
end
| Some (FStar_Util.Inr (l)) when (FStar_Options.print_implicits ()) -> begin
(let _137_149 = (binders_to_string " " bs)
in (let _137_148 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))" _137_149 _137_148 l.FStar_Ident.str)))
end
| _40_296 -> begin
(let _137_151 = (binders_to_string " " bs)
in (let _137_150 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _137_151 _137_150)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _137_154 = (bv_to_string xt)
in (let _137_153 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _137_152 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _137_154 _137_153 _137_152))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _137_156 = (term_to_string t)
in (let _137_155 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _137_156 _137_155)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _137_158 = (lbs_to_string [] lbs)
in (let _137_157 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _137_158 _137_157)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _40_313) -> begin
(let _137_160 = (term_to_string e)
in (let _137_159 = (term_to_string t)
in (FStar_Util.format2 "(%s <: %s)" _137_160 _137_159)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _40_320) -> begin
(let _137_162 = (term_to_string e)
in (let _137_161 = (comp_to_string c)
in (FStar_Util.format2 "(%s <: %s)" _137_162 _137_161)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _137_170 = (term_to_string head)
in (let _137_169 = (let _137_168 = (FStar_All.pipe_right branches (FStar_List.map (fun _40_330 -> (match (_40_330) with
| (p, wopt, e) -> begin
(let _137_167 = (FStar_All.pipe_right p pat_to_string)
in (let _137_166 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _137_164 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _137_164))
end)
in (let _137_165 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _137_167 _137_166 _137_165))))
end))))
in (FStar_Util.concat_l "\n\t|" _137_168))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _137_170 _137_169)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_Options.print_universes ()) then begin
(let _137_172 = (term_to_string t)
in (let _137_171 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _137_172 _137_171)))
end else begin
(term_to_string t)
end
end
| _40_339 -> begin
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _137_177 = (fv_to_string l)
in (let _137_176 = (let _137_175 = (FStar_List.map (fun _40_347 -> (match (_40_347) with
| (x, b) -> begin
(

let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _137_175 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _137_177 _137_176)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _40_351) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _137_179 = (bv_to_string x)
in (let _137_178 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" _137_179 _137_178)))
end else begin
(let _137_180 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _137_180))
end
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _137_182 = (bv_to_string x)
in (let _137_181 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" _137_182 _137_181)))
end else begin
(bv_to_string x)
end
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_Options.print_real_names ()) then begin
(let _137_183 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _137_183))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _137_184 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _137_184))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (

let lbs = if (FStar_Options.print_universes ()) then begin
(let _137_190 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _40_367 = (let _137_188 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _137_188))
in (match (_40_367) with
| (us, td) -> begin
(

let _40_385 = (match ((let _137_189 = (FStar_Syntax_Subst.compress td)
in _137_189.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_40_369, ((t, _40_376))::((d, _40_372))::[]) -> begin
((t), (d))
end
| _40_382 -> begin
(FStar_All.failwith "Impossibe")
end)
in (match (_40_385) with
| (t, d) -> begin
(

let _40_386 = lb
in {FStar_Syntax_Syntax.lbname = _40_386.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _40_386.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((Prims.fst lbs)), (_137_190)))
end else begin
lbs
end
in (let _137_200 = (quals_to_string' quals)
in (let _137_199 = (let _137_198 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _137_197 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _137_196 = if (FStar_Options.print_universes ()) then begin
(let _137_193 = (let _137_192 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat _137_192 ">"))
in (Prims.strcat "<" _137_193))
end else begin
""
end
in (let _137_195 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _137_194 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _137_197 _137_196 _137_195 _137_194))))))))
in (FStar_Util.concat_l "\n and " _137_198))
in (FStar_Util.format3 "%slet %s %s" _137_200 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _137_199)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> if (FStar_Options.print_effect_args ()) then begin
(let _137_202 = (lc.FStar_Syntax_Syntax.comp ())
in (comp_to_string _137_202))
end else begin
(let _137_204 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _137_203 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _137_204 _137_203)))
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
| _40_402 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (

let _40_407 = b
in (match (_40_407) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(let _137_209 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" _137_209))
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_bound_var_types ())))) then begin
(let _137_210 = (nm_to_string a)
in (imp_to_string _137_210 imp))
end else begin
(let _137_214 = (let _137_213 = (nm_to_string a)
in (let _137_212 = (let _137_211 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" _137_211))
in (Prims.strcat _137_213 _137_212)))
in (imp_to_string _137_214 imp))
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
(let _137_219 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _137_219 (FStar_String.concat sep)))
end else begin
(let _137_220 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _137_220 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _40_6 -> (match (_40_6) with
| (a, imp) -> begin
(let _137_222 = (term_to_string a)
in (imp_to_string _137_222 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args = if (FStar_Options.print_implicits ()) then begin
args
end else begin
(filter_imp args)
end
in (let _137_224 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _137_224 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _40_422) -> begin
(match ((let _137_226 = (FStar_Syntax_Subst.compress t)
in _137_226.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_40_426) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _40_429 -> begin
(let _137_227 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _137_227))
end)
end
| FStar_Syntax_Syntax.GTotal (t, _40_432) -> begin
(match ((let _137_228 = (FStar_Syntax_Subst.compress t)
in _137_228.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_40_436) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _40_439 -> begin
(let _137_229 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _137_229))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let basic = if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _40_7 -> (match (_40_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _40_445 -> begin
false
end)))) && (not ((FStar_Options.print_effect_args ())))) then begin
(let _137_231 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _137_231))
end else begin
if (((not ((FStar_Options.print_effect_args ()))) && (not ((FStar_Options.print_implicits ())))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_Options.print_effect_args ()))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _40_8 -> (match (_40_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _40_449 -> begin
false
end))))) then begin
(let _137_233 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _137_233))
end else begin
if (FStar_Options.print_effect_args ()) then begin
(let _137_237 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _137_236 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _137_235 = (let _137_234 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _137_234 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _137_237 _137_236 _137_235))))
end else begin
(let _137_239 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _137_238 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _137_239 _137_238)))
end
end
end
end
in (

let dec = (let _137_243 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _40_9 -> (match (_40_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _137_242 = (let _137_241 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _137_241))
in (_137_242)::[])
end
| _40_455 -> begin
[]
end))))
in (FStar_All.pipe_right _137_243 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> if (FStar_Options.print_universes ()) then begin
(Prims.strcat "<" (Prims.strcat s ">"))
end else begin
""
end)


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun _40_461 -> (match (_40_461) with
| (us, t) -> begin
(let _137_251 = (let _137_249 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes _137_249))
in (let _137_250 = (term_to_string t)
in (FStar_Util.format2 "%s%s" _137_251 _137_250)))
end))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (

let actions_to_string = (fun actions -> (let _137_264 = (FStar_All.pipe_right actions (FStar_List.map (fun a -> (let _137_263 = (sli a.FStar_Syntax_Syntax.action_name)
in (let _137_262 = (let _137_259 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes _137_259))
in (let _137_261 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (let _137_260 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format4 "%s%s : %s = %s" _137_263 _137_262 _137_261 _137_260))))))))
in (FStar_All.pipe_right _137_264 (FStar_String.concat ",\n\t"))))
in (let _137_302 = (let _137_301 = (let _137_300 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _137_299 = (let _137_298 = (let _137_265 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes _137_265))
in (let _137_297 = (let _137_296 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _137_295 = (let _137_294 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _137_293 = (let _137_292 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (let _137_291 = (let _137_290 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _137_289 = (let _137_288 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _137_287 = (let _137_286 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _137_285 = (let _137_284 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (let _137_283 = (let _137_282 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _137_281 = (let _137_280 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _137_279 = (let _137_278 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _137_277 = (let _137_276 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _137_275 = (let _137_274 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (let _137_273 = (let _137_272 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _137_271 = (let _137_270 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (let _137_269 = (let _137_268 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (let _137_267 = (let _137_266 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (_137_266)::[])
in (_137_268)::_137_267))
in (_137_270)::_137_269))
in (_137_272)::_137_271))
in (_137_274)::_137_273))
in (_137_276)::_137_275))
in (_137_278)::_137_277))
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
in (if for_free then begin
"_for_free "
end else begin
""
end)::_137_301)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" _137_302))))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None), _40_471) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s)), _40_478) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _40_484) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _40_492, _40_494, quals, _40_497) -> begin
(let _137_307 = (quals_to_string' quals)
in (let _137_306 = (binders_to_string " " tps)
in (let _137_305 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" _137_307 lid.FStar_Ident.str _137_306 _137_305))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _40_504, _40_506, _40_508, _40_510, _40_512) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _40_517 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_40_517) with
| (univs, t) -> begin
(let _137_309 = (univ_names_to_string univs)
in (let _137_308 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _137_309 lid.FStar_Ident.str _137_308)))
end))
end else begin
(let _137_310 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _137_310))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _40_523) -> begin
(

let _40_528 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_40_528) with
| (univs, t) -> begin
(let _137_314 = (quals_to_string' quals)
in (let _137_313 = if (FStar_Options.print_universes ()) then begin
(let _137_311 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _137_311))
end else begin
""
end
in (let _137_312 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" _137_314 lid.FStar_Ident.str _137_313 _137_312))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _40_532, _40_534) -> begin
(let _137_315 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _137_315))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _40_539, _40_541, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _40_547) -> begin
(let _137_316 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _137_316))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _40_552, _40_554, _40_556) -> begin
(let _137_317 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _137_317 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _40_561) -> begin
(eff_decl_to_string false ed)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed, _40_566) -> begin
(eff_decl_to_string true ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(

let lift_wp = (match (((se.FStar_Syntax_Syntax.lift_wp), (se.FStar_Syntax_Syntax.lift))) with
| (None, None) -> begin
(FStar_All.failwith "impossible")
end
| (Some (lift_wp), _40_579) -> begin
lift_wp
end
| (_40_582, Some (lift)) -> begin
lift
end)
in (

let _40_589 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp) (Prims.snd lift_wp))
in (match (_40_589) with
| (us, t) -> begin
(let _137_321 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _137_320 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _137_319 = (univ_names_to_string us)
in (let _137_318 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _137_321 _137_320 _137_319 _137_318)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _40_595, _40_597) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _40_602 = (let _137_322 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _137_322))
in (match (_40_602) with
| (univs, t) -> begin
(

let _40_611 = (match ((let _137_323 = (FStar_Syntax_Subst.compress t)
in _137_323.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((bs), (c))
end
| _40_608 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_40_611) with
| (tps, c) -> begin
(let _137_327 = (sli l)
in (let _137_326 = (univ_names_to_string univs)
in (let _137_325 = (binders_to_string " " tps)
in (let _137_324 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _137_327 _137_326 _137_325 _137_324)))))
end))
end))
end else begin
(let _137_330 = (sli l)
in (let _137_329 = (binders_to_string " " tps)
in (let _137_328 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _137_330 _137_329 _137_328))))
end
end))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _137_335 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _137_335 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_40_616, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = _40_623; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _40_620; FStar_Syntax_Syntax.lbdef = _40_618})::[]), _40_629, _40_631, _40_633) -> begin
(let _137_339 = (lbname_to_string lb)
in (let _137_338 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _137_339 _137_338)))
end
| _40_637 -> begin
(let _137_342 = (let _137_341 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _137_341 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _137_342 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _137_347 = (sli m.FStar_Syntax_Syntax.name)
in (let _137_346 = (let _137_345 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _137_345 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _137_347 _137_346))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _40_10 -> (match (_40_10) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(let _137_351 = (FStar_Util.string_of_int i)
in (let _137_350 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _137_351 _137_350)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _137_353 = (bv_to_string x)
in (let _137_352 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _137_353 _137_352)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _137_355 = (bv_to_string x)
in (let _137_354 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _137_355 _137_354)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _137_357 = (FStar_Util.string_of_int i)
in (let _137_356 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _137_357 _137_356)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _137_358 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _137_358))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _137_361 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _137_361 (FStar_String.concat "; "))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in (

let _40_675 = (match (ascription) with
| None -> begin
(FStar_Util.string_builder_append strb "None")
end
| Some (FStar_Util.Inl (lc)) -> begin
(

let _40_668 = (FStar_Util.string_builder_append strb "Some Inr ")
in (FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name)))
end
| Some (FStar_Util.Inr (lid)) -> begin
(

let _40_673 = (FStar_Util.string_builder_append strb "Some Inr ")
in (FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lid)))
end)
in (FStar_Util.string_of_string_builder strb))))




