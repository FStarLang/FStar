
open Prims

let sli : FStar_Ident.lident  ->  Prims.string = (fun l -> (

let s = if (FStar_Options.print_real_names ()) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end
in (let _133_4 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid l))
in (let _133_3 = (FStar_Range.string_of_use_range (FStar_Ident.range_of_lid l))
in (FStar_Util.format3 "%s@{def=%s;use=%s}" s _133_4 _133_3)))))


let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> (sli l))


let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _133_12 = (let _133_11 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "#" _133_11))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _133_12)))


let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> if (FStar_Options.print_real_names ()) then begin
(bv_to_string bv)
end else begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)


let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _133_18 = (let _133_17 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "@" _133_17))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _133_18)))


let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Syntax_Const.op_Addition), ("+")))::(((FStar_Syntax_Const.op_Subtraction), ("-")))::(((FStar_Syntax_Const.op_Multiply), ("*")))::(((FStar_Syntax_Const.op_Division), ("/")))::(((FStar_Syntax_Const.op_Eq), ("=")))::(((FStar_Syntax_Const.op_ColonEq), (":=")))::(((FStar_Syntax_Const.op_notEq), ("<>")))::(((FStar_Syntax_Const.op_And), ("&&")))::(((FStar_Syntax_Const.op_Or), ("||")))::(((FStar_Syntax_Const.op_LTE), ("<=")))::(((FStar_Syntax_Const.op_GTE), (">=")))::(((FStar_Syntax_Const.op_LT), ("<")))::(((FStar_Syntax_Const.op_GT), (">")))::(((FStar_Syntax_Const.op_Modulus), ("mod")))::(((FStar_Syntax_Const.and_lid), ("/\\")))::(((FStar_Syntax_Const.or_lid), ("\\/")))::(((FStar_Syntax_Const.imp_lid), ("==>")))::(((FStar_Syntax_Const.iff_lid), ("<==>")))::(((FStar_Syntax_Const.precedes_lid), ("<<")))::(((FStar_Syntax_Const.eq2_lid), ("==")))::(((FStar_Syntax_Const.eq3_lid), ("===")))::[]


let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Syntax_Const.op_Negation), ("not")))::(((FStar_Syntax_Const.op_Minus), ("-")))::(((FStar_Syntax_Const.not_lid), ("~")))::[]


let is_prim_op = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
end
| _39_24 -> begin
false
end))


let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| _39_29 -> begin
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
| FStar_Util.Inl (_39_39) -> begin
false
end
| FStar_Util.Inr (_39_42) -> begin
true
end))


let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _39_2 -> (match (_39_2) with
| (_39_47, Some (FStar_Syntax_Syntax.Implicit (_39_49))) -> begin
false
end
| _39_54 -> begin
true
end)))))


let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _133_41 = (FStar_Syntax_Subst.compress e)
in _133_41.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args = (filter_imp args)
in (

let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = (Prims.parse_int "2"))) then begin
(match ((let _133_42 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex _133_42))) with
| Some (xs) -> begin
(let _133_44 = (let _133_43 = (FStar_List.nth exps (Prims.parse_int "0"))
in (_133_43)::xs)
in Some (_133_44))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _39_66 -> begin
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


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _133_58 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _133_58)))


let infix_prim_op_to_string = (fun e -> (let _133_60 = (get_lid e)
in (find_lid _133_60 infix_prim_ops)))


let unary_prim_op_to_string = (fun e -> (let _133_62 = (get_lid e)
in (find_lid _133_62 unary_prim_ops)))


let quant_to_string = (fun t -> (let _133_64 = (get_lid t)
in (find_lid _133_64 quants)))


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
| FStar_Const.Const_string (bytes, _39_89) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_39_93) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x, _39_97) -> begin
x
end
| FStar_Const.Const_char (c) -> begin
(FStar_Util.string_of_char c)
end
| FStar_Const.Const_range (r) -> begin
(FStar_Range.string_of_range r)
end
| FStar_Const.Const_reify -> begin
"reify"
end
| FStar_Const.Const_reflect (l) -> begin
(let _133_67 = (sli l)
in (FStar_Util.format1 "[[%s.reflect]]" _133_67))
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
(let _133_72 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _133_72))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _133_73 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _133_73))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _133_74 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _133_74))
end
| FStar_Syntax_Syntax.Tm_uinst (_39_120) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (_39_123) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (_39_126) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (_39_129) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (_39_132) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (_39_135) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (_39_138) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (_39_141) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (_39_144) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (_39_147) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (_39_150) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (_39_153, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
"Tm_delayed"
end
| Some (_39_159) -> begin
"Tm_delayed-resolved"
end)
end
| FStar_Syntax_Syntax.Tm_meta (_39_162) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))


let uvar_to_string = (fun u -> if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _133_79 = (let _133_78 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _133_78 FStar_Util.string_of_int))
in (Prims.strcat "?" _133_79))
end)


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_unif (u) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(Prims.strcat "n" x.FStar_Ident.idText)
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(let _133_82 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _133_82))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _133_83 = (univ_to_string u)
in (FStar_Util.format1 "(S %s)" _133_83))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _133_85 = (let _133_84 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _133_84 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _133_85))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _133_88 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _133_88 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _133_92 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _133_92 (FStar_String.concat ", "))))


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
(let _133_95 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _133_95))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _133_96 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _133_96 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(let _133_98 = (let _133_97 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _133_97 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordType %s)" _133_98))
end
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
(let _133_100 = (let _133_99 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _133_99 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordConstructor %s)" _133_100))
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
(let _133_103 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _133_103 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| _39_216 -> begin
(let _133_106 = (quals_to_string quals)
in (Prims.strcat _133_106 " "))
end))


let rec term_to_string' : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

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

let pats = (let _133_132 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _133_131 = (FStar_All.pipe_right args (FStar_List.map (fun _39_236 -> (match (_39_236) with
| (t, _39_235) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _133_131 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _133_132 (FStar_String.concat "\\/")))
in (let _133_133 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _133_133)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _133_137 = (tag_of_term t)
in (let _133_136 = (sli m)
in (let _133_135 = (term_to_string t')
in (let _133_134 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s )" _133_137 _133_136 _133_135 _133_134)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1)) -> begin
(let _133_141 = (tag_of_term t)
in (let _133_140 = (term_to_string t)
in (let _133_139 = (sli m0)
in (let _133_138 = (sli m1)
in (FStar_Util.format4 "(MonadicLift-%s{%s} %s -> %s)" _133_141 _133_140 _133_139 _133_138)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(let _133_143 = (FStar_Range.string_of_range r)
in (let _133_142 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l _133_143 _133_142)))
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
(let _133_145 = (uvar_to_string u)
in (let _133_144 = (FStar_Range.string_of_use_range x.FStar_Syntax_Syntax.pos)
in (Prims.strcat _133_145 _133_144)))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_Options.print_universes ()) then begin
(let _133_146 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _133_146))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _133_148 = (binders_to_string " -> " bs)
in (let _133_147 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _133_148 _133_147)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
(let _133_152 = (binders_to_string " " bs)
in (let _133_151 = (term_to_string t2)
in (let _133_150 = (let _133_149 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _133_149))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _133_152 _133_151 _133_150))))
end
| Some (FStar_Util.Inr (l)) when (FStar_Options.print_implicits ()) -> begin
(let _133_154 = (binders_to_string " " bs)
in (let _133_153 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))" _133_154 _133_153 l.FStar_Ident.str)))
end
| _39_296 -> begin
(let _133_156 = (binders_to_string " " bs)
in (let _133_155 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _133_156 _133_155)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _133_159 = (bv_to_string xt)
in (let _133_158 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _133_157 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _133_159 _133_158 _133_157))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _133_161 = (term_to_string t)
in (let _133_160 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _133_161 _133_160)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _133_163 = (lbs_to_string [] lbs)
in (let _133_162 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _133_163 _133_162)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _39_313) -> begin
(let _133_165 = (term_to_string e)
in (let _133_164 = (term_to_string t)
in (FStar_Util.format2 "(%s : %s)" _133_165 _133_164)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _39_320) -> begin
(let _133_167 = (term_to_string e)
in (let _133_166 = (comp_to_string c)
in (FStar_Util.format2 "(%s : %s)" _133_167 _133_166)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _133_175 = (term_to_string head)
in (let _133_174 = (let _133_173 = (FStar_All.pipe_right branches (FStar_List.map (fun _39_330 -> (match (_39_330) with
| (p, wopt, e) -> begin
(let _133_172 = (FStar_All.pipe_right p pat_to_string)
in (let _133_171 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _133_169 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _133_169))
end)
in (let _133_170 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _133_172 _133_171 _133_170))))
end))))
in (FStar_Util.concat_l "\n\t|" _133_173))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _133_175 _133_174)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_Options.print_universes ()) then begin
(let _133_177 = (term_to_string t)
in (let _133_176 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _133_177 _133_176)))
end else begin
(term_to_string t)
end
end
| _39_339 -> begin
(tag_of_term x)
end)))
and term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (term_to_string' t))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _133_183 = (fv_to_string l)
in (let _133_182 = (let _133_181 = (FStar_List.map (fun _39_348 -> (match (_39_348) with
| (x, b) -> begin
(

let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _133_181 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _133_183 _133_182)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _39_352) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _133_185 = (bv_to_string x)
in (let _133_184 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" _133_185 _133_184)))
end else begin
(let _133_186 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _133_186))
end
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _133_188 = (bv_to_string x)
in (let _133_187 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" _133_188 _133_187)))
end else begin
(bv_to_string x)
end
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_Options.print_real_names ()) then begin
(let _133_189 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _133_189))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _133_190 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _133_190))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (

let lbs = if (FStar_Options.print_universes ()) then begin
(let _133_196 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _39_368 = (let _133_194 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _133_194))
in (match (_39_368) with
| (us, td) -> begin
(

let _39_386 = (match ((let _133_195 = (FStar_Syntax_Subst.compress td)
in _133_195.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_39_370, ((t, _39_377))::((d, _39_373))::[]) -> begin
((t), (d))
end
| _39_383 -> begin
(FStar_All.failwith "Impossibe")
end)
in (match (_39_386) with
| (t, d) -> begin
(

let _39_387 = lb
in {FStar_Syntax_Syntax.lbname = _39_387.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_387.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((Prims.fst lbs)), (_133_196)))
end else begin
lbs
end
in (let _133_206 = (quals_to_string' quals)
in (let _133_205 = (let _133_204 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _133_203 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _133_202 = if (FStar_Options.print_universes ()) then begin
(let _133_199 = (let _133_198 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat _133_198 ">"))
in (Prims.strcat "<" _133_199))
end else begin
""
end
in (let _133_201 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _133_200 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _133_203 _133_202 _133_201 _133_200))))))))
in (FStar_Util.concat_l "\n and " _133_204))
in (FStar_Util.format3 "%slet %s %s" _133_206 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _133_205)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _133_209 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _133_208 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _133_209 _133_208))))
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
| _39_403 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (

let _39_408 = b
in (match (_39_408) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(let _133_214 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" _133_214))
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_bound_var_types ())))) then begin
(let _133_215 = (nm_to_string a)
in (imp_to_string _133_215 imp))
end else begin
(let _133_219 = (let _133_218 = (nm_to_string a)
in (let _133_217 = (let _133_216 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" _133_216))
in (Prims.strcat _133_218 _133_217)))
in (imp_to_string _133_219 imp))
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
(let _133_224 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _133_224 (FStar_String.concat sep)))
end else begin
(let _133_225 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _133_225 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _39_6 -> (match (_39_6) with
| (a, imp) -> begin
(let _133_227 = (term_to_string a)
in (imp_to_string _133_227 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args = if (FStar_Options.print_implicits ()) then begin
args
end else begin
(filter_imp args)
end
in (let _133_229 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _133_229 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _39_423) -> begin
(match ((let _133_231 = (FStar_Syntax_Subst.compress t)
in _133_231.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_427) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_430 -> begin
(let _133_232 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _133_232))
end)
end
| FStar_Syntax_Syntax.GTotal (t, _39_433) -> begin
(match ((let _133_233 = (FStar_Syntax_Subst.compress t)
in _133_233.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_437) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_440 -> begin
(let _133_234 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _133_234))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let basic = if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_7 -> (match (_39_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _39_446 -> begin
false
end)))) && (not ((FStar_Options.print_effect_args ())))) then begin
(let _133_236 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _133_236))
end else begin
if (((not ((FStar_Options.print_effect_args ()))) && (not ((FStar_Options.print_implicits ())))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_Options.print_effect_args ()))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_8 -> (match (_39_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _39_450 -> begin
false
end))))) then begin
(let _133_238 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _133_238))
end else begin
if (FStar_Options.print_effect_args ()) then begin
(let _133_242 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _133_241 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _133_240 = (let _133_239 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _133_239 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _133_242 _133_241 _133_240))))
end else begin
(let _133_244 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _133_243 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _133_244 _133_243)))
end
end
end
end
in (

let dec = (let _133_248 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _39_9 -> (match (_39_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _133_247 = (let _133_246 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _133_246))
in (_133_247)::[])
end
| _39_456 -> begin
[]
end))))
in (FStar_All.pipe_right _133_248 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun _39_461 -> (match (_39_461) with
| (us, t) -> begin
(let _133_253 = (univ_names_to_string us)
in (let _133_252 = (term_to_string t)
in (FStar_Util.format2 "<%s> %s" _133_253 _133_252)))
end))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (

let actions_to_string = (fun actions -> (let _133_265 = (FStar_All.pipe_right actions (FStar_List.map (fun a -> (let _133_264 = (sli a.FStar_Syntax_Syntax.action_name)
in (let _133_263 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (let _133_262 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (let _133_261 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format4 "%s<%s> : %s = %s" _133_264 _133_263 _133_262 _133_261))))))))
in (FStar_All.pipe_right _133_265 (FStar_String.concat ",\n\t"))))
in (let _133_302 = (let _133_301 = (let _133_300 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _133_299 = (let _133_298 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (let _133_297 = (let _133_296 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _133_295 = (let _133_294 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _133_293 = (let _133_292 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (let _133_291 = (let _133_290 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _133_289 = (let _133_288 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _133_287 = (let _133_286 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _133_285 = (let _133_284 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (let _133_283 = (let _133_282 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _133_281 = (let _133_280 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _133_279 = (let _133_278 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _133_277 = (let _133_276 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _133_275 = (let _133_274 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (let _133_273 = (let _133_272 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _133_271 = (let _133_270 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (let _133_269 = (let _133_268 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (let _133_267 = (let _133_266 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (_133_266)::[])
in (_133_268)::_133_267))
in (_133_270)::_133_269))
in (_133_272)::_133_271))
in (_133_274)::_133_273))
in (_133_276)::_133_275))
in (_133_278)::_133_277))
in (_133_280)::_133_279))
in (_133_282)::_133_281))
in (_133_284)::_133_283))
in (_133_286)::_133_285))
in (_133_288)::_133_287))
in (_133_290)::_133_289))
in (_133_292)::_133_291))
in (_133_294)::_133_293))
in (_133_296)::_133_295))
in (_133_298)::_133_297))
in (_133_300)::_133_299))
in (if for_free then begin
"for free "
end else begin
""
end)::_133_301)
in (FStar_Util.format "new_effect %s{ %s<%s> %s : %s \n  ret         = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\n; actions     = \n\t%s\n}\n" _133_302))))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None), _39_471) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s)), _39_478) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _39_484) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _39_492, _39_494, quals, _39_497) -> begin
(let _133_307 = (quals_to_string' quals)
in (let _133_306 = (binders_to_string " " tps)
in (let _133_305 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" _133_307 lid.FStar_Ident.str _133_306 _133_305))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _39_504, _39_506, _39_508, _39_510, _39_512) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_517 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_517) with
| (univs, t) -> begin
(let _133_309 = (univ_names_to_string univs)
in (let _133_308 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _133_309 lid.FStar_Ident.str _133_308)))
end))
end else begin
(let _133_310 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _133_310))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _39_523) -> begin
(

let _39_528 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_528) with
| (univs, t) -> begin
(let _133_314 = (quals_to_string' quals)
in (let _133_313 = if (FStar_Options.print_universes ()) then begin
(let _133_311 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _133_311))
end else begin
""
end
in (let _133_312 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" _133_314 lid.FStar_Ident.str _133_313 _133_312))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _39_532, _39_534) -> begin
(let _133_315 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _133_315))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _39_539, _39_541, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _39_547) -> begin
(let _133_316 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _133_316))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _39_552, _39_554, _39_556) -> begin
(let _133_317 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _133_317 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _39_561) -> begin
(eff_decl_to_string false ed)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed, _39_566) -> begin
(eff_decl_to_string true ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(

let _39_575 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst se.FStar_Syntax_Syntax.lift_wp) (Prims.snd se.FStar_Syntax_Syntax.lift_wp))
in (match (_39_575) with
| (us, t) -> begin
(let _133_321 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _133_320 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _133_319 = (univ_names_to_string us)
in (let _133_318 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _133_321 _133_320 _133_319 _133_318)))))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _39_581, _39_583) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_588 = (let _133_322 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _133_322))
in (match (_39_588) with
| (univs, t) -> begin
(

let _39_597 = (match ((let _133_323 = (FStar_Syntax_Subst.compress t)
in _133_323.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((bs), (c))
end
| _39_594 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_39_597) with
| (tps, c) -> begin
(let _133_327 = (sli l)
in (let _133_326 = (univ_names_to_string univs)
in (let _133_325 = (binders_to_string " " tps)
in (let _133_324 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _133_327 _133_326 _133_325 _133_324)))))
end))
end))
end else begin
(let _133_330 = (sli l)
in (let _133_329 = (binders_to_string " " tps)
in (let _133_328 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _133_330 _133_329 _133_328))))
end
end))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _133_335 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _133_335 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_39_602, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = _39_609; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_606; FStar_Syntax_Syntax.lbdef = _39_604})::[]), _39_615, _39_617, _39_619) -> begin
(let _133_339 = (lbname_to_string lb)
in (let _133_338 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _133_339 _133_338)))
end
| _39_623 -> begin
(let _133_342 = (let _133_341 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _133_341 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _133_342 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _133_347 = (sli m.FStar_Syntax_Syntax.name)
in (let _133_346 = (let _133_345 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _133_345 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _133_347 _133_346))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _39_10 -> (match (_39_10) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(let _133_351 = (FStar_Util.string_of_int i)
in (let _133_350 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _133_351 _133_350)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _133_353 = (bv_to_string x)
in (let _133_352 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _133_353 _133_352)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _133_355 = (bv_to_string x)
in (let _133_354 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _133_355 _133_354)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _133_357 = (FStar_Util.string_of_int i)
in (let _133_356 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _133_357 _133_356)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _133_358 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _133_358))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _133_361 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _133_361 (FStar_String.concat "; "))))




