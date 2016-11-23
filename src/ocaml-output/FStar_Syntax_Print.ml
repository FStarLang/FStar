
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
| _39_23 -> begin
false
end))


let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| _39_28 -> begin
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
| FStar_Util.Inl (_39_38) -> begin
false
end
| FStar_Util.Inr (_39_41) -> begin
true
end))


let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _39_2 -> (match (_39_2) with
| (_39_46, Some (FStar_Syntax_Syntax.Implicit (_39_48))) -> begin
false
end
| _39_53 -> begin
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
| _39_65 -> begin
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
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(let _134_96 = (let _134_95 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _134_95 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordType %s)" _134_96))
end
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
(let _134_98 = (let _134_97 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _134_97 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordConstructor %s)" _134_98))
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
(let _134_101 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _134_101 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| _39_216 -> begin
(let _134_104 = (quals_to_string quals)
in (Prims.strcat _134_104 " "))
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

let pats = (let _134_129 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _134_128 = (FStar_All.pipe_right args (FStar_List.map (fun _39_236 -> (match (_39_236) with
| (t, _39_235) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _134_128 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _134_129 (FStar_String.concat "\\/")))
in (let _134_130 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _134_130)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _134_134 = (tag_of_term t)
in (let _134_133 = (sli m)
in (let _134_132 = (term_to_string t')
in (let _134_131 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" _134_134 _134_133 _134_132 _134_131)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(let _134_139 = (tag_of_term t)
in (let _134_138 = (term_to_string t')
in (let _134_137 = (sli m0)
in (let _134_136 = (sli m1)
in (let _134_135 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" _134_139 _134_138 _134_137 _134_136 _134_135))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(let _134_141 = (FStar_Range.string_of_range r)
in (let _134_140 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l _134_141 _134_140)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _39_263) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, _39_274) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_Options.print_universes ()) then begin
(let _134_142 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _134_142))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _134_144 = (binders_to_string " -> " bs)
in (let _134_143 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _134_144 _134_143)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
(let _134_148 = (binders_to_string " " bs)
in (let _134_147 = (term_to_string t2)
in (let _134_146 = (let _134_145 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _134_145))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _134_148 _134_147 _134_146))))
end
| Some (FStar_Util.Inr (l)) when (FStar_Options.print_implicits ()) -> begin
(let _134_150 = (binders_to_string " " bs)
in (let _134_149 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))" _134_150 _134_149 l.FStar_Ident.str)))
end
| _39_297 -> begin
(let _134_152 = (binders_to_string " " bs)
in (let _134_151 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _134_152 _134_151)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _134_155 = (bv_to_string xt)
in (let _134_154 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _134_153 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _134_155 _134_154 _134_153))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _134_157 = (term_to_string t)
in (let _134_156 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _134_157 _134_156)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _134_159 = (lbs_to_string [] lbs)
in (let _134_158 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _134_159 _134_158)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _39_314) -> begin
(let _134_161 = (term_to_string e)
in (let _134_160 = (term_to_string t)
in (FStar_Util.format2 "(%s <: %s)" _134_161 _134_160)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _39_321) -> begin
(let _134_163 = (term_to_string e)
in (let _134_162 = (comp_to_string c)
in (FStar_Util.format2 "(%s <: %s)" _134_163 _134_162)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _134_171 = (term_to_string head)
in (let _134_170 = (let _134_169 = (FStar_All.pipe_right branches (FStar_List.map (fun _39_331 -> (match (_39_331) with
| (p, wopt, e) -> begin
(let _134_168 = (FStar_All.pipe_right p pat_to_string)
in (let _134_167 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _134_165 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _134_165))
end)
in (let _134_166 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _134_168 _134_167 _134_166))))
end))))
in (FStar_Util.concat_l "\n\t|" _134_169))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _134_171 _134_170)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_Options.print_universes ()) then begin
(let _134_173 = (term_to_string t)
in (let _134_172 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _134_173 _134_172)))
end else begin
(term_to_string t)
end
end
| _39_340 -> begin
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _134_178 = (fv_to_string l)
in (let _134_177 = (let _134_176 = (FStar_List.map (fun _39_348 -> (match (_39_348) with
| (x, b) -> begin
(

let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _134_176 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _134_178 _134_177)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _39_352) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _134_180 = (bv_to_string x)
in (let _134_179 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" _134_180 _134_179)))
end else begin
(let _134_181 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _134_181))
end
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _134_183 = (bv_to_string x)
in (let _134_182 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" _134_183 _134_182)))
end else begin
(bv_to_string x)
end
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_Options.print_real_names ()) then begin
(let _134_184 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _134_184))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _134_185 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _134_185))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (

let lbs = if (FStar_Options.print_universes ()) then begin
(let _134_191 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _39_368 = (let _134_189 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _134_189))
in (match (_39_368) with
| (us, td) -> begin
(

let _39_386 = (match ((let _134_190 = (FStar_Syntax_Subst.compress td)
in _134_190.FStar_Syntax_Syntax.n)) with
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
in (((Prims.fst lbs)), (_134_191)))
end else begin
lbs
end
in (let _134_201 = (quals_to_string' quals)
in (let _134_200 = (let _134_199 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _134_198 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _134_197 = if (FStar_Options.print_universes ()) then begin
(let _134_194 = (let _134_193 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat _134_193 ">"))
in (Prims.strcat "<" _134_194))
end else begin
""
end
in (let _134_196 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _134_195 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _134_198 _134_197 _134_196 _134_195))))))))
in (FStar_Util.concat_l "\n and " _134_199))
in (FStar_Util.format3 "%slet %s %s" _134_201 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _134_200)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> if (FStar_Options.print_effect_args ()) then begin
(let _134_203 = (lc.FStar_Syntax_Syntax.comp ())
in (comp_to_string _134_203))
end else begin
(let _134_205 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _134_204 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _134_205 _134_204)))
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
| _39_403 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (

let _39_408 = b
in (match (_39_408) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(let _134_210 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" _134_210))
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_bound_var_types ())))) then begin
(let _134_211 = (nm_to_string a)
in (imp_to_string _134_211 imp))
end else begin
(let _134_215 = (let _134_214 = (nm_to_string a)
in (let _134_213 = (let _134_212 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" _134_212))
in (Prims.strcat _134_214 _134_213)))
in (imp_to_string _134_215 imp))
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
(let _134_220 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _134_220 (FStar_String.concat sep)))
end else begin
(let _134_221 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _134_221 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _39_6 -> (match (_39_6) with
| (a, imp) -> begin
(let _134_223 = (term_to_string a)
in (imp_to_string _134_223 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args = if (FStar_Options.print_implicits ()) then begin
args
end else begin
(filter_imp args)
end
in (let _134_225 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _134_225 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _39_423) -> begin
(match ((let _134_227 = (FStar_Syntax_Subst.compress t)
in _134_227.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_427) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_430 -> begin
(let _134_228 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _134_228))
end)
end
| FStar_Syntax_Syntax.GTotal (t, _39_433) -> begin
(match ((let _134_229 = (FStar_Syntax_Subst.compress t)
in _134_229.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_437) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_440 -> begin
(let _134_230 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _134_230))
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
(let _134_232 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _134_232))
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
(let _134_234 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _134_234))
end else begin
if (FStar_Options.print_effect_args ()) then begin
(let _134_238 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _134_237 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _134_236 = (let _134_235 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _134_235 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _134_238 _134_237 _134_236))))
end else begin
(let _134_240 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _134_239 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _134_240 _134_239)))
end
end
end
end
in (

let dec = (let _134_244 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _39_9 -> (match (_39_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _134_243 = (let _134_242 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _134_242))
in (_134_243)::[])
end
| _39_456 -> begin
[]
end))))
in (FStar_All.pipe_right _134_244 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> if (FStar_Options.print_universes ()) then begin
(Prims.strcat "<" (Prims.strcat s ">"))
end else begin
""
end)


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun _39_462 -> (match (_39_462) with
| (us, t) -> begin
(let _134_252 = (let _134_250 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes _134_250))
in (let _134_251 = (term_to_string t)
in (FStar_Util.format2 "%s%s" _134_252 _134_251)))
end))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (

let actions_to_string = (fun actions -> (let _134_265 = (FStar_All.pipe_right actions (FStar_List.map (fun a -> (let _134_264 = (sli a.FStar_Syntax_Syntax.action_name)
in (let _134_263 = (let _134_260 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes _134_260))
in (let _134_262 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (let _134_261 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format4 "%s%s : %s = %s" _134_264 _134_263 _134_262 _134_261))))))))
in (FStar_All.pipe_right _134_265 (FStar_String.concat ",\n\t"))))
in (let _134_303 = (let _134_302 = (let _134_301 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _134_300 = (let _134_299 = (let _134_266 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes _134_266))
in (let _134_298 = (let _134_297 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _134_296 = (let _134_295 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _134_294 = (let _134_293 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (let _134_292 = (let _134_291 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _134_290 = (let _134_289 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _134_288 = (let _134_287 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _134_286 = (let _134_285 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (let _134_284 = (let _134_283 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _134_282 = (let _134_281 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _134_280 = (let _134_279 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _134_278 = (let _134_277 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _134_276 = (let _134_275 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (let _134_274 = (let _134_273 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _134_272 = (let _134_271 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (let _134_270 = (let _134_269 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (let _134_268 = (let _134_267 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (_134_267)::[])
in (_134_269)::_134_268))
in (_134_271)::_134_270))
in (_134_273)::_134_272))
in (_134_275)::_134_274))
in (_134_277)::_134_276))
in (_134_279)::_134_278))
in (_134_281)::_134_280))
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
in (if for_free then begin
"_for_free "
end else begin
""
end)::_134_302)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" _134_303))))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None), _39_472) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s)), _39_479) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _39_485) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _39_493, _39_495, quals, _39_498) -> begin
(let _134_308 = (quals_to_string' quals)
in (let _134_307 = (binders_to_string " " tps)
in (let _134_306 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" _134_308 lid.FStar_Ident.str _134_307 _134_306))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _39_505, _39_507, _39_509, _39_511, _39_513) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_518 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_518) with
| (univs, t) -> begin
(let _134_310 = (univ_names_to_string univs)
in (let _134_309 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _134_310 lid.FStar_Ident.str _134_309)))
end))
end else begin
(let _134_311 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _134_311))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _39_524) -> begin
(

let _39_529 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_529) with
| (univs, t) -> begin
(let _134_315 = (quals_to_string' quals)
in (let _134_314 = if (FStar_Options.print_universes ()) then begin
(let _134_312 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _134_312))
end else begin
""
end
in (let _134_313 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" _134_315 lid.FStar_Ident.str _134_314 _134_313))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _39_533, _39_535) -> begin
(let _134_316 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _134_316))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _39_540, _39_542, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _39_548) -> begin
(let _134_317 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _134_317))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _39_553, _39_555, _39_557) -> begin
(let _134_318 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _134_318 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _39_562) -> begin
(eff_decl_to_string false ed)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed, _39_567) -> begin
(eff_decl_to_string true ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(

let lift_wp = (match (((se.FStar_Syntax_Syntax.lift_wp), (se.FStar_Syntax_Syntax.lift))) with
| (None, None) -> begin
(FStar_All.failwith "impossible")
end
| (Some (lift_wp), _39_580) -> begin
lift_wp
end
| (_39_583, Some (lift)) -> begin
lift
end)
in (

let _39_590 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp) (Prims.snd lift_wp))
in (match (_39_590) with
| (us, t) -> begin
(let _134_322 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _134_321 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _134_320 = (univ_names_to_string us)
in (let _134_319 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _134_322 _134_321 _134_320 _134_319)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _39_596, _39_598) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_603 = (let _134_323 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _134_323))
in (match (_39_603) with
| (univs, t) -> begin
(

let _39_612 = (match ((let _134_324 = (FStar_Syntax_Subst.compress t)
in _134_324.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((bs), (c))
end
| _39_609 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_39_612) with
| (tps, c) -> begin
(let _134_328 = (sli l)
in (let _134_327 = (univ_names_to_string univs)
in (let _134_326 = (binders_to_string " " tps)
in (let _134_325 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _134_328 _134_327 _134_326 _134_325)))))
end))
end))
end else begin
(let _134_331 = (sli l)
in (let _134_330 = (binders_to_string " " tps)
in (let _134_329 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _134_331 _134_330 _134_329))))
end
end))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _134_336 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _134_336 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_39_617, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = _39_624; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_621; FStar_Syntax_Syntax.lbdef = _39_619})::[]), _39_630, _39_632, _39_634) -> begin
(let _134_340 = (lbname_to_string lb)
in (let _134_339 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _134_340 _134_339)))
end
| _39_638 -> begin
(let _134_343 = (let _134_342 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _134_342 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _134_343 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _134_348 = (sli m.FStar_Syntax_Syntax.name)
in (let _134_347 = (let _134_346 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _134_346 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _134_348 _134_347))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _39_10 -> (match (_39_10) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(let _134_352 = (FStar_Util.string_of_int i)
in (let _134_351 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _134_352 _134_351)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _134_354 = (bv_to_string x)
in (let _134_353 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _134_354 _134_353)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _134_356 = (bv_to_string x)
in (let _134_355 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _134_356 _134_355)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _134_358 = (FStar_Util.string_of_int i)
in (let _134_357 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _134_358 _134_357)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _134_359 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _134_359))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _134_362 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _134_362 (FStar_String.concat "; "))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in (

let _39_676 = (match (ascription) with
| None -> begin
(FStar_Util.string_builder_append strb "None")
end
| Some (FStar_Util.Inl (lc)) -> begin
(

let _39_669 = (FStar_Util.string_builder_append strb "Some Inr ")
in (FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name)))
end
| Some (FStar_Util.Inr (lid)) -> begin
(

let _39_674 = (FStar_Util.string_builder_append strb "Some Inr ")
in (FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lid)))
end)
in (FStar_Util.string_of_string_builder strb))))




