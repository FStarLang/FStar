
open Prims

let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> l.FStar_Ident.str)


let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _129_7 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "#") _129_7)))


let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> if (FStar_Options.print_real_names ()) then begin
(bv_to_string bv)
end else begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)


<<<<<<< HEAD
let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _128_12 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "!") _128_12)))
=======
let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _129_12 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "@") _129_12)))
>>>>>>> master


let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.op_Addition, "+"))::((FStar_Syntax_Const.op_Subtraction, "-"))::((FStar_Syntax_Const.op_Multiply, "*"))::((FStar_Syntax_Const.op_Division, "/"))::((FStar_Syntax_Const.op_Eq, "="))::((FStar_Syntax_Const.op_ColonEq, ":="))::((FStar_Syntax_Const.op_notEq, "<>"))::((FStar_Syntax_Const.op_And, "&&"))::((FStar_Syntax_Const.op_Or, "||"))::((FStar_Syntax_Const.op_LTE, "<="))::((FStar_Syntax_Const.op_GTE, ">="))::((FStar_Syntax_Const.op_LT, "<"))::((FStar_Syntax_Const.op_GT, ">"))::((FStar_Syntax_Const.op_Modulus, "mod"))::((FStar_Syntax_Const.and_lid, "/\\"))::((FStar_Syntax_Const.or_lid, "\\/"))::((FStar_Syntax_Const.imp_lid, "==>"))::((FStar_Syntax_Const.iff_lid, "<==>"))::((FStar_Syntax_Const.precedes_lid, "<<"))::((FStar_Syntax_Const.eq2_lid, "=="))::[]


let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.op_Negation, "not"))::((FStar_Syntax_Const.op_Minus, "-"))::((FStar_Syntax_Const.not_lid, "~"))::[]


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


let quants : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.forall_lid, "forall"))::((FStar_Syntax_Const.exists_lid, "exists"))::[]


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


let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _129_35 = (FStar_Syntax_Subst.compress e)
in _129_35.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args = (filter_imp args)
in (

let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = 2)) then begin
(match ((let _129_36 = (FStar_List.nth exps 1)
in (reconstruct_lex _129_36))) with
| Some (xs) -> begin
(let _129_38 = (let _129_37 = (FStar_List.nth exps 0)
in (_129_37)::xs)
in Some (_129_38))
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


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _129_52 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _129_52)))


let infix_prim_op_to_string = (fun e -> (let _129_54 = (get_lid e)
in (find_lid _129_54 infix_prim_ops)))


let unary_prim_op_to_string = (fun e -> (let _129_56 = (get_lid e)
in (find_lid _129_56 unary_prim_ops)))


let quant_to_string = (fun t -> (let _129_58 = (get_lid t)
in (find_lid _129_58 quants)))


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
(FStar_Util.string_of_char c)
end
| FStar_Const.Const_range (r) -> begin
(FStar_Range.string_of_range r)
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
(let _129_67 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _129_67))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _129_68 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _129_68))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _129_69 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _129_69))
end
| FStar_Syntax_Syntax.Tm_uinst (_39_116) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (_39_119) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (_39_122) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (_39_125) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (_39_128) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (_39_131) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (_39_134) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (_39_137) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (_39_140) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (_39_143) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (_39_146) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (_39_149, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
"Tm_delayed"
end
| Some (_39_155) -> begin
"Tm_delayed-resolved"
end)
end
| FStar_Syntax_Syntax.Tm_meta (_39_158) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))


let uvar_to_string = (fun u -> if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _129_74 = (let _129_73 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _129_73 FStar_Util.string_of_int))
in (Prims.strcat "?" _129_74))
end)


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_unif (u) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(FStar_Util.format1 "U_name<%s>" x.FStar_Ident.idText)
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(let _129_77 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _129_77))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _129_78 = (univ_to_string u)
in (FStar_Util.format1 "(S %s)" _129_78))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _129_80 = (let _129_79 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _129_79 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _129_80))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _129_83 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _129_83 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _129_87 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _129_87 (FStar_String.concat ", "))))


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
| FStar_Syntax_Syntax.Logic -> begin
"logic"
end
| FStar_Syntax_Syntax.TotalEffect -> begin
"total"
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(let _129_90 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _129_90))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _129_91 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _129_91 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(let _129_93 = (let _129_92 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _129_92 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordType %s)" _129_93))
end
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
(let _129_95 = (let _129_94 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _129_94 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordConstructor %s)" _129_95))
end
| FStar_Syntax_Syntax.ExceptionConstructor -> begin
"ExceptionConstructor"
end
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
"HasMaskedEffect"
end
| FStar_Syntax_Syntax.Effect -> begin
"Effect"
end))


let quals_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
<<<<<<< HEAD
| _39_205 -> begin
(let _128_99 = (let _128_98 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _128_98 (FStar_String.concat " ")))
in (Prims.strcat _128_99 " "))
=======
| _39_204 -> begin
(let _129_99 = (let _129_98 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _129_98 (FStar_String.concat " ")))
in (Prims.strcat _129_99 " "))
>>>>>>> master
end))


let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let x = (FStar_Syntax_Subst.compress x)
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_39_209) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_39_212, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

<<<<<<< HEAD
let pats = (let _128_124 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _128_123 = (FStar_All.pipe_right args (FStar_List.map (fun _39_225 -> (match (_39_225) with
| (t, _39_224) -> begin
=======
let pats = (let _129_124 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _129_123 = (FStar_All.pipe_right args (FStar_List.map (fun _39_224 -> (match (_39_224) with
| (t, _39_223) -> begin
>>>>>>> master
(term_to_string t)
end))))
in (FStar_All.pipe_right _129_123 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _129_124 (FStar_String.concat "\\/")))
in (let _129_125 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _129_125)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _39_229) -> begin
(term_to_string t)
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _128_126 = (db_to_string x)
in (FStar_Util.format1 "Tm_bvar:%s" _128_126))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _128_127 = (nm_to_string x)
in (FStar_Util.format1 "Tm_name:%s" _128_127))
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(let _128_128 = (fv_to_string f)
in (FStar_Util.format1 "Tm_fvar:%s" _128_128))
end
| FStar_Syntax_Syntax.Tm_uvar (u, _39_240) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_Options.print_universes ()) then begin
<<<<<<< HEAD
(let _128_129 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _128_129))
=======
(let _129_126 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _129_126))
>>>>>>> master
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
<<<<<<< HEAD
(let _128_131 = (binders_to_string " -> " bs)
in (let _128_130 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _128_131 _128_130)))
=======
(let _129_128 = (binders_to_string " -> " bs)
in (let _129_127 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _129_128 _129_127)))
>>>>>>> master
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
<<<<<<< HEAD
(let _128_135 = (binders_to_string " " bs)
in (let _128_134 = (term_to_string t2)
in (let _128_133 = (let _128_132 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _128_132))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _128_135 _128_134 _128_133))))
end
| _39_260 -> begin
(let _128_137 = (binders_to_string " " bs)
in (let _128_136 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _128_137 _128_136)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _128_140 = (bv_to_string xt)
in (let _128_139 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _128_138 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _128_140 _128_139 _128_138))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _128_142 = (term_to_string t)
in (let _128_141 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _128_142 _128_141)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _128_144 = (lbs_to_string [] lbs)
in (let _128_143 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _128_144 _128_143)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _39_277) -> begin
(let _128_146 = (term_to_string e)
in (let _128_145 = (term_to_string t)
in (FStar_Util.format2 "(%s : %s)" _128_146 _128_145)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _39_284) -> begin
(let _128_148 = (term_to_string e)
in (let _128_147 = (comp_to_string c)
in (FStar_Util.format2 "(%s : %s)" _128_148 _128_147)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _128_156 = (term_to_string head)
in (let _128_155 = (let _128_154 = (FStar_All.pipe_right branches (FStar_List.map (fun _39_294 -> (match (_39_294) with
| (p, wopt, e) -> begin
(let _128_153 = (FStar_All.pipe_right p pat_to_string)
in (let _128_152 = (match (wopt) with
=======
(let _129_132 = (binders_to_string " " bs)
in (let _129_131 = (term_to_string t2)
in (let _129_130 = (let _129_129 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _129_129))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _129_132 _129_131 _129_130))))
end
| _39_259 -> begin
(let _129_134 = (binders_to_string " " bs)
in (let _129_133 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _129_134 _129_133)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _129_137 = (bv_to_string xt)
in (let _129_136 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _129_135 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _129_137 _129_136 _129_135))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _129_139 = (term_to_string t)
in (let _129_138 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _129_139 _129_138)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _129_141 = (lbs_to_string [] lbs)
in (let _129_140 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _129_141 _129_140)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _39_276) -> begin
(let _129_143 = (term_to_string e)
in (let _129_142 = (term_to_string t)
in (FStar_Util.format2 "(%s : %s)" _129_143 _129_142)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _39_283) -> begin
(let _129_145 = (term_to_string e)
in (let _129_144 = (comp_to_string c)
in (FStar_Util.format2 "(%s : %s)" _129_145 _129_144)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _129_153 = (term_to_string head)
in (let _129_152 = (let _129_151 = (FStar_All.pipe_right branches (FStar_List.map (fun _39_293 -> (match (_39_293) with
| (p, wopt, e) -> begin
(let _129_150 = (FStar_All.pipe_right p pat_to_string)
in (let _129_149 = (match (wopt) with
>>>>>>> master
| None -> begin
""
end
| Some (w) -> begin
<<<<<<< HEAD
(let _128_150 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _128_150))
end)
in (let _128_151 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _128_153 _128_152 _128_151))))
end))))
in (FStar_Util.concat_l "\n\t|" _128_154))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _128_156 _128_155)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_Options.print_universes ()) then begin
(let _128_158 = (term_to_string t)
in (let _128_157 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _128_158 _128_157)))
=======
(let _129_147 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _129_147))
end)
in (let _129_148 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _129_150 _129_149 _129_148))))
end))))
in (FStar_Util.concat_l "\n\t|" _129_151))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _129_153 _129_152)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_Options.print_universes ()) then begin
(let _129_155 = (term_to_string t)
in (let _129_154 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _129_155 _129_154)))
>>>>>>> master
end else begin
(term_to_string t)
end
end
| _39_303 -> begin
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
<<<<<<< HEAD
(let _128_163 = (fv_to_string l)
in (let _128_162 = (let _128_161 = (FStar_List.map (fun _39_311 -> (match (_39_311) with
=======
(let _129_160 = (fv_to_string l)
in (let _129_159 = (let _129_158 = (FStar_List.map (fun _39_310 -> (match (_39_310) with
>>>>>>> master
| (x, b) -> begin
(

let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
<<<<<<< HEAD
in (FStar_All.pipe_right _128_161 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _128_163 _128_162)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _39_315) -> begin
(let _128_164 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _128_164))
=======
in (FStar_All.pipe_right _129_158 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _129_160 _129_159)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _39_314) -> begin
(let _129_161 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _129_161))
>>>>>>> master
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(bv_to_string x)
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_Options.print_real_names ()) then begin
<<<<<<< HEAD
(let _128_165 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _128_165))
=======
(let _129_162 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _129_162))
>>>>>>> master
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
<<<<<<< HEAD
(let _128_166 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _128_166))
=======
(let _129_163 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _129_163))
>>>>>>> master
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (

let lbs = if (FStar_Options.print_universes ()) then begin
<<<<<<< HEAD
(let _128_172 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _39_331 = (let _128_170 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _128_170))
in (match (_39_331) with
| (us, td) -> begin
(

let _39_349 = (match ((let _128_171 = (FStar_Syntax_Subst.compress td)
in _128_171.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_39_333, ((t, _39_340))::((d, _39_336))::[]) -> begin
=======
(let _129_169 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _39_330 = (let _129_167 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _129_167))
in (match (_39_330) with
| (us, td) -> begin
(

let _39_348 = (match ((let _129_168 = (FStar_Syntax_Subst.compress td)
in _129_168.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_39_332, ((t, _39_339))::((d, _39_335))::[]) -> begin
>>>>>>> master
(t, d)
end
| _39_346 -> begin
(FStar_All.failwith "Impossibe")
end)
in (match (_39_349) with
| (t, d) -> begin
(

let _39_350 = lb
in {FStar_Syntax_Syntax.lbname = _39_350.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_350.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
<<<<<<< HEAD
in ((Prims.fst lbs), _128_172))
end else begin
lbs
end
in (let _128_182 = (quals_to_string quals)
in (let _128_181 = (let _128_180 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _128_179 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _128_178 = if (FStar_Options.print_universes ()) then begin
(let _128_175 = (let _128_174 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat "<" _128_174))
in (Prims.strcat _128_175 ">"))
end else begin
""
end
in (let _128_177 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _128_176 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _128_179 _128_178 _128_177 _128_176))))))))
in (FStar_Util.concat_l "\n and " _128_180))
in (FStar_Util.format3 "%slet %s %s" _128_182 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _128_181)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _128_185 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _128_184 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _128_185 _128_184))))
=======
in ((Prims.fst lbs), _129_169))
end else begin
lbs
end
in (let _129_179 = (quals_to_string quals)
in (let _129_178 = (let _129_177 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _129_176 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _129_175 = if (FStar_Options.print_universes ()) then begin
(let _129_172 = (let _129_171 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat "<" _129_171))
in (Prims.strcat _129_172 ">"))
end else begin
""
end
in (let _129_174 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _129_173 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _129_176 _129_175 _129_174 _129_173))))))))
in (FStar_Util.concat_l "\n and " _129_177))
in (FStar_Util.format3 "%slet %s %s" _129_179 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _129_178)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _129_182 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _129_181 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _129_182 _129_181))))
>>>>>>> master
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
| _39_366 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (

let _39_371 = b
in (match (_39_371) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
<<<<<<< HEAD
(let _128_190 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" _128_190))
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_bound_var_types ())))) then begin
(let _128_191 = (nm_to_string a)
in (imp_to_string _128_191 imp))
end else begin
(let _128_195 = (let _128_194 = (let _128_192 = (nm_to_string a)
in (Prims.strcat _128_192 ":"))
in (let _128_193 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat _128_194 _128_193)))
in (imp_to_string _128_195 imp))
=======
(let _129_187 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" _129_187))
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_bound_var_types ())))) then begin
(let _129_188 = (nm_to_string a)
in (imp_to_string _129_188 imp))
end else begin
(let _129_192 = (let _129_191 = (let _129_189 = (nm_to_string a)
in (Prims.strcat _129_189 ":"))
in (let _129_190 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat _129_191 _129_190)))
in (imp_to_string _129_192 imp))
>>>>>>> master
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
<<<<<<< HEAD
(let _128_200 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _128_200 (FStar_String.concat sep)))
end else begin
(let _128_201 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _128_201 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _39_6 -> (match (_39_6) with
| (a, imp) -> begin
(let _128_203 = (term_to_string a)
in (imp_to_string _128_203 imp))
=======
(let _129_197 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _129_197 (FStar_String.concat sep)))
end else begin
(let _129_198 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _129_198 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _39_6 -> (match (_39_6) with
| (a, imp) -> begin
(let _129_200 = (term_to_string a)
in (imp_to_string _129_200 imp))
>>>>>>> master
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args = if (FStar_Options.print_implicits ()) then begin
args
end else begin
(filter_imp args)
end
<<<<<<< HEAD
in (let _128_205 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _128_205 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(match ((let _128_207 = (FStar_Syntax_Subst.compress t)
in _128_207.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_387) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_390 -> begin
(let _128_208 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _128_208))
end)
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(match ((let _128_209 = (FStar_Syntax_Subst.compress t)
in _128_209.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_394) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_397 -> begin
(let _128_210 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _128_210))
=======
in (let _129_202 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _129_202 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(match ((let _129_204 = (FStar_Syntax_Subst.compress t)
in _129_204.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_386) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_389 -> begin
(let _129_205 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _129_205))
end)
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(match ((let _129_206 = (FStar_Syntax_Subst.compress t)
in _129_206.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_393) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_396 -> begin
(let _129_207 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _129_207))
>>>>>>> master
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let basic = if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_7 -> (match (_39_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _39_403 -> begin
false
end)))) && (not ((FStar_Options.print_effect_args ())))) then begin
<<<<<<< HEAD
(let _128_212 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _128_212))
=======
(let _129_209 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _129_209))
>>>>>>> master
end else begin
if (((not ((FStar_Options.print_effect_args ()))) && (not ((FStar_Options.print_implicits ())))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_Options.print_effect_args ()))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_8 -> (match (_39_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _39_407 -> begin
false
end))))) then begin
<<<<<<< HEAD
(let _128_214 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _128_214))
end else begin
if (FStar_Options.print_effect_args ()) then begin
(let _128_218 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _128_217 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _128_216 = (let _128_215 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _128_215 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _128_218 _128_217 _128_216))))
end else begin
(let _128_220 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _128_219 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _128_220 _128_219)))
=======
(let _129_211 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _129_211))
end else begin
if (FStar_Options.print_effect_args ()) then begin
(let _129_215 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _129_214 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _129_213 = (let _129_212 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _129_212 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _129_215 _129_214 _129_213))))
end else begin
(let _129_217 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _129_216 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _129_217 _129_216)))
>>>>>>> master
end
end
end
end
in (

<<<<<<< HEAD
let dec = (let _128_224 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _39_9 -> (match (_39_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _128_223 = (let _128_222 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _128_222))
in (_128_223)::[])
=======
let dec = (let _129_221 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _39_9 -> (match (_39_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _129_220 = (let _129_219 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _129_219))
in (_129_220)::[])
>>>>>>> master
end
| _39_413 -> begin
[]
end))))
<<<<<<< HEAD
in (FStar_All.pipe_right _128_224 (FStar_String.concat " ")))
=======
in (FStar_All.pipe_right _129_221 (FStar_String.concat " ")))
>>>>>>> master
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))


let tscheme_to_string : (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  Prims.string = (fun _39_418 -> (match (_39_418) with
| (us, t) -> begin
<<<<<<< HEAD
(let _128_229 = (univ_names_to_string us)
in (let _128_228 = (term_to_string t)
in (FStar_Util.format2 "<%s> %s" _128_229 _128_228)))
end))


let eff_decl_to_string : FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun ed -> (let _128_261 = (let _128_260 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _128_259 = (let _128_258 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (let _128_257 = (let _128_256 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _128_255 = (let _128_254 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _128_253 = (let _128_252 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret)
in (let _128_251 = (let _128_250 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _128_249 = (let _128_248 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _128_247 = (let _128_246 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _128_245 = (let _128_244 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_binop)
in (let _128_243 = (let _128_242 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_as_type)
in (let _128_241 = (let _128_240 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _128_239 = (let _128_238 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _128_237 = (let _128_236 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _128_235 = (let _128_234 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _128_233 = (let _128_232 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (_128_232)::[])
in (_128_234)::_128_233))
in (_128_236)::_128_235))
in (_128_238)::_128_237))
in (_128_240)::_128_239))
in (_128_242)::_128_241))
in (_128_244)::_128_243))
in (_128_246)::_128_245))
in (_128_248)::_128_247))
in (_128_250)::_128_249))
in (_128_252)::_128_251))
in (_128_254)::_128_253))
in (_128_256)::_128_255))
in (_128_258)::_128_257))
in (_128_260)::_128_259))
in (FStar_Util.format "new_effect { %s<%s> %s : %s \n\tret         = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; wp_binop    = %s\n; wp_as_type  = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s}\n" _128_261)))
=======
(let _129_226 = (univ_names_to_string us)
in (let _129_225 = (term_to_string t)
in (FStar_Util.format2 "<%s> %s" _129_226 _129_225)))
end))


let eff_decl_to_string : FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun ed -> (let _129_258 = (let _129_257 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _129_256 = (let _129_255 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (let _129_254 = (let _129_253 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _129_252 = (let _129_251 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _129_250 = (let _129_249 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret)
in (let _129_248 = (let _129_247 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _129_246 = (let _129_245 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _129_244 = (let _129_243 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _129_242 = (let _129_241 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_binop)
in (let _129_240 = (let _129_239 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_as_type)
in (let _129_238 = (let _129_237 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _129_236 = (let _129_235 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _129_234 = (let _129_233 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _129_232 = (let _129_231 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _129_230 = (let _129_229 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (_129_229)::[])
in (_129_231)::_129_230))
in (_129_233)::_129_232))
in (_129_235)::_129_234))
in (_129_237)::_129_236))
in (_129_239)::_129_238))
in (_129_241)::_129_240))
in (_129_243)::_129_242))
in (_129_245)::_129_244))
in (_129_247)::_129_246))
in (_129_249)::_129_248))
in (_129_251)::_129_250))
in (_129_253)::_129_252))
in (_129_255)::_129_254))
in (_129_257)::_129_256))
in (FStar_Util.format "new_effect { %s<%s> %s : %s \n\tret         = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; wp_binop    = %s\n; wp_as_type  = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s}\n" _129_258)))
>>>>>>> master


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None), _39_424) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s)), _39_431) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _39_437) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
<<<<<<< HEAD
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _39_445, _39_447, quals, _39_450) -> begin
(let _128_267 = (quals_to_string quals)
in (let _128_266 = (univ_names_to_string univs)
in (let _128_265 = (binders_to_string " " tps)
in (let _128_264 = (term_to_string k)
in (FStar_Util.format5 "%s type %s<%s> %s : %s" _128_267 lid.FStar_Ident.str _128_266 _128_265 _128_264)))))
=======
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _39_444, _39_446, quals, _39_449) -> begin
(let _129_263 = (quals_to_string quals)
in (let _129_262 = (binders_to_string " " tps)
in (let _129_261 = (term_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _129_263 lid.FStar_Ident.str _129_262 _129_261))))
>>>>>>> master
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _39_457, _39_459, _39_461, _39_463, _39_465) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_470 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_470) with
| (univs, t) -> begin
<<<<<<< HEAD
(let _128_269 = (univ_names_to_string univs)
in (let _128_268 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _128_269 lid.FStar_Ident.str _128_268)))
end))
end else begin
(let _128_270 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _128_270))
=======
(let _129_265 = (univ_names_to_string univs)
in (let _129_264 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _129_265 lid.FStar_Ident.str _129_264)))
end))
end else begin
(let _129_266 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _129_266))
>>>>>>> master
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _39_476) -> begin
(

let _39_481 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_481) with
| (univs, t) -> begin
<<<<<<< HEAD
(let _128_274 = (quals_to_string quals)
in (let _128_273 = if (FStar_Options.print_universes ()) then begin
(let _128_271 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _128_271))
end else begin
""
end
in (let _128_272 = (term_to_string t)
in (FStar_Util.format4 "%s val %s %s : %s" _128_274 lid.FStar_Ident.str _128_273 _128_272))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _39_485, _39_487) -> begin
(let _128_275 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _128_275))
=======
(let _129_270 = (quals_to_string quals)
in (let _129_269 = if (FStar_Options.print_universes ()) then begin
(let _129_267 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _129_267))
end else begin
""
end
in (let _129_268 = (term_to_string t)
in (FStar_Util.format4 "%s val %s %s : %s" _129_270 lid.FStar_Ident.str _129_269 _129_268))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _39_484, _39_486) -> begin
(let _129_271 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _129_271))
>>>>>>> master
end
| FStar_Syntax_Syntax.Sig_let (lbs, _39_492, _39_494, qs) -> begin
(lbs_to_string qs lbs)
end
<<<<<<< HEAD
| FStar_Syntax_Syntax.Sig_main (e, _39_500) -> begin
(let _128_276 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _128_276))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _39_505, _39_507, _39_509) -> begin
(let _128_277 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _128_277 (FStar_String.concat "\n")))
=======
| FStar_Syntax_Syntax.Sig_main (e, _39_499) -> begin
(let _129_272 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _129_272))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _39_504, _39_506, _39_508) -> begin
(let _129_273 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _129_273 (FStar_String.concat "\n")))
>>>>>>> master
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _39_514) -> begin
(eff_decl_to_string ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(

let _39_523 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst se.FStar_Syntax_Syntax.lift) (Prims.snd se.FStar_Syntax_Syntax.lift))
in (match (_39_523) with
| (us, t) -> begin
<<<<<<< HEAD
(let _128_281 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _128_280 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _128_279 = (univ_names_to_string us)
in (let _128_278 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _128_281 _128_280 _128_279 _128_278)))))
=======
(let _129_277 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _129_276 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _129_275 = (univ_names_to_string us)
in (let _129_274 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _129_277 _129_276 _129_275 _129_274)))))
>>>>>>> master
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _39_529, _39_531) -> begin
if (FStar_Options.print_universes ()) then begin
(

<<<<<<< HEAD
let _39_536 = (let _128_282 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _128_282))
in (match (_39_536) with
| (univs, t) -> begin
(

let _39_545 = (match ((let _128_283 = (FStar_Syntax_Subst.compress t)
in _128_283.FStar_Syntax_Syntax.n)) with
=======
let _39_535 = (let _129_278 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _129_278))
in (match (_39_535) with
| (univs, t) -> begin
(

let _39_544 = (match ((let _129_279 = (FStar_Syntax_Subst.compress t)
in _129_279.FStar_Syntax_Syntax.n)) with
>>>>>>> master
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(bs, c)
end
| _39_542 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_39_545) with
| (tps, c) -> begin
<<<<<<< HEAD
(let _128_287 = (sli l)
in (let _128_286 = (univ_names_to_string univs)
in (let _128_285 = (binders_to_string " " tps)
in (let _128_284 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _128_287 _128_286 _128_285 _128_284)))))
end))
end))
end else begin
(let _128_290 = (sli l)
in (let _128_289 = (binders_to_string " " tps)
in (let _128_288 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _128_290 _128_289 _128_288))))
=======
(let _129_283 = (sli l)
in (let _129_282 = (univ_names_to_string univs)
in (let _129_281 = (binders_to_string " " tps)
in (let _129_280 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _129_283 _129_282 _129_281 _129_280)))))
end))
end))
end else begin
(let _129_286 = (sli l)
in (let _129_285 = (binders_to_string " " tps)
in (let _129_284 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _129_286 _129_285 _129_284))))
>>>>>>> master
end
end))


<<<<<<< HEAD
let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _128_295 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _128_295 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_39_550, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = _39_557; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_554; FStar_Syntax_Syntax.lbdef = _39_552})::[]), _39_563, _39_565, _39_567) -> begin
(let _128_299 = (lbname_to_string lb)
in (let _128_298 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _128_299 _128_298)))
end
| _39_571 -> begin
(let _128_302 = (let _128_301 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _128_301 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _128_302 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _128_307 = (sli m.FStar_Syntax_Syntax.name)
in (let _128_306 = (let _128_305 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _128_305 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _128_307 _128_306))))
=======
let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _129_291 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _129_291 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_39_549, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = _39_556; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_553; FStar_Syntax_Syntax.lbdef = _39_551})::[]), _39_562, _39_564, _39_566) -> begin
(let _129_295 = (lbname_to_string lb)
in (let _129_294 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _129_295 _129_294)))
end
| _39_570 -> begin
(let _129_298 = (let _129_297 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _129_297 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _129_298 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _129_303 = (sli m.FStar_Syntax_Syntax.name)
in (let _129_302 = (let _129_301 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _129_301 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _129_303 _129_302))))
>>>>>>> master


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _39_10 -> (match (_39_10) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
<<<<<<< HEAD
(let _128_311 = (FStar_Util.string_of_int i)
in (let _128_310 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _128_311 _128_310)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _128_313 = (bv_to_string x)
in (let _128_312 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _128_313 _128_312)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _128_315 = (bv_to_string x)
in (let _128_314 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _128_315 _128_314)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _128_317 = (FStar_Util.string_of_int i)
in (let _128_316 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _128_317 _128_316)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _128_318 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _128_318))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _128_321 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _128_321 (FStar_String.concat "; "))))
=======
(let _129_307 = (FStar_Util.string_of_int i)
in (let _129_306 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _129_307 _129_306)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _129_309 = (bv_to_string x)
in (let _129_308 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _129_309 _129_308)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _129_311 = (bv_to_string x)
in (let _129_310 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _129_311 _129_310)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _129_313 = (FStar_Util.string_of_int i)
in (let _129_312 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _129_313 _129_312)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _129_314 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _129_314))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _129_317 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _129_317 (FStar_String.concat "; "))))
>>>>>>> master




