
open Prims

let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> l.FStar_Ident.str)


let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _130_7 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "#") _130_7)))


let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> if (FStar_Options.print_real_names ()) then begin
(bv_to_string bv)
end else begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)


<<<<<<< HEAD
let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _129_12 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "!") _129_12)))
=======
let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _130_12 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "@") _130_12)))
>>>>>>> master


let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.op_Addition, "+"))::((FStar_Syntax_Const.op_Subtraction, "-"))::((FStar_Syntax_Const.op_Multiply, "*"))::((FStar_Syntax_Const.op_Division, "/"))::((FStar_Syntax_Const.op_Eq, "="))::((FStar_Syntax_Const.op_ColonEq, ":="))::((FStar_Syntax_Const.op_notEq, "<>"))::((FStar_Syntax_Const.op_And, "&&"))::((FStar_Syntax_Const.op_Or, "||"))::((FStar_Syntax_Const.op_LTE, "<="))::((FStar_Syntax_Const.op_GTE, ">="))::((FStar_Syntax_Const.op_LT, "<"))::((FStar_Syntax_Const.op_GT, ">"))::((FStar_Syntax_Const.op_Modulus, "mod"))::((FStar_Syntax_Const.and_lid, "/\\"))::((FStar_Syntax_Const.or_lid, "\\/"))::((FStar_Syntax_Const.imp_lid, "==>"))::((FStar_Syntax_Const.iff_lid, "<==>"))::((FStar_Syntax_Const.precedes_lid, "<<"))::((FStar_Syntax_Const.eq2_lid, "=="))::((FStar_Syntax_Const.eq3_lid, "==="))::[]


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


let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _130_35 = (FStar_Syntax_Subst.compress e)
in _130_35.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args = (filter_imp args)
in (

let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = 2)) then begin
(match ((let _130_36 = (FStar_List.nth exps 1)
in (reconstruct_lex _130_36))) with
| Some (xs) -> begin
(let _130_38 = (let _130_37 = (FStar_List.nth exps 0)
in (_130_37)::xs)
in Some (_130_38))
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


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _130_52 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _130_52)))


let infix_prim_op_to_string = (fun e -> (let _130_54 = (get_lid e)
in (find_lid _130_54 infix_prim_ops)))


let unary_prim_op_to_string = (fun e -> (let _130_56 = (get_lid e)
in (find_lid _130_56 unary_prim_ops)))


let quant_to_string = (fun t -> (let _130_58 = (get_lid t)
in (find_lid _130_58 quants)))


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
(let _130_67 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _130_67))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _130_68 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _130_68))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _130_69 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _130_69))
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
(let _130_74 = (let _130_73 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _130_73 FStar_Util.string_of_int))
in (Prims.strcat "?" _130_74))
end)


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_unif (u) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(FStar_Util.format1 "U_name<%s>" x.FStar_Ident.idText)
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(let _130_77 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _130_77))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _130_78 = (univ_to_string u)
in (FStar_Util.format1 "(S %s)" _130_78))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _130_80 = (let _130_79 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _130_79 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _130_80))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _130_83 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _130_83 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _130_87 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _130_87 (FStar_String.concat ", "))))


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
(let _130_90 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _130_90))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _130_91 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _130_91 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(let _130_93 = (let _130_92 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _130_92 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordType %s)" _130_93))
end
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
(let _130_95 = (let _130_94 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _130_94 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordConstructor %s)" _130_95))
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
(let _129_99 = (let _129_98 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _129_98 (FStar_String.concat " ")))
in (Prims.strcat _129_99 " "))
=======
| _39_204 -> begin
(let _130_99 = (let _130_98 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _130_98 (FStar_String.concat " ")))
in (Prims.strcat _130_99 " "))
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
let pats = (let _129_124 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _129_123 = (FStar_All.pipe_right args (FStar_List.map (fun _39_225 -> (match (_39_225) with
| (t, _39_224) -> begin
=======
let pats = (let _130_124 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _130_123 = (FStar_All.pipe_right args (FStar_List.map (fun _39_224 -> (match (_39_224) with
| (t, _39_223) -> begin
>>>>>>> master
(term_to_string t)
end))))
in (FStar_All.pipe_right _130_123 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _130_124 (FStar_String.concat "\\/")))
in (let _130_125 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _130_125)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _39_229) -> begin
(term_to_string t)
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _129_126 = (db_to_string x)
in (FStar_Util.format1 "Tm_bvar:%s" _129_126))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _129_127 = (nm_to_string x)
in (FStar_Util.format1 "Tm_name:%s" _129_127))
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(let _129_128 = (fv_to_string f)
in (FStar_Util.format1 "Tm_fvar:%s" _129_128))
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
(let _129_129 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _129_129))
=======
(let _130_126 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _130_126))
>>>>>>> master
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
<<<<<<< HEAD
(let _129_131 = (binders_to_string " -> " bs)
in (let _129_130 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _129_131 _129_130)))
=======
(let _130_128 = (binders_to_string " -> " bs)
in (let _130_127 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _130_128 _130_127)))
>>>>>>> master
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
<<<<<<< HEAD
(let _129_135 = (binders_to_string " " bs)
in (let _129_134 = (term_to_string t2)
in (let _129_133 = (let _129_132 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _129_132))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _129_135 _129_134 _129_133))))
end
| _39_260 -> begin
(let _129_137 = (binders_to_string " " bs)
in (let _129_136 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _129_137 _129_136)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _129_140 = (bv_to_string xt)
in (let _129_139 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _129_138 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _129_140 _129_139 _129_138))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _129_142 = (term_to_string t)
in (let _129_141 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _129_142 _129_141)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _129_144 = (lbs_to_string [] lbs)
in (let _129_143 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _129_144 _129_143)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _39_277) -> begin
(let _129_146 = (term_to_string e)
in (let _129_145 = (term_to_string t)
in (FStar_Util.format2 "(%s : %s)" _129_146 _129_145)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _39_284) -> begin
(let _129_148 = (term_to_string e)
in (let _129_147 = (comp_to_string c)
in (FStar_Util.format2 "(%s : %s)" _129_148 _129_147)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _129_156 = (term_to_string head)
in (let _129_155 = (let _129_154 = (FStar_All.pipe_right branches (FStar_List.map (fun _39_294 -> (match (_39_294) with
| (p, wopt, e) -> begin
(let _129_153 = (FStar_All.pipe_right p pat_to_string)
in (let _129_152 = (match (wopt) with
=======
(let _130_132 = (binders_to_string " " bs)
in (let _130_131 = (term_to_string t2)
in (let _130_130 = (let _130_129 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _130_129))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _130_132 _130_131 _130_130))))
end
| Some (FStar_Util.Inr (l)) when (FStar_Options.print_implicits ()) -> begin
(let _130_134 = (binders_to_string " " bs)
in (let _130_133 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _130_134 _130_133 l.FStar_Ident.str)))
end
| _39_262 -> begin
(let _130_136 = (binders_to_string " " bs)
in (let _130_135 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _130_136 _130_135)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _130_139 = (bv_to_string xt)
in (let _130_138 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _130_137 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _130_139 _130_138 _130_137))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _130_141 = (term_to_string t)
in (let _130_140 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _130_141 _130_140)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _130_143 = (lbs_to_string [] lbs)
in (let _130_142 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _130_143 _130_142)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _39_279) -> begin
(let _130_145 = (term_to_string e)
in (let _130_144 = (term_to_string t)
in (FStar_Util.format2 "(%s : %s)" _130_145 _130_144)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _39_286) -> begin
(let _130_147 = (term_to_string e)
in (let _130_146 = (comp_to_string c)
in (FStar_Util.format2 "(%s : %s)" _130_147 _130_146)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _130_155 = (term_to_string head)
in (let _130_154 = (let _130_153 = (FStar_All.pipe_right branches (FStar_List.map (fun _39_296 -> (match (_39_296) with
| (p, wopt, e) -> begin
(let _130_152 = (FStar_All.pipe_right p pat_to_string)
in (let _130_151 = (match (wopt) with
>>>>>>> master
| None -> begin
""
end
| Some (w) -> begin
<<<<<<< HEAD
(let _129_150 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _129_150))
end)
in (let _129_151 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _129_153 _129_152 _129_151))))
end))))
in (FStar_Util.concat_l "\n\t|" _129_154))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _129_156 _129_155)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_Options.print_universes ()) then begin
(let _129_158 = (term_to_string t)
in (let _129_157 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _129_158 _129_157)))
=======
(let _130_149 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _130_149))
end)
in (let _130_150 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _130_152 _130_151 _130_150))))
end))))
in (FStar_Util.concat_l "\n\t|" _130_153))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _130_155 _130_154)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_Options.print_universes ()) then begin
(let _130_157 = (term_to_string t)
in (let _130_156 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _130_157 _130_156)))
>>>>>>> master
end else begin
(term_to_string t)
end
end
<<<<<<< HEAD
| _39_303 -> begin
=======
| _39_305 -> begin
>>>>>>> master
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
<<<<<<< HEAD
(let _129_163 = (fv_to_string l)
in (let _129_162 = (let _129_161 = (FStar_List.map (fun _39_311 -> (match (_39_311) with
=======
(let _130_162 = (fv_to_string l)
in (let _130_161 = (let _130_160 = (FStar_List.map (fun _39_313 -> (match (_39_313) with
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
in (FStar_All.pipe_right _129_161 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _129_163 _129_162)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _39_315) -> begin
(let _129_164 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _129_164))
=======
in (FStar_All.pipe_right _130_160 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _130_162 _130_161)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _39_317) -> begin
(let _130_163 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _130_163))
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
(let _129_165 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _129_165))
=======
(let _130_164 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _130_164))
>>>>>>> master
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
<<<<<<< HEAD
(let _129_166 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _129_166))
=======
(let _130_165 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _130_165))
>>>>>>> master
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (

let lbs = if (FStar_Options.print_universes ()) then begin
<<<<<<< HEAD
(let _129_172 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _39_331 = (let _129_170 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _129_170))
in (match (_39_331) with
| (us, td) -> begin
(

let _39_349 = (match ((let _129_171 = (FStar_Syntax_Subst.compress td)
in _129_171.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_39_333, ((t, _39_340))::((d, _39_336))::[]) -> begin
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
in ((Prims.fst lbs), _129_172))
end else begin
lbs
end
in (let _129_182 = (quals_to_string quals)
in (let _129_181 = (let _129_180 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _129_179 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _129_178 = if (FStar_Options.print_universes ()) then begin
(let _129_175 = (let _129_174 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat "<" _129_174))
in (Prims.strcat _129_175 ">"))
end else begin
""
end
in (let _129_177 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _129_176 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _129_179 _129_178 _129_177 _129_176))))))))
in (FStar_Util.concat_l "\n and " _129_180))
in (FStar_Util.format3 "%slet %s %s" _129_182 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _129_181)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _129_185 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _129_184 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _129_185 _129_184))))
=======
(let _130_171 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _39_333 = (let _130_169 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _130_169))
in (match (_39_333) with
| (us, td) -> begin
(

let _39_351 = (match ((let _130_170 = (FStar_Syntax_Subst.compress td)
in _130_170.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_39_335, ((t, _39_342))::((d, _39_338))::[]) -> begin
(t, d)
end
| _39_348 -> begin
(FStar_All.failwith "Impossibe")
end)
in (match (_39_351) with
| (t, d) -> begin
(

let _39_352 = lb
in {FStar_Syntax_Syntax.lbname = _39_352.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_352.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in ((Prims.fst lbs), _130_171))
end else begin
lbs
end
in (let _130_181 = (quals_to_string quals)
in (let _130_180 = (let _130_179 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _130_178 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _130_177 = if (FStar_Options.print_universes ()) then begin
(let _130_174 = (let _130_173 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat "<" _130_173))
in (Prims.strcat _130_174 ">"))
end else begin
""
end
in (let _130_176 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _130_175 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _130_178 _130_177 _130_176 _130_175))))))))
in (FStar_Util.concat_l "\n and " _130_179))
in (FStar_Util.format3 "%slet %s %s" _130_181 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _130_180)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _130_184 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _130_183 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _130_184 _130_183))))
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
<<<<<<< HEAD
| _39_366 -> begin
=======
| _39_368 -> begin
>>>>>>> master
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (

<<<<<<< HEAD
let _39_371 = b
in (match (_39_371) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(let _129_190 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" _129_190))
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_bound_var_types ())))) then begin
(let _129_191 = (nm_to_string a)
in (imp_to_string _129_191 imp))
end else begin
(let _129_195 = (let _129_194 = (let _129_192 = (nm_to_string a)
in (Prims.strcat _129_192 ":"))
in (let _129_193 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat _129_194 _129_193)))
in (imp_to_string _129_195 imp))
=======
let _39_373 = b
in (match (_39_373) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(let _130_189 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" _130_189))
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_bound_var_types ())))) then begin
(let _130_190 = (nm_to_string a)
in (imp_to_string _130_190 imp))
end else begin
(let _130_194 = (let _130_193 = (let _130_191 = (nm_to_string a)
in (Prims.strcat _130_191 ":"))
in (let _130_192 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat _130_193 _130_192)))
in (imp_to_string _130_194 imp))
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
(let _129_200 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _129_200 (FStar_String.concat sep)))
end else begin
(let _129_201 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _129_201 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _39_6 -> (match (_39_6) with
| (a, imp) -> begin
(let _129_203 = (term_to_string a)
in (imp_to_string _129_203 imp))
=======
(let _130_199 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _130_199 (FStar_String.concat sep)))
end else begin
(let _130_200 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _130_200 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _39_6 -> (match (_39_6) with
| (a, imp) -> begin
(let _130_202 = (term_to_string a)
in (imp_to_string _130_202 imp))
>>>>>>> master
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args = if (FStar_Options.print_implicits ()) then begin
args
end else begin
(filter_imp args)
end
<<<<<<< HEAD
in (let _129_205 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _129_205 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(match ((let _129_207 = (FStar_Syntax_Subst.compress t)
in _129_207.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_387) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_390 -> begin
(let _129_208 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _129_208))
end)
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(match ((let _129_209 = (FStar_Syntax_Subst.compress t)
in _129_209.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_394) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_397 -> begin
(let _129_210 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _129_210))
=======
in (let _130_204 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _130_204 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(match ((let _130_206 = (FStar_Syntax_Subst.compress t)
in _130_206.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_389) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_392 -> begin
(let _130_207 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _130_207))
end)
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(match ((let _130_208 = (FStar_Syntax_Subst.compress t)
in _130_208.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_396) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_399 -> begin
(let _130_209 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _130_209))
>>>>>>> master
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let basic = if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_7 -> (match (_39_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
<<<<<<< HEAD
| _39_403 -> begin
false
end)))) && (not ((FStar_Options.print_effect_args ())))) then begin
(let _129_212 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _129_212))
=======
| _39_405 -> begin
false
end)))) && (not ((FStar_Options.print_effect_args ())))) then begin
(let _130_211 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _130_211))
>>>>>>> master
end else begin
if (((not ((FStar_Options.print_effect_args ()))) && (not ((FStar_Options.print_implicits ())))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_Options.print_effect_args ()))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_8 -> (match (_39_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
<<<<<<< HEAD
| _39_407 -> begin
false
end))))) then begin
(let _129_214 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _129_214))
end else begin
if (FStar_Options.print_effect_args ()) then begin
(let _129_218 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _129_217 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _129_216 = (let _129_215 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _129_215 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _129_218 _129_217 _129_216))))
end else begin
(let _129_220 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _129_219 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _129_220 _129_219)))
=======
| _39_409 -> begin
false
end))))) then begin
(let _130_213 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _130_213))
end else begin
if (FStar_Options.print_effect_args ()) then begin
(let _130_217 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _130_216 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _130_215 = (let _130_214 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _130_214 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _130_217 _130_216 _130_215))))
end else begin
(let _130_219 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _130_218 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _130_219 _130_218)))
>>>>>>> master
end
end
end
end
in (

<<<<<<< HEAD
let dec = (let _129_224 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _39_9 -> (match (_39_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _129_223 = (let _129_222 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _129_222))
in (_129_223)::[])
end
| _39_413 -> begin
[]
end))))
in (FStar_All.pipe_right _129_224 (FStar_String.concat " ")))
=======
let dec = (let _130_223 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _39_9 -> (match (_39_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _130_222 = (let _130_221 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _130_221))
in (_130_222)::[])
end
| _39_415 -> begin
[]
end))))
in (FStar_All.pipe_right _130_223 (FStar_String.concat " ")))
>>>>>>> master
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))


<<<<<<< HEAD
let tscheme_to_string : (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  Prims.string = (fun _39_418 -> (match (_39_418) with
| (us, t) -> begin
(let _129_229 = (univ_names_to_string us)
in (let _129_228 = (term_to_string t)
in (FStar_Util.format2 "<%s> %s" _129_229 _129_228)))
end))


let eff_decl_to_string : FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun ed -> (let _129_261 = (let _129_260 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _129_259 = (let _129_258 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (let _129_257 = (let _129_256 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _129_255 = (let _129_254 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _129_253 = (let _129_252 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret)
in (let _129_251 = (let _129_250 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _129_249 = (let _129_248 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _129_247 = (let _129_246 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _129_245 = (let _129_244 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_binop)
in (let _129_243 = (let _129_242 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_as_type)
in (let _129_241 = (let _129_240 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _129_239 = (let _129_238 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _129_237 = (let _129_236 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _129_235 = (let _129_234 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _129_233 = (let _129_232 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (_129_232)::[])
in (_129_234)::_129_233))
in (_129_236)::_129_235))
in (_129_238)::_129_237))
in (_129_240)::_129_239))
in (_129_242)::_129_241))
in (_129_244)::_129_243))
in (_129_246)::_129_245))
in (_129_248)::_129_247))
in (_129_250)::_129_249))
in (_129_252)::_129_251))
in (_129_254)::_129_253))
in (_129_256)::_129_255))
in (_129_258)::_129_257))
in (_129_260)::_129_259))
in (FStar_Util.format "new_effect { %s<%s> %s : %s \n\tret         = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; wp_binop    = %s\n; wp_as_type  = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s}\n" _129_261)))


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
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _39_445, _39_447, quals, _39_450) -> begin
(let _129_267 = (quals_to_string quals)
in (let _129_266 = (univ_names_to_string univs)
in (let _129_265 = (binders_to_string " " tps)
in (let _129_264 = (term_to_string k)
in (FStar_Util.format5 "%s type %s<%s> %s : %s" _129_267 lid.FStar_Ident.str _129_266 _129_265 _129_264)))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _39_457, _39_459, _39_461, _39_463, _39_465) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_470 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_470) with
| (univs, t) -> begin
(let _129_269 = (univ_names_to_string univs)
in (let _129_268 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _129_269 lid.FStar_Ident.str _129_268)))
end))
end else begin
(let _129_270 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _129_270))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _39_476) -> begin
(

let _39_481 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_481) with
| (univs, t) -> begin
(let _129_274 = (quals_to_string quals)
in (let _129_273 = if (FStar_Options.print_universes ()) then begin
(let _129_271 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _129_271))
end else begin
""
end
in (let _129_272 = (term_to_string t)
in (FStar_Util.format4 "%s val %s %s : %s" _129_274 lid.FStar_Ident.str _129_273 _129_272))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _39_485, _39_487) -> begin
(let _129_275 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _129_275))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _39_492, _39_494, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _39_500) -> begin
(let _129_276 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _129_276))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _39_505, _39_507, _39_509) -> begin
(let _129_277 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _129_277 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _39_514) -> begin
=======
let tscheme_to_string : (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  Prims.string = (fun _39_420 -> (match (_39_420) with
| (us, t) -> begin
(let _130_228 = (univ_names_to_string us)
in (let _130_227 = (term_to_string t)
in (FStar_Util.format2 "<%s> %s" _130_228 _130_227)))
end))


let eff_decl_to_string : FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun ed -> (let _130_258 = (let _130_257 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _130_256 = (let _130_255 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (let _130_254 = (let _130_253 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _130_252 = (let _130_251 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _130_250 = (let _130_249 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret)
in (let _130_248 = (let _130_247 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _130_246 = (let _130_245 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _130_244 = (let _130_243 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _130_242 = (let _130_241 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (let _130_240 = (let _130_239 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _130_238 = (let _130_237 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _130_236 = (let _130_235 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _130_234 = (let _130_233 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _130_232 = (let _130_231 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (_130_231)::[])
in (_130_233)::_130_232))
in (_130_235)::_130_234))
in (_130_237)::_130_236))
in (_130_239)::_130_238))
in (_130_241)::_130_240))
in (_130_243)::_130_242))
in (_130_245)::_130_244))
in (_130_247)::_130_246))
in (_130_249)::_130_248))
in (_130_251)::_130_250))
in (_130_253)::_130_252))
in (_130_255)::_130_254))
in (_130_257)::_130_256))
in (FStar_Util.format "new_effect { %s<%s> %s : %s \n\tret         = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s}\n" _130_258)))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None), _39_426) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s)), _39_433) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _39_439) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _39_447, _39_449, quals, _39_452) -> begin
(let _130_263 = (quals_to_string quals)
in (let _130_262 = (binders_to_string " " tps)
in (let _130_261 = (term_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _130_263 lid.FStar_Ident.str _130_262 _130_261))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _39_459, _39_461, _39_463, _39_465, _39_467) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_472 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_472) with
| (univs, t) -> begin
(let _130_265 = (univ_names_to_string univs)
in (let _130_264 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _130_265 lid.FStar_Ident.str _130_264)))
end))
end else begin
(let _130_266 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _130_266))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _39_478) -> begin
(

let _39_483 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_483) with
| (univs, t) -> begin
(let _130_270 = (quals_to_string quals)
in (let _130_269 = if (FStar_Options.print_universes ()) then begin
(let _130_267 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _130_267))
end else begin
""
end
in (let _130_268 = (term_to_string t)
in (FStar_Util.format4 "%s val %s %s : %s" _130_270 lid.FStar_Ident.str _130_269 _130_268))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _39_487, _39_489) -> begin
(let _130_271 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _130_271))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _39_494, _39_496, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _39_502) -> begin
(let _130_272 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _130_272))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _39_507, _39_509, _39_511) -> begin
(let _130_273 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _130_273 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _39_516) -> begin
>>>>>>> master
(eff_decl_to_string ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(

<<<<<<< HEAD
let _39_523 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst se.FStar_Syntax_Syntax.lift) (Prims.snd se.FStar_Syntax_Syntax.lift))
in (match (_39_523) with
| (us, t) -> begin
(let _129_281 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _129_280 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _129_279 = (univ_names_to_string us)
in (let _129_278 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _129_281 _129_280 _129_279 _129_278)))))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _39_529, _39_531) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_536 = (let _129_282 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _129_282))
in (match (_39_536) with
| (univs, t) -> begin
(

let _39_545 = (match ((let _129_283 = (FStar_Syntax_Subst.compress t)
in _129_283.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(bs, c)
end
| _39_542 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_39_545) with
| (tps, c) -> begin
(let _129_287 = (sli l)
in (let _129_286 = (univ_names_to_string univs)
in (let _129_285 = (binders_to_string " " tps)
in (let _129_284 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _129_287 _129_286 _129_285 _129_284)))))
end))
end))
end else begin
(let _129_290 = (sli l)
in (let _129_289 = (binders_to_string " " tps)
in (let _129_288 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _129_290 _129_289 _129_288))))
=======
let _39_525 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst se.FStar_Syntax_Syntax.lift) (Prims.snd se.FStar_Syntax_Syntax.lift))
in (match (_39_525) with
| (us, t) -> begin
(let _130_277 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _130_276 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _130_275 = (univ_names_to_string us)
in (let _130_274 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _130_277 _130_276 _130_275 _130_274)))))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _39_531, _39_533) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_538 = (let _130_278 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _130_278))
in (match (_39_538) with
| (univs, t) -> begin
(

let _39_547 = (match ((let _130_279 = (FStar_Syntax_Subst.compress t)
in _130_279.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(bs, c)
end
| _39_544 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_39_547) with
| (tps, c) -> begin
(let _130_283 = (sli l)
in (let _130_282 = (univ_names_to_string univs)
in (let _130_281 = (binders_to_string " " tps)
in (let _130_280 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _130_283 _130_282 _130_281 _130_280)))))
end))
end))
end else begin
(let _130_286 = (sli l)
in (let _130_285 = (binders_to_string " " tps)
in (let _130_284 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _130_286 _130_285 _130_284))))
>>>>>>> master
end
end))


<<<<<<< HEAD
let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _129_295 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _129_295 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_39_550, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = _39_557; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_554; FStar_Syntax_Syntax.lbdef = _39_552})::[]), _39_563, _39_565, _39_567) -> begin
(let _129_299 = (lbname_to_string lb)
in (let _129_298 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _129_299 _129_298)))
end
| _39_571 -> begin
(let _129_302 = (let _129_301 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _129_301 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _129_302 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _129_307 = (sli m.FStar_Syntax_Syntax.name)
in (let _129_306 = (let _129_305 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _129_305 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _129_307 _129_306))))
=======
let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _130_291 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _130_291 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_39_552, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = _39_559; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_556; FStar_Syntax_Syntax.lbdef = _39_554})::[]), _39_565, _39_567, _39_569) -> begin
(let _130_295 = (lbname_to_string lb)
in (let _130_294 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _130_295 _130_294)))
end
| _39_573 -> begin
(let _130_298 = (let _130_297 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _130_297 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _130_298 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _130_303 = (sli m.FStar_Syntax_Syntax.name)
in (let _130_302 = (let _130_301 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _130_301 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _130_303 _130_302))))
>>>>>>> master


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _39_10 -> (match (_39_10) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
<<<<<<< HEAD
(let _129_311 = (FStar_Util.string_of_int i)
in (let _129_310 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _129_311 _129_310)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _129_313 = (bv_to_string x)
in (let _129_312 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _129_313 _129_312)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _129_315 = (bv_to_string x)
in (let _129_314 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _129_315 _129_314)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _129_317 = (FStar_Util.string_of_int i)
in (let _129_316 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _129_317 _129_316)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _129_318 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _129_318))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _129_321 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _129_321 (FStar_String.concat "; "))))
=======
(let _130_307 = (FStar_Util.string_of_int i)
in (let _130_306 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _130_307 _130_306)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _130_309 = (bv_to_string x)
in (let _130_308 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _130_309 _130_308)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _130_311 = (bv_to_string x)
in (let _130_310 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _130_311 _130_310)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _130_313 = (FStar_Util.string_of_int i)
in (let _130_312 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _130_313 _130_312)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _130_314 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _130_314))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _130_317 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _130_317 (FStar_String.concat "; "))))
>>>>>>> master




