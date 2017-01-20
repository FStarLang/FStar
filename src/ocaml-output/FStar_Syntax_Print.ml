
open Prims

let sli : FStar_Ident.lident  ->  Prims.string = (fun l -> (

let uu____4 = (FStar_Options.print_real_names ())
in (match (uu____4) with
| true -> begin
l.FStar_Ident.str
end
| uu____5 -> begin
l.FStar_Ident.ident.FStar_Ident.idText
end)))


let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> (sli l))


let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))


<<<<<<< HEAD
let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _0_379 = (let _0_378 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "#" _0_378))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _0_379)))

=======
let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _138_10 = (let _138_9 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "#" _138_9))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _138_10)))
>>>>>>> origin/master

let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____22 = (FStar_Options.print_real_names ())
in (match (uu____22) with
| true -> begin
(bv_to_string bv)
end
| uu____23 -> begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)))


<<<<<<< HEAD
let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _0_381 = (let _0_380 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "@" _0_380))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _0_381)))
=======
let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _138_16 = (let _138_15 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "@" _138_15))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _138_16)))
>>>>>>> origin/master


let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Syntax_Const.op_Addition), ("+")))::(((FStar_Syntax_Const.op_Subtraction), ("-")))::(((FStar_Syntax_Const.op_Multiply), ("*")))::(((FStar_Syntax_Const.op_Division), ("/")))::(((FStar_Syntax_Const.op_Eq), ("=")))::(((FStar_Syntax_Const.op_ColonEq), (":=")))::(((FStar_Syntax_Const.op_notEq), ("<>")))::(((FStar_Syntax_Const.op_And), ("&&")))::(((FStar_Syntax_Const.op_Or), ("||")))::(((FStar_Syntax_Const.op_LTE), ("<=")))::(((FStar_Syntax_Const.op_GTE), (">=")))::(((FStar_Syntax_Const.op_LT), ("<")))::(((FStar_Syntax_Const.op_GT), (">")))::(((FStar_Syntax_Const.op_Modulus), ("mod")))::(((FStar_Syntax_Const.and_lid), ("/\\")))::(((FStar_Syntax_Const.or_lid), ("\\/")))::(((FStar_Syntax_Const.imp_lid), ("==>")))::(((FStar_Syntax_Const.iff_lid), ("<==>")))::(((FStar_Syntax_Const.precedes_lid), ("<<")))::(((FStar_Syntax_Const.eq2_lid), ("==")))::(((FStar_Syntax_Const.eq3_lid), ("===")))::[]


let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Syntax_Const.op_Negation), ("not")))::(((FStar_Syntax_Const.op_Minus), ("-")))::(((FStar_Syntax_Const.not_lid), ("~")))::[]


let is_prim_op = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
end
<<<<<<< HEAD
| uu____105 -> begin
=======
| _39_25 -> begin
>>>>>>> origin/master
false
end))


let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
<<<<<<< HEAD
| uu____122 -> begin
=======
| _39_30 -> begin
>>>>>>> origin/master
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


<<<<<<< HEAD
let is_inr = (fun uu___193_169 -> (match (uu___193_169) with
| FStar_Util.Inl (uu____172) -> begin
false
end
| FStar_Util.Inr (uu____173) -> begin
=======
let is_inr = (fun _39_1 -> (match (_39_1) with
| FStar_Util.Inl (_39_40) -> begin
false
end
| FStar_Util.Inr (_39_43) -> begin
>>>>>>> origin/master
true
end))


<<<<<<< HEAD
let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___194_204 -> (match (uu___194_204) with
| (uu____208, Some (FStar_Syntax_Syntax.Implicit (uu____209))) -> begin
false
end
| uu____211 -> begin
=======
let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _39_2 -> (match (_39_2) with
| (_39_48, Some (FStar_Syntax_Syntax.Implicit (_39_50))) -> begin
false
end
| _39_55 -> begin
>>>>>>> origin/master
true
end)))))


<<<<<<< HEAD
let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (

let uu____222 = (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
in (match (uu____222) with
=======
let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _138_39 = (FStar_Syntax_Subst.compress e)
in _138_39.FStar_Syntax_Syntax.n)) with
>>>>>>> origin/master
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args = (filter_imp args)
in (

let exps = (FStar_List.map Prims.fst args)
<<<<<<< HEAD
in (

let uu____266 = ((is_lex_cons f) && ((FStar_List.length exps) = (Prims.parse_int "2")))
in (match (uu____266) with
| true -> begin
(

let uu____275 = (reconstruct_lex (FStar_List.nth exps (Prims.parse_int "1")))
in (match (uu____275) with
| Some (xs) -> begin
Some ((let _0_382 = (FStar_List.nth exps (Prims.parse_int "0"))
in (_0_382)::xs))
=======
in if ((is_lex_cons f) && ((FStar_List.length exps) = (Prims.parse_int "2"))) then begin
(match ((let _138_40 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex _138_40))) with
| Some (xs) -> begin
(let _138_42 = (let _138_41 = (FStar_List.nth exps (Prims.parse_int "0"))
in (_138_41)::xs)
in Some (_138_42))
>>>>>>> origin/master
end
| None -> begin
None
end))
end
<<<<<<< HEAD
| uu____306 -> begin
=======
| _39_67 -> begin
if (is_lex_top e) then begin
Some ([])
end else begin
>>>>>>> origin/master
None
end))))
end
| uu____310 -> begin
(

let uu____311 = (is_lex_top e)
in (match (uu____311) with
| true -> begin
Some ([])
end
| uu____321 -> begin
None
end))
end)))


let rec find = (fun f l -> (match (l) with
| [] -> begin
(failwith "blah")
end
| (hd)::tl -> begin
(

let uu____347 = (f hd)
in (match (uu____347) with
| true -> begin
hd
end
| uu____348 -> begin
(find f tl)
end))
end))


<<<<<<< HEAD
let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (Prims.snd (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)))


let infix_prim_op_to_string = (fun e -> (let _0_383 = (get_lid e)
in (find_lid _0_383 infix_prim_ops)))


let unary_prim_op_to_string = (fun e -> (let _0_384 = (get_lid e)
in (find_lid _0_384 unary_prim_ops)))


let quant_to_string = (fun t -> (let _0_385 = (get_lid t)
in (find_lid _0_385 quants)))
=======
let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _138_56 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _138_56)))


let infix_prim_op_to_string = (fun e -> (let _138_58 = (get_lid e)
in (find_lid _138_58 infix_prim_ops)))


let unary_prim_op_to_string = (fun e -> (let _138_60 = (get_lid e)
in (find_lid _138_60 unary_prim_ops)))


let quant_to_string = (fun t -> (let _138_62 = (get_lid t)
in (find_lid _138_62 quants)))
>>>>>>> origin/master


let const_to_string : FStar_Const.sconst  ->  Prims.string = (fun x -> (match (x) with
| FStar_Const.Const_effect -> begin
"Effect"
end
| FStar_Const.Const_unit -> begin
"()"
end
| FStar_Const.Const_bool (b) -> begin
(match (b) with
| true -> begin
"true"
end
| uu____403 -> begin
"false"
end)
end
| FStar_Const.Const_float (x) -> begin
(FStar_Util.string_of_float x)
end
<<<<<<< HEAD
| FStar_Const.Const_string (bytes, uu____406) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (uu____409) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x, uu____414) -> begin
=======
| FStar_Const.Const_string (bytes, _39_90) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_39_94) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x, _39_98) -> begin
>>>>>>> origin/master
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
<<<<<<< HEAD
(let _0_386 = (sli l)
in (FStar_Util.format1 "[[%s.reflect]]" _0_386))
end))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun uu___195_426 -> (match (uu___195_426) with
=======
(let _138_65 = (sli l)
in (FStar_Util.format1 "[[%s.reflect]]" _138_65))
end))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun _39_3 -> (match (_39_3) with
>>>>>>> origin/master
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
<<<<<<< HEAD
(let _0_387 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _0_387))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _0_388 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _0_388))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _0_389 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _0_389))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____443) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (uu____448) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (uu____449) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (uu____450) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (uu____465) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (uu____473) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (uu____478) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (uu____488) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____504) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (uu____517) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (uu____525) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (uu____534, m) -> begin
(

let uu____572 = (FStar_ST.read m)
in (match (uu____572) with
| None -> begin
"Tm_delayed"
end
| Some (uu____583) -> begin
=======
(let _138_70 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _138_70))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _138_71 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _138_71))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _138_72 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _138_72))
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
>>>>>>> origin/master
"Tm_delayed-resolved"
end))
end
<<<<<<< HEAD
| FStar_Syntax_Syntax.Tm_meta (uu____588) -> begin
=======
| FStar_Syntax_Syntax.Tm_meta (_39_163) -> begin
>>>>>>> origin/master
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))


let uvar_to_string = (fun u -> (

let uu____602 = (FStar_Options.hide_uvar_nums ())
in (match (uu____602) with
| true -> begin
"?"
<<<<<<< HEAD
end
| uu____603 -> begin
(let _0_391 = (let _0_390 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _0_390 FStar_Util.string_of_int))
in (Prims.strcat "?" _0_391))
end)))

=======
end else begin
(let _138_77 = (let _138_76 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _138_76 FStar_Util.string_of_int))
in (Prims.strcat "?" _138_77))
end)
>>>>>>> origin/master

let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe Prims.option) = (fun n u -> (

let uu____613 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____613) with
| FStar_Syntax_Syntax.U_zero -> begin
((n), (None))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(int_of_univ (n + (Prims.parse_int "1")) u)
end
<<<<<<< HEAD
| uu____619 -> begin
=======
| _39_173 -> begin
>>>>>>> origin/master
((n), (Some (u)))
end)))


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (

let uu____624 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____624) with
| FStar_Syntax_Syntax.U_unif (u) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
<<<<<<< HEAD
(let _0_392 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _0_392))
=======
(let _138_84 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _138_84))
>>>>>>> origin/master
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(

let uu____632 = (int_of_univ (Prims.parse_int "1") u)
in (match (uu____632) with
| (n, None) -> begin
(FStar_Util.string_of_int n)
end
| (n, Some (u)) -> begin
<<<<<<< HEAD
(let _0_394 = (univ_to_string u)
in (let _0_393 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 "(%s + %s)" _0_394 _0_393)))
end))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _0_396 = (let _0_395 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _0_395 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _0_396))
=======
(let _138_86 = (univ_to_string u)
in (let _138_85 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 "(%s + %s)" _138_86 _138_85)))
end)
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _138_88 = (let _138_87 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _138_87 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _138_88))
>>>>>>> origin/master
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end)))


<<<<<<< HEAD
let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _0_397 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _0_397 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _0_398 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _0_398 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun uu___196_659 -> (match (uu___196_659) with
=======
let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _138_91 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _138_91 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _138_95 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _138_95 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun _39_4 -> (match (_39_4) with
>>>>>>> origin/master
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
<<<<<<< HEAD
(let _0_399 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _0_399))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _0_400 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _0_400 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(let _0_403 = (FStar_Ident.text_of_path (FStar_Ident.path_of_ns ns))
in (let _0_402 = (let _0_401 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right _0_401 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" _0_403 _0_402)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(let _0_406 = (FStar_Ident.text_of_path (FStar_Ident.path_of_ns ns))
in (let _0_405 = (let _0_404 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right _0_404 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" _0_406 _0_405)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(let _0_407 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" _0_407))
=======
(let _138_98 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _138_98))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _138_99 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _138_99 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(let _138_103 = (let _138_100 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path _138_100))
in (let _138_102 = (let _138_101 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right _138_101 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" _138_103 _138_102)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(let _138_107 = (let _138_104 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path _138_104))
in (let _138_106 = (let _138_105 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right _138_105 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" _138_107 _138_106)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(let _138_108 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" _138_108))
>>>>>>> origin/master
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
<<<<<<< HEAD
| uu____688 -> begin
(let _0_408 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _0_408 (FStar_String.concat " ")))
=======
| _39_237 -> begin
(let _138_111 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _138_111 (FStar_String.concat " ")))
>>>>>>> origin/master
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
<<<<<<< HEAD
| uu____698 -> begin
(let _0_409 = (quals_to_string quals)
in (Prims.strcat _0_409 " "))
=======
| _39_241 -> begin
(let _138_114 = (quals_to_string quals)
in (Prims.strcat _138_114 " "))
>>>>>>> origin/master
end))


let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let x = (FStar_Syntax_Subst.compress x)
in (

let x = (

let uu____755 = (FStar_Options.print_implicits ())
in (match (uu____755) with
| true -> begin
x
end
| uu____756 -> begin
(FStar_Syntax_Util.unmeta x)
end))
in (match (x.FStar_Syntax_Syntax.n) with
<<<<<<< HEAD
| FStar_Syntax_Syntax.Tm_delayed (uu____757) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (uu____778, []) -> begin
=======
| FStar_Syntax_Syntax.Tm_delayed (_39_245) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_39_248, []) -> begin
>>>>>>> origin/master
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

<<<<<<< HEAD
let pats = (let _0_411 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _0_410 = (FStar_All.pipe_right args (FStar_List.map (fun uu____827 -> (match (uu____827) with
| (t, uu____831) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _0_410 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _0_411 (FStar_String.concat "\\/")))
in (let _0_412 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _0_412)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _0_416 = (tag_of_term t)
in (let _0_415 = (sli m)
in (let _0_414 = (term_to_string t')
in (let _0_413 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" _0_416 _0_415 _0_414 _0_413)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(let _0_421 = (tag_of_term t)
in (let _0_420 = (term_to_string t')
in (let _0_419 = (sli m0)
in (let _0_418 = (sli m1)
in (let _0_417 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" _0_421 _0_420 _0_419 _0_418 _0_417))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(let _0_423 = (FStar_Range.string_of_range r)
in (let _0_422 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l _0_423 _0_422)))
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____864) -> begin
=======
let pats = (let _138_140 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _138_139 = (FStar_All.pipe_right args (FStar_List.map (fun _39_261 -> (match (_39_261) with
| (t, _39_260) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _138_139 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _138_140 (FStar_String.concat "\\/")))
in (let _138_141 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _138_141)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _138_145 = (tag_of_term t)
in (let _138_144 = (sli m)
in (let _138_143 = (term_to_string t')
in (let _138_142 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" _138_145 _138_144 _138_143 _138_142)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(let _138_150 = (tag_of_term t)
in (let _138_149 = (term_to_string t')
in (let _138_148 = (sli m0)
in (let _138_147 = (sli m1)
in (let _138_146 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" _138_150 _138_149 _138_148 _138_147 _138_146))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(let _138_152 = (FStar_Range.string_of_range r)
in (let _138_151 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l _138_152 _138_151)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _39_288) -> begin
>>>>>>> origin/master
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
<<<<<<< HEAD
| FStar_Syntax_Syntax.Tm_uvar (u, uu____873) -> begin
=======
| FStar_Syntax_Syntax.Tm_uvar (u, _39_299) -> begin
>>>>>>> origin/master
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
<<<<<<< HEAD
(

let uu____891 = (FStar_Options.print_universes ())
in (match (uu____891) with
| true -> begin
(let _0_424 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _0_424))
=======
if (FStar_Options.print_universes ()) then begin
(let _138_153 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _138_153))
end else begin
"Type"
>>>>>>> origin/master
end
| uu____892 -> begin
"Type"
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
<<<<<<< HEAD
(let _0_426 = (binders_to_string " -> " bs)
in (let _0_425 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _0_426 _0_425)))
=======
(let _138_155 = (binders_to_string " -> " bs)
in (let _138_154 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _138_155 _138_154)))
>>>>>>> origin/master
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
<<<<<<< HEAD
(let _0_430 = (binders_to_string " " bs)
in (let _0_429 = (term_to_string t2)
in (let _0_428 = (let _0_427 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _0_427))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _0_430 _0_429 _0_428))))
end
| Some (FStar_Util.Inr (l, flags)) when (FStar_Options.print_implicits ()) -> begin
(let _0_432 = (binders_to_string " " bs)
in (let _0_431 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))" _0_432 _0_431 l.FStar_Ident.str)))
end
| uu____951 -> begin
(let _0_434 = (binders_to_string " " bs)
in (let _0_433 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _0_434 _0_433)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _0_437 = (bv_to_string xt)
in (let _0_436 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _0_435 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _0_437 _0_436 _0_435))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _0_439 = (term_to_string t)
in (let _0_438 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _0_439 _0_438)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _0_441 = (lbs_to_string [] lbs)
in (let _0_440 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _0_441 _0_440)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), eff_name) -> begin
(let _0_445 = (term_to_string e)
in (let _0_444 = (let _0_442 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right _0_442 (FStar_Util.dflt "default")))
in (let _0_443 = (term_to_string t)
in (FStar_Util.format3 "(%s <: [%s] %s)" _0_445 _0_444 _0_443))))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), uu____1020) -> begin
(let _0_447 = (term_to_string e)
in (let _0_446 = (comp_to_string c)
in (FStar_Util.format2 "(%s <: %s)" _0_447 _0_446)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _0_454 = (term_to_string head)
in (let _0_453 = (let _0_452 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____1083 -> (match (uu____1083) with
| (p, wopt, e) -> begin
(let _0_451 = (FStar_All.pipe_right p pat_to_string)
in (let _0_450 = (match (wopt) with
=======
(let _138_159 = (binders_to_string " " bs)
in (let _138_158 = (term_to_string t2)
in (let _138_157 = (let _138_156 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _138_156))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _138_159 _138_158 _138_157))))
end
| Some (FStar_Util.Inr (l, flags)) when (FStar_Options.print_implicits ()) -> begin
(let _138_161 = (binders_to_string " " bs)
in (let _138_160 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))" _138_161 _138_160 l.FStar_Ident.str)))
end
| _39_324 -> begin
(let _138_163 = (binders_to_string " " bs)
in (let _138_162 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _138_163 _138_162)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _138_166 = (bv_to_string xt)
in (let _138_165 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _138_164 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _138_166 _138_165 _138_164))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _138_168 = (term_to_string t)
in (let _138_167 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _138_168 _138_167)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _138_170 = (lbs_to_string [] lbs)
in (let _138_169 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _138_170 _138_169)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), eff_name) -> begin
(let _138_174 = (term_to_string e)
in (let _138_173 = (let _138_171 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right _138_171 (FStar_Util.dflt "default")))
in (let _138_172 = (term_to_string t)
in (FStar_Util.format3 "(%s <: [%s] %s)" _138_174 _138_173 _138_172))))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _39_347) -> begin
(let _138_176 = (term_to_string e)
in (let _138_175 = (comp_to_string c)
in (FStar_Util.format2 "(%s <: %s)" _138_176 _138_175)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _138_184 = (term_to_string head)
in (let _138_183 = (let _138_182 = (FStar_All.pipe_right branches (FStar_List.map (fun _39_357 -> (match (_39_357) with
| (p, wopt, e) -> begin
(let _138_181 = (FStar_All.pipe_right p pat_to_string)
in (let _138_180 = (match (wopt) with
>>>>>>> origin/master
| None -> begin
""
end
| Some (w) -> begin
<<<<<<< HEAD
(let _0_448 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _0_448))
end)
in (let _0_449 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _0_451 _0_450 _0_449))))
end))))
in (FStar_Util.concat_l "\n\t|" _0_452))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _0_454 _0_453)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let uu____1100 = (FStar_Options.print_universes ())
in (match (uu____1100) with
| true -> begin
(let _0_456 = (term_to_string t)
in (let _0_455 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _0_456 _0_455)))
=======
(let _138_178 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _138_178))
end)
in (let _138_179 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _138_181 _138_180 _138_179))))
end))))
in (FStar_Util.concat_l "\n\t|" _138_182))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _138_184 _138_183)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_Options.print_universes ()) then begin
(let _138_186 = (term_to_string t)
in (let _138_185 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _138_186 _138_185)))
end else begin
(term_to_string t)
>>>>>>> origin/master
end
| uu____1101 -> begin
(term_to_string t)
end))
end
<<<<<<< HEAD
| uu____1102 -> begin
=======
| _39_366 -> begin
>>>>>>> origin/master
(tag_of_term x)
end))))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
<<<<<<< HEAD
(let _0_459 = (fv_to_string l)
in (let _0_458 = (let _0_457 = (FStar_List.map (fun uu____1119 -> (match (uu____1119) with
=======
(let _138_191 = (fv_to_string l)
in (let _138_190 = (let _138_189 = (FStar_List.map (fun _39_374 -> (match (_39_374) with
>>>>>>> origin/master
| (x, b) -> begin
(

let p = (pat_to_string x)
in (match (b) with
| true -> begin
(Prims.strcat "#" p)
end
| uu____1125 -> begin
p
end))
end)) pats)
<<<<<<< HEAD
in (FStar_All.pipe_right _0_457 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _0_459 _0_458)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____1127) -> begin
(

let uu____1132 = (FStar_Options.print_bound_var_types ())
in (match (uu____1132) with
| true -> begin
(let _0_461 = (bv_to_string x)
in (let _0_460 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" _0_461 _0_460)))
=======
in (FStar_All.pipe_right _138_189 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _138_191 _138_190)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _39_378) -> begin
if (FStar_Options.print_bound_var_types ()) then begin
(let _138_193 = (bv_to_string x)
in (let _138_192 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" _138_193 _138_192)))
end else begin
(let _138_194 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _138_194))
>>>>>>> origin/master
end
| uu____1133 -> begin
(let _0_462 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _0_462))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
<<<<<<< HEAD
(

let uu____1135 = (FStar_Options.print_bound_var_types ())
in (match (uu____1135) with
| true -> begin
(let _0_464 = (bv_to_string x)
in (let _0_463 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" _0_464 _0_463)))
=======
if (FStar_Options.print_bound_var_types ()) then begin
(let _138_196 = (bv_to_string x)
in (let _138_195 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" _138_196 _138_195)))
end else begin
(bv_to_string x)
>>>>>>> origin/master
end
| uu____1136 -> begin
(bv_to_string x)
end))
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
<<<<<<< HEAD
(

let uu____1139 = (FStar_Options.print_real_names ())
in (match (uu____1139) with
| true -> begin
(let _0_465 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _0_465))
=======
if (FStar_Options.print_real_names ()) then begin
(let _138_197 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _138_197))
end else begin
"_"
>>>>>>> origin/master
end
| uu____1140 -> begin
"_"
end))
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
<<<<<<< HEAD
(let _0_466 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _0_466))
=======
(let _138_198 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _138_198))
>>>>>>> origin/master
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  Prims.string = (fun quals lbs -> (

let lbs = (

<<<<<<< HEAD
let uu____1155 = (FStar_Options.print_universes ())
in (match (uu____1155) with
| true -> begin
(let _0_468 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let uu____1165 = (let _0_467 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _0_467))
in (match (uu____1165) with
| (us, td) -> begin
(

let uu____1170 = (

let uu____1177 = (FStar_Syntax_Subst.compress td).FStar_Syntax_Syntax.n
in (match (uu____1177) with
| FStar_Syntax_Syntax.Tm_app (uu____1184, ((t, uu____1186))::((d, uu____1188))::[]) -> begin
((t), (d))
end
| uu____1222 -> begin
(failwith "Impossibe")
end))
in (match (uu____1170) with
| (t, d) -> begin
(

let uu___203_1239 = lb
in {FStar_Syntax_Syntax.lbname = uu___203_1239.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu___203_1239.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((Prims.fst lbs)), (_0_468)))
end
| uu____1240 -> begin
lbs
end))
in (let _0_477 = (quals_to_string' quals)
in (let _0_476 = (let _0_475 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _0_474 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _0_473 = (

let uu____1247 = (FStar_Options.print_universes ())
in (match (uu____1247) with
| true -> begin
(let _0_470 = (let _0_469 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat _0_469 ">"))
in (Prims.strcat "<" _0_470))
end
| uu____1248 -> begin
""
end))
in (let _0_472 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _0_471 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _0_474 _0_473 _0_472 _0_471))))))))
in (FStar_Util.concat_l "\n and " _0_475))
in (FStar_Util.format3 "%slet %s %s" _0_477 (match ((Prims.fst lbs)) with
| true -> begin
=======
let lbs = if (FStar_Options.print_universes ()) then begin
(let _138_204 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _39_394 = (let _138_202 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _138_202))
in (match (_39_394) with
| (us, td) -> begin
(

let _39_412 = (match ((let _138_203 = (FStar_Syntax_Subst.compress td)
in _138_203.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_39_396, ((t, _39_403))::((d, _39_399))::[]) -> begin
((t), (d))
end
| _39_409 -> begin
(failwith "Impossibe")
end)
in (match (_39_412) with
| (t, d) -> begin
(

let _39_413 = lb
in {FStar_Syntax_Syntax.lbname = _39_413.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_413.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((Prims.fst lbs)), (_138_204)))
end else begin
lbs
end
in (let _138_214 = (quals_to_string' quals)
in (let _138_213 = (let _138_212 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _138_211 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _138_210 = if (FStar_Options.print_universes ()) then begin
(let _138_207 = (let _138_206 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat _138_206 ">"))
in (Prims.strcat "<" _138_207))
end else begin
""
end
in (let _138_209 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _138_208 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _138_211 _138_210 _138_209 _138_208))))))))
in (FStar_Util.concat_l "\n and " _138_212))
in (FStar_Util.format3 "%slet %s %s" _138_214 (if (Prims.fst lbs) then begin
>>>>>>> origin/master
"rec"
end
| uu____1242 -> begin
""
<<<<<<< HEAD
end) _0_476)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (

let uu____1252 = (FStar_Options.print_effect_args ())
in (match (uu____1252) with
| true -> begin
(comp_to_string (lc.FStar_Syntax_Syntax.comp ()))
end
| uu____1253 -> begin
(let _0_479 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _0_478 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _0_479 _0_478)))
end)))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s uu___197_1255 -> (match (uu___197_1255) with
=======
end) _138_213)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> if (FStar_Options.print_effect_args ()) then begin
(let _138_216 = (lc.FStar_Syntax_Syntax.comp ())
in (comp_to_string _138_216))
end else begin
(let _138_218 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _138_217 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _138_218 _138_217)))
end)
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s _39_5 -> (match (_39_5) with
>>>>>>> origin/master
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
| uu____1257 -> begin
=======
| _39_429 -> begin
>>>>>>> origin/master
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun is_arrow b -> (

<<<<<<< HEAD
let uu____1263 = b
in (match (uu____1263) with
| (a, imp) -> begin
(

let uu____1268 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____1268) with
| true -> begin
(let _0_480 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" _0_480))
=======
let _39_434 = b
in (match (_39_434) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(let _138_223 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" _138_223))
end else begin
if ((not (is_arrow)) && (not ((FStar_Options.print_bound_var_types ())))) then begin
(let _138_224 = (nm_to_string a)
in (imp_to_string _138_224 imp))
end else begin
(let _138_228 = (let _138_227 = (nm_to_string a)
in (let _138_226 = (let _138_225 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" _138_225))
in (Prims.strcat _138_227 _138_226)))
in (imp_to_string _138_228 imp))
end
>>>>>>> origin/master
end
| uu____1269 -> begin
(

let uu____1270 = ((not (is_arrow)) && (not ((FStar_Options.print_bound_var_types ()))))
in (match (uu____1270) with
| true -> begin
(let _0_481 = (nm_to_string a)
in (imp_to_string _0_481 imp))
end
| uu____1271 -> begin
(let _0_485 = (let _0_484 = (nm_to_string a)
in (let _0_483 = (let _0_482 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" _0_482))
in (Prims.strcat _0_484 _0_483)))
in (imp_to_string _0_485 imp))
end))
end))
end)))
and binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (

let bs = (

let uu____1281 = (FStar_Options.print_implicits ())
in (match (uu____1281) with
| true -> begin
bs
end
<<<<<<< HEAD
| uu____1282 -> begin
(filter_imp bs)
end))
in (match ((sep = " -> ")) with
| true -> begin
(let _0_486 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _0_486 (FStar_String.concat sep)))
end
| uu____1287 -> begin
(let _0_487 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _0_487 (FStar_String.concat sep)))
end)))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun uu___198_1292 -> (match (uu___198_1292) with
| (a, imp) -> begin
(let _0_488 = (term_to_string a)
in (imp_to_string _0_488 imp))
=======
in if (sep = " -> ") then begin
(let _138_233 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _138_233 (FStar_String.concat sep)))
end else begin
(let _138_234 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _138_234 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _39_6 -> (match (_39_6) with
| (a, imp) -> begin
(let _138_236 = (term_to_string a)
in (imp_to_string _138_236 imp))
>>>>>>> origin/master
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args = (

let uu____1302 = (FStar_Options.print_implicits ())
in (match (uu____1302) with
| true -> begin
args
end
<<<<<<< HEAD
| uu____1303 -> begin
(filter_imp args)
end))
in (let _0_489 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _0_489 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____1313) -> begin
(

let uu____1320 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____1320) with
| FStar_Syntax_Syntax.Tm_type (uu____1321) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| uu____1322 -> begin
(let _0_490 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _0_490))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____1324) -> begin
(

let uu____1331 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____1331) with
| FStar_Syntax_Syntax.Tm_type (uu____1332) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| uu____1333 -> begin
(let _0_491 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _0_491))
end))
=======
in (let _138_238 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _138_238 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _39_449) -> begin
(match ((let _138_240 = (FStar_Syntax_Subst.compress t)
in _138_240.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_453) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_456 -> begin
(let _138_241 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _138_241))
end)
end
| FStar_Syntax_Syntax.GTotal (t, _39_459) -> begin
(match ((let _138_242 = (FStar_Syntax_Subst.compress t)
in _138_242.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_463) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| _39_466 -> begin
(let _138_243 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _138_243))
end)
>>>>>>> origin/master
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

<<<<<<< HEAD
let basic = (

let uu____1336 = (FStar_Options.print_effect_args ())
in (match (uu____1336) with
| true -> begin
(let _0_497 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _0_496 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _0_495 = (let _0_492 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _0_492 (FStar_String.concat ", ")))
in (let _0_494 = (let _0_493 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right _0_493 (FStar_String.concat " ")))
in (FStar_Util.format4 "%s (%s) %s (attributes %s)" _0_497 _0_496 _0_495 _0_494)))))
end
| uu____1350 -> begin
(

let uu____1351 = ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___199_1353 -> (match (uu___199_1353) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____1354 -> begin
false
end)))) && (not ((FStar_Options.print_effect_args ()))))
in (match (uu____1351) with
| true -> begin
(let _0_498 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _0_498))
end
| uu____1355 -> begin
(

let uu____1356 = (((not ((FStar_Options.print_effect_args ()))) && (not ((FStar_Options.print_implicits ())))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid))
in (match (uu____1356) with
| true -> begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end
| uu____1357 -> begin
(

let uu____1358 = ((not ((FStar_Options.print_effect_args ()))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___200_1360 -> (match (uu___200_1360) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____1361 -> begin
false
end)))))
in (match (uu____1358) with
| true -> begin
(let _0_499 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _0_499))
end
| uu____1362 -> begin
(let _0_501 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _0_500 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _0_501 _0_500)))
end))
end))
end))
end))
in (

let dec = (let _0_504 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun uu___201_1367 -> (match (uu___201_1367) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _0_503 = (let _0_502 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _0_502))
in (_0_503)::[])
end
| uu____1372 -> begin
[]
end))))
in (FStar_All.pipe_right _0_504 (FStar_String.concat " ")))
=======
let basic = if (FStar_Options.print_effect_args ()) then begin
(let _138_249 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _138_248 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _138_247 = (let _138_244 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _138_244 (FStar_String.concat ", ")))
in (let _138_246 = (let _138_245 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right _138_245 (FStar_String.concat " ")))
in (FStar_Util.format4 "%s (%s) %s (attributes %s)" _138_249 _138_248 _138_247 _138_246)))))
end else begin
if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_7 -> (match (_39_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _39_472 -> begin
false
end)))) && (not ((FStar_Options.print_effect_args ())))) then begin
(let _138_251 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _138_251))
end else begin
if (((not ((FStar_Options.print_effect_args ()))) && (not ((FStar_Options.print_implicits ())))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_Options.print_effect_args ()))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_8 -> (match (_39_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _39_476 -> begin
false
end))))) then begin
(let _138_253 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _138_253))
end else begin
(let _138_255 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _138_254 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _138_255 _138_254)))
end
end
end
end
in (

let dec = (let _138_259 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _39_9 -> (match (_39_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _138_258 = (let _138_257 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _138_257))
in (_138_258)::[])
end
| _39_482 -> begin
[]
end))))
in (FStar_All.pipe_right _138_259 (FStar_String.concat " ")))
>>>>>>> origin/master
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
<<<<<<< HEAD
| FStar_Syntax_Syntax.DECREASES (uu____1374) -> begin
=======
| FStar_Syntax_Syntax.DECREASES (_39_493) -> begin
>>>>>>> origin/master
""
end))
and formula_to_string : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun phi -> (term_to_string phi))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> (

let uu____1383 = (FStar_Options.print_universes ())
in (match (uu____1383) with
| true -> begin
(Prims.strcat "<" (Prims.strcat s ">"))
end
| uu____1384 -> begin
""
end)))


<<<<<<< HEAD
let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun uu____1387 -> (match (uu____1387) with
| (us, t) -> begin
(let _0_507 = (let _0_505 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes _0_505))
in (let _0_506 = (term_to_string t)
in (FStar_Util.format2 "%s%s" _0_507 _0_506)))
=======
let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun _39_499 -> (match (_39_499) with
| (us, t) -> begin
(let _138_268 = (let _138_266 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes _138_266))
in (let _138_267 = (term_to_string t)
in (FStar_Util.format2 "%s%s" _138_268 _138_267)))
>>>>>>> origin/master
end))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (

<<<<<<< HEAD
let actions_to_string = (fun actions -> (let _0_513 = (FStar_All.pipe_right actions (FStar_List.map (fun a -> (let _0_512 = (sli a.FStar_Syntax_Syntax.action_name)
in (let _0_511 = (let _0_508 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes _0_508))
in (let _0_510 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (let _0_509 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format4 "%s%s : %s = %s" _0_512 _0_511 _0_510 _0_509))))))))
in (FStar_All.pipe_right _0_513 (FStar_String.concat ",\n\t"))))
in (let _0_551 = (let _0_550 = (let _0_549 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _0_548 = (let _0_547 = (let _0_514 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes _0_514))
in (let _0_546 = (let _0_545 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _0_544 = (let _0_543 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _0_542 = (let _0_541 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (let _0_540 = (let _0_539 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _0_538 = (let _0_537 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _0_536 = (let _0_535 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _0_534 = (let _0_533 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (let _0_532 = (let _0_531 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _0_530 = (let _0_529 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _0_528 = (let _0_527 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _0_526 = (let _0_525 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _0_524 = (let _0_523 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (let _0_522 = (let _0_521 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _0_520 = (let _0_519 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (let _0_518 = (let _0_517 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (let _0_516 = (let _0_515 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (_0_515)::[])
in (_0_517)::_0_516))
in (_0_519)::_0_518))
in (_0_521)::_0_520))
in (_0_523)::_0_522))
in (_0_525)::_0_524))
in (_0_527)::_0_526))
in (_0_529)::_0_528))
in (_0_531)::_0_530))
in (_0_533)::_0_532))
in (_0_535)::_0_534))
in (_0_537)::_0_536))
in (_0_539)::_0_538))
in (_0_541)::_0_540))
in (_0_543)::_0_542))
in (_0_545)::_0_544))
in (_0_547)::_0_546))
in (_0_549)::_0_548))
in ((match (for_free) with
| true -> begin
=======
let actions_to_string = (fun actions -> (let _138_281 = (FStar_All.pipe_right actions (FStar_List.map (fun a -> (let _138_280 = (sli a.FStar_Syntax_Syntax.action_name)
in (let _138_279 = (let _138_276 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes _138_276))
in (let _138_278 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (let _138_277 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format4 "%s%s : %s = %s" _138_280 _138_279 _138_278 _138_277))))))))
in (FStar_All.pipe_right _138_281 (FStar_String.concat ",\n\t"))))
in (let _138_319 = (let _138_318 = (let _138_317 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _138_316 = (let _138_315 = (let _138_282 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes _138_282))
in (let _138_314 = (let _138_313 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _138_312 = (let _138_311 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _138_310 = (let _138_309 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (let _138_308 = (let _138_307 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _138_306 = (let _138_305 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _138_304 = (let _138_303 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _138_302 = (let _138_301 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (let _138_300 = (let _138_299 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _138_298 = (let _138_297 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _138_296 = (let _138_295 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _138_294 = (let _138_293 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _138_292 = (let _138_291 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (let _138_290 = (let _138_289 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _138_288 = (let _138_287 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (let _138_286 = (let _138_285 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (let _138_284 = (let _138_283 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (_138_283)::[])
in (_138_285)::_138_284))
in (_138_287)::_138_286))
in (_138_289)::_138_288))
in (_138_291)::_138_290))
in (_138_293)::_138_292))
in (_138_295)::_138_294))
in (_138_297)::_138_296))
in (_138_299)::_138_298))
in (_138_301)::_138_300))
in (_138_303)::_138_302))
in (_138_305)::_138_304))
in (_138_307)::_138_306))
in (_138_309)::_138_308))
in (_138_311)::_138_310))
in (_138_313)::_138_312))
in (_138_315)::_138_314))
in (_138_317)::_138_316))
in (if for_free then begin
>>>>>>> origin/master
"_for_free "
end
| uu____1408 -> begin
""
<<<<<<< HEAD
end))::_0_550)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" _0_551))))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None), uu____1412) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s)), uu____1414) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), uu____1416) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, uu____1421, uu____1422, quals, uu____1424) -> begin
(let _0_554 = (quals_to_string' quals)
in (let _0_553 = (binders_to_string " " tps)
in (let _0_552 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" _0_554 lid.FStar_Ident.str _0_553 _0_552))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, uu____1434, uu____1435, uu____1436, uu____1437, uu____1438) -> begin
(

let uu____1443 = (FStar_Options.print_universes ())
in (match (uu____1443) with
| true -> begin
(

let uu____1444 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (uu____1444) with
| (univs, t) -> begin
(let _0_556 = (univ_names_to_string univs)
in (let _0_555 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _0_556 lid.FStar_Ident.str _0_555)))
end))
=======
end)::_138_318)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" _138_319))))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None), _39_509) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s)), _39_516) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _39_522) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _39_530, _39_532, quals, _39_535) -> begin
(let _138_324 = (quals_to_string' quals)
in (let _138_323 = (binders_to_string " " tps)
in (let _138_322 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" _138_324 lid.FStar_Ident.str _138_323 _138_322))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _39_542, _39_544, _39_546, _39_548, _39_550) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_555 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_555) with
| (univs, t) -> begin
(let _138_326 = (univ_names_to_string univs)
in (let _138_325 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _138_326 lid.FStar_Ident.str _138_325)))
end))
end else begin
(let _138_327 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _138_327))
>>>>>>> origin/master
end
| uu____1449 -> begin
(let _0_557 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _0_557))
end))
end
<<<<<<< HEAD
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, uu____1454) -> begin
(

let uu____1457 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (uu____1457) with
| (univs, t) -> begin
(let _0_561 = (quals_to_string' quals)
in (let _0_560 = (

let uu____1462 = (FStar_Options.print_universes ())
in (match (uu____1462) with
| true -> begin
(let _0_558 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _0_558))
end
| uu____1463 -> begin
""
end))
in (let _0_559 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" _0_561 lid.FStar_Ident.str _0_560 _0_559))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, uu____1466, uu____1467) -> begin
(let _0_562 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _0_562))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____1471, uu____1472, qs, uu____1474) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, uu____1482) -> begin
(let _0_563 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _0_563))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____1484, uu____1485, uu____1486) -> begin
(let _0_564 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _0_564 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, uu____1495) -> begin
(eff_decl_to_string false ed)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed, uu____1497) -> begin
=======
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _39_561) -> begin
(

let _39_566 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_39_566) with
| (univs, t) -> begin
(let _138_331 = (quals_to_string' quals)
in (let _138_330 = if (FStar_Options.print_universes ()) then begin
(let _138_328 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _138_328))
end else begin
""
end
in (let _138_329 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" _138_331 lid.FStar_Ident.str _138_330 _138_329))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _39_570, _39_572) -> begin
(let _138_332 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _138_332))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _39_577, _39_579, qs, _39_582) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _39_587) -> begin
(let _138_333 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _138_333))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _39_592, _39_594, _39_596) -> begin
(let _138_334 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _138_334 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _39_601) -> begin
(eff_decl_to_string false ed)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed, _39_606) -> begin
>>>>>>> origin/master
(eff_decl_to_string true ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(

let lift_wp = (match (((se.FStar_Syntax_Syntax.lift_wp), (se.FStar_Syntax_Syntax.lift))) with
| (None, None) -> begin
(failwith "impossible")
end
<<<<<<< HEAD
| (Some (lift_wp), uu____1506) -> begin
lift_wp
end
| (uu____1510, Some (lift)) -> begin
=======
| (Some (lift_wp), _39_619) -> begin
lift_wp
end
| (_39_622, Some (lift)) -> begin
>>>>>>> origin/master
lift
end)
in (

<<<<<<< HEAD
let uu____1515 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp) (Prims.snd lift_wp))
in (match (uu____1515) with
| (us, t) -> begin
(let _0_568 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _0_567 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _0_566 = (univ_names_to_string us)
in (let _0_565 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _0_568 _0_567 _0_566 _0_565)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, uu____1526, flags, uu____1528) -> begin
(

let uu____1533 = (FStar_Options.print_universes ())
in (match (uu____1533) with
| true -> begin
(

let uu____1534 = (let _0_569 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c))))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _0_569))
in (match (uu____1534) with
| (univs, t) -> begin
(

let uu____1551 = (

let uu____1559 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____1559) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((bs), (c))
end
| uu____1584 -> begin
(failwith "impossible")
end))
in (match (uu____1551) with
| (tps, c) -> begin
(let _0_573 = (sli l)
in (let _0_572 = (univ_names_to_string univs)
in (let _0_571 = (binders_to_string " " tps)
in (let _0_570 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _0_573 _0_572 _0_571 _0_570)))))
end))
end))
=======
let _39_629 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp) (Prims.snd lift_wp))
in (match (_39_629) with
| (us, t) -> begin
(let _138_338 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _138_337 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _138_336 = (univ_names_to_string us)
in (let _138_335 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _138_338 _138_337 _138_336 _138_335)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _39_635, flags, _39_638) -> begin
if (FStar_Options.print_universes ()) then begin
(

let _39_643 = (let _138_339 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _138_339))
in (match (_39_643) with
| (univs, t) -> begin
(

let _39_652 = (match ((let _138_340 = (FStar_Syntax_Subst.compress t)
in _138_340.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((bs), (c))
end
| _39_649 -> begin
(failwith "impossible")
end)
in (match (_39_652) with
| (tps, c) -> begin
(let _138_344 = (sli l)
in (let _138_343 = (univ_names_to_string univs)
in (let _138_342 = (binders_to_string " " tps)
in (let _138_341 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _138_344 _138_343 _138_342 _138_341)))))
end))
end))
end else begin
(let _138_347 = (sli l)
in (let _138_346 = (binders_to_string " " tps)
in (let _138_345 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _138_347 _138_346 _138_345))))
>>>>>>> origin/master
end
| uu____1604 -> begin
(let _0_576 = (sli l)
in (let _0_575 = (binders_to_string " " tps)
in (let _0_574 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _0_576 _0_575 _0_574))))
end))
end))


<<<<<<< HEAD
let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _0_577 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _0_577 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((uu____1614, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = uu____1616; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____1618; FStar_Syntax_Syntax.lbdef = uu____1619})::[]), uu____1620, uu____1621, uu____1622, uu____1623) -> begin
(let _0_579 = (lbname_to_string lb)
in (let _0_578 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _0_579 _0_578)))
end
| uu____1641 -> begin
(let _0_580 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right _0_580 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _0_583 = (sli m.FStar_Syntax_Syntax.name)
in (let _0_582 = (let _0_581 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _0_581 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _0_583 _0_582))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun uu___202_1652 -> (match (uu___202_1652) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(let _0_585 = (FStar_Util.string_of_int i)
in (let _0_584 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _0_585 _0_584)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _0_587 = (bv_to_string x)
in (let _0_586 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _0_587 _0_586)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _0_589 = (bv_to_string x)
in (let _0_588 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _0_589 _0_588)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _0_591 = (FStar_Util.string_of_int i)
in (let _0_590 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _0_591 _0_590)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _0_592 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _0_592))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _0_593 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _0_593 (FStar_String.concat "; "))))
=======
let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _138_352 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _138_352 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_39_657, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = _39_664; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _39_661; FStar_Syntax_Syntax.lbdef = _39_659})::[]), _39_670, _39_672, _39_674, _39_676) -> begin
(let _138_356 = (lbname_to_string lb)
in (let _138_355 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _138_356 _138_355)))
end
| _39_680 -> begin
(let _138_358 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right _138_358 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _138_363 = (sli m.FStar_Syntax_Syntax.name)
in (let _138_362 = (let _138_361 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _138_361 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _138_363 _138_362))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _39_10 -> (match (_39_10) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(let _138_367 = (FStar_Util.string_of_int i)
in (let _138_366 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _138_367 _138_366)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _138_369 = (bv_to_string x)
in (let _138_368 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _138_369 _138_368)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _138_371 = (bv_to_string x)
in (let _138_370 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _138_371 _138_370)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _138_373 = (FStar_Util.string_of_int i)
in (let _138_372 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _138_373 _138_372)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _138_374 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _138_374))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _138_377 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _138_377 (FStar_String.concat "; "))))
>>>>>>> origin/master


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
<<<<<<< HEAD
in ((match (ascription) with
=======
in (

let _39_718 = (match (ascription) with
>>>>>>> origin/master
| None -> begin
(FStar_Util.string_builder_append strb "None")
end
| Some (FStar_Util.Inl (lc)) -> begin
<<<<<<< HEAD
((FStar_Util.string_builder_append strb "Some Inr ");
(FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name));
)
end
| Some (FStar_Util.Inr (lid)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lid));
)
end);
(FStar_Util.string_of_string_builder strb);
)))
=======
(

let _39_711 = (FStar_Util.string_builder_append strb "Some Inr ")
in (FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name)))
end
| Some (FStar_Util.Inr (lid)) -> begin
(

let _39_716 = (FStar_Util.string_builder_append strb "Some Inr ")
in (FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lid)))
end)
in (FStar_Util.string_of_string_builder strb))))
>>>>>>> origin/master


let list_to_string = (fun f elts -> (match (elts) with
| [] -> begin
"[]"
end
| (x)::xs -> begin
(

let strb = (FStar_Util.new_string_builder ())
<<<<<<< HEAD
in ((FStar_Util.string_builder_append strb "{");
(let _0_594 = (f x)
in (FStar_Util.string_builder_append strb _0_594));
(FStar_List.iter (fun x -> ((FStar_Util.string_builder_append strb ", ");
(let _0_595 = (f x)
in (FStar_Util.string_builder_append strb _0_595));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))
=======
in (

let _39_727 = (FStar_Util.string_builder_append strb "[")
in (

let _39_729 = (let _138_385 = (f x)
in (FStar_Util.string_builder_append strb _138_385))
in (

let _39_734 = (FStar_List.iter (fun x -> (

let _39_732 = (FStar_Util.string_builder_append strb "; ")
in (let _138_387 = (f x)
in (FStar_Util.string_builder_append strb _138_387)))) xs)
in (

let _39_736 = (FStar_Util.string_builder_append strb "]")
in (FStar_Util.string_of_string_builder strb))))))
end))
>>>>>>> origin/master


let set_to_string = (fun f s -> (

let elts = (FStar_Util.set_elements s)
in (match (elts) with
| [] -> begin
"{}"
end
| (x)::xs -> begin
(

let strb = (FStar_Util.new_string_builder ())
<<<<<<< HEAD
in ((FStar_Util.string_builder_append strb "[");
(let _0_596 = (f x)
in (FStar_Util.string_builder_append strb _0_596));
(FStar_List.iter (fun x -> ((FStar_Util.string_builder_append strb "; ");
(let _0_597 = (f x)
in (FStar_Util.string_builder_append strb _0_597));
)) xs);
(FStar_Util.string_builder_append strb "]");
(FStar_Util.string_of_string_builder strb);
))
end))
=======
in (

let _39_746 = (FStar_Util.string_builder_append strb "{")
in (

let _39_748 = (let _138_393 = (f x)
in (FStar_Util.string_builder_append strb _138_393))
in (

let _39_753 = (FStar_List.iter (fun x -> (

let _39_751 = (FStar_Util.string_builder_append strb ", ")
in (let _138_395 = (f x)
in (FStar_Util.string_builder_append strb _138_395)))) xs)
in (

let _39_755 = (FStar_Util.string_builder_append strb "}")
in (FStar_Util.string_of_string_builder strb))))))
end)))
>>>>>>> origin/master




