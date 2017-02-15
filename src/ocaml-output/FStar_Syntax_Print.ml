
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


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _0_305 = (let _0_304 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "#" _0_304))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _0_305)))


let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____22 = (FStar_Options.print_real_names ())
in (match (uu____22) with
| true -> begin
(bv_to_string bv)
end
| uu____23 -> begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)))


let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _0_307 = (let _0_306 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "@" _0_306))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText _0_307)))


let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Syntax_Const.op_Addition), ("+")))::(((FStar_Syntax_Const.op_Subtraction), ("-")))::(((FStar_Syntax_Const.op_Multiply), ("*")))::(((FStar_Syntax_Const.op_Division), ("/")))::(((FStar_Syntax_Const.op_Eq), ("=")))::(((FStar_Syntax_Const.op_ColonEq), (":=")))::(((FStar_Syntax_Const.op_notEq), ("<>")))::(((FStar_Syntax_Const.op_And), ("&&")))::(((FStar_Syntax_Const.op_Or), ("||")))::(((FStar_Syntax_Const.op_LTE), ("<=")))::(((FStar_Syntax_Const.op_GTE), (">=")))::(((FStar_Syntax_Const.op_LT), ("<")))::(((FStar_Syntax_Const.op_GT), (">")))::(((FStar_Syntax_Const.op_Modulus), ("mod")))::(((FStar_Syntax_Const.and_lid), ("/\\")))::(((FStar_Syntax_Const.or_lid), ("\\/")))::(((FStar_Syntax_Const.imp_lid), ("==>")))::(((FStar_Syntax_Const.iff_lid), ("<==>")))::(((FStar_Syntax_Const.precedes_lid), ("<<")))::(((FStar_Syntax_Const.eq2_lid), ("==")))::(((FStar_Syntax_Const.eq3_lid), ("===")))::[]


let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Syntax_Const.op_Negation), ("not")))::(((FStar_Syntax_Const.op_Minus), ("-")))::(((FStar_Syntax_Const.not_lid), ("~")))::[]


let is_prim_op = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
end
| uu____105 -> begin
false
end))


let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____122 -> begin
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


let is_inr = (fun uu___180_169 -> (match (uu___180_169) with
| FStar_Util.Inl (uu____172) -> begin
false
end
| FStar_Util.Inr (uu____173) -> begin
true
end))


let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___181_204 -> (match (uu___181_204) with
| (uu____208, Some (FStar_Syntax_Syntax.Implicit (uu____209))) -> begin
false
end
| uu____211 -> begin
true
end)))))


let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (

let uu____222 = (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
in (match (uu____222) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args = (filter_imp args)
in (

let exps = (FStar_List.map Prims.fst args)
in (

let uu____266 = ((is_lex_cons f) && ((FStar_List.length exps) = (Prims.parse_int "2")))
in (match (uu____266) with
| true -> begin
(

let uu____275 = (reconstruct_lex (FStar_List.nth exps (Prims.parse_int "1")))
in (match (uu____275) with
| Some (xs) -> begin
Some ((let _0_308 = (FStar_List.nth exps (Prims.parse_int "0"))
in (_0_308)::xs))
end
| None -> begin
None
end))
end
| uu____306 -> begin
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


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (Prims.snd (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)))


let infix_prim_op_to_string = (fun e -> (let _0_309 = (get_lid e)
in (find_lid _0_309 infix_prim_ops)))


let unary_prim_op_to_string = (fun e -> (let _0_310 = (get_lid e)
in (find_lid _0_310 unary_prim_ops)))


let quant_to_string = (fun t -> (let _0_311 = (get_lid t)
in (find_lid _0_311 quants)))


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
| FStar_Const.Const_string (bytes, uu____406) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (uu____409) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x, uu____414) -> begin
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
(let _0_312 = (sli l)
in (FStar_Util.format1 "[[%s.reflect]]" _0_312))
end))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun uu___182_426 -> (match (uu___182_426) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _0_313 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _0_313))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _0_314 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _0_314))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _0_315 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _0_315))
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
"Tm_delayed-resolved"
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____588) -> begin
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
end
| uu____603 -> begin
(let _0_317 = (let _0_316 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _0_316 FStar_Util.string_of_int))
in (Prims.strcat "?" _0_317))
end)))


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe Prims.option) = (fun n u -> (

let uu____613 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____613) with
| FStar_Syntax_Syntax.U_zero -> begin
((n), (None))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(int_of_univ (n + (Prims.parse_int "1")) u)
end
| uu____619 -> begin
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
(let _0_318 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _0_318))
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
(let _0_320 = (univ_to_string u)
in (let _0_319 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 "(%s + %s)" _0_320 _0_319)))
end))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _0_322 = (let _0_321 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _0_321 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _0_322))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end)))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _0_323 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _0_323 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _0_324 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _0_324 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun uu___183_659 -> (match (uu___183_659) with
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
(let _0_325 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _0_325))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _0_326 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _0_326 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(let _0_329 = (FStar_Ident.text_of_path (FStar_Ident.path_of_ns ns))
in (let _0_328 = (let _0_327 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right _0_327 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" _0_329 _0_328)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(let _0_332 = (FStar_Ident.text_of_path (FStar_Ident.path_of_ns ns))
in (let _0_331 = (let _0_330 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right _0_330 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" _0_332 _0_331)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(let _0_333 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" _0_333))
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
| uu____688 -> begin
(let _0_334 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _0_334 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| uu____698 -> begin
(let _0_335 = (quals_to_string quals)
in (Prims.strcat _0_335 " "))
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
| FStar_Syntax_Syntax.Tm_delayed (uu____757) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (uu____778, []) -> begin
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (let _0_337 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _0_336 = (FStar_All.pipe_right args (FStar_List.map (fun uu____827 -> (match (uu____827) with
| (t, uu____831) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _0_336 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _0_337 (FStar_String.concat "\\/")))
in (let _0_338 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _0_338)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _0_342 = (tag_of_term t)
in (let _0_341 = (sli m)
in (let _0_340 = (term_to_string t')
in (let _0_339 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" _0_342 _0_341 _0_340 _0_339)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(let _0_347 = (tag_of_term t)
in (let _0_346 = (term_to_string t')
in (let _0_345 = (sli m0)
in (let _0_344 = (sli m1)
in (let _0_343 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" _0_347 _0_346 _0_345 _0_344 _0_343))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(let _0_349 = (FStar_Range.string_of_range r)
in (let _0_348 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l _0_349 _0_348)))
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____864) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, uu____873) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____891 = (FStar_Options.print_universes ())
in (match (uu____891) with
| true -> begin
(let _0_350 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _0_350))
end
| uu____892 -> begin
"Type"
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _0_352 = (binders_to_string " -> " bs)
in (let _0_351 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _0_352 _0_351)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
(let _0_356 = (binders_to_string " " bs)
in (let _0_355 = (term_to_string t2)
in (let _0_354 = (let _0_353 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _0_353))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _0_356 _0_355 _0_354))))
end
| Some (FStar_Util.Inr (l, flags)) when (FStar_Options.print_implicits ()) -> begin
(let _0_358 = (binders_to_string " " bs)
in (let _0_357 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))" _0_358 _0_357 l.FStar_Ident.str)))
end
| uu____951 -> begin
(let _0_360 = (binders_to_string " " bs)
in (let _0_359 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _0_360 _0_359)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _0_363 = (bv_to_string xt)
in (let _0_362 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _0_361 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _0_363 _0_362 _0_361))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _0_365 = (term_to_string t)
in (let _0_364 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _0_365 _0_364)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _0_367 = (lbs_to_string [] lbs)
in (let _0_366 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _0_367 _0_366)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), eff_name) -> begin
(let _0_371 = (term_to_string e)
in (let _0_370 = (let _0_368 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right _0_368 (FStar_Util.dflt "default")))
in (let _0_369 = (term_to_string t)
in (FStar_Util.format3 "(%s <: [%s] %s)" _0_371 _0_370 _0_369))))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), uu____1020) -> begin
(let _0_373 = (term_to_string e)
in (let _0_372 = (comp_to_string c)
in (FStar_Util.format2 "(%s <: %s)" _0_373 _0_372)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _0_380 = (term_to_string head)
in (let _0_379 = (let _0_378 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____1083 -> (match (uu____1083) with
| (p, wopt, e) -> begin
(let _0_377 = (FStar_All.pipe_right p pat_to_string)
in (let _0_376 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _0_374 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _0_374))
end)
in (let _0_375 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _0_377 _0_376 _0_375))))
end))))
in (FStar_Util.concat_l "\n\t|" _0_378))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _0_380 _0_379)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let uu____1100 = (FStar_Options.print_universes ())
in (match (uu____1100) with
| true -> begin
(let _0_382 = (term_to_string t)
in (let _0_381 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _0_382 _0_381)))
end
| uu____1101 -> begin
(term_to_string t)
end))
end
| uu____1102 -> begin
(tag_of_term x)
end))))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _0_385 = (fv_to_string l)
in (let _0_384 = (let _0_383 = (FStar_List.map (fun uu____1119 -> (match (uu____1119) with
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
in (FStar_All.pipe_right _0_383 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _0_385 _0_384)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____1127) -> begin
(

let uu____1132 = (FStar_Options.print_bound_var_types ())
in (match (uu____1132) with
| true -> begin
(let _0_387 = (bv_to_string x)
in (let _0_386 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" _0_387 _0_386)))
end
| uu____1133 -> begin
(let _0_388 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _0_388))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____1135 = (FStar_Options.print_bound_var_types ())
in (match (uu____1135) with
| true -> begin
(let _0_390 = (bv_to_string x)
in (let _0_389 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" _0_390 _0_389)))
end
| uu____1136 -> begin
(bv_to_string x)
end))
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____1139 = (FStar_Options.print_real_names ())
in (match (uu____1139) with
| true -> begin
(let _0_391 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _0_391))
end
| uu____1140 -> begin
"_"
end))
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _0_392 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _0_392))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  Prims.string = (fun quals lbs -> (

let lbs = (

let uu____1155 = (FStar_Options.print_universes ())
in (match (uu____1155) with
| true -> begin
(let _0_394 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let uu____1165 = (let _0_393 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _0_393))
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

let uu___190_1239 = lb
in {FStar_Syntax_Syntax.lbname = uu___190_1239.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu___190_1239.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((Prims.fst lbs)), (_0_394)))
end
| uu____1240 -> begin
lbs
end))
in (let _0_403 = (quals_to_string' quals)
in (let _0_402 = (let _0_401 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _0_400 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _0_399 = (

let uu____1247 = (FStar_Options.print_universes ())
in (match (uu____1247) with
| true -> begin
(let _0_396 = (let _0_395 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat _0_395 ">"))
in (Prims.strcat "<" _0_396))
end
| uu____1248 -> begin
""
end))
in (let _0_398 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _0_397 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _0_400 _0_399 _0_398 _0_397))))))))
in (FStar_Util.concat_l "\n and " _0_401))
in (FStar_Util.format3 "%slet %s %s" _0_403 (match ((Prims.fst lbs)) with
| true -> begin
"rec"
end
| uu____1242 -> begin
""
end) _0_402)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (

let uu____1252 = (FStar_Options.print_effect_args ())
in (match (uu____1252) with
| true -> begin
(comp_to_string (lc.FStar_Syntax_Syntax.comp ()))
end
| uu____1253 -> begin
(let _0_405 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _0_404 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _0_405 _0_404)))
end)))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s uu___184_1255 -> (match (uu___184_1255) with
| Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
(Prims.strcat "#." s)
end
| Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "$" s)
end
| uu____1257 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun is_arrow b -> (

let uu____1263 = b
in (match (uu____1263) with
| (a, imp) -> begin
(

let uu____1268 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____1268) with
| true -> begin
(let _0_406 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" _0_406))
end
| uu____1269 -> begin
(

let uu____1270 = ((not (is_arrow)) && (not ((FStar_Options.print_bound_var_types ()))))
in (match (uu____1270) with
| true -> begin
(let _0_407 = (nm_to_string a)
in (imp_to_string _0_407 imp))
end
| uu____1271 -> begin
(let _0_411 = (let _0_410 = (nm_to_string a)
in (let _0_409 = (let _0_408 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" _0_408))
in (Prims.strcat _0_410 _0_409)))
in (imp_to_string _0_411 imp))
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
| uu____1282 -> begin
(filter_imp bs)
end))
in (match ((sep = " -> ")) with
| true -> begin
(let _0_412 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _0_412 (FStar_String.concat sep)))
end
| uu____1287 -> begin
(let _0_413 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _0_413 (FStar_String.concat sep)))
end)))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun uu___185_1292 -> (match (uu___185_1292) with
| (a, imp) -> begin
(let _0_414 = (term_to_string a)
in (imp_to_string _0_414 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args = (

let uu____1302 = (FStar_Options.print_implicits ())
in (match (uu____1302) with
| true -> begin
args
end
| uu____1303 -> begin
(filter_imp args)
end))
in (let _0_415 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _0_415 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____1313) -> begin
(

let uu____1320 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____1320) with
| FStar_Syntax_Syntax.Tm_type (uu____1321) when (not ((FStar_Options.print_implicits ()))) -> begin
(term_to_string t)
end
| uu____1322 -> begin
(let _0_416 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _0_416))
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
(let _0_417 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _0_417))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let basic = (

let uu____1336 = (FStar_Options.print_effect_args ())
in (match (uu____1336) with
| true -> begin
(let _0_423 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _0_422 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _0_421 = (let _0_418 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _0_418 (FStar_String.concat ", ")))
in (let _0_420 = (let _0_419 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right _0_419 (FStar_String.concat " ")))
in (FStar_Util.format4 "%s (%s) %s (attributes %s)" _0_423 _0_422 _0_421 _0_420)))))
end
| uu____1350 -> begin
(

let uu____1351 = ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___186_1353 -> (match (uu___186_1353) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____1354 -> begin
false
end)))) && (not ((FStar_Options.print_effect_args ()))))
in (match (uu____1351) with
| true -> begin
(let _0_424 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _0_424))
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

let uu____1358 = ((not ((FStar_Options.print_effect_args ()))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___187_1360 -> (match (uu___187_1360) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____1361 -> begin
false
end)))))
in (match (uu____1358) with
| true -> begin
(let _0_425 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _0_425))
end
| uu____1362 -> begin
(let _0_427 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _0_426 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _0_427 _0_426)))
end))
end))
end))
end))
in (

let dec = (let _0_430 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun uu___188_1367 -> (match (uu___188_1367) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _0_429 = (let _0_428 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _0_428))
in (_0_429)::[])
end
| uu____1372 -> begin
[]
end))))
in (FStar_All.pipe_right _0_430 (FStar_String.concat " ")))
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
| FStar_Syntax_Syntax.DECREASES (uu____1374) -> begin
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


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun uu____1387 -> (match (uu____1387) with
| (us, t) -> begin
(let _0_433 = (let _0_431 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes _0_431))
in (let _0_432 = (term_to_string t)
in (FStar_Util.format2 "%s%s" _0_433 _0_432)))
end))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (

let actions_to_string = (fun actions -> (let _0_439 = (FStar_All.pipe_right actions (FStar_List.map (fun a -> (let _0_438 = (sli a.FStar_Syntax_Syntax.action_name)
in (let _0_437 = (let _0_434 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes _0_434))
in (let _0_436 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (let _0_435 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format4 "%s%s : %s = %s" _0_438 _0_437 _0_436 _0_435))))))))
in (FStar_All.pipe_right _0_439 (FStar_String.concat ",\n\t"))))
in (let _0_477 = (let _0_476 = (let _0_475 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _0_474 = (let _0_473 = (let _0_440 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes _0_440))
in (let _0_472 = (let _0_471 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _0_470 = (let _0_469 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _0_468 = (let _0_467 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (let _0_466 = (let _0_465 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _0_464 = (let _0_463 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _0_462 = (let _0_461 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _0_460 = (let _0_459 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (let _0_458 = (let _0_457 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _0_456 = (let _0_455 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _0_454 = (let _0_453 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _0_452 = (let _0_451 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _0_450 = (let _0_449 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (let _0_448 = (let _0_447 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _0_446 = (let _0_445 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (let _0_444 = (let _0_443 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (let _0_442 = (let _0_441 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (_0_441)::[])
in (_0_443)::_0_442))
in (_0_445)::_0_444))
in (_0_447)::_0_446))
in (_0_449)::_0_448))
in (_0_451)::_0_450))
in (_0_453)::_0_452))
in (_0_455)::_0_454))
in (_0_457)::_0_456))
in (_0_459)::_0_458))
in (_0_461)::_0_460))
in (_0_463)::_0_462))
in (_0_465)::_0_464))
in (_0_467)::_0_466))
in (_0_469)::_0_468))
in (_0_471)::_0_470))
in (_0_473)::_0_472))
in (_0_475)::_0_474))
in ((match (for_free) with
| true -> begin
"_for_free "
end
| uu____1408 -> begin
""
end))::_0_476)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" _0_477))))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.LightOff, uu____1412) -> begin
"#light \"off\""
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None), uu____1413) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s)), uu____1415) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), uu____1417) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, uu____1422, uu____1423, quals, uu____1425) -> begin
(let _0_480 = (quals_to_string' quals)
in (let _0_479 = (binders_to_string " " tps)
in (let _0_478 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" _0_480 lid.FStar_Ident.str _0_479 _0_478))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, uu____1435, uu____1436, uu____1437, uu____1438, uu____1439) -> begin
(

let uu____1444 = (FStar_Options.print_universes ())
in (match (uu____1444) with
| true -> begin
(

let uu____1445 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (uu____1445) with
| (univs, t) -> begin
(let _0_482 = (univ_names_to_string univs)
in (let _0_481 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _0_482 lid.FStar_Ident.str _0_481)))
end))
end
| uu____1450 -> begin
(let _0_483 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _0_483))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, uu____1455) -> begin
(

let uu____1458 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (uu____1458) with
| (univs, t) -> begin
(let _0_487 = (quals_to_string' quals)
in (let _0_486 = (

let uu____1463 = (FStar_Options.print_universes ())
in (match (uu____1463) with
| true -> begin
(let _0_484 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _0_484))
end
| uu____1464 -> begin
""
end))
in (let _0_485 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" _0_487 lid.FStar_Ident.str _0_486 _0_485))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, uu____1467, uu____1468) -> begin
(let _0_488 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _0_488))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____1472, uu____1473, qs, uu____1475) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, uu____1483) -> begin
(let _0_489 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _0_489))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____1485, uu____1486, uu____1487) -> begin
(let _0_490 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _0_490 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, uu____1496) -> begin
(eff_decl_to_string false ed)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed, uu____1498) -> begin
(eff_decl_to_string true ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(

let lift_wp = (match (((se.FStar_Syntax_Syntax.lift_wp), (se.FStar_Syntax_Syntax.lift))) with
| (None, None) -> begin
(failwith "impossible")
end
| (Some (lift_wp), uu____1507) -> begin
lift_wp
end
| (uu____1511, Some (lift)) -> begin
lift
end)
in (

let uu____1516 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp) (Prims.snd lift_wp))
in (match (uu____1516) with
| (us, t) -> begin
(let _0_494 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _0_493 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _0_492 = (univ_names_to_string us)
in (let _0_491 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _0_494 _0_493 _0_492 _0_491)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, uu____1527, flags, uu____1529) -> begin
(

let uu____1534 = (FStar_Options.print_universes ())
in (match (uu____1534) with
| true -> begin
(

let uu____1535 = (let _0_495 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c))))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _0_495))
in (match (uu____1535) with
| (univs, t) -> begin
(

let uu____1552 = (

let uu____1560 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____1560) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((bs), (c))
end
| uu____1585 -> begin
(failwith "impossible")
end))
in (match (uu____1552) with
| (tps, c) -> begin
(let _0_499 = (sli l)
in (let _0_498 = (univ_names_to_string univs)
in (let _0_497 = (binders_to_string " " tps)
in (let _0_496 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _0_499 _0_498 _0_497 _0_496)))))
end))
end))
end
| uu____1605 -> begin
(let _0_502 = (sli l)
in (let _0_501 = (binders_to_string " " tps)
in (let _0_500 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _0_502 _0_501 _0_500))))
end))
end))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _0_503 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _0_503 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((uu____1615, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = uu____1617; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____1619; FStar_Syntax_Syntax.lbdef = uu____1620})::[]), uu____1621, uu____1622, uu____1623, uu____1624) -> begin
(let _0_505 = (lbname_to_string lb)
in (let _0_504 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _0_505 _0_504)))
end
| uu____1642 -> begin
(let _0_506 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right _0_506 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _0_509 = (sli m.FStar_Syntax_Syntax.name)
in (let _0_508 = (let _0_507 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _0_507 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _0_509 _0_508))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun uu___189_1653 -> (match (uu___189_1653) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(let _0_511 = (FStar_Util.string_of_int i)
in (let _0_510 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _0_511 _0_510)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _0_513 = (bv_to_string x)
in (let _0_512 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _0_513 _0_512)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _0_515 = (bv_to_string x)
in (let _0_514 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _0_515 _0_514)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _0_517 = (FStar_Util.string_of_int i)
in (let _0_516 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _0_517 _0_516)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _0_518 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _0_518))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _0_519 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _0_519 (FStar_String.concat "; "))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in ((match (ascription) with
| None -> begin
(FStar_Util.string_builder_append strb "None")
end
| Some (FStar_Util.Inl (lc)) -> begin
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


let list_to_string = (fun f elts -> (match (elts) with
| [] -> begin
"[]"
end
| (x)::xs -> begin
(

let strb = (FStar_Util.new_string_builder ())
in ((FStar_Util.string_builder_append strb "[");
(let _0_520 = (f x)
in (FStar_Util.string_builder_append strb _0_520));
(FStar_List.iter (fun x -> ((FStar_Util.string_builder_append strb "; ");
(let _0_521 = (f x)
in (FStar_Util.string_builder_append strb _0_521));
)) xs);
(FStar_Util.string_builder_append strb "]");
(FStar_Util.string_of_string_builder strb);
))
end))


let set_to_string = (fun f s -> (

let elts = (FStar_Util.set_elements s)
in (match (elts) with
| [] -> begin
"{}"
end
| (x)::xs -> begin
(

let strb = (FStar_Util.new_string_builder ())
in ((FStar_Util.string_builder_append strb "{");
(let _0_522 = (f x)
in (FStar_Util.string_builder_append strb _0_522));
(FStar_List.iter (fun x -> ((FStar_Util.string_builder_append strb ", ");
(let _0_523 = (f x)
in (FStar_Util.string_builder_append strb _0_523));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))




