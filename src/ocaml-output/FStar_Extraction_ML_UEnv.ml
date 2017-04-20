
open Prims

type ty_or_exp_b =
((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty), (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool)) FStar_Util.either

type binding =
| Bv of (FStar_Syntax_Syntax.bv * ty_or_exp_b)
| Fv of (FStar_Syntax_Syntax.fv * ty_or_exp_b)


let uu___is_Bv : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bv (_0) -> begin
true
end
| uu____25 -> begin
false
end))


let __proj__Bv__item___0 : binding  ->  (FStar_Syntax_Syntax.bv * ty_or_exp_b) = (fun projectee -> (match (projectee) with
| Bv (_0) -> begin
_0
end))


let uu___is_Fv : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fv (_0) -> begin
true
end
| uu____45 -> begin
false
end))


let __proj__Fv__item___0 : binding  ->  (FStar_Syntax_Syntax.fv * ty_or_exp_b) = (fun projectee -> (match (projectee) with
| Fv (_0) -> begin
_0
end))

type env =
{tcenv : FStar_TypeChecker_Env.env; gamma : binding Prims.list; tydefs : (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * FStar_Extraction_ML_Syntax.mltydecl) Prims.list; currentModule : FStar_Extraction_ML_Syntax.mlpath}


let debug : env  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun g f -> (

let c = (FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule)
in (

let uu____114 = (FStar_Options.debug_at_level c (FStar_Options.Other ("Extraction")))
in (match (uu____114) with
| true -> begin
(f ())
end
| uu____115 -> begin
()
end))))


let mkFvvar : FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.fv = (fun l t -> (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant None))


let erasedContent : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.ml_unit_ty


let erasableTypeNoDelta : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> (match ((t = FStar_Extraction_ML_Syntax.ml_unit_ty)) with
| true -> begin
true
end
| uu____125 -> begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____126, (("FStar")::("Ghost")::[], "erased")) -> begin
true
end
| uu____133 -> begin
false
end)
end))


let unknownType : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Top


let prependTick = (fun uu____144 -> (match (uu____144) with
| (x, n1) -> begin
(match ((FStar_Util.starts_with x "\'")) with
| true -> begin
((x), (n1))
end
| uu____151 -> begin
(((Prims.strcat "\'A" x)), (n1))
end)
end))


let removeTick = (fun uu____162 -> (match (uu____162) with
| (x, n1) -> begin
(match ((FStar_Util.starts_with x "\'")) with
| true -> begin
(

let uu____169 = (FStar_Util.substring_from x (Prims.parse_int "1"))
in ((uu____169), (n1)))
end
| uu____170 -> begin
((x), (n1))
end)
end))


let convRange : FStar_Range.range  ->  Prims.int = (fun r -> (Prims.parse_int "0"))


let convIdent : FStar_Ident.ident  ->  FStar_Extraction_ML_Syntax.mlident = (fun id -> ((id.FStar_Ident.idText), ((Prims.parse_int "0"))))


let bv_as_ml_tyvar : FStar_Syntax_Syntax.bv  ->  (Prims.string * Prims.int) = (fun x -> (

let uu____182 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (prependTick uu____182)))


let bv_as_ml_termvar : FStar_Syntax_Syntax.bv  ->  (Prims.string * Prims.int) = (fun x -> (

let uu____190 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (removeTick uu____190)))


let rec lookup_ty_local : binding Prims.list  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun gamma b -> (match (gamma) with
| (Bv (b', FStar_Util.Inl (mli, mlt)))::tl1 -> begin
(match ((FStar_Syntax_Syntax.bv_eq b b')) with
| true -> begin
mlt
end
| uu____220 -> begin
(lookup_ty_local tl1 b)
end)
end
| (Bv (b', FStar_Util.Inr (uu____222)))::tl1 -> begin
(match ((FStar_Syntax_Syntax.bv_eq b b')) with
| true -> begin
(failwith (Prims.strcat "Type/Expr clash: " b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
end
| uu____243 -> begin
(lookup_ty_local tl1 b)
end)
end
| (uu____244)::tl1 -> begin
(lookup_ty_local tl1 b)
end
| [] -> begin
(failwith (Prims.strcat "extraction: unbound type var " b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
end))


let tyscheme_of_td = (fun uu____264 -> (match (uu____264) with
| (uu____271, uu____272, uu____273, vars, body_opt) -> begin
(match (body_opt) with
| Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t)) -> begin
Some (((vars), (t)))
end
| uu____283 -> begin
None
end)
end))


let lookup_ty_const : env  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme Prims.option = (fun env uu____291 -> (match (uu____291) with
| (module_name, ty_name) -> begin
(FStar_Util.find_map env.tydefs (fun uu____301 -> (match (uu____301) with
| (m, tds) -> begin
(match ((module_name = m)) with
| true -> begin
(FStar_Util.find_map tds (fun td -> (

let uu____313 = td
in (match (uu____313) with
| (uu____315, n1, uu____317, uu____318, uu____319) -> begin
(match ((n1 = ty_name)) with
| true -> begin
(tyscheme_of_td td)
end
| uu____326 -> begin
None
end)
end))))
end
| uu____327 -> begin
None
end)
end)))
end))


let module_name_of_fv : FStar_Syntax_Syntax.fv  ->  Prims.string Prims.list = (fun fv -> (FStar_All.pipe_right fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ns (FStar_List.map (fun i -> i.FStar_Ident.idText))))


let maybe_mangle_type_projector : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mlpath Prims.option = (fun env fv -> (

let mname = (module_name_of_fv fv)
in (

let ty_name = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ident.FStar_Ident.idText
in (FStar_Util.find_map env.tydefs (fun uu____360 -> (match (uu____360) with
| (m, tds) -> begin
(FStar_Util.find_map tds (fun uu____375 -> (match (uu____375) with
| (uu____380, n1, mangle_opt, uu____383, uu____384) -> begin
(match ((m = mname)) with
| true -> begin
(match ((n1 = ty_name)) with
| true -> begin
(match (mangle_opt) with
| None -> begin
Some (((m), (n1)))
end
| Some (mangled) -> begin
(

let modul = m
in Some (((modul), (mangled))))
end)
end
| uu____413 -> begin
None
end)
end
| uu____417 -> begin
None
end)
end)))
end))))))


let lookup_tyvar : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bt -> (lookup_ty_local g.gamma bt))


let lookup_eff_action : env  ->  (FStar_Syntax_Syntax.fv, FStar_Ident.lident) FStar_Util.either  ->  ty_or_exp_b = (fun g x -> (

let uu____437 = (match (x) with
| FStar_Util.Inl (fv) -> begin
(

let uu____443 = (FStar_Range.string_of_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.p)
in ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (uu____443)))
end
| FStar_Util.Inr (lid) -> begin
(

let uu____453 = (FStar_Range.string_of_range FStar_Range.dummyRange)
in ((lid), (uu____453)))
end)
in (match (uu____437) with
| (name, range) -> begin
(

let fv_not_found = (

let uu____457 = (FStar_Syntax_Print.lid_to_string name)
in (FStar_Util.format2 "(%s) free Variable %s not found\n" range uu____457))
in (

let eff_action = (

let bits = (FStar_All.pipe_right (FStar_String.split (('_')::[]) name.FStar_Ident.ident.FStar_Ident.idText) (FStar_List.filter (fun x1 -> (not ((x1 = ""))))))
in (match (((FStar_List.length bits) = (Prims.parse_int "4"))) with
| true -> begin
(

let uu____468 = ((

let uu____469 = (FStar_List.hd bits)
in (uu____469 = "proj")) && (

let uu____470 = (FStar_List.nth bits (Prims.parse_int "2"))
in (uu____470 = "item")))
in (match (uu____468) with
| true -> begin
(

let uu____472 = (FStar_List.nth bits (Prims.parse_int "1"))
in (FStar_All.pipe_left (fun _0_29 -> Some (_0_29)) uu____472))
end
| uu____474 -> begin
None
end))
end
| uu____475 -> begin
None
end))
in (

let eff_name = (match (eff_action) with
| Some (n1) -> begin
n1
end
| None -> begin
(failwith fv_not_found)
end)
in (

let constructed_name = (

let uu____479 = (

let uu____481 = (FStar_List.map (fun x1 -> x1.FStar_Ident.idText) name.FStar_Ident.ns)
in (FStar_List.append uu____481 ((eff_name)::(name.FStar_Ident.ident.FStar_Ident.idText)::[])))
in (FStar_All.pipe_left (FStar_String.concat ".") uu____479))
in (

let x1 = (FStar_Util.find_map g.gamma (fun uu___103_487 -> (match (uu___103_487) with
| Fv (fv', t) when (fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str = constructed_name) -> begin
Some (t)
end
| uu____495 -> begin
None
end)))
in (match (x1) with
| None -> begin
(failwith fv_not_found)
end
| Some (y) -> begin
y
end))))))
end)))


let lookup_fv_by_lid : env  ->  FStar_Ident.lident  ->  ty_or_exp_b = (fun g lid -> (

let x = (FStar_Util.find_map g.gamma (fun uu___104_505 -> (match (uu___104_505) with
| Fv (fv', x) when (FStar_Syntax_Syntax.fv_eq_lid fv' lid) -> begin
Some (x)
end
| uu____509 -> begin
None
end)))
in (match (x) with
| None -> begin
(lookup_eff_action g (FStar_Util.Inr (lid)))
end
| Some (y) -> begin
y
end)))


let lookup_fv : env  ->  FStar_Syntax_Syntax.fv  ->  ty_or_exp_b = (fun g fv -> (

let x = (FStar_Util.find_map g.gamma (fun uu___105_519 -> (match (uu___105_519) with
| Fv (fv', t) when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
Some (t)
end
| uu____523 -> begin
None
end)))
in (match (x) with
| None -> begin
(lookup_eff_action g (FStar_Util.Inl (fv)))
end
| Some (y) -> begin
y
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  ty_or_exp_b = (fun g bv -> (

let x = (FStar_Util.find_map g.gamma (fun uu___106_533 -> (match (uu___106_533) with
| Bv (bv', r) when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
Some (r)
end
| uu____537 -> begin
None
end)))
in (match (x) with
| None -> begin
(

let uu____538 = (

let uu____539 = (FStar_Range.string_of_range bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)
in (

let uu____540 = (FStar_Syntax_Print.bv_to_string bv)
in (FStar_Util.format2 "(%s) bound Variable %s not found\n" uu____539 uu____540)))
in (failwith uu____538))
end
| Some (y) -> begin
y
end)))


let lookup : env  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual Prims.option) = (fun g x -> (match (x) with
| FStar_Util.Inl (x1) -> begin
(

let uu____562 = (lookup_bv g x1)
in ((uu____562), (None)))
end
| FStar_Util.Inr (x1) -> begin
(

let uu____565 = (lookup_fv g x1)
in ((uu____565), (x1.FStar_Syntax_Syntax.fv_qual)))
end))


let lookup_term : env  ->  FStar_Syntax_Syntax.term  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual Prims.option) = (fun g t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(lookup g (FStar_Util.Inl (x)))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(lookup g (FStar_Util.Inr (x)))
end
| uu____581 -> begin
(failwith "Impossible: lookup_term for a non-name")
end))


let extend_ty : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty Prims.option  ->  env = (fun g a mapped_to -> (

let ml_a = (bv_as_ml_tyvar a)
in (

let mapped_to1 = (match (mapped_to) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Var (ml_a)
end
| Some (t) -> begin
t
end)
in (

let gamma = (Bv (((a), (FStar_Util.Inl (((ml_a), (mapped_to1)))))))::g.gamma
in (

let tcenv = (FStar_TypeChecker_Env.push_bv g.tcenv a)
in (

let uu___108_624 = g
in {tcenv = tcenv; gamma = gamma; tydefs = uu___108_624.tydefs; currentModule = uu___108_624.currentModule}))))))


let find_uniq : binding Prims.list  ->  Prims.string  ->  Prims.string = (fun gamma mlident -> (

let rec find_uniq = (fun mlident1 i -> (

let suffix = (match ((i = (Prims.parse_int "0"))) with
| true -> begin
""
end
| uu____641 -> begin
(FStar_Util.string_of_int i)
end)
in (

let target_mlident = (Prims.strcat mlident1 suffix)
in (

let has_collision = (FStar_List.existsb (fun uu___107_644 -> (match (uu___107_644) with
| (Bv (_, FStar_Util.Inl (mlident', _))) | (Fv (_, FStar_Util.Inl (mlident', _))) -> begin
(target_mlident = (Prims.fst mlident'))
end
| (Fv (_, FStar_Util.Inr (mlident', _, _, _))) | (Bv (_, FStar_Util.Inr (mlident', _, _, _))) -> begin
(target_mlident = mlident')
end)) gamma)
in (match (has_collision) with
| true -> begin
(find_uniq mlident1 (i + (Prims.parse_int "1")))
end
| uu____715 -> begin
target_mlident
end)))))
in (find_uniq mlident (Prims.parse_int "0"))))


let extend_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g x t_x add_unit is_rec mk_unit -> (

let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| uu____741 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let uu____742 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (match (uu____742) with
| (mlident, nocluewhat) -> begin
(

let mlsymbol = (find_uniq g.gamma mlident)
in (

let mlident1 = ((mlsymbol), (nocluewhat))
in (

let mlx = FStar_Extraction_ML_Syntax.MLE_Var (mlident1)
in (

let mlx1 = (match (mk_unit) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____753 -> begin
(match (add_unit) with
| true -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mlx)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end
| uu____755 -> begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mlx)
end)
end)
in (

let gamma = (Bv (((x), (FStar_Util.Inr (((mlsymbol), (mlx1), (t_x), (is_rec)))))))::g.gamma
in (

let tcenv = (

let uu____773 = (FStar_Syntax_Syntax.binders_of_list ((x)::[]))
in (FStar_TypeChecker_Env.push_binders g.tcenv uu____773))
in (((

let uu___109_776 = g
in {tcenv = tcenv; gamma = gamma; tydefs = uu___109_776.tydefs; currentModule = uu___109_776.currentModule})), (mlident1))))))))
end))))


let rec mltyFvars : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlident Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(

let uu____787 = (mltyFvars t1)
in (

let uu____789 = (mltyFvars t2)
in (FStar_List.append uu____787 uu____789)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, path) -> begin
(FStar_List.collect mltyFvars args)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(FStar_List.collect mltyFvars ts)
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
[]
end))


let rec subsetMlidents : FStar_Extraction_ML_Syntax.mlident Prims.list  ->  FStar_Extraction_ML_Syntax.mlident Prims.list  ->  Prims.bool = (fun la lb -> (match (la) with
| (h)::tla -> begin
((FStar_List.contains h lb) && (subsetMlidents tla lb))
end
| [] -> begin
true
end))


let tySchemeIsClosed : FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool = (fun tys -> (

let uu____813 = (mltyFvars (Prims.snd tys))
in (subsetMlidents uu____813 (Prims.fst tys))))


let extend_fv' : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g x y t_x add_unit is_rec -> (

let uu____837 = (tySchemeIsClosed t_x)
in (match (uu____837) with
| true -> begin
(

let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| uu____843 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let uu____844 = (

let uu____850 = y
in (match (uu____850) with
| (ns, i) -> begin
(

let mlsymbol = (FStar_Extraction_ML_Syntax.avoid_keyword i)
in ((((ns), (mlsymbol))), (mlsymbol)))
end))
in (match (uu____844) with
| (mlpath, mlsymbol) -> begin
(

let mly = FStar_Extraction_ML_Syntax.MLE_Name (mlpath)
in (

let mly1 = (match (add_unit) with
| true -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mly)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end
| uu____878 -> begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mly)
end)
in (

let gamma = (Fv (((x), (FStar_Util.Inr (((mlsymbol), (mly1), (t_x), (is_rec)))))))::g.gamma
in (((

let uu___110_897 = g
in {tcenv = uu___110_897.tcenv; gamma = gamma; tydefs = uu___110_897.tydefs; currentModule = uu___110_897.currentModule})), (((mlsymbol), ((Prims.parse_int "0"))))))))
end)))
end
| uu____898 -> begin
(failwith "freevars found")
end)))


let extend_fv : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g x t_x add_unit is_rec -> (

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (extend_fv' g x mlp t_x add_unit is_rec)))


let extend_lb : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g l t t_x add_unit is_rec -> (match (l) with
| FStar_Util.Inl (x) -> begin
(extend_bv g x t_x add_unit is_rec false)
end
| FStar_Util.Inr (f) -> begin
(

let uu____951 = (FStar_Extraction_ML_Syntax.mlpath_of_lident f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____951) with
| (p, y) -> begin
(extend_fv' g f ((p), (y)) t_x add_unit is_rec)
end))
end))


let extend_tydef : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  env = (fun g fv td -> (

let m = (module_name_of_fv fv)
in (

let uu___111_974 = g
in {tcenv = uu___111_974.tcenv; gamma = uu___111_974.gamma; tydefs = (((m), (td)))::g.tydefs; currentModule = uu___111_974.currentModule})))


let emptyMlPath : (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * Prims.string) = (([]), (""))


let mkContext : FStar_TypeChecker_Env.env  ->  env = (fun e -> (

let env = {tcenv = e; gamma = []; tydefs = []; currentModule = emptyMlPath}
in (

let a = (("\'a"), ((~- ((Prims.parse_int "1")))))
in (

let failwith_ty = (((a)::[]), (FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.MLTY_Named ((([]), (((("Prims")::[]), ("string")))))), (FStar_Extraction_ML_Syntax.E_IMPURE), (FStar_Extraction_ML_Syntax.MLTY_Var (a))))))
in (

let uu____1011 = (

let uu____1014 = (

let uu____1015 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (uu____1015))
in (extend_lb env uu____1014 FStar_Syntax_Syntax.tun failwith_ty false false))
in (FStar_All.pipe_right uu____1011 Prims.fst))))))


let monad_op_name : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident) = (fun ed nm -> (

let uu____1026 = ((ed.FStar_Syntax_Syntax.mname.FStar_Ident.ns), (ed.FStar_Syntax_Syntax.mname.FStar_Ident.ident))
in (match (uu____1026) with
| (module_name, eff_name) -> begin
(

let mangled_name = (Prims.strcat FStar_Ident.reserved_prefix (Prims.strcat eff_name.FStar_Ident.idText (Prims.strcat "_" nm)))
in (

let mangled_lid = (FStar_Ident.lid_of_ids (FStar_List.append module_name (((FStar_Ident.id_of_text mangled_name))::[])))
in (

let ml_name = (FStar_Extraction_ML_Syntax.mlpath_of_lident mangled_lid)
in (

let lid = (FStar_All.pipe_right (FStar_List.append (FStar_Ident.ids_of_lid ed.FStar_Syntax_Syntax.mname) (((FStar_Ident.id_of_text nm))::[])) FStar_Ident.lid_of_ids)
in ((ml_name), (lid))))))
end)))


let action_name : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.action  ->  (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident) = (fun ed a -> (monad_op_name ed a.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText))


let bind_name : FStar_Syntax_Syntax.eff_decl  ->  (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident) = (fun ed -> (monad_op_name ed "bind"))


let return_name : FStar_Syntax_Syntax.eff_decl  ->  (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident) = (fun ed -> (monad_op_name ed "return"))




