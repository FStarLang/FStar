
open Prims

type ty_or_exp_b =
((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty), (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool)) FStar_Util.either

type binding =
| Bv of (FStar_Syntax_Syntax.bv * ty_or_exp_b)
| Fv of (FStar_Syntax_Syntax.fv * ty_or_exp_b)


let uu___is_Bv : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bv (_0) -> begin
true
end
| uu____24 -> begin
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
| uu____44 -> begin
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

let uu____113 = (FStar_Options.debug_at_level c (FStar_Options.Other ("Extraction")))
in (match (uu____113) with
| true -> begin
(f ())
end
| uu____114 -> begin
()
end))))


let mkFvvar : FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.fv = (fun l t -> (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant None))


let erasedContent : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.ml_unit_ty


let erasableTypeNoDelta : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> (match ((t = FStar_Extraction_ML_Syntax.ml_unit_ty)) with
| true -> begin
true
end
| uu____124 -> begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____125, (("FStar")::("Ghost")::[], "erased")) -> begin
true
end
| uu____132 -> begin
false
end)
end))


let unknownType : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Top


let prependTick = (fun uu____143 -> (match (uu____143) with
| (x, n) -> begin
(match ((FStar_Util.starts_with x "\'")) with
| true -> begin
((x), (n))
end
| uu____150 -> begin
(((Prims.strcat "\'A" x)), (n))
end)
end))


let removeTick = (fun uu____161 -> (match (uu____161) with
| (x, n) -> begin
(match ((FStar_Util.starts_with x "\'")) with
| true -> begin
(

let uu____168 = (FStar_Util.substring_from x (Prims.parse_int "1"))
in ((uu____168), (n)))
end
| uu____169 -> begin
((x), (n))
end)
end))


let convRange : FStar_Range.range  ->  Prims.int = (fun r -> (Prims.parse_int "0"))


let convIdent : FStar_Ident.ident  ->  FStar_Extraction_ML_Syntax.mlident = (fun id -> ((id.FStar_Ident.idText), ((Prims.parse_int "0"))))


let bv_as_ml_tyvar : FStar_Syntax_Syntax.bv  ->  (Prims.string * Prims.int) = (fun x -> (

let uu____181 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (prependTick uu____181)))


let bv_as_ml_termvar : FStar_Syntax_Syntax.bv  ->  (Prims.string * Prims.int) = (fun x -> (

let uu____189 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (removeTick uu____189)))


let rec lookup_ty_local : binding Prims.list  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun gamma b -> (match (gamma) with
| (Bv (b', FStar_Util.Inl (mli, mlt)))::tl -> begin
(match ((FStar_Syntax_Syntax.bv_eq b b')) with
| true -> begin
mlt
end
| uu____217 -> begin
(lookup_ty_local tl b)
end)
end
| (Bv (b', FStar_Util.Inr (uu____219)))::tl -> begin
(match ((FStar_Syntax_Syntax.bv_eq b b')) with
| true -> begin
(failwith (Prims.strcat "Type/Expr clash: " b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
end
| uu____237 -> begin
(lookup_ty_local tl b)
end)
end
| (uu____238)::tl -> begin
(lookup_ty_local tl b)
end
| [] -> begin
(failwith (Prims.strcat "extraction: unbound type var " b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
end))


let tyscheme_of_td = (fun uu____258 -> (match (uu____258) with
| (uu____265, uu____266, uu____267, vars, body_opt) -> begin
(match (body_opt) with
| Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t)) -> begin
Some (((vars), (t)))
end
| uu____277 -> begin
None
end)
end))


let lookup_ty_const : env  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme Prims.option = (fun env uu____285 -> (match (uu____285) with
| (module_name, ty_name) -> begin
(FStar_Util.find_map env.tydefs (fun uu____295 -> (match (uu____295) with
| (m, tds) -> begin
(match ((module_name = m)) with
| true -> begin
(FStar_Util.find_map tds (fun td -> (

let uu____307 = td
in (match (uu____307) with
| (uu____309, n, uu____311, uu____312, uu____313) -> begin
(match ((n = ty_name)) with
| true -> begin
(tyscheme_of_td td)
end
| uu____320 -> begin
None
end)
end))))
end
| uu____321 -> begin
None
end)
end)))
end))


let module_name_of_fv : FStar_Syntax_Syntax.fv  ->  Prims.string Prims.list = (fun fv -> (FStar_All.pipe_right fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ns (FStar_List.map (fun i -> i.FStar_Ident.idText))))


let maybe_mangle_type_projector : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mlpath Prims.option = (fun env fv -> (

let mname = (module_name_of_fv fv)
in (

let ty_name = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ident.FStar_Ident.idText
in (FStar_Util.find_map env.tydefs (fun uu____354 -> (match (uu____354) with
| (m, tds) -> begin
(FStar_Util.find_map tds (fun uu____369 -> (match (uu____369) with
| (uu____374, n, mangle_opt, uu____377, uu____378) -> begin
(match ((m = mname)) with
| true -> begin
(match ((n = ty_name)) with
| true -> begin
(match (mangle_opt) with
| None -> begin
Some (((m), (n)))
end
| Some (mangled) -> begin
(

let modul = m
in Some (((modul), (mangled))))
end)
end
| uu____407 -> begin
None
end)
end
| uu____411 -> begin
None
end)
end)))
end))))))


let lookup_tyvar : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bt -> (lookup_ty_local g.gamma bt))


let lookup_fv_by_lid : env  ->  FStar_Ident.lident  ->  ty_or_exp_b = (fun g lid -> (

let x = (FStar_Util.find_map g.gamma (fun uu___100_429 -> (match (uu___100_429) with
| Fv (fv', x) when (FStar_Syntax_Syntax.fv_eq_lid fv' lid) -> begin
Some (x)
end
| uu____433 -> begin
None
end)))
in (match (x) with
| None -> begin
(

let uu____434 = (FStar_Util.format1 "free Variable %s not found\n" lid.FStar_Ident.nsstr)
in (failwith uu____434))
end
| Some (y) -> begin
y
end)))


let lookup_fv : env  ->  FStar_Syntax_Syntax.fv  ->  ty_or_exp_b = (fun g fv -> (

let x = (FStar_Util.find_map g.gamma (fun uu___101_444 -> (match (uu___101_444) with
| Fv (fv', t) when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
Some (t)
end
| uu____448 -> begin
None
end)))
in (match (x) with
| None -> begin
(

let uu____449 = (

let uu____450 = (FStar_Range.string_of_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.p)
in (

let uu____455 = (FStar_Syntax_Print.lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "(%s) free Variable %s not found\n" uu____450 uu____455)))
in (failwith uu____449))
end
| Some (y) -> begin
y
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  ty_or_exp_b = (fun g bv -> (

let x = (FStar_Util.find_map g.gamma (fun uu___102_469 -> (match (uu___102_469) with
| Bv (bv', r) when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
Some (r)
end
| uu____473 -> begin
None
end)))
in (match (x) with
| None -> begin
(

let uu____474 = (

let uu____475 = (FStar_Range.string_of_range bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)
in (

let uu____476 = (FStar_Syntax_Print.bv_to_string bv)
in (FStar_Util.format2 "(%s) bound Variable %s not found\n" uu____475 uu____476)))
in (failwith uu____474))
end
| Some (y) -> begin
y
end)))


let lookup : env  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual Prims.option) = (fun g x -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let uu____498 = (lookup_bv g x)
in ((uu____498), (None)))
end
| FStar_Util.Inr (x) -> begin
(

let uu____501 = (lookup_fv g x)
in ((uu____501), (x.FStar_Syntax_Syntax.fv_qual)))
end))


let lookup_term : env  ->  FStar_Syntax_Syntax.term  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual Prims.option) = (fun g t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(lookup g (FStar_Util.Inl (x)))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(lookup g (FStar_Util.Inr (x)))
end
| uu____517 -> begin
(failwith "Impossible: lookup_term for a non-name")
end))


let extend_ty : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty Prims.option  ->  env = (fun g a mapped_to -> (

let ml_a = (bv_as_ml_tyvar a)
in (

let mapped_to = (match (mapped_to) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Var (ml_a)
end
| Some (t) -> begin
t
end)
in (

let gamma = (Bv (((a), (FStar_Util.Inl (((ml_a), (mapped_to)))))))::g.gamma
in (

let tcenv = (FStar_TypeChecker_Env.push_bv g.tcenv a)
in (

let uu___103_558 = g
in {tcenv = tcenv; gamma = gamma; tydefs = uu___103_558.tydefs; currentModule = uu___103_558.currentModule}))))))


let extend_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x t_x add_unit is_rec mk_unit -> (

let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| uu____580 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let mlx = (

let uu____582 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLE_Var (uu____582))
in (

let mlx = (match (mk_unit) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____584 -> begin
(match (add_unit) with
| true -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mlx)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end
| uu____586 -> begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mlx)
end)
end)
in (

let gamma = (Bv (((x), (FStar_Util.Inr (((mlx), (t_x), (is_rec)))))))::g.gamma
in (

let tcenv = (

let uu____602 = (FStar_Syntax_Syntax.binders_of_list ((x)::[]))
in (FStar_TypeChecker_Env.push_binders g.tcenv uu____602))
in (

let uu___104_603 = g
in {tcenv = tcenv; gamma = gamma; tydefs = uu___104_603.tydefs; currentModule = uu___104_603.currentModule})))))))


let rec mltyFvars : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlident Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(

let uu____614 = (mltyFvars t1)
in (

let uu____616 = (mltyFvars t2)
in (FStar_List.append uu____614 uu____616)))
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

let uu____640 = (mltyFvars (Prims.snd tys))
in (subsetMlidents uu____640 (Prims.fst tys))))


let extend_fv' : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x y t_x add_unit is_rec -> (

let uu____660 = (tySchemeIsClosed t_x)
in (match (uu____660) with
| true -> begin
(

let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| uu____664 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let mly = FStar_Extraction_ML_Syntax.MLE_Name ((

let uu____666 = y
in (match (uu____666) with
| (ns, i) -> begin
((ns), ((FStar_Extraction_ML_Syntax.avoid_keyword i)))
end)))
in (

let mly = (match (add_unit) with
| true -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mly)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end
| uu____674 -> begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mly)
end)
in (

let gamma = (Fv (((x), (FStar_Util.Inr (((mly), (t_x), (is_rec)))))))::g.gamma
in (

let uu___105_689 = g
in {tcenv = uu___105_689.tcenv; gamma = gamma; tydefs = uu___105_689.tydefs; currentModule = uu___105_689.currentModule})))))
end
| uu____690 -> begin
(failwith "freevars found")
end)))


let extend_fv : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x t_x add_unit is_rec -> (

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (extend_fv' g x mlp t_x add_unit is_rec)))


let extend_lb : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g l t t_x add_unit is_rec -> (match (l) with
| FStar_Util.Inl (x) -> begin
(

let uu____736 = (extend_bv g x t_x add_unit is_rec false)
in (

let uu____737 = (bv_as_ml_termvar x)
in ((uu____736), (uu____737))))
end
| FStar_Util.Inr (f) -> begin
(

let uu____743 = (FStar_Extraction_ML_Syntax.mlpath_of_lident f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____743) with
| (p, y) -> begin
(

let uu____754 = (extend_fv' g f ((p), (y)) t_x add_unit is_rec)
in ((uu____754), ((((FStar_Extraction_ML_Syntax.avoid_keyword y)), ((Prims.parse_int "0"))))))
end))
end))


let extend_tydef : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  env = (fun g fv td -> (

let m = (module_name_of_fv fv)
in (

let uu___106_769 = g
in {tcenv = uu___106_769.tcenv; gamma = uu___106_769.gamma; tydefs = (((m), (td)))::g.tydefs; currentModule = uu___106_769.currentModule})))


let emptyMlPath : (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * Prims.string) = (([]), (""))


let mkContext : FStar_TypeChecker_Env.env  ->  env = (fun e -> (

let env = {tcenv = e; gamma = []; tydefs = []; currentModule = emptyMlPath}
in (

let a = (("\'a"), ((~- ((Prims.parse_int "1")))))
in (

let failwith_ty = (((a)::[]), (FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.MLTY_Named ((([]), (((("Prims")::[]), ("string")))))), (FStar_Extraction_ML_Syntax.E_IMPURE), (FStar_Extraction_ML_Syntax.MLTY_Var (a))))))
in (

let uu____806 = (

let uu____809 = (

let uu____810 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (uu____810))
in (extend_lb env uu____809 FStar_Syntax_Syntax.tun failwith_ty false false))
in (FStar_All.pipe_right uu____806 Prims.fst))))))


let monad_op_name : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident) = (fun ed nm -> (

let uu____821 = ((ed.FStar_Syntax_Syntax.mname.FStar_Ident.ns), (ed.FStar_Syntax_Syntax.mname.FStar_Ident.ident))
in (match (uu____821) with
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




