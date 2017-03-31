
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


let lookup_fv_by_lid : env  ->  FStar_Ident.lident  ->  ty_or_exp_b = (fun g lid -> (

let x = (FStar_Util.find_map g.gamma (fun uu___102_435 -> (match (uu___102_435) with
| Fv (fv', x) when (FStar_Syntax_Syntax.fv_eq_lid fv' lid) -> begin
Some (x)
end
| uu____439 -> begin
None
end)))
in (match (x) with
| None -> begin
(

let uu____440 = (FStar_Util.format1 "free Variable %s not found\n" lid.FStar_Ident.nsstr)
in (failwith uu____440))
end
| Some (y) -> begin
y
end)))


let lookup_fv : env  ->  FStar_Syntax_Syntax.fv  ->  ty_or_exp_b = (fun g fv -> (

let x = (FStar_Util.find_map g.gamma (fun uu___103_450 -> (match (uu___103_450) with
| Fv (fv', t) when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
Some (t)
end
| uu____454 -> begin
None
end)))
in (match (x) with
| None -> begin
(

let uu____455 = (

let uu____456 = (FStar_Range.string_of_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.p)
in (

let uu____461 = (FStar_Syntax_Print.lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "(%s) free Variable %s not found\n" uu____456 uu____461)))
in (failwith uu____455))
end
| Some (y) -> begin
y
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  ty_or_exp_b = (fun g bv -> (

let x = (FStar_Util.find_map g.gamma (fun uu___104_475 -> (match (uu___104_475) with
| Bv (bv', r) when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
Some (r)
end
| uu____479 -> begin
None
end)))
in (match (x) with
| None -> begin
(

let uu____480 = (

let uu____481 = (FStar_Range.string_of_range bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)
in (

let uu____482 = (FStar_Syntax_Print.bv_to_string bv)
in (FStar_Util.format2 "(%s) bound Variable %s not found\n" uu____481 uu____482)))
in (failwith uu____480))
end
| Some (y) -> begin
y
end)))


let lookup : env  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual Prims.option) = (fun g x -> (match (x) with
| FStar_Util.Inl (x1) -> begin
(

let uu____504 = (lookup_bv g x1)
in ((uu____504), (None)))
end
| FStar_Util.Inr (x1) -> begin
(

let uu____507 = (lookup_fv g x1)
in ((uu____507), (x1.FStar_Syntax_Syntax.fv_qual)))
end))


let lookup_term : env  ->  FStar_Syntax_Syntax.term  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual Prims.option) = (fun g t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(lookup g (FStar_Util.Inl (x)))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(lookup g (FStar_Util.Inr (x)))
end
| uu____523 -> begin
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

let uu___106_566 = g
in {tcenv = tcenv; gamma = gamma; tydefs = uu___106_566.tydefs; currentModule = uu___106_566.currentModule}))))))


let find_uniq : binding Prims.list  ->  Prims.string  ->  Prims.string = (fun gamma mlident -> (

let rec find_uniq = (fun mlident1 i -> (

let suffix = (match ((i = (Prims.parse_int "0"))) with
| true -> begin
""
end
| uu____583 -> begin
(FStar_Util.string_of_int i)
end)
in (

let target_mlident = (Prims.strcat mlident1 suffix)
in (

let has_collision = (FStar_List.existsb (fun uu___105_586 -> (match (uu___105_586) with
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
| uu____657 -> begin
target_mlident
end)))))
in (find_uniq mlident (Prims.parse_int "0"))))


let extend_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g x t_x add_unit is_rec mk_unit -> (

let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| uu____683 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let uu____684 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (match (uu____684) with
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
| uu____695 -> begin
(match (add_unit) with
| true -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mlx)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end
| uu____697 -> begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mlx)
end)
end)
in (

let gamma = (Bv (((x), (FStar_Util.Inr (((mlsymbol), (mlx1), (t_x), (is_rec)))))))::g.gamma
in (

let tcenv = (

let uu____715 = (FStar_Syntax_Syntax.binders_of_list ((x)::[]))
in (FStar_TypeChecker_Env.push_binders g.tcenv uu____715))
in (((

let uu___107_718 = g
in {tcenv = tcenv; gamma = gamma; tydefs = uu___107_718.tydefs; currentModule = uu___107_718.currentModule})), (mlident1))))))))
end))))


let rec mltyFvars : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlident Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(

let uu____729 = (mltyFvars t1)
in (

let uu____731 = (mltyFvars t2)
in (FStar_List.append uu____729 uu____731)))
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

let uu____755 = (mltyFvars (Prims.snd tys))
in (subsetMlidents uu____755 (Prims.fst tys))))


let extend_fv' : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g x y t_x add_unit is_rec -> (

let uu____779 = (tySchemeIsClosed t_x)
in (match (uu____779) with
| true -> begin
(

let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| uu____785 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let uu____786 = (

let uu____792 = y
in (match (uu____792) with
| (ns, i) -> begin
(

let mlsymbol = (FStar_Extraction_ML_Syntax.avoid_keyword i)
in ((((ns), (mlsymbol))), (mlsymbol)))
end))
in (match (uu____786) with
| (mlpath, mlsymbol) -> begin
(

let mly = FStar_Extraction_ML_Syntax.MLE_Name (mlpath)
in (

let mly1 = (match (add_unit) with
| true -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mly)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end
| uu____820 -> begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mly)
end)
in (

let gamma = (Fv (((x), (FStar_Util.Inr (((mlsymbol), (mly1), (t_x), (is_rec)))))))::g.gamma
in (((

let uu___108_839 = g
in {tcenv = uu___108_839.tcenv; gamma = gamma; tydefs = uu___108_839.tydefs; currentModule = uu___108_839.currentModule})), (((mlsymbol), ((Prims.parse_int "0"))))))))
end)))
end
| uu____840 -> begin
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

let uu____893 = (FStar_Extraction_ML_Syntax.mlpath_of_lident f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____893) with
| (p, y) -> begin
(extend_fv' g f ((p), (y)) t_x add_unit is_rec)
end))
end))


let extend_tydef : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  env = (fun g fv td -> (

let m = (module_name_of_fv fv)
in (

let uu___109_916 = g
in {tcenv = uu___109_916.tcenv; gamma = uu___109_916.gamma; tydefs = (((m), (td)))::g.tydefs; currentModule = uu___109_916.currentModule})))


let emptyMlPath : (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * Prims.string) = (([]), (""))


let mkContext : FStar_TypeChecker_Env.env  ->  env = (fun e -> (

let env = {tcenv = e; gamma = []; tydefs = []; currentModule = emptyMlPath}
in (

let a = (("\'a"), ((~- ((Prims.parse_int "1")))))
in (

let failwith_ty = (((a)::[]), (FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.MLTY_Named ((([]), (((("Prims")::[]), ("string")))))), (FStar_Extraction_ML_Syntax.E_IMPURE), (FStar_Extraction_ML_Syntax.MLTY_Var (a))))))
in (

let uu____953 = (

let uu____956 = (

let uu____957 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (uu____957))
in (extend_lb env uu____956 FStar_Syntax_Syntax.tun failwith_ty false false))
in (FStar_All.pipe_right uu____953 Prims.fst))))))


let monad_op_name : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident) = (fun ed nm -> (

let uu____968 = ((ed.FStar_Syntax_Syntax.mname.FStar_Ident.ns), (ed.FStar_Syntax_Syntax.mname.FStar_Ident.ident))
in (match (uu____968) with
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




