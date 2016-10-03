
open Prims

type ty_or_exp_b =
((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty), (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool)) FStar_Util.either


type binding =
| Bv of (FStar_Syntax_Syntax.bv * ty_or_exp_b)
| Fv of (FStar_Syntax_Syntax.fv * ty_or_exp_b)


let is_Bv = (fun _discr_ -> (match (_discr_) with
| Bv (_) -> begin
true
end
| _ -> begin
false
end))


let is_Fv = (fun _discr_ -> (match (_discr_) with
| Fv (_) -> begin
true
end
| _ -> begin
false
end))


let ___Bv____0 = (fun projectee -> (match (projectee) with
| Bv (_73_6) -> begin
_73_6
end))


let ___Fv____0 = (fun projectee -> (match (projectee) with
| Fv (_73_9) -> begin
_73_9
end))


type env =
{tcenv : FStar_TypeChecker_Env.env; gamma : binding Prims.list; tydefs : (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * FStar_Extraction_ML_Syntax.mltydecl) Prims.list; currentModule : FStar_Extraction_ML_Syntax.mlpath}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let debug : env  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun g f -> (

let c = (FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule)
in if (FStar_Options.debug_at_level c (FStar_Options.Other ("Extraction"))) then begin
(f ())
end else begin
()
end))


let mkFvvar : FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.fv = (fun l t -> (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant None))


let erasedContent : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.ml_unit_ty


let erasableTypeNoDelta : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> if (t = FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
true
end else begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_73_22, (("FStar")::("Ghost")::[], "erased")) -> begin
true
end
| _73_31 -> begin
false
end)
end)


let unknownType : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Top


let prependTick = (fun _73_34 -> (match (_73_34) with
| (x, n) -> begin
if (FStar_Util.starts_with x "\'") then begin
((x), (n))
end else begin
(((Prims.strcat "\'A" x)), (n))
end
end))


let removeTick = (fun _73_37 -> (match (_73_37) with
| (x, n) -> begin
if (FStar_Util.starts_with x "\'") then begin
(let _170_59 = (FStar_Util.substring_from x (Prims.parse_int "1"))
in ((_170_59), (n)))
end else begin
((x), (n))
end
end))


let convRange : FStar_Range.range  ->  Prims.int = (fun r -> (Prims.parse_int "0"))


let convIdent : FStar_Ident.ident  ->  (Prims.string * Prims.int) = (fun id -> ((id.FStar_Ident.idText), ((Prims.parse_int "0"))))


let bv_as_ml_tyvar : FStar_Syntax_Syntax.bv  ->  (Prims.string * Prims.int) = (fun x -> (let _170_66 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (prependTick _170_66)))


let bv_as_ml_termvar : FStar_Syntax_Syntax.bv  ->  (Prims.string * Prims.int) = (fun x -> (let _170_69 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (removeTick _170_69)))


let rec lookup_ty_local : binding Prims.list  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun gamma b -> (match (gamma) with
| (Bv (b', FStar_Util.Inl (mli, mlt)))::tl -> begin
if (FStar_Syntax_Syntax.bv_eq b b') then begin
mlt
end else begin
(lookup_ty_local tl b)
end
end
| (Bv (b', FStar_Util.Inr (_73_56)))::tl -> begin
if (FStar_Syntax_Syntax.bv_eq b b') then begin
(FStar_All.failwith (Prims.strcat "Type/Expr clash: " b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
end else begin
(lookup_ty_local tl b)
end
end
| (_73_63)::tl -> begin
(lookup_ty_local tl b)
end
| [] -> begin
(FStar_All.failwith (Prims.strcat "extraction: unbound type var " b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
end))


let tyscheme_of_td = (fun _73_72 -> (match (_73_72) with
| (_73_67, _73_69, vars, body_opt) -> begin
(match (body_opt) with
| Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t)) -> begin
Some (((vars), (t)))
end
| _73_77 -> begin
None
end)
end))


let lookup_ty_const : env  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme Prims.option = (fun env _73_81 -> (match (_73_81) with
| (module_name, ty_name) -> begin
(FStar_Util.find_map env.tydefs (fun _73_84 -> (match (_73_84) with
| (m, tds) -> begin
if (module_name = m) then begin
(FStar_Util.find_map tds (fun td -> (

let _73_93 = td
in (match (_73_93) with
| (_73_87, n, _73_90, _73_92) -> begin
if (n = ty_name) then begin
(tyscheme_of_td td)
end else begin
None
end
end))))
end else begin
None
end
end)))
end))


let lookup_tyvar : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bt -> (lookup_ty_local g.gamma bt))


let lookup_fv_by_lid : env  ->  FStar_Ident.lident  ->  ty_or_exp_b = (fun g lid -> (

let x = (FStar_Util.find_map g.gamma (fun _73_1 -> (match (_73_1) with
| Fv (fv', x) when (FStar_Syntax_Syntax.fv_eq_lid fv' lid) -> begin
Some (x)
end
| _73_104 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _170_90 = (FStar_Util.format1 "free Variable %s not found\n" lid.FStar_Ident.nsstr)
in (FStar_All.failwith _170_90))
end
| Some (y) -> begin
y
end)))


let lookup_fv : env  ->  FStar_Syntax_Syntax.fv  ->  ty_or_exp_b = (fun g fv -> (

let x = (FStar_Util.find_map g.gamma (fun _73_2 -> (match (_73_2) with
| Fv (fv', t) when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
Some (t)
end
| _73_117 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _170_98 = (let _170_97 = (FStar_Range.string_of_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.p)
in (let _170_96 = (FStar_Syntax_Print.lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "(%s) free Variable %s not found\n" _170_97 _170_96)))
in (FStar_All.failwith _170_98))
end
| Some (y) -> begin
y
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  ty_or_exp_b = (fun g bv -> (

let x = (FStar_Util.find_map g.gamma (fun _73_3 -> (match (_73_3) with
| Bv (bv', r) when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
Some (r)
end
| _73_130 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _170_106 = (let _170_105 = (FStar_Range.string_of_range bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)
in (let _170_104 = (FStar_Syntax_Print.bv_to_string bv)
in (FStar_Util.format2 "(%s) bound Variable %s not found\n" _170_105 _170_104)))
in (FStar_All.failwith _170_106))
end
| Some (y) -> begin
y
end)))


let lookup : env  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual Prims.option) = (fun g x -> (match (x) with
| FStar_Util.Inl (x) -> begin
(let _170_111 = (lookup_bv g x)
in ((_170_111), (None)))
end
| FStar_Util.Inr (x) -> begin
(let _170_112 = (lookup_fv g x)
in ((_170_112), (x.FStar_Syntax_Syntax.fv_qual)))
end))


let lookup_term : env  ->  FStar_Syntax_Syntax.term  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual Prims.option) = (fun g t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(lookup g (FStar_Util.Inl (x)))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(lookup g (FStar_Util.Inr (x)))
end
| _73_148 -> begin
(FStar_All.failwith "Impossible: lookup_term for a non-name")
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

let _73_159 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _73_159.tydefs; currentModule = _73_159.currentModule}))))))


let extend_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x t_x add_unit is_rec mk_unit -> (

let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| _73_171 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let mlx = (let _170_135 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLE_Var (_170_135))
in (

let mlx = if mk_unit then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
if add_unit then begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mlx)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end else begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mlx)
end
end
in (

let gamma = (Bv (((x), (FStar_Util.Inr (((mlx), (t_x), (is_rec)))))))::g.gamma
in (

let tcenv = (let _170_136 = (FStar_Syntax_Syntax.binders_of_list ((x)::[]))
in (FStar_TypeChecker_Env.push_binders g.tcenv _170_136))
in (

let _73_177 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _73_177.tydefs; currentModule = _73_177.currentModule})))))))


let rec mltyFvars : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlident Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(let _170_140 = (mltyFvars t1)
in (let _170_139 = (mltyFvars t2)
in (FStar_List.append _170_140 _170_139)))
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


let tySchemeIsClosed : FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool = (fun tys -> (let _170_147 = (mltyFvars (Prims.snd tys))
in (subsetMlidents _170_147 (Prims.fst tys))))


let extend_fv' : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x y t_x add_unit is_rec -> if (tySchemeIsClosed t_x) then begin
(

let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| _73_211 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let mly = FStar_Extraction_ML_Syntax.MLE_Name (y)
in (

let mly = if add_unit then begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mly)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end else begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mly)
end
in (

let gamma = (Fv (((x), (FStar_Util.Inr (((mly), (t_x), (is_rec)))))))::g.gamma
in (

let tcenv = (FStar_TypeChecker_Env.push_let_binding g.tcenv (FStar_Util.Inr (x)) (([]), (x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)))
in (

let _73_217 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _73_217.tydefs; currentModule = _73_217.currentModule}))))))
end else begin
(FStar_All.failwith "freevars found")
end)


let extend_fv : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x t_x add_unit is_rec -> (

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (extend_fv' g x mlp t_x add_unit is_rec)))


let extend_lb : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g l t t_x add_unit is_rec -> (match (l) with
| FStar_Util.Inl (x) -> begin
(let _170_183 = (extend_bv g x t_x add_unit is_rec false)
in (let _170_182 = (bv_as_ml_termvar x)
in ((_170_183), (_170_182))))
end
| FStar_Util.Inr (f) -> begin
(

let _73_237 = (FStar_Extraction_ML_Syntax.mlpath_of_lident f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_73_237) with
| (p, y) -> begin
(let _170_184 = (extend_fv' g f ((p), (y)) t_x add_unit is_rec)
in ((_170_184), (((y), ((Prims.parse_int "0"))))))
end))
end))


let extend_tydef : env  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  env = (fun g td -> (

let m = (FStar_List.append (Prims.fst g.currentModule) (((Prims.snd g.currentModule))::[]))
in (

let _73_241 = g
in {tcenv = _73_241.tcenv; gamma = _73_241.gamma; tydefs = (((m), (td)))::g.tydefs; currentModule = _73_241.currentModule})))


let emptyMlPath : (Prims.string Prims.list * Prims.string) = (([]), (""))


let mkContext : FStar_TypeChecker_Env.env  ->  env = (fun e -> (

let env = {tcenv = e; gamma = []; tydefs = []; currentModule = emptyMlPath}
in (

let a = (("\'a"), ((~- ((Prims.parse_int "1")))))
in (

let failwith_ty = (((a)::[]), (FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.MLTY_Named ((([]), (((("Prims")::[]), ("string")))))), (FStar_Extraction_ML_Syntax.E_IMPURE), (FStar_Extraction_ML_Syntax.MLTY_Var (a))))))
in (let _170_193 = (let _170_192 = (let _170_191 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (_170_191))
in (extend_lb env _170_192 FStar_Syntax_Syntax.tun failwith_ty false false))
in (FStar_All.pipe_right _170_193 Prims.fst))))))


let monad_op_name : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  ((Prims.string Prims.list * Prims.string) * FStar_Ident.lident) = (fun ed nm -> (

let _73_251 = ((ed.FStar_Syntax_Syntax.mname.FStar_Ident.ns), (ed.FStar_Syntax_Syntax.mname.FStar_Ident.ident))
in (match (_73_251) with
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


let action_name : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.action  ->  ((Prims.string Prims.list * Prims.string) * FStar_Ident.lident) = (fun ed a -> (monad_op_name ed a.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText))


let bind_name : FStar_Syntax_Syntax.eff_decl  ->  ((Prims.string Prims.list * Prims.string) * FStar_Ident.lident) = (fun ed -> (monad_op_name ed "bind"))


let return_name : FStar_Syntax_Syntax.eff_decl  ->  ((Prims.string Prims.list * Prims.string) * FStar_Ident.lident) = (fun ed -> (monad_op_name ed "return"))




