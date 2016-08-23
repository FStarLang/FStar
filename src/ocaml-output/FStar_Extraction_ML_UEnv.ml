
open Prims
# 25 "FStar.Extraction.ML.UEnv.fst"
type ty_or_exp_b =
((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty), (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool)) FStar_Util.either

# 27 "FStar.Extraction.ML.UEnv.fst"
type binding =
| Bv of (FStar_Syntax_Syntax.bv * ty_or_exp_b)
| Fv of (FStar_Syntax_Syntax.fv * ty_or_exp_b)

# 28 "FStar.Extraction.ML.UEnv.fst"
let is_Bv = (fun _discr_ -> (match (_discr_) with
| Bv (_) -> begin
true
end
| _ -> begin
false
end))

# 29 "FStar.Extraction.ML.UEnv.fst"
let is_Fv = (fun _discr_ -> (match (_discr_) with
| Fv (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.Extraction.ML.UEnv.fst"
let ___Bv____0 = (fun projectee -> (match (projectee) with
| Bv (_72_6) -> begin
_72_6
end))

# 29 "FStar.Extraction.ML.UEnv.fst"
let ___Fv____0 = (fun projectee -> (match (projectee) with
| Fv (_72_9) -> begin
_72_9
end))

# 31 "FStar.Extraction.ML.UEnv.fst"
type env =
{tcenv : FStar_TypeChecker_Env.env; gamma : binding Prims.list; tydefs : (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * FStar_Extraction_ML_Syntax.mltydecl) Prims.list; currentModule : FStar_Extraction_ML_Syntax.mlpath}

# 31 "FStar.Extraction.ML.UEnv.fst"
let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

# 40 "FStar.Extraction.ML.UEnv.fst"
let debug : env  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun g f -> (
# 41 "FStar.Extraction.ML.UEnv.fst"
let c = (FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule)
in if (FStar_Options.debug_at_level c (FStar_Options.Other ("Extraction"))) then begin
(f ())
end else begin
()
end))

# 46 "FStar.Extraction.ML.UEnv.fst"
let mkFvvar : FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.fv = (fun l t -> (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant None))

# 50 "FStar.Extraction.ML.UEnv.fst"
let erasedContent : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.ml_unit_ty

# 52 "FStar.Extraction.ML.UEnv.fst"
let erasableTypeNoDelta : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> if (t = FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
true
end else begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_72_22, (("FStar")::("Ghost")::[], "erased")) -> begin
true
end
| _72_31 -> begin
false
end)
end)

# 59 "FStar.Extraction.ML.UEnv.fst"
let unknownType : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Top

# 62 "FStar.Extraction.ML.UEnv.fst"
let prependTick = (fun _72_34 -> (match (_72_34) with
| (x, n) -> begin
if (FStar_Util.starts_with x "\'") then begin
((x), (n))
end else begin
(((Prims.strcat "\'A" x)), (n))
end
end))

# 63 "FStar.Extraction.ML.UEnv.fst"
let removeTick = (fun _72_37 -> (match (_72_37) with
| (x, n) -> begin
if (FStar_Util.starts_with x "\'") then begin
(let _165_59 = (FStar_Util.substring_from x 1)
in ((_165_59), (n)))
end else begin
((x), (n))
end
end))

# 65 "FStar.Extraction.ML.UEnv.fst"
let convRange : FStar_Range.range  ->  Prims.int = (fun r -> 0)

# 66 "FStar.Extraction.ML.UEnv.fst"
let convIdent : FStar_Ident.ident  ->  (Prims.string * Prims.int) = (fun id -> ((id.FStar_Ident.idText), (0)))

# 81 "FStar.Extraction.ML.UEnv.fst"
let bv_as_ml_tyvar : FStar_Syntax_Syntax.bv  ->  (Prims.string * Prims.int) = (fun x -> (let _165_66 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (prependTick _165_66)))

# 82 "FStar.Extraction.ML.UEnv.fst"
let bv_as_ml_termvar : FStar_Syntax_Syntax.bv  ->  (Prims.string * Prims.int) = (fun x -> (let _165_69 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (removeTick _165_69)))

# 84 "FStar.Extraction.ML.UEnv.fst"
let rec lookup_ty_local : binding Prims.list  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun gamma b -> (match (gamma) with
| (Bv (b', FStar_Util.Inl (mli, mlt)))::tl -> begin
if (FStar_Syntax_Syntax.bv_eq b b') then begin
mlt
end else begin
(lookup_ty_local tl b)
end
end
| (Bv (b', FStar_Util.Inr (_72_56)))::tl -> begin
if (FStar_Syntax_Syntax.bv_eq b b') then begin
(FStar_All.failwith (Prims.strcat "Type/Expr clash: " b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
end else begin
(lookup_ty_local tl b)
end
end
| (_72_63)::tl -> begin
(lookup_ty_local tl b)
end
| [] -> begin
(FStar_All.failwith (Prims.strcat "extraction: unbound type var " b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
end))

# 91 "FStar.Extraction.ML.UEnv.fst"
let tyscheme_of_td = (fun _72_70 -> (match (_72_70) with
| (_72_67, vars, body_opt) -> begin
(match (body_opt) with
| Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t)) -> begin
Some (((vars), (t)))
end
| _72_75 -> begin
None
end)
end))

# 96 "FStar.Extraction.ML.UEnv.fst"
let lookup_ty_const : env  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme Prims.option = (fun env _72_79 -> (match (_72_79) with
| (module_name, ty_name) -> begin
(FStar_Util.find_map env.tydefs (fun _72_82 -> (match (_72_82) with
| (m, tds) -> begin
if (module_name = m) then begin
(FStar_Util.find_map tds (fun td -> (
# 100 "FStar.Extraction.ML.UEnv.fst"
let _72_89 = td
in (match (_72_89) with
| (n, _72_86, _72_88) -> begin
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

# 106 "FStar.Extraction.ML.UEnv.fst"
let lookup_tyvar : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bt -> (lookup_ty_local g.gamma bt))

# 108 "FStar.Extraction.ML.UEnv.fst"
let lookup_fv_by_lid : env  ->  FStar_Ident.lident  ->  ty_or_exp_b = (fun g lid -> (
# 109 "FStar.Extraction.ML.UEnv.fst"
let x = (FStar_Util.find_map g.gamma (fun _72_1 -> (match (_72_1) with
| Fv (fv', x) when (FStar_Syntax_Syntax.fv_eq_lid fv' lid) -> begin
Some (x)
end
| _72_100 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _165_90 = (FStar_Util.format1 "free Variable %s not found\n" lid.FStar_Ident.nsstr)
in (FStar_All.failwith _165_90))
end
| Some (y) -> begin
y
end)))

# 117 "FStar.Extraction.ML.UEnv.fst"
let lookup_fv : env  ->  FStar_Syntax_Syntax.fv  ->  ty_or_exp_b = (fun g fv -> (
# 118 "FStar.Extraction.ML.UEnv.fst"
let x = (FStar_Util.find_map g.gamma (fun _72_2 -> (match (_72_2) with
| Fv (fv', t) when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
Some (t)
end
| _72_113 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _165_98 = (let _165_97 = (FStar_Range.string_of_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.p)
in (let _165_96 = (FStar_Syntax_Print.lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "(%s) free Variable %s not found\n" _165_97 _165_96)))
in (FStar_All.failwith _165_98))
end
| Some (y) -> begin
y
end)))

# 125 "FStar.Extraction.ML.UEnv.fst"
let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  ty_or_exp_b = (fun g bv -> (
# 126 "FStar.Extraction.ML.UEnv.fst"
let x = (FStar_Util.find_map g.gamma (fun _72_3 -> (match (_72_3) with
| Bv (bv', r) when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
Some (r)
end
| _72_126 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _165_106 = (let _165_105 = (FStar_Range.string_of_range bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)
in (let _165_104 = (FStar_Syntax_Print.bv_to_string bv)
in (FStar_Util.format2 "(%s) bound Variable %s not found\n" _165_105 _165_104)))
in (FStar_All.failwith _165_106))
end
| Some (y) -> begin
y
end)))

# 134 "FStar.Extraction.ML.UEnv.fst"
let lookup : env  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual Prims.option) = (fun g x -> (match (x) with
| FStar_Util.Inl (x) -> begin
(let _165_111 = (lookup_bv g x)
in ((_165_111), (None)))
end
| FStar_Util.Inr (x) -> begin
(let _165_112 = (lookup_fv g x)
in ((_165_112), (x.FStar_Syntax_Syntax.fv_qual)))
end))

# 139 "FStar.Extraction.ML.UEnv.fst"
let lookup_term : env  ->  FStar_Syntax_Syntax.term  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual Prims.option) = (fun g t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(lookup g (FStar_Util.Inl (x)))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(lookup g (FStar_Util.Inr (x)))
end
| _72_144 -> begin
(FStar_All.failwith "Impossible: lookup_term for a non-name")
end))

# 153 "FStar.Extraction.ML.UEnv.fst"
let extend_ty : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty Prims.option  ->  env = (fun g a mapped_to -> (
# 154 "FStar.Extraction.ML.UEnv.fst"
let ml_a = (bv_as_ml_tyvar a)
in (
# 155 "FStar.Extraction.ML.UEnv.fst"
let mapped_to = (match (mapped_to) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Var (ml_a)
end
| Some (t) -> begin
t
end)
in (
# 158 "FStar.Extraction.ML.UEnv.fst"
let gamma = (Bv (((a), (FStar_Util.Inl (((ml_a), (mapped_to)))))))::g.gamma
in (
# 159 "FStar.Extraction.ML.UEnv.fst"
let tcenv = (FStar_TypeChecker_Env.push_bv g.tcenv a)
in (
# 160 "FStar.Extraction.ML.UEnv.fst"
let _72_155 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _72_155.tydefs; currentModule = _72_155.currentModule}))))))

# 162 "FStar.Extraction.ML.UEnv.fst"
let extend_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x t_x add_unit is_rec mk_unit -> (
# 163 "FStar.Extraction.ML.UEnv.fst"
let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| _72_167 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (
# 166 "FStar.Extraction.ML.UEnv.fst"
let mlx = (let _165_135 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLE_Var (_165_135))
in (
# 167 "FStar.Extraction.ML.UEnv.fst"
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
# 172 "FStar.Extraction.ML.UEnv.fst"
let gamma = (Bv (((x), (FStar_Util.Inr (((mlx), (t_x), (is_rec)))))))::g.gamma
in (
# 173 "FStar.Extraction.ML.UEnv.fst"
let tcenv = (let _165_136 = (FStar_Syntax_Syntax.binders_of_list ((x)::[]))
in (FStar_TypeChecker_Env.push_binders g.tcenv _165_136))
in (
# 174 "FStar.Extraction.ML.UEnv.fst"
let _72_173 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _72_173.tydefs; currentModule = _72_173.currentModule})))))))

# 176 "FStar.Extraction.ML.UEnv.fst"
let rec mltyFvars : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlident Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(let _165_140 = (mltyFvars t1)
in (let _165_139 = (mltyFvars t2)
in (FStar_List.append _165_140 _165_139)))
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

# 184 "FStar.Extraction.ML.UEnv.fst"
let rec subsetMlidents : FStar_Extraction_ML_Syntax.mlident Prims.list  ->  FStar_Extraction_ML_Syntax.mlident Prims.list  ->  Prims.bool = (fun la lb -> (match (la) with
| (h)::tla -> begin
((FStar_List.contains h lb) && (subsetMlidents tla lb))
end
| [] -> begin
true
end))

# 189 "FStar.Extraction.ML.UEnv.fst"
let tySchemeIsClosed : FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool = (fun tys -> (let _165_147 = (mltyFvars (Prims.snd tys))
in (subsetMlidents _165_147 (Prims.fst tys))))

# 192 "FStar.Extraction.ML.UEnv.fst"
let extend_fv' : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x y t_x add_unit is_rec -> if (tySchemeIsClosed t_x) then begin
(
# 195 "FStar.Extraction.ML.UEnv.fst"
let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| _72_207 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (
# 198 "FStar.Extraction.ML.UEnv.fst"
let mly = FStar_Extraction_ML_Syntax.MLE_Name (y)
in (
# 199 "FStar.Extraction.ML.UEnv.fst"
let mly = if add_unit then begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mly)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end else begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mly)
end
in (
# 200 "FStar.Extraction.ML.UEnv.fst"
let gamma = (Fv (((x), (FStar_Util.Inr (((mly), (t_x), (is_rec)))))))::g.gamma
in (
# 201 "FStar.Extraction.ML.UEnv.fst"
let tcenv = (FStar_TypeChecker_Env.push_let_binding g.tcenv (FStar_Util.Inr (x)) (([]), (x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)))
in (
# 202 "FStar.Extraction.ML.UEnv.fst"
let _72_213 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _72_213.tydefs; currentModule = _72_213.currentModule}))))))
end else begin
(FStar_All.failwith "freevars found")
end)

# 206 "FStar.Extraction.ML.UEnv.fst"
let extend_fv : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x t_x add_unit is_rec -> (
# 207 "FStar.Extraction.ML.UEnv.fst"
let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (extend_fv' g x mlp t_x add_unit is_rec)))

# 214 "FStar.Extraction.ML.UEnv.fst"
let extend_lb : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g l t t_x add_unit is_rec -> (match (l) with
| FStar_Util.Inl (x) -> begin
(let _165_183 = (extend_bv g x t_x add_unit is_rec false)
in (let _165_182 = (bv_as_ml_termvar x)
in ((_165_183), (_165_182))))
end
| FStar_Util.Inr (f) -> begin
(
# 219 "FStar.Extraction.ML.UEnv.fst"
let _72_233 = (FStar_Extraction_ML_Syntax.mlpath_of_lident f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_72_233) with
| (p, y) -> begin
(let _165_184 = (extend_fv' g f ((p), (y)) t_x add_unit is_rec)
in ((_165_184), (((y), (0)))))
end))
end))

# 222 "FStar.Extraction.ML.UEnv.fst"
let extend_tydef : env  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  env = (fun g td -> (
# 223 "FStar.Extraction.ML.UEnv.fst"
let m = (FStar_List.append (Prims.fst g.currentModule) (((Prims.snd g.currentModule))::[]))
in (
# 224 "FStar.Extraction.ML.UEnv.fst"
let _72_237 = g
in {tcenv = _72_237.tcenv; gamma = _72_237.gamma; tydefs = (((m), (td)))::g.tydefs; currentModule = _72_237.currentModule})))

# 227 "FStar.Extraction.ML.UEnv.fst"
let emptyMlPath : (Prims.string Prims.list * Prims.string) = (([]), (""))

# 229 "FStar.Extraction.ML.UEnv.fst"
let mkContext : FStar_TypeChecker_Env.env  ->  env = (fun e -> (
# 230 "FStar.Extraction.ML.UEnv.fst"
let env = {tcenv = e; gamma = []; tydefs = []; currentModule = emptyMlPath}
in (
# 231 "FStar.Extraction.ML.UEnv.fst"
let a = (("\'a"), ((- (1))))
in (
# 232 "FStar.Extraction.ML.UEnv.fst"
let failwith_ty = (((a)::[]), (FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.MLTY_Named ((([]), (((("Prims")::[]), ("string")))))), (FStar_Extraction_ML_Syntax.E_IMPURE), (FStar_Extraction_ML_Syntax.MLTY_Var (a))))))
in (let _165_193 = (let _165_192 = (let _165_191 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (_165_191))
in (extend_lb env _165_192 FStar_Syntax_Syntax.tun failwith_ty false false))
in (FStar_All.pipe_right _165_193 Prims.fst))))))

# 235 "FStar.Extraction.ML.UEnv.fst"
let monad_op_name : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  ((Prims.string Prims.list * Prims.string) * FStar_Ident.lident) = (fun ed nm -> (
# 236 "FStar.Extraction.ML.UEnv.fst"
let _72_247 = ((ed.FStar_Syntax_Syntax.mname.FStar_Ident.ns), (ed.FStar_Syntax_Syntax.mname.FStar_Ident.ident))
in (match (_72_247) with
| (module_name, eff_name) -> begin
(
# 237 "FStar.Extraction.ML.UEnv.fst"
let mangled_name = (Prims.strcat FStar_Ident.reserved_prefix (Prims.strcat eff_name.FStar_Ident.idText (Prims.strcat "_" nm)))
in (
# 238 "FStar.Extraction.ML.UEnv.fst"
let mangled_lid = (FStar_Ident.lid_of_ids (FStar_List.append module_name (((FStar_Ident.id_of_text mangled_name))::[])))
in (
# 239 "FStar.Extraction.ML.UEnv.fst"
let ml_name = (FStar_Extraction_ML_Syntax.mlpath_of_lident mangled_lid)
in (
# 240 "FStar.Extraction.ML.UEnv.fst"
let lid = (FStar_All.pipe_right (FStar_List.append (FStar_Ident.ids_of_lid ed.FStar_Syntax_Syntax.mname) (((FStar_Ident.id_of_text nm))::[])) FStar_Ident.lid_of_ids)
in ((ml_name), (lid))))))
end)))

# 243 "FStar.Extraction.ML.UEnv.fst"
let action_name : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.action  ->  ((Prims.string Prims.list * Prims.string) * FStar_Ident.lident) = (fun ed a -> (monad_op_name ed a.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText))

# 246 "FStar.Extraction.ML.UEnv.fst"
let bind_name : FStar_Syntax_Syntax.eff_decl  ->  ((Prims.string Prims.list * Prims.string) * FStar_Ident.lident) = (fun ed -> (monad_op_name ed "bind"))

# 249 "FStar.Extraction.ML.UEnv.fst"
let return_name : FStar_Syntax_Syntax.eff_decl  ->  ((Prims.string Prims.list * Prims.string) * FStar_Ident.lident) = (fun ed -> (monad_op_name ed "return"))




