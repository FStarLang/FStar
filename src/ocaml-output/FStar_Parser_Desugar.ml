
open Prims
let as_imp : FStar_Parser_AST.imp  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _64_1 -> (match (_64_1) with
| (FStar_Parser_AST.Hash) | (FStar_Parser_AST.FsTypApp) -> begin
Some (FStar_Absyn_Syntax.Implicit)
end
| _64_35 -> begin
None
end))

let arg_withimp_e = (fun imp t -> (t, (as_imp imp)))

let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
(t, Some (FStar_Absyn_Syntax.Implicit))
end
| _64_42 -> begin
(t, None)
end))

let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_64_46) -> begin
true
end
| _64_49 -> begin
false
end)))))

let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _64_54 -> begin
t
end))

let rec unlabel : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unlabel t)
end
| FStar_Parser_AST.Labeled (t, _64_60, _64_62) -> begin
(unlabel t)
end
| _64_66 -> begin
t
end))

let kind_star : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _167_17 = (let _167_16 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_167_16))
in (FStar_Parser_AST.mk_term _167_17 r FStar_Parser_AST.Kind)))

let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (let name_of_char = (fun _64_2 -> (match (_64_2) with
| '&' -> begin
"Amp"
end
| '@' -> begin
"At"
end
| '+' -> begin
"Plus"
end
| '-' when (arity = 1) -> begin
"Minus"
end
| '-' -> begin
"Subtraction"
end
| '/' -> begin
"Slash"
end
| '<' -> begin
"Less"
end
| '=' -> begin
"Equals"
end
| '>' -> begin
"Greater"
end
| '_' -> begin
"Underscore"
end
| '|' -> begin
"Bar"
end
| '!' -> begin
"Bang"
end
| '^' -> begin
"Hat"
end
| '%' -> begin
"Percent"
end
| '*' -> begin
"Star"
end
| '?' -> begin
"Question"
end
| ':' -> begin
"Colon"
end
| _64_89 -> begin
"UNKNOWN"
end))
in (let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _167_28 = (let _167_26 = (FStar_Util.char_at s i)
in (name_of_char _167_26))
in (let _167_27 = (aux (i + 1))
in (_167_28)::_167_27))
end)
in (let _167_30 = (let _167_29 = (aux 0)
in (FStar_String.concat "_" _167_29))
in (Prims.strcat "op_" _167_30)))))

let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _167_40 = (let _167_39 = (let _167_38 = (let _167_37 = (compile_op n s)
in (_167_37, r))
in (FStar_Absyn_Syntax.mk_ident _167_38))
in (_167_39)::[])
in (FStar_All.pipe_right _167_40 FStar_Absyn_Syntax.lid_of_ids)))

let op_as_vlid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Absyn_Syntax.lident Prims.option = (fun env arity rng s -> (let r = (fun l -> (let _167_51 = (FStar_Ident.set_lid_range l rng)
in Some (_167_51)))
in (let fallback = (fun _64_103 -> (match (()) with
| () -> begin
(match (s) with
| "=" -> begin
(r FStar_Absyn_Const.op_Eq)
end
| ":=" -> begin
(r FStar_Absyn_Const.op_ColonEq)
end
| "<" -> begin
(r FStar_Absyn_Const.op_LT)
end
| "<=" -> begin
(r FStar_Absyn_Const.op_LTE)
end
| ">" -> begin
(r FStar_Absyn_Const.op_GT)
end
| ">=" -> begin
(r FStar_Absyn_Const.op_GTE)
end
| "&&" -> begin
(r FStar_Absyn_Const.op_And)
end
| "||" -> begin
(r FStar_Absyn_Const.op_Or)
end
| "*" -> begin
(r FStar_Absyn_Const.op_Multiply)
end
| "+" -> begin
(r FStar_Absyn_Const.op_Addition)
end
| "-" when (arity = 1) -> begin
(r FStar_Absyn_Const.op_Minus)
end
| "-" -> begin
(r FStar_Absyn_Const.op_Subtraction)
end
| "/" -> begin
(r FStar_Absyn_Const.op_Division)
end
| "%" -> begin
(r FStar_Absyn_Const.op_Modulus)
end
| "!" -> begin
(r FStar_Absyn_Const.read_lid)
end
| "@" -> begin
(r FStar_Absyn_Const.list_append_lid)
end
| "^" -> begin
(r FStar_Absyn_Const.strcat_lid)
end
| "|>" -> begin
(r FStar_Absyn_Const.pipe_right_lid)
end
| "<|" -> begin
(r FStar_Absyn_Const.pipe_left_lid)
end
| "<>" -> begin
(r FStar_Absyn_Const.op_notEq)
end
| _64_125 -> begin
None
end)
end))
in (match ((let _167_54 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_lid env _167_54))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _64_136); FStar_Absyn_Syntax.tk = _64_133; FStar_Absyn_Syntax.pos = _64_131; FStar_Absyn_Syntax.fvs = _64_129; FStar_Absyn_Syntax.uvs = _64_127}) -> begin
Some (fv.FStar_Absyn_Syntax.v)
end
| _64_142 -> begin
(fallback ())
end))))

let op_as_tylid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Absyn_Syntax.lident Prims.option = (fun env arity rng s -> (let r = (fun l -> (let _167_65 = (FStar_Ident.set_lid_range l rng)
in Some (_167_65)))
in (match (s) with
| "~" -> begin
(r FStar_Absyn_Const.not_lid)
end
| "==" -> begin
(r FStar_Absyn_Const.eq2_lid)
end
| "=!=" -> begin
(r FStar_Absyn_Const.neq2_lid)
end
| "<<" -> begin
(r FStar_Absyn_Const.precedes_lid)
end
| "/\\" -> begin
(r FStar_Absyn_Const.and_lid)
end
| "\\/" -> begin
(r FStar_Absyn_Const.or_lid)
end
| "==>" -> begin
(r FStar_Absyn_Const.imp_lid)
end
| "<==>" -> begin
(r FStar_Absyn_Const.iff_lid)
end
| s -> begin
(match ((let _167_66 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_typ_name env _167_66))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ftv); FStar_Absyn_Syntax.tk = _64_165; FStar_Absyn_Syntax.pos = _64_163; FStar_Absyn_Syntax.fvs = _64_161; FStar_Absyn_Syntax.uvs = _64_159}) -> begin
Some (ftv.FStar_Absyn_Syntax.v)
end
| _64_171 -> begin
None
end)
end)))

let rec is_type : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> if (t.FStar_Parser_AST.level = FStar_Parser_AST.Type) then begin
true
end else begin
(match ((let _167_73 = (unparen t)
in _167_73.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
true
end
| FStar_Parser_AST.Labeled (_64_176) -> begin
true
end
| FStar_Parser_AST.Op ("*", hd::_64_180) -> begin
(is_type env hd)
end
| (FStar_Parser_AST.Op ("==", _)) | (FStar_Parser_AST.Op ("=!=", _)) | (FStar_Parser_AST.Op ("~", _)) | (FStar_Parser_AST.Op ("/\\", _)) | (FStar_Parser_AST.Op ("\\/", _)) | (FStar_Parser_AST.Op ("==>", _)) | (FStar_Parser_AST.Op ("<==>", _)) | (FStar_Parser_AST.Op ("<<", _)) -> begin
true
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_tylid env (FStar_List.length args) t.FStar_Parser_AST.range s)) with
| None -> begin
false
end
| _64_231 -> begin
true
end)
end
| (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.NamedTyp (_)) -> begin
true
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = 0) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (_64_254) -> begin
true
end
| _64_257 -> begin
(FStar_Parser_DesugarEnv.is_type_lid env l)
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) | (FStar_Parser_AST.Construct (l, _)) -> begin
(FStar_Parser_DesugarEnv.is_type_lid env l)
end
| (FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (l); FStar_Parser_AST.range = _; FStar_Parser_AST.level = _}, arg, FStar_Parser_AST.Nothing)) | (FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = _; FStar_Parser_AST.level = _}, arg, FStar_Parser_AST.Nothing)) when (l.FStar_Ident.str = "ref") -> begin
(is_type env arg)
end
| (FStar_Parser_AST.App (t, _, _)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(is_type env t)
end
| FStar_Parser_AST.Product (_64_298, t) -> begin
(not ((is_kind env t)))
end
| FStar_Parser_AST.If (t, t1, t2) -> begin
(((is_type env t) || (is_type env t1)) || (is_type env t2))
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(let rec aux = (fun env pats -> (match (pats) with
| [] -> begin
(is_type env t)
end
| hd::pats -> begin
(match (hd.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatVar (_)) -> begin
(aux env pats)
end
| FStar_Parser_AST.PatTvar (id, _64_324) -> begin
(let _64_330 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_64_330) with
| (env, _64_329) -> begin
(aux env pats)
end))
end
| FStar_Parser_AST.PatAscribed (p, tm) -> begin
(let env = if (is_kind env tm) then begin
(match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatVar (id, _)) | (FStar_Parser_AST.PatTvar (id, _)) -> begin
(let _167_78 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (FStar_All.pipe_right _167_78 Prims.fst))
end
| _64_345 -> begin
env
end)
end else begin
env
end
in (aux env pats))
end
| _64_348 -> begin
false
end)
end))
in (aux env pats))
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_64_353); FStar_Parser_AST.prange = _64_351}, _64_357)::[], t) -> begin
(is_type env t)
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_64_369); FStar_Parser_AST.prange = _64_367}, _64_373); FStar_Parser_AST.prange = _64_365}, _64_378)::[], t) -> begin
(is_type env t)
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_64_388); FStar_Parser_AST.prange = _64_386}, _64_392)::[], t) -> begin
(is_type env t)
end
| _64_399 -> begin
false
end)
end)
and is_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> if (t.FStar_Parser_AST.level = FStar_Parser_AST.Kind) then begin
true
end else begin
(match ((let _167_81 = (unparen t)
in _167_81.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _64_408; FStar_Ident.ident = _64_406; FStar_Ident.nsstr = _64_404; FStar_Ident.str = "Type"}) -> begin
true
end
| FStar_Parser_AST.Product (_64_412, t) -> begin
(is_kind env t)
end
| FStar_Parser_AST.Paren (t) -> begin
(is_kind env t)
end
| (FStar_Parser_AST.Construct (l, _)) | (FStar_Parser_AST.Name (l)) -> begin
(FStar_Parser_DesugarEnv.is_kind_abbrev env l)
end
| _64_425 -> begin
false
end)
end)

let rec is_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  Prims.bool = (fun env b -> if (b.FStar_Parser_AST.blevel = FStar_Parser_AST.Formula) then begin
(match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_64_429) -> begin
false
end
| (FStar_Parser_AST.TAnnotated (_)) | (FStar_Parser_AST.TVariable (_)) -> begin
true
end
| (FStar_Parser_AST.Annotated (_, t)) | (FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end else begin
(match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_64_444) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected binder without annotation", b.FStar_Parser_AST.brange))))
end
| FStar_Parser_AST.TVariable (_64_447) -> begin
false
end
| FStar_Parser_AST.TAnnotated (_64_450) -> begin
true
end
| (FStar_Parser_AST.Annotated (_, t)) | (FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end)

let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _167_92 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _167_92)))

let rec free_type_vars_b : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_DesugarEnv.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_64_466) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _64_473 = (FStar_Parser_DesugarEnv.push_local_tbinding env x)
in (match (_64_473) with
| (env, _64_472) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_64_475, term) -> begin
(let _167_99 = (free_type_vars env term)
in (env, _167_99))
end
| FStar_Parser_AST.TAnnotated (id, _64_481) -> begin
(let _64_487 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_64_487) with
| (env, _64_486) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _167_100 = (free_type_vars env t)
in (env, _167_100))
end))
and free_type_vars : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _167_103 = (unparen t)
in _167_103.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env a)) with
| None -> begin
(a)::[]
end
| _64_496 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.Labeled (t, _, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_64_532, ts) -> begin
(FStar_List.collect (fun _64_539 -> (match (_64_539) with
| (t, _64_538) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_64_541, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _64_548) -> begin
(let _167_106 = (free_type_vars env t1)
in (let _167_105 = (free_type_vars env t2)
in (FStar_List.append _167_106 _167_105)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(let _64_557 = (free_type_vars_b env b)
in (match (_64_557) with
| (env, f) -> begin
(let _167_107 = (free_type_vars env t)
in (FStar_List.append f _167_107))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(let _64_573 = (FStar_List.fold_left (fun _64_566 binder -> (match (_64_566) with
| (env, free) -> begin
(let _64_570 = (free_type_vars_b env binder)
in (match (_64_570) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_64_573) with
| (env, free) -> begin
(let _167_110 = (free_type_vars env body)
in (FStar_List.append free _167_110))
end))
end
| FStar_Parser_AST.Project (t, _64_576) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
(FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.FStar_Parser_AST.range)
end))

let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (let rec aux = (fun args t -> (match ((let _167_117 = (unparen t)
in _167_117.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _64_620 -> begin
(t, args)
end))
in (aux [] t)))

let close : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (let ftv = (let _167_122 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _167_122))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _167_126 = (let _167_125 = (let _167_124 = (kind_star x.FStar_Ident.idRange)
in (x, _167_124))
in FStar_Parser_AST.TAnnotated (_167_125))
in (FStar_Parser_AST.mk_binder _167_126 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

let close_fun : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (let ftv = (let _167_131 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _167_131))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _167_135 = (let _167_134 = (let _167_133 = (kind_star x.FStar_Ident.idRange)
in (x, _167_133))
in FStar_Parser_AST.TAnnotated (_167_134))
in (FStar_Parser_AST.mk_binder _167_135 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (let t = (match ((let _167_136 = (unlabel t)
in _167_136.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_64_633) -> begin
t
end
| _64_636 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))

let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _64_646 -> begin
(bs, t)
end))

let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _64_650) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_64_656); FStar_Parser_AST.prange = _64_654}, _64_660) -> begin
true
end
| _64_664 -> begin
false
end))

let rec destruct_app_pattern : FStar_Parser_DesugarEnv.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Absyn_Syntax.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(let _64_676 = (destruct_app_pattern env is_top_level p)
in (match (_64_676) with
| (name, args, _64_675) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _64_681); FStar_Parser_AST.prange = _64_678}, args) when is_top_level -> begin
(let _167_150 = (let _167_149 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_167_149))
in (_167_150, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _64_692); FStar_Parser_AST.prange = _64_689}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _64_700 -> begin
(FStar_All.failwith "Not an app pattern")
end))

type bnd =
| TBinder of (FStar_Absyn_Syntax.btvdef * FStar_Absyn_Syntax.knd * FStar_Absyn_Syntax.aqual)
| VBinder of (FStar_Absyn_Syntax.bvvdef * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Absyn_Syntax.typ)

let is_TBinder : bnd  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| TBinder (_) -> begin
true
end
| _ -> begin
false
end))

let is_VBinder : bnd  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| VBinder (_) -> begin
true
end
| _ -> begin
false
end))

let is_LetBinder : bnd  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| LetBinder (_) -> begin
true
end
| _ -> begin
false
end))

let ___TBinder____0 : bnd  ->  (FStar_Absyn_Syntax.btvdef * FStar_Absyn_Syntax.knd * FStar_Absyn_Syntax.aqual) = (fun projectee -> (match (projectee) with
| TBinder (_64_703) -> begin
_64_703
end))

let ___VBinder____0 : bnd  ->  (FStar_Absyn_Syntax.bvvdef * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.aqual) = (fun projectee -> (match (projectee) with
| VBinder (_64_706) -> begin
_64_706
end))

let ___LetBinder____0 : bnd  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.typ) = (fun projectee -> (match (projectee) with
| LetBinder (_64_709) -> begin
_64_709
end))

let binder_of_bnd : bnd  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) = (fun _64_3 -> (match (_64_3) with
| TBinder (a, k, aq) -> begin
(FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), aq)
end
| VBinder (x, t, aq) -> begin
(FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), aq)
end
| _64_722 -> begin
(FStar_All.failwith "Impossible")
end))

let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _64_4 -> (match (_64_4) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Absyn_Syntax.Implicit)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Absyn_Syntax.Equality)
end
| _64_729 -> begin
None
end))

let as_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  ((FStar_Absyn_Syntax.ident Prims.option * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax), (FStar_Absyn_Syntax.ident Prims.option * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either  ->  (((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) * FStar_Parser_DesugarEnv.env) = (fun env imp _64_5 -> (match (_64_5) with
| FStar_Util.Inl (None, k) -> begin
((FStar_Absyn_Syntax.null_t_binder k), env)
end
| FStar_Util.Inr (None, t) -> begin
((FStar_Absyn_Syntax.null_v_binder t), env)
end
| FStar_Util.Inl (Some (a), k) -> begin
(let _64_748 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_64_748) with
| (env, a) -> begin
((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), (trans_aqual imp)), env)
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(let _64_756 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_64_756) with
| (env, x) -> begin
((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), (trans_aqual imp)), env)
end))
end))

type env_t =
FStar_Parser_DesugarEnv.env

type lenv_t =
(FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list

let label_conjuncts : Prims.string  ->  Prims.bool  ->  Prims.string Prims.option  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun tag polarity label_opt f -> (let label = (fun f -> (let msg = (match (label_opt) with
| Some (l) -> begin
l
end
| _64_766 -> begin
(let _167_213 = (FStar_Range.string_of_range f.FStar_Parser_AST.range)
in (FStar_Util.format2 "%s at %s" tag _167_213))
end)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled ((f, msg, polarity))) f.FStar_Parser_AST.range f.FStar_Parser_AST.level)))
in (let rec aux = (fun f -> (match (f.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (g) -> begin
(let _167_217 = (let _167_216 = (aux g)
in FStar_Parser_AST.Paren (_167_216))
in (FStar_Parser_AST.mk_term _167_217 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("/\\", f1::f2::[]) -> begin
(let _167_223 = (let _167_222 = (let _167_221 = (let _167_220 = (aux f1)
in (let _167_219 = (let _167_218 = (aux f2)
in (_167_218)::[])
in (_167_220)::_167_219))
in ("/\\", _167_221))
in FStar_Parser_AST.Op (_167_222))
in (FStar_Parser_AST.mk_term _167_223 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _167_227 = (let _167_226 = (let _167_225 = (aux f2)
in (let _167_224 = (aux f3)
in (f1, _167_225, _167_224)))
in FStar_Parser_AST.If (_167_226))
in (FStar_Parser_AST.mk_term _167_227 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Abs (binders, g) -> begin
(let _167_230 = (let _167_229 = (let _167_228 = (aux g)
in (binders, _167_228))
in FStar_Parser_AST.Abs (_167_229))
in (FStar_Parser_AST.mk_term _167_230 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| _64_788 -> begin
(label f)
end))
in (aux f))))

let mk_lb : (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.exp)  ->  FStar_Absyn_Syntax.letbinding = (fun _64_792 -> (match (_64_792) with
| (n, t, e) -> begin
{FStar_Absyn_Syntax.lbname = n; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = e}
end))

let rec desugar_data_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat) = (fun env p -> (let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _64_6 -> (match (_64_6) with
| FStar_Util.Inr (y) -> begin
(y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText)
end
| _64_803 -> begin
false
end))))) with
| Some (FStar_Util.Inr (y)) -> begin
(l, e, y)
end
| _64_808 -> begin
(let _64_811 = (FStar_Parser_DesugarEnv.push_local_vbinding e x)
in (match (_64_811) with
| (e, x) -> begin
((FStar_Util.Inr (x))::l, e, x)
end))
end))
in (let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _64_7 -> (match (_64_7) with
| FStar_Util.Inl (b) -> begin
(b.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText)
end
| _64_820 -> begin
false
end))))) with
| Some (FStar_Util.Inl (b)) -> begin
(l, e, b)
end
| _64_825 -> begin
(let _64_828 = (FStar_Parser_DesugarEnv.push_local_tbinding e a)
in (match (_64_828) with
| (e, a) -> begin
((FStar_Util.Inl (a))::l, e, a)
end))
end))
in (let rec aux = (fun loc env p -> (let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p.FStar_Parser_AST.prange))
in (let pos_r = (fun r q -> (FStar_Absyn_Syntax.withinfo q None r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr (p::ps) -> begin
(let _64_850 = (aux loc env p)
in (match (_64_850) with
| (loc, env, var, p, _64_849) -> begin
(let _64_867 = (FStar_List.fold_left (fun _64_854 p -> (match (_64_854) with
| (loc, env, ps) -> begin
(let _64_863 = (aux loc env p)
in (match (_64_863) with
| (loc, env, _64_859, p, _64_862) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_64_867) with
| (loc, env, ps) -> begin
(let pat = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (let _64_869 = (let _167_302 = (FStar_Absyn_Syntax.pat_vars pat)
in (Prims.ignore _167_302))
in (loc, env, var, pat, false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(let p = if (is_kind env t) then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTvar (_64_876) -> begin
p
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(let _64_882 = p
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar ((x, imp)); FStar_Parser_AST.prange = _64_882.FStar_Parser_AST.prange})
end
| _64_885 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end)
end else begin
p
end
in (let _64_892 = (aux loc env p)
in (match (_64_892) with
| (loc, env', binder, p, imp) -> begin
(let binder = (match (binder) with
| LetBinder (_64_894) -> begin
(FStar_All.failwith "impossible")
end
| TBinder (x, _64_898, aq) -> begin
(let _167_304 = (let _167_303 = (desugar_kind env t)
in (x, _167_303, aq))
in TBinder (_167_304))
end
| VBinder (x, _64_904, aq) -> begin
(let t = (close_fun env t)
in (let _167_306 = (let _167_305 = (desugar_typ env t)
in (x, _167_305, aq))
in VBinder (_167_306)))
end)
in (loc, env', binder, p, imp))
end)))
end
| FStar_Parser_AST.PatTvar (a, imp) -> begin
(let aq = if imp then begin
Some (FStar_Absyn_Syntax.Implicit)
end else begin
None
end
in if (a.FStar_Ident.idText = "\'_") then begin
(let a = (FStar_All.pipe_left FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _167_307 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_twild ((FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((a, FStar_Absyn_Syntax.kun, aq)), _167_307, imp)))
end else begin
(let _64_919 = (resolvea loc env a)
in (match (_64_919) with
| (loc, env, abvd) -> begin
(let _167_308 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_tvar ((FStar_Absyn_Util.bvd_to_bvar_s abvd FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((abvd, FStar_Absyn_Syntax.kun, aq)), _167_308, imp))
end))
end)
end
| FStar_Parser_AST.PatWild -> begin
(let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let y = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _167_309 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_wild ((FStar_Absyn_Util.bvd_to_bvar_s y FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _167_309, false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _167_310 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_constant (c)))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _167_310, false)))
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(let aq = if imp then begin
Some (FStar_Absyn_Syntax.Implicit)
end else begin
None
end
in (let _64_934 = (resolvex loc env x)
in (match (_64_934) with
| (loc, env, xbvd) -> begin
(let _167_311 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_var ((FStar_Absyn_Util.bvd_to_bvar_s xbvd FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((xbvd, FStar_Absyn_Syntax.tun, aq)), _167_311, imp))
end)))
end
| FStar_Parser_AST.PatName (l) -> begin
(let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _167_312 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), []))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _167_312, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _64_940}, args) -> begin
(let _64_962 = (FStar_List.fold_right (fun arg _64_951 -> (match (_64_951) with
| (loc, env, args) -> begin
(let _64_958 = (aux loc env arg)
in (match (_64_958) with
| (loc, env, _64_955, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_64_962) with
| (loc, env, args) -> begin
(let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _167_315 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _167_315, false))))
end))
end
| FStar_Parser_AST.PatApp (_64_966) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _64_986 = (FStar_List.fold_right (fun pat _64_974 -> (match (_64_974) with
| (loc, env, pats) -> begin
(let _64_982 = (aux loc env pat)
in (match (_64_982) with
| (loc, env, _64_978, pat, _64_981) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_64_986) with
| (loc, env, pats) -> begin
(let pat = (let _167_322 = (let _167_321 = (let _167_320 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _167_320))
in (FStar_All.pipe_left _167_321 (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv FStar_Absyn_Const.nil_lid), Some (FStar_Absyn_Syntax.Data_ctor), [])))))
in (FStar_List.fold_right (fun hd tl -> (let r = (FStar_Range.union_ranges hd.FStar_Absyn_Syntax.p tl.FStar_Absyn_Syntax.p)
in (FStar_All.pipe_left (pos_r r) (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv FStar_Absyn_Const.cons_lid), Some (FStar_Absyn_Syntax.Data_ctor), ((hd, false))::((tl, false))::[])))))) pats _167_322))
in (let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(let _64_1012 = (FStar_List.fold_left (fun _64_999 p -> (match (_64_999) with
| (loc, env, pats) -> begin
(let _64_1008 = (aux loc env p)
in (match (_64_1008) with
| (loc, env, _64_1004, pat, _64_1007) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_64_1012) with
| (loc, env, args) -> begin
(let args = (FStar_List.rev args)
in (let l = if dep then begin
(FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end else begin
(FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
in (let constr = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (let l = (match (constr.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (v, _64_1018) -> begin
v
end
| _64_1022 -> begin
(FStar_All.failwith "impossible")
end)
in (let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _167_325 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _167_325, false)))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(let _64_1032 = (FStar_List.hd fields)
in (match (_64_1032) with
| (f, _64_1031) -> begin
(let _64_1036 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_64_1036) with
| (record, _64_1035) -> begin
(let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _64_1039 -> (match (_64_1039) with
| (f, p) -> begin
(let _167_327 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in (_167_327, p))
end))))
in (let args = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _64_1044 -> (match (_64_1044) with
| (f, _64_1043) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _64_1048 -> (match (_64_1048) with
| (g, _64_1047) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_64_1051, p) -> begin
p
end)
end))))
in (let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_DesugarEnv.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (let _64_1063 = (aux loc env app)
in (match (_64_1063) with
| (env, e, b, p, _64_1062) -> begin
(let p = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, _64_1066, args) -> begin
(let _167_335 = (let _167_334 = (let _167_333 = (let _167_332 = (let _167_331 = (let _167_330 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_DesugarEnv.typename, _167_330))
in FStar_Absyn_Syntax.Record_ctor (_167_331))
in Some (_167_332))
in (fv, _167_333, args))
in FStar_Absyn_Syntax.Pat_cons (_167_334))
in (FStar_All.pipe_left pos _167_335))
end
| _64_1071 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (let _64_1080 = (aux [] env p)
in (match (_64_1080) with
| (_64_1074, env, b, p, _64_1079) -> begin
(env, b, p)
end))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _64_1086) -> begin
(let _167_341 = (let _167_340 = (let _167_339 = (FStar_Parser_DesugarEnv.qualify env x)
in (_167_339, FStar_Absyn_Syntax.tun))
in LetBinder (_167_340))
in (env, _167_341, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _64_1093); FStar_Parser_AST.prange = _64_1090}, t) -> begin
(let _167_345 = (let _167_344 = (let _167_343 = (FStar_Parser_DesugarEnv.qualify env x)
in (let _167_342 = (desugar_typ env t)
in (_167_343, _167_342)))
in LetBinder (_167_344))
in (env, _167_345, None))
end
| _64_1101 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(let _64_1105 = (desugar_data_pat env p)
in (match (_64_1105) with
| (env, binder, p) -> begin
(let p = (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) -> begin
None
end
| _64_1116 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun _64_1120 env pat -> (let _64_1128 = (desugar_data_pat env pat)
in (match (_64_1128) with
| (env, _64_1126, pat) -> begin
(env, pat)
end)))
and desugar_match_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_typ_or_exp : env_t  ->  FStar_Parser_AST.term  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either = (fun env t -> if (is_type env t) then begin
(let _167_355 = (desugar_typ env t)
in FStar_Util.Inl (_167_355))
end else begin
(let _167_356 = (desugar_exp env t)
in FStar_Util.Inr (_167_356))
end)
and desugar_exp : env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun env e -> (desugar_exp_maybe_top false env e))
and desugar_exp_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun top_level env top -> (let pos = (fun e -> (e None top.FStar_Parser_AST.range))
in (let setpos = (fun e -> (let _64_1142 = e
in {FStar_Absyn_Syntax.n = _64_1142.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _64_1142.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _64_1142.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _64_1142.FStar_Absyn_Syntax.uvs}))
in (match ((let _167_376 = (unparen top)
in _167_376.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Const (c) -> begin
(FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_constant c))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_vlid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat "Unexpected operator: " s), top.FStar_Parser_AST.range))))
end
| Some (l) -> begin
(let op = (FStar_Absyn_Util.fvar None l (FStar_Ident.range_of_lid l))
in (let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _167_380 = (desugar_typ_or_exp env t)
in (_167_380, None)))))
in (let _167_381 = (FStar_Absyn_Util.mk_exp_app op args)
in (FStar_All.pipe_left setpos _167_381))))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
if (l.FStar_Ident.str = "ref") then begin
(match ((FStar_Parser_DesugarEnv.try_lookup_lid env FStar_Absyn_Const.alloc_lid)) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Identifier \'ref\' not found; include lib/FStar.ST.fst in your path", (FStar_Ident.range_of_lid l)))))
end
| Some (e) -> begin
(setpos e)
end)
end else begin
(let _167_382 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _167_382))
end
end
| FStar_Parser_AST.Construct (l, args) -> begin
(let dt = (let _167_387 = (let _167_386 = (let _167_385 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (_167_385, Some (FStar_Absyn_Syntax.Data_ctor)))
in (FStar_Absyn_Syntax.mk_Exp_fvar _167_386))
in (FStar_All.pipe_left pos _167_387))
in (match (args) with
| [] -> begin
dt
end
| _64_1169 -> begin
(let args = (FStar_List.map (fun _64_1172 -> (match (_64_1172) with
| (t, imp) -> begin
(let te = (desugar_typ_or_exp env t)
in (arg_withimp_e imp te))
end)) args)
in (let _167_392 = (let _167_391 = (let _167_390 = (let _167_389 = (FStar_Absyn_Util.mk_exp_app dt args)
in (_167_389, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_167_390))
in (FStar_Absyn_Syntax.mk_Exp_meta _167_391))
in (FStar_All.pipe_left setpos _167_392)))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(let _64_1209 = (FStar_List.fold_left (fun _64_1181 pat -> (match (_64_1181) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar (a, imp); FStar_Parser_AST.prange = _64_1184}, t) -> begin
(let ftvs = (let _167_395 = (free_type_vars env t)
in (FStar_List.append _167_395 ftvs))
in (let _167_397 = (let _167_396 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _167_396))
in (_167_397, ftvs)))
end
| FStar_Parser_AST.PatTvar (a, _64_1196) -> begin
(let _167_399 = (let _167_398 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _167_398))
in (_167_399, ftvs))
end
| FStar_Parser_AST.PatAscribed (_64_1200, t) -> begin
(let _167_401 = (let _167_400 = (free_type_vars env t)
in (FStar_List.append _167_400 ftvs))
in (env, _167_401))
end
| _64_1205 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_64_1209) with
| (_64_1207, ftv) -> begin
(let ftv = (sort_ftv ftv)
in (let binders = (let _167_403 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, true))) top.FStar_Parser_AST.range))))
in (FStar_List.append _167_403 binders))
in (let rec aux = (fun env bs sc_pat_opt _64_8 -> (match (_64_8) with
| [] -> begin
(let body = (desugar_exp env body)
in (let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(FStar_Absyn_Syntax.mk_Exp_match (sc, ((pat, None, body))::[]) None body.FStar_Absyn_Syntax.pos)
end
| None -> begin
body
end)
in (FStar_Absyn_Syntax.mk_Exp_abs' ((FStar_List.rev bs), body) None top.FStar_Parser_AST.range)))
end
| p::rest -> begin
(let _64_1232 = (desugar_binding_pat env p)
in (match (_64_1232) with
| (env, b, pat) -> begin
(let _64_1292 = (match (b) with
| LetBinder (_64_1234) -> begin
(FStar_All.failwith "Impossible")
end
| TBinder (a, k, aq) -> begin
(let _167_412 = (binder_of_bnd b)
in (_167_412, sc_pat_opt))
end
| VBinder (x, t, aq) -> begin
(let b = (FStar_Absyn_Util.bvd_to_bvar_s x t)
in (let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _64_1249) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _167_414 = (let _167_413 = (FStar_Absyn_Util.bvar_to_exp b)
in (_167_413, p))
in Some (_167_414))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Absyn_Syntax.n, p'.FStar_Absyn_Syntax.v)) with
| (FStar_Absyn_Syntax.Exp_bvar (_64_1263), _64_1266) -> begin
(let tup = (FStar_Absyn_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (let sc = (let _167_420 = (let _167_419 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _167_418 = (let _167_417 = (let _167_416 = (let _167_415 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _167_415))
in (_167_416)::[])
in ((FStar_Absyn_Syntax.varg sc))::_167_417)
in (_167_419, _167_418)))
in (FStar_Absyn_Syntax.mk_Exp_app _167_420 None top.FStar_Parser_AST.range))
in (let p = (let _167_421 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv tup), Some (FStar_Absyn_Syntax.Data_ctor), ((p', false))::((p, false))::[]))) None _167_421))
in Some ((sc, p)))))
end
| (FStar_Absyn_Syntax.Exp_app (_64_1272, args), FStar_Absyn_Syntax.Pat_cons (_64_1277, _64_1279, pats)) -> begin
(let tup = (FStar_Absyn_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (let sc = (let _167_427 = (let _167_426 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _167_425 = (let _167_424 = (let _167_423 = (let _167_422 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _167_422))
in (_167_423)::[])
in (FStar_List.append args _167_424))
in (_167_426, _167_425)))
in (FStar_Absyn_Syntax.mk_Exp_app _167_427 None top.FStar_Parser_AST.range))
in (let p = (let _167_428 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv tup), Some (FStar_Absyn_Syntax.Data_ctor), (FStar_List.append pats (((p, false))::[]))))) None _167_428))
in Some ((sc, p)))))
end
| _64_1288 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((FStar_Util.Inr (b), aq), sc_pat_opt)))
end)
in (match (_64_1292) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _64_1296; FStar_Parser_AST.level = _64_1294}, arg, _64_1302) when ((FStar_Ident.lid_equals a FStar_Absyn_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Absyn_Const.assume_lid)) -> begin
(let phi = (desugar_formula env arg)
in (let _167_438 = (let _167_437 = (let _167_436 = (FStar_Absyn_Util.fvar None a (FStar_Ident.range_of_lid a))
in (let _167_435 = (let _167_434 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ phi)
in (let _167_433 = (let _167_432 = (let _167_431 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None top.FStar_Parser_AST.range)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _167_431))
in (_167_432)::[])
in (_167_434)::_167_433))
in (_167_436, _167_435)))
in (FStar_Absyn_Syntax.mk_Exp_app _167_437))
in (FStar_All.pipe_left pos _167_438)))
end
| FStar_Parser_AST.App (_64_1307) -> begin
(let rec aux = (fun args e -> (match ((let _167_443 = (unparen e)
in _167_443.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(let arg = (let _167_444 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _167_444))
in (aux ((arg)::args) e))
end
| _64_1319 -> begin
(let head = (desugar_exp env e)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_app (head, args))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _167_450 = (let _167_449 = (let _167_448 = (let _167_447 = (desugar_exp env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_167_447, FStar_Absyn_Syntax.Sequence))
in FStar_Absyn_Syntax.Meta_desugared (_167_448))
in (FStar_Absyn_Syntax.mk_Exp_meta _167_449))
in (FStar_All.pipe_left setpos _167_450))
end
| FStar_Parser_AST.Let (is_rec, (pat, _snd)::_tl, body) -> begin
(let ds_let_rec = (fun _64_1335 -> (match (()) with
| () -> begin
(let bindings = ((pat, _snd))::_tl
in (let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _64_1339 -> (match (_64_1339) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _167_454 = (destruct_app_pattern env top_level p)
in (_167_454, def))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _167_455 = (destruct_app_pattern env top_level p)
in (_167_455, def))
end
| _64_1345 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _64_1350); FStar_Parser_AST.prange = _64_1347}, t) -> begin
if top_level then begin
(let _167_458 = (let _167_457 = (let _167_456 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_167_456))
in (_167_457, [], Some (t)))
in (_167_458, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _64_1359) -> begin
if top_level then begin
(let _167_461 = (let _167_460 = (let _167_459 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_167_459))
in (_167_460, [], None))
in (_167_461, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _64_1363 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (let _64_1389 = (FStar_List.fold_left (fun _64_1367 _64_1376 -> (match ((_64_1367, _64_1376)) with
| ((env, fnames), ((f, _64_1370, _64_1372), _64_1375)) -> begin
(let _64_1386 = (match (f) with
| FStar_Util.Inl (x) -> begin
(let _64_1381 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_64_1381) with
| (env, xx) -> begin
(env, FStar_Util.Inl (xx))
end))
end
| FStar_Util.Inr (l) -> begin
(let _167_464 = (FStar_Parser_DesugarEnv.push_rec_binding env (FStar_Parser_DesugarEnv.Binding_let (l)))
in (_167_464, FStar_Util.Inr (l)))
end)
in (match (_64_1386) with
| (env, lbname) -> begin
(env, (lbname)::fnames)
end))
end)) (env, []) funs)
in (match (_64_1389) with
| (env', fnames) -> begin
(let fnames = (FStar_List.rev fnames)
in (let desugar_one_def = (fun env lbname _64_1400 -> (match (_64_1400) with
| ((_64_1395, args, result_t), def) -> begin
(let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _167_471 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _167_471 FStar_Parser_AST.Expr))
end)
in (let def = (match (args) with
| [] -> begin
def
end
| _64_1407 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args def) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (let body = (desugar_exp env def)
in (mk_lb (lbname, FStar_Absyn_Syntax.tun, body)))))
end))
in (let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (let body = (desugar_exp env' body)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), body)))))))
end))))
end))
in (let ds_non_rec = (fun pat t1 t2 -> (let t1 = (desugar_exp env t1)
in (let _64_1420 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_64_1420) with
| (env, binder, pat) -> begin
(match (binder) with
| TBinder (_64_1422) -> begin
(FStar_All.failwith "Unexpected type binder in let")
end
| LetBinder (l, t) -> begin
(let body = (desugar_exp env t2)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = t1})::[]), body))))
end
| VBinder (x, t, _64_1432) -> begin
(let body = (desugar_exp env t2)
in (let body = (match (pat) with
| (None) | (Some ({FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_wild (_); FStar_Absyn_Syntax.sort = _; FStar_Absyn_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _167_483 = (let _167_482 = (FStar_Absyn_Util.bvd_to_exp x t)
in (_167_482, ((pat, None, body))::[]))
in (FStar_Absyn_Syntax.mk_Exp_match _167_483 None body.FStar_Absyn_Syntax.pos))
end)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((false, ((mk_lb (FStar_Util.Inl (x), t, t1)))::[]), body)))))
end)
end))))
in if (is_rec || (is_app_pattern pat)) then begin
(ds_let_rec ())
end else begin
(ds_non_rec pat _snd body)
end))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(let _167_496 = (let _167_495 = (let _167_494 = (desugar_exp env t1)
in (let _167_493 = (let _167_492 = (let _167_488 = (desugar_exp env t2)
in ((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) None t2.FStar_Parser_AST.range), None, _167_488))
in (let _167_491 = (let _167_490 = (let _167_489 = (desugar_exp env t3)
in ((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) None t3.FStar_Parser_AST.range), None, _167_489))
in (_167_490)::[])
in (_167_492)::_167_491))
in (_167_494, _167_493)))
in (FStar_Absyn_Syntax.mk_Exp_match _167_495))
in (FStar_All.pipe_left pos _167_496))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(let r = top.FStar_Parser_AST.range
in (let handler = (FStar_Parser_AST.mk_function branches r r)
in (let body = (FStar_Parser_AST.mk_function ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r), None, e))::[]) r r)
in (let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Absyn_Const.try_with_lid)) r top.FStar_Parser_AST.level), body, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((a1, handler, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (desugar_exp env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(let desugar_branch = (fun _64_1471 -> (match (_64_1471) with
| (pat, wopt, b) -> begin
(let _64_1474 = (desugar_match_pat env pat)
in (match (_64_1474) with
| (env, pat) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _167_499 = (desugar_exp env e)
in Some (_167_499))
end)
in (let b = (desugar_exp env b)
in (pat, wopt, b)))
end))
end))
in (let _167_505 = (let _167_504 = (let _167_503 = (desugar_exp env e)
in (let _167_502 = (FStar_List.map desugar_branch branches)
in (_167_503, _167_502)))
in (FStar_Absyn_Syntax.mk_Exp_match _167_504))
in (FStar_All.pipe_left pos _167_505)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _167_511 = (let _167_510 = (let _167_509 = (desugar_exp env e)
in (let _167_508 = (desugar_typ env t)
in (_167_509, _167_508, None)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _167_510))
in (FStar_All.pipe_left pos _167_511))
end
| FStar_Parser_AST.Record (_64_1485, []) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(let _64_1496 = (FStar_List.hd fields)
in (match (_64_1496) with
| (f, _64_1495) -> begin
(let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (let _64_1502 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_64_1502) with
| (record, _64_1501) -> begin
(let get_field = (fun xopt f -> (let fn = f.FStar_Ident.ident
in (let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _64_1510 -> (match (_64_1510) with
| (g, _64_1509) -> begin
(let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_64_1514, e) -> begin
(let _167_519 = (qfn fn)
in (_167_519, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _167_522 = (let _167_521 = (let _167_520 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in (_167_520, top.FStar_Parser_AST.range))
in FStar_Absyn_Syntax.Error (_167_521))
in (Prims.raise _167_522))
end
| Some (x) -> begin
(let _167_523 = (qfn fn)
in (_167_523, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (let recterm = (match (eopt) with
| None -> begin
(let _167_528 = (let _167_527 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _64_1526 -> (match (_64_1526) with
| (f, _64_1525) -> begin
(let _167_526 = (let _167_525 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _167_525))
in (_167_526, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_DesugarEnv.constrname, _167_527))
in FStar_Parser_AST.Construct (_167_528))
end
| Some (e) -> begin
(let x = (FStar_Absyn_Util.genident (Some (e.FStar_Parser_AST.range)))
in (let xterm = (let _167_530 = (let _167_529 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_167_529))
in (FStar_Parser_AST.mk_term _167_530 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (let record = (let _167_533 = (let _167_532 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _64_1534 -> (match (_64_1534) with
| (f, _64_1533) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _167_532))
in FStar_Parser_AST.Record (_167_533))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, false))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (let e = (desugar_exp env recterm)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _64_1557); FStar_Absyn_Syntax.tk = _64_1554; FStar_Absyn_Syntax.pos = _64_1552; FStar_Absyn_Syntax.fvs = _64_1550; FStar_Absyn_Syntax.uvs = _64_1548}, args); FStar_Absyn_Syntax.tk = _64_1546; FStar_Absyn_Syntax.pos = _64_1544; FStar_Absyn_Syntax.fvs = _64_1542; FStar_Absyn_Syntax.uvs = _64_1540}, FStar_Absyn_Syntax.Data_app)) -> begin
(let e = (let _167_543 = (let _167_542 = (let _167_541 = (let _167_540 = (let _167_539 = (let _167_538 = (let _167_537 = (let _167_536 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_DesugarEnv.typename, _167_536))
in FStar_Absyn_Syntax.Record_ctor (_167_537))
in Some (_167_538))
in (fv, _167_539))
in (FStar_Absyn_Syntax.mk_Exp_fvar _167_540 None e.FStar_Absyn_Syntax.pos))
in (_167_541, args))
in (FStar_Absyn_Syntax.mk_Exp_app _167_542))
in (FStar_All.pipe_left pos _167_543))
in (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, FStar_Absyn_Syntax.Data_app)))))
end
| _64_1571 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(let _64_1578 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_projector_by_field_name env) f)
in (match (_64_1578) with
| (fieldname, is_rec) -> begin
(let e = (desugar_exp env e)
in (let fn = (let _64_1583 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_64_1583) with
| (ns, _64_1582) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (let qual = if is_rec then begin
Some (FStar_Absyn_Syntax.Record_projector (fn))
end else begin
None
end
in (let _167_548 = (let _167_547 = (let _167_546 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Record_projector (fn))) fieldname (FStar_Ident.range_of_lid f))
in (_167_546, ((FStar_Absyn_Syntax.varg e))::[]))
in (FStar_Absyn_Syntax.mk_Exp_app _167_547))
in (FStar_All.pipe_left pos _167_548)))))
end))
end
| FStar_Parser_AST.Paren (e) -> begin
(desugar_exp env e)
end
| _64_1589 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_typ : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env top -> (let wpos = (fun t -> (t None top.FStar_Parser_AST.range))
in (let setpos = (fun t -> (let _64_1596 = t
in {FStar_Absyn_Syntax.n = _64_1596.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _64_1596.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _64_1596.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _64_1596.FStar_Absyn_Syntax.uvs}))
in (let top = (unparen top)
in (let head_and_args = (fun t -> (let rec aux = (fun args t -> (match ((let _167_571 = (unparen t)
in _167_571.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _64_1614 -> begin
(t, args)
end))
in (aux [] t)))
in (match (top.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.tun)
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(let t = (label_conjuncts "pre-condition" true lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(let _167_572 = (desugar_exp env t)
in (FStar_All.pipe_right _167_572 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(let t = (label_conjuncts "post-condition" false lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(let _167_573 = (desugar_exp env t)
in (FStar_All.pipe_right _167_573 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Op ("*", t1::_64_1628::[]) -> begin
if (is_type env t1) then begin
(let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(let rest = (flatten t2)
in (t1)::rest)
end
| _64_1643 -> begin
(t)::[]
end))
in (let targs = (let _167_578 = (flatten top)
in (FStar_All.pipe_right _167_578 (FStar_List.map (fun t -> (let _167_577 = (desugar_typ env t)
in (FStar_Absyn_Syntax.targ _167_577))))))
in (let tup = (let _167_579 = (FStar_Absyn_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _167_579))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))))
end else begin
(let _167_585 = (let _167_584 = (let _167_583 = (let _167_582 = (FStar_Parser_AST.term_to_string t1)
in (FStar_Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _167_582))
in (_167_583, top.FStar_Parser_AST.range))
in FStar_Absyn_Syntax.Error (_167_584))
in (Prims.raise _167_585))
end
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_typ env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("~", ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("==", args))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[]))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_tylid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(let _167_586 = (desugar_exp env top)
in (FStar_All.pipe_right _167_586 FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(let args = (FStar_List.map (fun t -> (let _167_588 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _167_588))) args)
in (let _167_589 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _167_589 args)))
end)
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _167_590 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (FStar_All.pipe_left setpos _167_590))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = 0) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _167_591 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _167_591))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let l = (FStar_Absyn_Util.set_lid_range l top.FStar_Parser_AST.range)
in (let _167_592 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _167_592)))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(let t = (let _167_593 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _167_593))
in (let args = (FStar_List.map (fun _64_1679 -> (match (_64_1679) with
| (t, imp) -> begin
(let _167_595 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _167_595))
end)) args)
in (FStar_Absyn_Util.mk_typ_app t args)))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(let rec aux = (fun env bs _64_9 -> (match (_64_9) with
| [] -> begin
(let body = (desugar_typ env body)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_lam ((FStar_List.rev bs), body))))
end
| hd::tl -> begin
(let _64_1697 = (desugar_binding_pat env hd)
in (match (_64_1697) with
| (env, bnd, pat) -> begin
(match (pat) with
| Some (q) -> begin
(let _167_607 = (let _167_606 = (let _167_605 = (let _167_604 = (FStar_Absyn_Print.pat_to_string q)
in (FStar_Util.format1 "Pattern matching at the type level is not supported; got %s\n" _167_604))
in (_167_605, hd.FStar_Parser_AST.prange))
in FStar_Absyn_Syntax.Error (_167_606))
in (Prims.raise _167_607))
end
| None -> begin
(let b = (binder_of_bnd bnd)
in (aux env ((b)::bs) tl))
end)
end))
end))
in (aux env [] binders))
end
| FStar_Parser_AST.App (_64_1703) -> begin
(let rec aux = (fun args e -> (match ((let _167_612 = (unparen e)
in _167_612.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, arg, imp) -> begin
(let arg = (let _167_613 = (desugar_typ_or_exp env arg)
in (FStar_All.pipe_left (arg_withimp_t imp) _167_613))
in (aux ((arg)::args) e))
end
| _64_1715 -> begin
(let head = (desugar_typ env e)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (head, args))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Product ([], t) -> begin
(FStar_All.failwith "Impossible: product with no binders")
end
| FStar_Parser_AST.Product (binders, t) -> begin
(let _64_1727 = (uncurry binders t)
in (match (_64_1727) with
| (bs, t) -> begin
(let rec aux = (fun env bs _64_10 -> (match (_64_10) with
| [] -> begin
(let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_fun ((FStar_List.rev bs), cod))))
end
| hd::tl -> begin
(let mlenv = (FStar_Parser_DesugarEnv.default_ml env)
in (let bb = (desugar_binder mlenv hd)
in (let _64_1741 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_64_1741) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_exp_binder env b)) with
| (None, _64_1748) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(let _64_1762 = (match ((as_binder env None (FStar_Util.Inr (b)))) with
| ((FStar_Util.Inr (x), _64_1754), env) -> begin
(x, env)
end
| _64_1759 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_64_1762) with
| (b, env) -> begin
(let f = if (is_type env f) then begin
(desugar_formula env f)
end else begin
(let _167_624 = (desugar_exp env f)
in (FStar_All.pipe_right _167_624 FStar_Absyn_Util.b2t))
end
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_refine (b, f))))
end))
end)
end
| (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| FStar_Parser_AST.Ascribed (t, k) -> begin
(let _167_632 = (let _167_631 = (let _167_630 = (desugar_typ env t)
in (let _167_629 = (desugar_kind env k)
in (_167_630, _167_629)))
in (FStar_Absyn_Syntax.mk_Typ_ascribed' _167_631))
in (FStar_All.pipe_left wpos _167_632))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(let _64_1796 = (FStar_List.fold_left (fun _64_1781 b -> (match (_64_1781) with
| (env, tparams, typs) -> begin
(let _64_1785 = (desugar_exp_binder env b)
in (match (_64_1785) with
| (xopt, t) -> begin
(let _64_1791 = (match (xopt) with
| None -> begin
(let _167_635 = (FStar_Absyn_Util.new_bvd (Some (top.FStar_Parser_AST.range)))
in (env, _167_635))
end
| Some (x) -> begin
(FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_64_1791) with
| (env, x) -> begin
(let _167_639 = (let _167_638 = (let _167_637 = (let _167_636 = (FStar_Absyn_Util.close_with_lam tparams t)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _167_636))
in (_167_637)::[])
in (FStar_List.append typs _167_638))
in (env, (FStar_List.append tparams (((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), None))::[])), _167_639))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_64_1796) with
| (env, _64_1794, targs) -> begin
(let tup = (let _167_640 = (FStar_Absyn_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _167_640))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))
end))
end
| FStar_Parser_AST.Record (_64_1799) -> begin
(FStar_All.failwith "Unexpected record type")
end
| FStar_Parser_AST.Let (false, (x, v)::[], t) -> begin
(let let_v = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.let_in_typ)) top.FStar_Parser_AST.range top.FStar_Parser_AST.level), v, FStar_Parser_AST.Nothing))) v.FStar_Parser_AST.range v.FStar_Parser_AST.level)
in (let t' = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((let_v, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs (((x)::[], t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), FStar_Parser_AST.Nothing))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (desugar_typ env t')))
end
| (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Labeled (_)) -> begin
(desugar_formula env top)
end
| _64_1818 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _64_1820 -> begin
(FStar_Parser_AST.error "Expected a type" top top.FStar_Parser_AST.range)
end))))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.comp = (fun r default_ok env t -> (let fail = (fun msg -> (Prims.raise (FStar_Absyn_Syntax.Error ((msg, r)))))
in (let pre_process_comp_typ = (fun t -> (let _64_1831 = (head_and_args t)
in (match (_64_1831) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(let unit = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (let nil_pat = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr), FStar_Parser_AST.Nothing)
in (let _64_1857 = (FStar_All.pipe_right args (FStar_List.partition (fun _64_1839 -> (match (_64_1839) with
| (arg, _64_1838) -> begin
(match ((let _167_652 = (unparen arg)
in _167_652.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _64_1843; FStar_Parser_AST.level = _64_1841}, _64_1848, _64_1850) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = "decreases")
end
| _64_1854 -> begin
false
end)
end))))
in (match (_64_1857) with
| (decreases_clause, args) -> begin
(let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Not enough arguments to \'Lemma\'", t.FStar_Parser_AST.range))))
end
| ens::[] -> begin
(let req_true = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Requires (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.true_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Formula), None))) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (unit)::(req_true)::(ens)::(nil_pat)::[])
end
| req::ens::[] -> begin
(unit)::(req)::(ens)::(nil_pat)::[]
end
| more -> begin
(unit)::more
end)
in (let t = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct ((lemma, (FStar_List.append args decreases_clause)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (desugar_typ env t)))
end))))
end
| FStar_Parser_AST.Name (tot) when (((tot.FStar_Ident.ident.FStar_Ident.idText = "Tot") && (not ((FStar_Parser_DesugarEnv.is_effect_name env FStar_Absyn_Const.effect_Tot_lid)))) && (let _167_653 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals _167_653 FStar_Absyn_Const.prims_lid))) -> begin
(let args = (FStar_List.map (fun _64_1872 -> (match (_64_1872) with
| (t, imp) -> begin
(let _167_655 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _167_655))
end)) args)
in (let _167_656 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.effect_Tot_lid FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _167_656 args)))
end
| _64_1875 -> begin
(desugar_typ env t)
end)
end)))
in (let t = (pre_process_comp_typ t)
in (let _64_1879 = (FStar_Absyn_Util.head_and_args t)
in (match (_64_1879) with
| (head, args) -> begin
(match ((let _167_658 = (let _167_657 = (FStar_Absyn_Util.compress_typ head)
in _167_657.FStar_Absyn_Syntax.n)
in (_167_658, args))) with
| (FStar_Absyn_Syntax.Typ_const (eff), (FStar_Util.Inl (result_typ), _64_1886)::rest) -> begin
(let _64_1926 = (FStar_All.pipe_right rest (FStar_List.partition (fun _64_11 -> (match (_64_11) with
| (FStar_Util.Inr (_64_1892), _64_1895) -> begin
false
end
| (FStar_Util.Inl (t), _64_1900) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _64_1909; FStar_Absyn_Syntax.pos = _64_1907; FStar_Absyn_Syntax.fvs = _64_1905; FStar_Absyn_Syntax.uvs = _64_1903}, (FStar_Util.Inr (_64_1914), _64_1917)::[]) -> begin
(FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.decreases_lid)
end
| _64_1923 -> begin
false
end)
end))))
in (match (_64_1926) with
| (dec, rest) -> begin
(let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _64_12 -> (match (_64_12) with
| (FStar_Util.Inl (t), _64_1931) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (_64_1934, (FStar_Util.Inr (arg), _64_1938)::[]) -> begin
FStar_Absyn_Syntax.DECREASES (arg)
end
| _64_1944 -> begin
(FStar_All.failwith "impos")
end)
end
| _64_1946 -> begin
(FStar_All.failwith "impos")
end))))
in if ((FStar_Parser_DesugarEnv.is_effect_name env eff.FStar_Absyn_Syntax.v) || (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid)) then begin
if ((FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid) && ((FStar_List.length decreases_clause) = 0)) then begin
(FStar_Absyn_Syntax.mk_Total result_typ)
end else begin
(let flags = if (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Lemma_lid) then begin
(FStar_Absyn_Syntax.LEMMA)::[]
end else begin
if (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid) then begin
(FStar_Absyn_Syntax.TOTAL)::[]
end else begin
if (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_ML_lid) then begin
(FStar_Absyn_Syntax.MLEFFECT)::[]
end else begin
[]
end
end
end
in (let rest = if (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Lemma_lid) then begin
(match (rest) with
| req::ens::(FStar_Util.Inr (pat), aq)::[] -> begin
(let _167_665 = (let _167_664 = (let _167_663 = (let _167_662 = (let _167_661 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((pat, FStar_Absyn_Syntax.Meta_smt_pat))))
in FStar_Util.Inr (_167_661))
in (_167_662, aq))
in (_167_663)::[])
in (ens)::_167_664)
in (req)::_167_665)
end
| _64_1957 -> begin
rest
end)
end else begin
rest
end
in (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = eff.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.result_typ = result_typ; FStar_Absyn_Syntax.effect_args = rest; FStar_Absyn_Syntax.flags = (FStar_List.append flags decreases_clause)})))
end
end else begin
if default_ok then begin
(env.FStar_Parser_DesugarEnv.default_result_effect t r)
end else begin
(let _167_667 = (let _167_666 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _167_666))
in (fail _167_667))
end
end)
end))
end
| _64_1960 -> begin
if default_ok then begin
(env.FStar_Parser_DesugarEnv.default_result_effect t r)
end else begin
(let _167_669 = (let _167_668 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _167_668))
in (fail _167_669))
end
end)
end))))))
and desugar_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.knd = (fun env k -> (let pos = (fun f -> (f k.FStar_Parser_AST.range))
in (let setpos = (fun kk -> (let _64_1967 = kk
in {FStar_Absyn_Syntax.n = _64_1967.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _64_1967.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = k.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _64_1967.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _64_1967.FStar_Absyn_Syntax.uvs}))
in (let k = (unparen k)
in (match (k.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _64_1976; FStar_Ident.ident = _64_1974; FStar_Ident.nsstr = _64_1972; FStar_Ident.str = "Type"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_type)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _64_1985; FStar_Ident.ident = _64_1983; FStar_Ident.nsstr = _64_1981; FStar_Ident.str = "Effect"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_effect)
end
| FStar_Parser_AST.Name (l) -> begin
(match ((let _167_681 = (FStar_Parser_DesugarEnv.qualify_lid env l)
in (FStar_Parser_DesugarEnv.find_kind_abbrev env _167_681))) with
| Some (l) -> begin
(FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, []), FStar_Absyn_Syntax.mk_Kind_unknown)))
end
| _64_1993 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)
end
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.kun)
end
| FStar_Parser_AST.Product (bs, k) -> begin
(let _64_2001 = (uncurry bs k)
in (match (_64_2001) with
| (bs, k) -> begin
(let rec aux = (fun env bs _64_13 -> (match (_64_13) with
| [] -> begin
(let _167_692 = (let _167_691 = (let _167_690 = (desugar_kind env k)
in ((FStar_List.rev bs), _167_690))
in (FStar_Absyn_Syntax.mk_Kind_arrow _167_691))
in (FStar_All.pipe_left pos _167_692))
end
| hd::tl -> begin
(let _64_2012 = (let _167_694 = (let _167_693 = (FStar_Parser_DesugarEnv.default_ml env)
in (desugar_binder _167_693 hd))
in (FStar_All.pipe_right _167_694 (as_binder env hd.FStar_Parser_AST.aqual)))
in (match (_64_2012) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(match ((FStar_Parser_DesugarEnv.find_kind_abbrev env l)) with
| None -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end
| Some (l) -> begin
(let args = (FStar_List.map (fun _64_2022 -> (match (_64_2022) with
| (t, b) -> begin
(let qual = if (b = FStar_Parser_AST.Hash) then begin
Some (FStar_Absyn_Syntax.Implicit)
end else begin
None
end
in (let _167_696 = (desugar_typ_or_exp env t)
in (_167_696, qual)))
end)) args)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), FStar_Absyn_Syntax.mk_Kind_unknown))))
end)
end
| _64_2026 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)))))
and desugar_formula' : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env f -> (let connective = (fun s -> (match (s) with
| "/\\" -> begin
Some (FStar_Absyn_Const.and_lid)
end
| "\\/" -> begin
Some (FStar_Absyn_Const.or_lid)
end
| "==>" -> begin
Some (FStar_Absyn_Const.imp_lid)
end
| "<==>" -> begin
Some (FStar_Absyn_Const.iff_lid)
end
| "~" -> begin
Some (FStar_Absyn_Const.not_lid)
end
| _64_2037 -> begin
None
end))
in (let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (let setpos = (fun t -> (let _64_2042 = t
in {FStar_Absyn_Syntax.n = _64_2042.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _64_2042.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = f.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _64_2042.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _64_2042.FStar_Absyn_Syntax.uvs}))
in (let desugar_quant = (fun q qt b pats body -> (let tk = (desugar_binder env (let _64_2050 = b
in {FStar_Parser_AST.b = _64_2050.FStar_Parser_AST.b; FStar_Parser_AST.brange = _64_2050.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _64_2050.FStar_Parser_AST.aqual}))
in (let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _167_732 = (desugar_typ_or_exp env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _167_732)))))) pats))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(let _64_2065 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_64_2065) with
| (env, a) -> begin
(let pats = (desugar_pats env pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _64_2070 -> begin
(let _167_733 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
in (FStar_All.pipe_left setpos _167_733))
end)
in (let body = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k)))::[], body)))
in (let _167_738 = (let _167_737 = (let _167_736 = (FStar_Ident.set_lid_range qt b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _167_736 FStar_Absyn_Syntax.kun))
in (FStar_Absyn_Util.mk_typ_app _167_737 (((FStar_Absyn_Syntax.targ body))::[])))
in (FStar_All.pipe_left setpos _167_738))))))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(let _64_2080 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_64_2080) with
| (env, x) -> begin
(let pats = (desugar_pats env pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _64_2085 -> begin
(FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
end)
in (let body = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t)))::[], body)))
in (let _167_743 = (let _167_742 = (let _167_741 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _167_741 FStar_Absyn_Syntax.kun))
in (FStar_Absyn_Util.mk_typ_app _167_742 (((FStar_Absyn_Syntax.targ body))::[])))
in (FStar_All.pipe_left setpos _167_743))))))
end))
end
| _64_2089 -> begin
(FStar_All.failwith "impossible")
end))))
in (let push_quant = (fun q binders pats body -> (match (binders) with
| b::b'::_rest -> begin
(let rest = (b')::_rest
in (let body = (let _167_758 = (q (rest, pats, body))
in (let _167_757 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _167_758 _167_757 FStar_Parser_AST.Formula)))
in (let _167_759 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _167_759 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _64_2103 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _167_760 = (unparen f)
in _167_760.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(let f = (desugar_formula env f)
in (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((f, l, FStar_Absyn_Syntax.dummyRange, p)))))
end
| FStar_Parser_AST.Op ("==", hd::_args) -> begin
(let args = (hd)::_args
in (let args = (FStar_List.map (fun t -> (let _167_762 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _167_762))) args)
in (let eq = if (is_type env hd) then begin
(let _167_763 = (FStar_Ident.set_lid_range FStar_Absyn_Const.eqT_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _167_763 FStar_Absyn_Syntax.kun))
end else begin
(let _167_764 = (FStar_Ident.set_lid_range FStar_Absyn_Const.eq2_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _167_764 FStar_Absyn_Syntax.kun))
end
in (FStar_Absyn_Util.mk_typ_app eq args))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match (((connective s), args)) with
| (Some (conn), _64_2129::_64_2127::[]) -> begin
(let _167_769 = (let _167_765 = (FStar_Ident.set_lid_range conn f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _167_765 FStar_Absyn_Syntax.kun))
in (let _167_768 = (FStar_List.map (fun x -> (let _167_767 = (desugar_formula env x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _167_767))) args)
in (FStar_Absyn_Util.mk_typ_app _167_769 _167_768)))
end
| _64_2134 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _167_770 = (desugar_exp env f)
in (FStar_All.pipe_right _167_770 FStar_Absyn_Util.b2t))
end
end)
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _167_775 = (let _167_771 = (FStar_Ident.set_lid_range FStar_Absyn_Const.ite_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _167_771 FStar_Absyn_Syntax.kun))
in (let _167_774 = (FStar_List.map (fun x -> (match ((desugar_typ_or_exp env x)) with
| FStar_Util.Inl (t) -> begin
(FStar_Absyn_Syntax.targ t)
end
| FStar_Util.Inr (v) -> begin
(let _167_773 = (FStar_Absyn_Util.b2t v)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _167_773))
end)) ((f1)::(f2)::(f3)::[]))
in (FStar_Absyn_Util.mk_typ_app _167_775 _167_774)))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall (_1::_2::_3, pats, body) -> begin
(let binders = (_1)::(_2)::_3
in (let _167_777 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _167_777)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(let binders = (_1)::(_2)::_3
in (let _167_779 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _167_779)))
end
| FStar_Parser_AST.QForall (b::[], pats, body) -> begin
(desugar_quant FStar_Absyn_Const.forall_lid FStar_Absyn_Const.allTyp_lid b pats body)
end
| FStar_Parser_AST.QExists (b::[], pats, body) -> begin
(desugar_quant FStar_Absyn_Const.exists_lid FStar_Absyn_Const.allTyp_lid b pats body)
end
| FStar_Parser_AST.Paren (f) -> begin
(desugar_formula env f)
end
| _64_2196 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _167_780 = (desugar_exp env f)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _167_780))
end
end)))))))
and desugar_formula : env_t  ->  FStar_Parser_AST.term  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t -> (desugar_formula' (let _64_2199 = env
in {FStar_Parser_DesugarEnv.curmodule = _64_2199.FStar_Parser_DesugarEnv.curmodule; FStar_Parser_DesugarEnv.modules = _64_2199.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _64_2199.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _64_2199.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _64_2199.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _64_2199.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _64_2199.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = FStar_Parser_AST.Formula; FStar_Parser_DesugarEnv.sigmap = _64_2199.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _64_2199.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _64_2199.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _64_2199.FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  ((FStar_Absyn_Syntax.ident Prims.option * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax), (FStar_Absyn_Syntax.ident Prims.option * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either = (fun env b -> if (is_type_binder env b) then begin
(let _167_785 = (desugar_type_binder env b)
in FStar_Util.Inl (_167_785))
end else begin
(let _167_786 = (desugar_exp_binder env b)
in FStar_Util.Inr (_167_786))
end)
and typars_of_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (let _64_2232 = (FStar_List.fold_left (fun _64_2207 b -> (match (_64_2207) with
| (env, out) -> begin
(let tk = (desugar_binder env (let _64_2209 = b
in {FStar_Parser_AST.b = _64_2209.FStar_Parser_AST.b; FStar_Parser_AST.brange = _64_2209.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _64_2209.FStar_Parser_AST.aqual}))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(let _64_2219 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_64_2219) with
| (env, a) -> begin
(env, ((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), (trans_aqual b.FStar_Parser_AST.aqual)))::out)
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(let _64_2227 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_64_2227) with
| (env, x) -> begin
(env, ((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), (trans_aqual b.FStar_Parser_AST.aqual)))::out)
end))
end
| _64_2229 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_64_2232) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_exp_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Absyn_Syntax.ident Prims.option * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, t) -> begin
(let _167_793 = (desugar_typ env t)
in (Some (x), _167_793))
end
| FStar_Parser_AST.TVariable (t) -> begin
(let _167_794 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in (None, _167_794))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _167_795 = (desugar_typ env t)
in (None, _167_795))
end
| FStar_Parser_AST.Variable (x) -> begin
(Some (x), FStar_Absyn_Syntax.tun)
end
| _64_2246 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a type)", b.FStar_Parser_AST.brange))))
end))
and desugar_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Absyn_Syntax.ident Prims.option * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun env b -> (let fail = (fun _64_2250 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a kind)", b.FStar_Parser_AST.brange))))
end))
in (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, t)) | (FStar_Parser_AST.TAnnotated (x, t)) -> begin
(let _167_800 = (desugar_kind env t)
in (Some (x), _167_800))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _167_801 = (desugar_kind env t)
in (None, _167_801))
end
| FStar_Parser_AST.TVariable (x) -> begin
(Some (x), (let _64_2261 = FStar_Absyn_Syntax.mk_Kind_type
in {FStar_Absyn_Syntax.n = _64_2261.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _64_2261.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = b.FStar_Parser_AST.brange; FStar_Absyn_Syntax.fvs = _64_2261.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _64_2261.FStar_Absyn_Syntax.uvs}))
end
| _64_2264 -> begin
(fail ())
end)))

let gather_tc_binders : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun tps k -> (let rec aux = (fun bs k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(aux (FStar_List.append bs binders) k)
end
| FStar_Absyn_Syntax.Kind_abbrev (_64_2275, k) -> begin
(aux bs k)
end
| _64_2280 -> begin
bs
end))
in (let _167_810 = (aux tps k)
in (FStar_All.pipe_right _167_810 FStar_Absyn_Util.name_binders))))

let mk_data_discriminators : FStar_Absyn_Syntax.qualifier Prims.list  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Ident.lid  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_DesugarEnv.iface) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_List.append ((FStar_Absyn_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (let binders = (gather_tc_binders tps k)
in (let p = (FStar_Ident.range_of_lid t)
in (let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _64_2294 -> (match (_64_2294) with
| (x, _64_2293) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end))))
in (let binders = (let _167_831 = (let _167_830 = (let _167_829 = (let _167_828 = (let _167_827 = (FStar_Absyn_Util.ftv t FStar_Absyn_Syntax.kun)
in (let _167_826 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (_167_827, _167_826)))
in (FStar_Absyn_Syntax.mk_Typ_app' _167_828 None p))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder _167_829))
in (_167_830)::[])
in (FStar_List.append imp_binders _167_831))
in (let disc_type = (let _167_834 = (let _167_833 = (let _167_832 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.total_comp _167_832 p))
in (binders, _167_833))
in (FStar_Absyn_Syntax.mk_Typ_fun _167_834 None p))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (let disc_name = (FStar_Absyn_Util.mk_discriminator d)
in (let _167_837 = (let _167_836 = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Discriminator (d))::[]))
in (disc_name, disc_type, _167_836, (FStar_Ident.range_of_lid disc_name)))
in FStar_Absyn_Syntax.Sig_val_decl (_167_837)))))))))))))

let mk_indexed_projectors = (fun fvq refine_domain env _64_2306 lid formals t -> (match (_64_2306) with
| (tc, tps, k) -> begin
(let binders = (gather_tc_binders tps k)
in (let p = (FStar_Ident.range_of_lid lid)
in (let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p))
in (let projectee = (let _167_847 = (FStar_Absyn_Util.genident (Some (p)))
in {FStar_Absyn_Syntax.ppname = (FStar_Absyn_Syntax.mk_ident ("projectee", p)); FStar_Absyn_Syntax.realname = _167_847})
in (let arg_exp = (FStar_Absyn_Util.bvd_to_exp projectee FStar_Absyn_Syntax.tun)
in (let arg_binder = (let arg_typ = (let _167_850 = (let _167_849 = (FStar_Absyn_Util.ftv tc FStar_Absyn_Syntax.kun)
in (let _167_848 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (_167_849, _167_848)))
in (FStar_Absyn_Syntax.mk_Typ_app' _167_850 None p))
in if (not (refine_domain)) then begin
(FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end else begin
(let disc_name = (FStar_Absyn_Util.mk_discriminator lid)
in (let x = (FStar_Absyn_Util.gen_bvar arg_typ)
in (let _167_860 = (let _167_859 = (let _167_858 = (let _167_857 = (let _167_856 = (let _167_855 = (let _167_854 = (FStar_Absyn_Util.fvar None disc_name p)
in (let _167_853 = (let _167_852 = (let _167_851 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _167_851))
in (_167_852)::[])
in (_167_854, _167_853)))
in (FStar_Absyn_Syntax.mk_Exp_app _167_855 None p))
in (FStar_Absyn_Util.b2t _167_856))
in (x, _167_857))
in (FStar_Absyn_Syntax.mk_Typ_refine _167_858 None p))
in (FStar_All.pipe_left (FStar_Absyn_Util.bvd_to_bvar_s projectee) _167_859))
in (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder _167_860))))
end)
in (let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _64_2323 -> (match (_64_2323) with
| (x, _64_2322) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end))))
in (let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (let arg = (FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (let subst = (let _167_868 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i f -> (match ((Prims.fst f)) with
| FStar_Util.Inl (a) -> begin
(let _64_2334 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_64_2334) with
| (field_name, _64_2333) -> begin
(let proj = (let _167_865 = (let _167_864 = (FStar_Absyn_Util.ftv field_name FStar_Absyn_Syntax.kun)
in (_167_864, (arg)::[]))
in (FStar_Absyn_Syntax.mk_Typ_app _167_865 None p))
in (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, proj)))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(let _64_2341 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_64_2341) with
| (field_name, _64_2340) -> begin
(let proj = (let _167_867 = (let _167_866 = (FStar_Absyn_Util.fvar None field_name p)
in (_167_866, (arg)::[]))
in (FStar_Absyn_Syntax.mk_Exp_app _167_867 None p))
in (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, proj)))::[])
end))
end))))
in (FStar_All.pipe_right _167_868 FStar_List.flatten))
in (let ntps = (FStar_List.length tps)
in (let all_params = (let _167_870 = (FStar_All.pipe_right tps (FStar_List.map (fun _64_2348 -> (match (_64_2348) with
| (b, _64_2347) -> begin
(b, Some (FStar_Absyn_Syntax.Implicit))
end))))
in (FStar_List.append _167_870 formals))
in (let _167_898 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i ax -> (match ((Prims.fst ax)) with
| FStar_Util.Inl (a) -> begin
(let _64_2357 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_64_2357) with
| (field_name, _64_2356) -> begin
(let kk = (let _167_874 = (let _167_873 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (binders, _167_873))
in (FStar_Absyn_Syntax.mk_Kind_arrow _167_874 p))
in (FStar_Absyn_Syntax.Sig_tycon ((field_name, [], kk, [], [], (FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector ((lid, FStar_Util.Inl (a.FStar_Absyn_Syntax.v))))::[], (FStar_Ident.range_of_lid field_name))))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(let _64_2364 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_64_2364) with
| (field_name, _64_2363) -> begin
(let t = (let _167_877 = (let _167_876 = (let _167_875 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Absyn_Util.total_comp _167_875 p))
in (binders, _167_876))
in (FStar_Absyn_Syntax.mk_Typ_fun _167_877 None p))
in (let quals = (fun q -> if ((not (env.FStar_Parser_DesugarEnv.iface)) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_Absyn_Syntax.Assumption)::q
end else begin
q
end)
in (let quals = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector ((lid, FStar_Util.Inr (x.FStar_Absyn_Syntax.v))))::[]))
in (let impl = if (((let _167_880 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _167_880)) || (fvq <> FStar_Absyn_Syntax.Data_ctor)) || (let _167_882 = (let _167_881 = (FStar_Parser_DesugarEnv.current_module env)
in _167_881.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _167_882))) then begin
[]
end else begin
(let projection = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (let as_imp = (fun _64_14 -> (match (_64_14) with
| Some (FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _64_2374 -> begin
false
end))
in (let arg_pats = (let _167_895 = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j by -> (match (by) with
| (FStar_Util.Inl (_64_2379), imp) -> begin
if (j < ntps) then begin
[]
end else begin
(let _167_890 = (let _167_889 = (let _167_888 = (let _167_887 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.kun)
in FStar_Absyn_Syntax.Pat_tvar (_167_887))
in (pos _167_888))
in (_167_889, (as_imp imp)))
in (_167_890)::[])
end
end
| (FStar_Util.Inr (_64_2384), imp) -> begin
if ((i + ntps) = j) then begin
(((pos (FStar_Absyn_Syntax.Pat_var (projection))), (as_imp imp)))::[]
end else begin
(let _167_894 = (let _167_893 = (let _167_892 = (let _167_891 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in FStar_Absyn_Syntax.Pat_wild (_167_891))
in (pos _167_892))
in (_167_893, (as_imp imp)))
in (_167_894)::[])
end
end))))
in (FStar_All.pipe_right _167_895 FStar_List.flatten))
in (let pat = (let _167_897 = (FStar_All.pipe_right (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv lid), Some (fvq), arg_pats))) pos)
in (let _167_896 = (FStar_Absyn_Util.bvar_to_exp projection)
in (_167_897, None, _167_896)))
in (let body = (FStar_Absyn_Syntax.mk_Exp_match (arg_exp, (pat)::[]) None p)
in (let imp = (FStar_Absyn_Syntax.mk_Exp_abs (binders, body) None (FStar_Ident.range_of_lid field_name))
in (let lb = {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (field_name); FStar_Absyn_Syntax.lbtyp = FStar_Absyn_Syntax.tun; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_Tot_lid; FStar_Absyn_Syntax.lbdef = imp}
in (FStar_Absyn_Syntax.Sig_let (((false, (lb)::[]), p, [], quals)))::[])))))))
end
in (FStar_Absyn_Syntax.Sig_val_decl ((field_name, t, quals, (FStar_Ident.range_of_lid field_name))))::impl))))
end))
end))))
in (FStar_All.pipe_right _167_898 FStar_List.flatten))))))))))))))
end))

let mk_data_projectors : FStar_Parser_DesugarEnv.env  ->  FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun env _64_17 -> (match (_64_17) with
| FStar_Absyn_Syntax.Sig_datacon (lid, t, tycon, quals, _64_2401, _64_2403) when (not ((FStar_Ident.lid_equals lid FStar_Absyn_Const.lexcons_lid))) -> begin
(let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _64_15 -> (match (_64_15) with
| FStar_Absyn_Syntax.RecordConstructor (_64_2408) -> begin
true
end
| _64_2411 -> begin
false
end)))) then begin
false
end else begin
(let _64_2417 = tycon
in (match (_64_2417) with
| (l, _64_2414, _64_2416) -> begin
(match ((FStar_Parser_DesugarEnv.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _64_2421 -> begin
true
end)
end))
end
in (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
(let cod = (FStar_Absyn_Util.comp_result cod)
in (let qual = (match ((FStar_Util.find_map quals (fun _64_16 -> (match (_64_16) with
| FStar_Absyn_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Absyn_Syntax.Record_ctor ((lid, fns)))
end
| _64_2432 -> begin
None
end)))) with
| None -> begin
FStar_Absyn_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)
in (mk_indexed_projectors qual refine_domain env tycon lid formals cod)))
end
| _64_2438 -> begin
[]
end))
end
| _64_2440 -> begin
[]
end))

let rec desugar_tycon : FStar_Parser_DesugarEnv.env  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Absyn_Syntax.sigelts) = (fun env rng quals tcs -> (let tycon_id = (fun _64_18 -> (match (_64_18) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _167_918 = (let _167_917 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_167_917))
in (FStar_Parser_AST.mk_term _167_918 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((tot, t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (let apply_binders = (fun t binders -> (let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _64_2505 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _167_931 = (let _167_930 = (let _167_929 = (binder_to_term b)
in (out, _167_929, (imp_of_aqual b)))
in FStar_Parser_AST.App (_167_930))
in (FStar_Parser_AST.mk_term _167_931 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (let tycon_record_as_variant = (fun _64_19 -> (match (_64_19) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (let mfields = (FStar_List.map (fun _64_2518 -> (match (_64_2518) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Absyn_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (let result = (let _167_937 = (let _167_936 = (let _167_935 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_167_935))
in (FStar_Parser_AST.mk_term _167_936 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _167_937 parms))
in (let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _167_939 = (FStar_All.pipe_right fields (FStar_List.map (fun _64_2525 -> (match (_64_2525) with
| (x, _64_2524) -> begin
(FStar_Parser_DesugarEnv.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _167_939))))))
end
| _64_2527 -> begin
(FStar_All.failwith "impossible")
end))
in (let desugar_abstract_tc = (fun quals _env mutuals _64_20 -> (match (_64_20) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(let _64_2541 = (typars_of_binders _env binders)
in (match (_64_2541) with
| (_env', typars) -> begin
(let k = (match (kopt) with
| None -> begin
FStar_Absyn_Syntax.kun
end
| Some (k) -> begin
(desugar_kind _env' k)
end)
in (let tconstr = (let _167_950 = (let _167_949 = (let _167_948 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_167_948))
in (FStar_Parser_AST.mk_term _167_949 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _167_950 binders))
in (let qlid = (FStar_Parser_DesugarEnv.qualify _env id)
in (let se = FStar_Absyn_Syntax.Sig_tycon ((qlid, typars, k, mutuals, [], quals, rng))
in (let _env = (FStar_Parser_DesugarEnv.push_rec_binding _env (FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (let _env2 = (FStar_Parser_DesugarEnv.push_rec_binding _env' (FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (_env, _env2, se, tconstr)))))))
end))
end
| _64_2552 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (let push_tparam = (fun env _64_21 -> (match (_64_21) with
| (FStar_Util.Inr (x), _64_2559) -> begin
(FStar_Parser_DesugarEnv.push_bvvdef env x.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inl (a), _64_2564) -> begin
(FStar_Parser_DesugarEnv.push_btvdef env a.FStar_Absyn_Syntax.v)
end))
in (let push_tparams = (FStar_List.fold_left push_tparam)
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (_64_2568)::[] -> begin
(let tc = (FStar_List.hd tcs)
in (let _64_2579 = (desugar_abstract_tc quals env [] tc)
in (match (_64_2579) with
| (_64_2573, _64_2575, se, _64_2578) -> begin
(let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))
end)))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t)::[] -> begin
(let _64_2590 = (typars_of_binders env binders)
in (match (_64_2590) with
| (env', typars) -> begin
(let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _64_22 -> (match (_64_22) with
| FStar_Absyn_Syntax.Effect -> begin
true
end
| _64_2595 -> begin
false
end)) quals) then begin
FStar_Absyn_Syntax.mk_Kind_effect
end else begin
FStar_Absyn_Syntax.kun
end
end
| Some (k) -> begin
(desugar_kind env' k)
end)
in (let t0 = t
in (let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _64_23 -> (match (_64_23) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _64_2603 -> begin
false
end)))) then begin
quals
end else begin
if (t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula) then begin
(FStar_Absyn_Syntax.Logic)::quals
end else begin
quals
end
end
in (let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Effect)) then begin
(let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (let _167_962 = (let _167_961 = (FStar_Parser_DesugarEnv.qualify env id)
in (let _167_960 = (FStar_All.pipe_right quals (FStar_List.filter (fun _64_24 -> (match (_64_24) with
| FStar_Absyn_Syntax.Effect -> begin
false
end
| _64_2609 -> begin
true
end))))
in (_167_961, typars, c, _167_960, rng)))
in FStar_Absyn_Syntax.Sig_effect_abbrev (_167_962)))
end else begin
(let t = (desugar_typ env' t)
in (let _167_964 = (let _167_963 = (FStar_Parser_DesugarEnv.qualify env id)
in (_167_963, typars, k, t, quals, rng))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_167_964)))
end
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| FStar_Parser_AST.TyconRecord (_64_2614)::[] -> begin
(let trec = (FStar_List.hd tcs)
in (let _64_2620 = (tycon_record_as_variant trec)
in (match (_64_2620) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _64_2624::_64_2622 -> begin
(let env0 = env
in (let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (let rec collect_tcs = (fun quals et tc -> (let _64_2635 = et
in (match (_64_2635) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_64_2637) -> begin
(let trec = tc
in (let _64_2642 = (tycon_record_as_variant trec)
in (match (_64_2642) with
| (t, fs) -> begin
(collect_tcs ((FStar_Absyn_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(let _64_2654 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_64_2654) with
| (env, _64_2651, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(let _64_2666 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_64_2666) with
| (env, _64_2663, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _64_2668 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (let _64_2671 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_64_2671) with
| (env, tcs) -> begin
(let tcs = (FStar_List.rev tcs)
in (let sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _64_26 -> (match (_64_26) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (id, tpars, k, _64_2678, _64_2680, _64_2682, _64_2684), t, quals) -> begin
(let env_tps = (push_tparams env tpars)
in (let t = (desugar_typ env_tps t)
in (FStar_Absyn_Syntax.Sig_typ_abbrev ((id, tpars, k, t, [], rng)))::[]))
end
| FStar_Util.Inl (FStar_Absyn_Syntax.Sig_tycon (tname, tpars, k, mutuals, _64_2698, tags, _64_2701), constrs, tconstr, quals) -> begin
(let tycon = (tname, tpars, k)
in (let env_tps = (push_tparams env tpars)
in (let _64_2732 = (let _167_980 = (FStar_All.pipe_right constrs (FStar_List.map (fun _64_2714 -> (match (_64_2714) with
| (id, topt, of_notation) -> begin
(let t = if of_notation then begin
(match (topt) with
| Some (t) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level None))::[], tconstr))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end
| None -> begin
tconstr
end)
end else begin
(match (topt) with
| None -> begin
(FStar_All.failwith "Impossible")
end
| Some (t) -> begin
t
end)
end
in (let t = (let _167_975 = (FStar_Parser_DesugarEnv.default_total env_tps)
in (let _167_974 = (close env_tps t)
in (desugar_typ _167_975 _167_974)))
in (let name = (FStar_Parser_DesugarEnv.qualify env id)
in (let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _64_25 -> (match (_64_25) with
| FStar_Absyn_Syntax.RecordType (fns) -> begin
(FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _64_2728 -> begin
[]
end))))
in (let _167_979 = (let _167_978 = (let _167_977 = (FStar_All.pipe_right t FStar_Absyn_Util.name_function_binders)
in (name, _167_977, tycon, quals, mutuals, rng))
in FStar_Absyn_Syntax.Sig_datacon (_167_978))
in (name, _167_979))))))
end))))
in (FStar_All.pipe_left FStar_List.split _167_980))
in (match (_64_2732) with
| (constrNames, constrs) -> begin
(FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, constrNames, tags, rng)))::constrs
end))))
end
| _64_2734 -> begin
(FStar_All.failwith "impossible")
end))))
in (let bundle = (let _167_982 = (let _167_981 = (FStar_List.collect FStar_Absyn_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _167_981, rng))
in FStar_Absyn_Syntax.Sig_bundle (_167_982))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (let data_ops = (FStar_All.pipe_right sigelts (FStar_List.collect (mk_data_projectors env)))
in (let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _64_27 -> (match (_64_27) with
| FStar_Absyn_Syntax.Sig_tycon (tname, tps, k, _64_2744, constrs, quals, _64_2748) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _64_2752 -> begin
[]
end))))
in (let ops = (FStar_List.append discs data_ops)
in (let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env ops)
in (env, (FStar_List.append ((bundle)::[]) ops))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end)))))))))))

let desugar_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * ((FStar_Absyn_Syntax.btvar, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env binders -> (let _64_2783 = (FStar_List.fold_left (fun _64_2761 b -> (match (_64_2761) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| FStar_Util.Inl (Some (a), k) -> begin
(let _64_2770 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_64_2770) with
| (env, a) -> begin
(env, ((FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k)))::binders)
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(let _64_2778 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_64_2778) with
| (env, x) -> begin
(env, ((FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t)))::binders)
end))
end
| _64_2780 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_64_2783) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))

let trans_qual : FStar_Parser_AST.qualifier  ->  FStar_Absyn_Syntax.qualifier = (fun _64_28 -> (match (_64_28) with
| FStar_Parser_AST.Private -> begin
FStar_Absyn_Syntax.Private
end
| FStar_Parser_AST.Assumption -> begin
FStar_Absyn_Syntax.Assumption
end
| FStar_Parser_AST.Opaque -> begin
FStar_Absyn_Syntax.Opaque
end
| FStar_Parser_AST.Logic -> begin
FStar_Absyn_Syntax.Logic
end
| FStar_Parser_AST.TotalEffect -> begin
FStar_Absyn_Syntax.TotalEffect
end
| FStar_Parser_AST.DefaultEffect -> begin
FStar_Absyn_Syntax.DefaultEffect (None)
end
| FStar_Parser_AST.Effect -> begin
FStar_Absyn_Syntax.Effect
end))

let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Absyn_Syntax.pragma = (fun _64_29 -> (match (_64_29) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Absyn_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions -> begin
FStar_Absyn_Syntax.ResetOptions
end))

let trans_quals : FStar_Parser_AST.qualifier Prims.list  ->  FStar_Absyn_Syntax.qualifier Prims.list = (FStar_List.map trans_qual)

let rec desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Absyn_Syntax.sigelts) = (fun env d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(let se = FStar_Absyn_Syntax.Sig_pragma (((trans_pragma p), d.FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| FStar_Parser_AST.Open (lid) -> begin
(let env = (FStar_Parser_DesugarEnv.push_namespace env lid)
in (env, []))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _167_999 = (FStar_Parser_DesugarEnv.push_module_abbrev env x l)
in (_167_999, []))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _167_1000 = (trans_quals qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _167_1000 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _167_1002 = (let _167_1001 = (desugar_exp_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Absyn_Util.compress_exp _167_1001))
in _167_1002.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let (lbs, _64_2819) -> begin
(let lids = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inr (l) -> begin
l
end
| _64_2826 -> begin
(FStar_All.failwith "impossible")
end))))
in (let quals = (match (quals) with
| _64_2831::_64_2829 -> begin
(trans_quals quals)
end
| _64_2834 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _64_30 -> (match (_64_30) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_64_2843); FStar_Absyn_Syntax.lbtyp = _64_2841; FStar_Absyn_Syntax.lbeff = _64_2839; FStar_Absyn_Syntax.lbdef = _64_2837} -> begin
[]
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = _64_2851; FStar_Absyn_Syntax.lbeff = _64_2849; FStar_Absyn_Syntax.lbdef = _64_2847} -> begin
(FStar_Parser_DesugarEnv.lookup_letbinding_quals env l)
end))))
end)
in (let s = FStar_Absyn_Syntax.Sig_let ((lbs, d.FStar_Parser_AST.drange, lids, quals))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env s)
in (env, (s)::[])))))
end
| _64_2859 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(let e = (desugar_exp env t)
in (let se = FStar_Absyn_Syntax.Sig_main ((e, d.FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(let f = (desugar_formula env t)
in (let _167_1008 = (let _167_1007 = (let _167_1006 = (let _167_1005 = (FStar_Parser_DesugarEnv.qualify env id)
in (_167_1005, f, (FStar_Absyn_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Sig_assume (_167_1006))
in (_167_1007)::[])
in (env, _167_1008)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(let t = (let _167_1009 = (close_fun env t)
in (desugar_typ env _167_1009))
in (let quals = if (env.FStar_Parser_DesugarEnv.iface && env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(let _167_1010 = (trans_quals quals)
in (FStar_Absyn_Syntax.Assumption)::_167_1010)
end else begin
(trans_quals quals)
end
in (let se = (let _167_1012 = (let _167_1011 = (FStar_Parser_DesugarEnv.qualify env id)
in (_167_1011, t, quals, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Sig_val_decl (_167_1012))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[])))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(let t = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (let l = (FStar_Parser_DesugarEnv.qualify env id)
in (let se = FStar_Absyn_Syntax.Sig_datacon ((l, t, (FStar_Absyn_Const.exn_lid, [], FStar_Absyn_Syntax.ktype), (FStar_Absyn_Syntax.ExceptionConstructor)::[], (FStar_Absyn_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (let se' = FStar_Absyn_Syntax.Sig_bundle (((se)::[], (FStar_Absyn_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env se')
in (let data_ops = (mk_data_projectors env se)
in (let discs = (mk_data_discriminators [] env FStar_Absyn_Const.exn_lid [] FStar_Absyn_Syntax.ktype ((l)::[]))
in (let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(let t = (desugar_typ env term)
in (let t = (let _167_1015 = (let _167_1014 = (let _167_1013 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (FStar_Absyn_Syntax.mk_Total _167_1013))
in (((FStar_Absyn_Syntax.null_v_binder t))::[], _167_1014))
in (FStar_Absyn_Syntax.mk_Typ_fun _167_1015 None d.FStar_Parser_AST.drange))
in (let l = (FStar_Parser_DesugarEnv.qualify env id)
in (let se = FStar_Absyn_Syntax.Sig_datacon ((l, t, (FStar_Absyn_Const.exn_lid, [], FStar_Absyn_Syntax.ktype), (FStar_Absyn_Syntax.ExceptionConstructor)::[], (FStar_Absyn_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (let se' = FStar_Absyn_Syntax.Sig_bundle (((se)::[], (FStar_Absyn_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env se')
in (let data_ops = (mk_data_projectors env se)
in (let discs = (mk_data_discriminators [] env FStar_Absyn_Const.exn_lid [] FStar_Absyn_Syntax.ktype ((l)::[]))
in (let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(let _64_2912 = (desugar_binders env binders)
in (match (_64_2912) with
| (env_k, binders) -> begin
(let k = (desugar_kind env_k k)
in (let name = (FStar_Parser_DesugarEnv.qualify env id)
in (let se = FStar_Absyn_Syntax.Sig_kind_abbrev ((name, binders, k, d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[])))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(let env0 = env
in (let _64_2928 = (desugar_binders env eff_binders)
in (match (_64_2928) with
| (env, binders) -> begin
(let defn = (desugar_typ env defn)
in (let _64_2932 = (FStar_Absyn_Util.head_and_args defn)
in (match (_64_2932) with
| (head, args) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (eff) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_effect_defn env eff.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _167_1020 = (let _167_1019 = (let _167_1018 = (let _167_1017 = (let _167_1016 = (FStar_Absyn_Print.sli eff.FStar_Absyn_Syntax.v)
in (Prims.strcat "Effect " _167_1016))
in (Prims.strcat _167_1017 " not found"))
in (_167_1018, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_167_1019))
in (Prims.raise _167_1020))
end
| Some (ed) -> begin
(let subst = (FStar_Absyn_Util.subst_of_list ed.FStar_Absyn_Syntax.binders args)
in (let sub = (FStar_Absyn_Util.subst_typ subst)
in (let ed = (let _167_1038 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _167_1037 = (trans_quals quals)
in (let _167_1036 = (FStar_Absyn_Util.subst_kind subst ed.FStar_Absyn_Syntax.signature)
in (let _167_1035 = (sub ed.FStar_Absyn_Syntax.ret)
in (let _167_1034 = (sub ed.FStar_Absyn_Syntax.bind_wp)
in (let _167_1033 = (sub ed.FStar_Absyn_Syntax.bind_wlp)
in (let _167_1032 = (sub ed.FStar_Absyn_Syntax.if_then_else)
in (let _167_1031 = (sub ed.FStar_Absyn_Syntax.ite_wp)
in (let _167_1030 = (sub ed.FStar_Absyn_Syntax.ite_wlp)
in (let _167_1029 = (sub ed.FStar_Absyn_Syntax.wp_binop)
in (let _167_1028 = (sub ed.FStar_Absyn_Syntax.wp_as_type)
in (let _167_1027 = (sub ed.FStar_Absyn_Syntax.close_wp)
in (let _167_1026 = (sub ed.FStar_Absyn_Syntax.close_wp_t)
in (let _167_1025 = (sub ed.FStar_Absyn_Syntax.assert_p)
in (let _167_1024 = (sub ed.FStar_Absyn_Syntax.assume_p)
in (let _167_1023 = (sub ed.FStar_Absyn_Syntax.null_wp)
in (let _167_1022 = (sub ed.FStar_Absyn_Syntax.trivial)
in {FStar_Absyn_Syntax.mname = _167_1038; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _167_1037; FStar_Absyn_Syntax.signature = _167_1036; FStar_Absyn_Syntax.ret = _167_1035; FStar_Absyn_Syntax.bind_wp = _167_1034; FStar_Absyn_Syntax.bind_wlp = _167_1033; FStar_Absyn_Syntax.if_then_else = _167_1032; FStar_Absyn_Syntax.ite_wp = _167_1031; FStar_Absyn_Syntax.ite_wlp = _167_1030; FStar_Absyn_Syntax.wp_binop = _167_1029; FStar_Absyn_Syntax.wp_as_type = _167_1028; FStar_Absyn_Syntax.close_wp = _167_1027; FStar_Absyn_Syntax.close_wp_t = _167_1026; FStar_Absyn_Syntax.assert_p = _167_1025; FStar_Absyn_Syntax.assume_p = _167_1024; FStar_Absyn_Syntax.null_wp = _167_1023; FStar_Absyn_Syntax.trivial = _167_1022})))))))))))))))))
in (let se = FStar_Absyn_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)
end
| _64_2944 -> begin
(let _167_1042 = (let _167_1041 = (let _167_1040 = (let _167_1039 = (FStar_Absyn_Print.typ_to_string head)
in (Prims.strcat _167_1039 " is not an effect"))
in (_167_1040, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_167_1041))
in (Prims.raise _167_1042))
end)
end)))
end)))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(let env0 = env
in (let env = (FStar_Parser_DesugarEnv.enter_monad_scope env eff_name)
in (let _64_2958 = (desugar_binders env eff_binders)
in (match (_64_2958) with
| (env, binders) -> begin
(let eff_k = (desugar_kind env eff_kind)
in (let _64_2969 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _64_2962 decl -> (match (_64_2962) with
| (env, out) -> begin
(let _64_2966 = (desugar_decl env decl)
in (match (_64_2966) with
| (env, ses) -> begin
(let _167_1046 = (let _167_1045 = (FStar_List.hd ses)
in (_167_1045)::out)
in (env, _167_1046))
end))
end)) (env, [])))
in (match (_64_2969) with
| (env, decls) -> begin
(let decls = (FStar_List.rev decls)
in (let lookup = (fun s -> (match ((let _167_1049 = (FStar_Parser_DesugarEnv.qualify env (FStar_Absyn_Syntax.mk_ident (s, d.FStar_Parser_AST.drange)))
in (FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _167_1049))) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat (Prims.strcat "Monad " eff_name.FStar_Ident.idText) " expects definition of ") s), d.FStar_Parser_AST.drange))))
end
| Some (t) -> begin
t
end))
in (let ed = (let _167_1065 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _167_1064 = (trans_quals quals)
in (let _167_1063 = (lookup "return")
in (let _167_1062 = (lookup "bind_wp")
in (let _167_1061 = (lookup "bind_wlp")
in (let _167_1060 = (lookup "if_then_else")
in (let _167_1059 = (lookup "ite_wp")
in (let _167_1058 = (lookup "ite_wlp")
in (let _167_1057 = (lookup "wp_binop")
in (let _167_1056 = (lookup "wp_as_type")
in (let _167_1055 = (lookup "close_wp")
in (let _167_1054 = (lookup "close_wp_t")
in (let _167_1053 = (lookup "assert_p")
in (let _167_1052 = (lookup "assume_p")
in (let _167_1051 = (lookup "null_wp")
in (let _167_1050 = (lookup "trivial")
in {FStar_Absyn_Syntax.mname = _167_1065; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _167_1064; FStar_Absyn_Syntax.signature = eff_k; FStar_Absyn_Syntax.ret = _167_1063; FStar_Absyn_Syntax.bind_wp = _167_1062; FStar_Absyn_Syntax.bind_wlp = _167_1061; FStar_Absyn_Syntax.if_then_else = _167_1060; FStar_Absyn_Syntax.ite_wp = _167_1059; FStar_Absyn_Syntax.ite_wlp = _167_1058; FStar_Absyn_Syntax.wp_binop = _167_1057; FStar_Absyn_Syntax.wp_as_type = _167_1056; FStar_Absyn_Syntax.close_wp = _167_1055; FStar_Absyn_Syntax.close_wp_t = _167_1054; FStar_Absyn_Syntax.assert_p = _167_1053; FStar_Absyn_Syntax.assume_p = _167_1052; FStar_Absyn_Syntax.null_wp = _167_1051; FStar_Absyn_Syntax.trivial = _167_1050}))))))))))))))))
in (let se = FStar_Absyn_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)))
end))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(let lookup = (fun l -> (match ((FStar_Parser_DesugarEnv.try_lookup_effect_name env l)) with
| None -> begin
(let _167_1072 = (let _167_1071 = (let _167_1070 = (let _167_1069 = (let _167_1068 = (FStar_Absyn_Print.sli l)
in (Prims.strcat "Effect name " _167_1068))
in (Prims.strcat _167_1069 " not found"))
in (_167_1070, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_167_1071))
in (Prims.raise _167_1072))
end
| Some (l) -> begin
l
end))
in (let src = (lookup l.FStar_Parser_AST.msource)
in (let dst = (lookup l.FStar_Parser_AST.mdest)
in (let lift = (desugar_typ env l.FStar_Parser_AST.lift_op)
in (let se = FStar_Absyn_Syntax.Sig_sub_effect (({FStar_Absyn_Syntax.source = src; FStar_Absyn_Syntax.target = dst; FStar_Absyn_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end))

let desugar_decls : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _64_2994 d -> (match (_64_2994) with
| (env, sigelts) -> begin
(let _64_2998 = (desugar_decl env d)
in (match (_64_2998) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))

let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.prims_lid)) FStar_Absyn_Syntax.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.all_lid)) FStar_Absyn_Syntax.dummyRange))::[]

let desugar_modul_common = (fun curmod env m -> (let open_ns = (fun mname d -> (let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _167_1088 = (let _167_1087 = (let _167_1086 = (FStar_Absyn_Syntax.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_167_1086))
in (FStar_Parser_AST.mk_decl _167_1087 (FStar_Absyn_Syntax.range_of_lid mname)))
in (_167_1088)::d)
end else begin
d
end
in d))
in (let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod, _64_3009) -> begin
(FStar_Parser_DesugarEnv.finish_module_or_interface env prev_mod)
end)
in (let _64_3028 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _167_1090 = (FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _167_1089 = (open_ns mname decls)
in (_167_1090, mname, _167_1089, true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _167_1092 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _167_1091 = (open_ns mname decls)
in (_167_1092, mname, _167_1091, false)))
end)
in (match (_64_3028) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(let _64_3031 = (desugar_decls env decls)
in (match (_64_3031) with
| (env, sigelts) -> begin
(let modul = {FStar_Absyn_Syntax.name = mname; FStar_Absyn_Syntax.declarations = sigelts; FStar_Absyn_Syntax.exports = []; FStar_Absyn_Syntax.is_interface = intf; FStar_Absyn_Syntax.is_deserialized = false}
in (env, modul, pop_when_done))
end))
end)))))

let desugar_partial_modul = (fun curmod env m -> (let m = if (FStar_ST.read FStar_Options.interactive_fsi) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _167_1099 = (let _167_1098 = (let _167_1097 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_Util.for_some (fun m -> (m = mname.FStar_Ident.str)) _167_1097))
in (mname, decls, _167_1098))
in FStar_Parser_AST.Interface (_167_1099))
end
| FStar_Parser_AST.Interface (mname, _64_3043, _64_3045) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (let _64_3053 = (desugar_modul_common curmod env m)
in (match (_64_3053) with
| (x, y, _64_3052) -> begin
(x, y)
end))))

let desugar_modul : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul) = (fun env m -> (let _64_3059 = (desugar_modul_common None env m)
in (match (_64_3059) with
| (env, modul, pop_when_done) -> begin
(let env = (FStar_Parser_DesugarEnv.finish_module_or_interface env modul)
in (let _64_3061 = if (FStar_Options.should_dump modul.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _167_1104 = (FStar_Absyn_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _167_1104))
end else begin
()
end
in (let _167_1105 = if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface modul.FStar_Absyn_Syntax.name env)
end else begin
env
end
in (_167_1105, modul))))
end)))

let desugar_file : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul Prims.list) = (fun env f -> (let _64_3074 = (FStar_List.fold_left (fun _64_3067 m -> (match (_64_3067) with
| (env, mods) -> begin
(let _64_3071 = (desugar_modul env m)
in (match (_64_3071) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_64_3074) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))

let add_modul_to_env : FStar_Absyn_Syntax.modul  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_DesugarEnv.env = (fun m en -> (let _64_3079 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false en m.FStar_Absyn_Syntax.name)
in (match (_64_3079) with
| (en, pop_when_done) -> begin
(let en = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt (let _64_3080 = en
in {FStar_Parser_DesugarEnv.curmodule = Some (m.FStar_Absyn_Syntax.name); FStar_Parser_DesugarEnv.modules = _64_3080.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _64_3080.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _64_3080.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _64_3080.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _64_3080.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _64_3080.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = _64_3080.FStar_Parser_DesugarEnv.phase; FStar_Parser_DesugarEnv.sigmap = _64_3080.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _64_3080.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _64_3080.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _64_3080.FStar_Parser_DesugarEnv.admitted_iface}) m.FStar_Absyn_Syntax.exports)
in (let env = (FStar_Parser_DesugarEnv.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface m.FStar_Absyn_Syntax.name env)
end else begin
env
end))
end)))




