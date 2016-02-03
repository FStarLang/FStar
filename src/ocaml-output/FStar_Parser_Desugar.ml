
open Prims
let as_imp = (fun _59_1 -> (match (_59_1) with
| (FStar_Parser_AST.Hash) | (FStar_Parser_AST.FsTypApp) -> begin
Some (FStar_Absyn_Syntax.Implicit)
end
| _59_35 -> begin
None
end))

let arg_withimp_e = (fun imp t -> (t, (as_imp imp)))

let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
(t, Some (FStar_Absyn_Syntax.Implicit))
end
| _59_42 -> begin
(t, None)
end))

let contains_binder = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_59_46) -> begin
true
end
| _59_49 -> begin
false
end)))))

let rec unparen = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _59_54 -> begin
t
end))

let rec unlabel = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unlabel t)
end
| FStar_Parser_AST.Labeled (t, _59_60, _59_62) -> begin
(unlabel t)
end
| _59_66 -> begin
t
end))

let kind_star = (fun r -> (let _150_17 = (let _150_16 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_150_16))
in (FStar_Parser_AST.mk_term _150_17 r FStar_Parser_AST.Kind)))

let compile_op = (fun arity s -> (let name_of_char = (fun _59_2 -> (match (_59_2) with
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
| _59_89 -> begin
"UNKNOWN"
end))
in (let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _150_28 = (let _150_26 = (FStar_Util.char_at s i)
in (name_of_char _150_26))
in (let _150_27 = (aux (i + 1))
in (_150_28)::_150_27))
end)
in (let _150_30 = (let _150_29 = (aux 0)
in (FStar_String.concat "_" _150_29))
in (Prims.strcat "op_" _150_30)))))

let compile_op_lid = (fun n s r -> (let _150_40 = (let _150_39 = (let _150_38 = (let _150_37 = (compile_op n s)
in (_150_37, r))
in (FStar_Absyn_Syntax.mk_ident _150_38))
in (_150_39)::[])
in (FStar_All.pipe_right _150_40 FStar_Absyn_Syntax.lid_of_ids)))

let op_as_vlid = (fun env arity rng s -> (let r = (fun l -> (let _150_51 = (FStar_Ident.set_lid_range l rng)
in Some (_150_51)))
in (let fallback = (fun _59_103 -> (match (()) with
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
| _59_125 -> begin
None
end)
end))
in (match ((let _150_54 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_lid env _150_54))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _59_136); FStar_Absyn_Syntax.tk = _59_133; FStar_Absyn_Syntax.pos = _59_131; FStar_Absyn_Syntax.fvs = _59_129; FStar_Absyn_Syntax.uvs = _59_127}) -> begin
Some (fv.FStar_Absyn_Syntax.v)
end
| _59_142 -> begin
(fallback ())
end))))

let op_as_tylid = (fun env arity rng s -> (let r = (fun l -> (let _150_65 = (FStar_Ident.set_lid_range l rng)
in Some (_150_65)))
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
(match ((let _150_66 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_typ_name env _150_66))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ftv); FStar_Absyn_Syntax.tk = _59_165; FStar_Absyn_Syntax.pos = _59_163; FStar_Absyn_Syntax.fvs = _59_161; FStar_Absyn_Syntax.uvs = _59_159}) -> begin
Some (ftv.FStar_Absyn_Syntax.v)
end
| _59_171 -> begin
None
end)
end)))

let rec is_type = (fun env t -> if (t.FStar_Parser_AST.level = FStar_Parser_AST.Type) then begin
true
end else begin
(match ((let _150_73 = (unparen t)
in _150_73.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
true
end
| FStar_Parser_AST.Labeled (_59_176) -> begin
true
end
| FStar_Parser_AST.Op ("*", hd::_59_180) -> begin
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
| _59_231 -> begin
true
end)
end
| (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.NamedTyp (_)) -> begin
true
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = 0) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (_59_254) -> begin
true
end
| _59_257 -> begin
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
| FStar_Parser_AST.Product (_59_298, t) -> begin
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
| FStar_Parser_AST.PatTvar (id, _59_324) -> begin
(let _59_330 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_59_330) with
| (env, _59_329) -> begin
(aux env pats)
end))
end
| FStar_Parser_AST.PatAscribed (p, tm) -> begin
(let env = if (is_kind env tm) then begin
(match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatVar (id, _)) | (FStar_Parser_AST.PatTvar (id, _)) -> begin
(let _150_78 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (FStar_All.pipe_right _150_78 Prims.fst))
end
| _59_345 -> begin
env
end)
end else begin
env
end
in (aux env pats))
end
| _59_348 -> begin
false
end)
end))
in (aux env pats))
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_59_353); FStar_Parser_AST.prange = _59_351}, _59_357)::[], t) -> begin
(is_type env t)
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_59_369); FStar_Parser_AST.prange = _59_367}, _59_373); FStar_Parser_AST.prange = _59_365}, _59_378)::[], t) -> begin
(is_type env t)
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_59_388); FStar_Parser_AST.prange = _59_386}, _59_392)::[], t) -> begin
(is_type env t)
end
| _59_399 -> begin
false
end)
end)
and is_kind = (fun env t -> if (t.FStar_Parser_AST.level = FStar_Parser_AST.Kind) then begin
true
end else begin
(match ((let _150_81 = (unparen t)
in _150_81.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _59_408; FStar_Ident.ident = _59_406; FStar_Ident.nsstr = _59_404; FStar_Ident.str = "Type"}) -> begin
true
end
| FStar_Parser_AST.Product (_59_412, t) -> begin
(is_kind env t)
end
| FStar_Parser_AST.Paren (t) -> begin
(is_kind env t)
end
| (FStar_Parser_AST.Construct (l, _)) | (FStar_Parser_AST.Name (l)) -> begin
(FStar_Parser_DesugarEnv.is_kind_abbrev env l)
end
| _59_425 -> begin
false
end)
end)

let rec is_type_binder = (fun env b -> if (b.FStar_Parser_AST.blevel = FStar_Parser_AST.Formula) then begin
(match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_59_429) -> begin
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
| FStar_Parser_AST.Variable (_59_444) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected binder without annotation", b.FStar_Parser_AST.brange))))
end
| FStar_Parser_AST.TVariable (_59_447) -> begin
false
end
| FStar_Parser_AST.TAnnotated (_59_450) -> begin
true
end
| (FStar_Parser_AST.Annotated (_, t)) | (FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end)

let sort_ftv = (fun ftv -> (let _150_92 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _150_92)))

let rec free_type_vars_b = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_59_466) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _59_473 = (FStar_Parser_DesugarEnv.push_local_tbinding env x)
in (match (_59_473) with
| (env, _59_472) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_59_475, term) -> begin
(let _150_99 = (free_type_vars env term)
in (env, _150_99))
end
| FStar_Parser_AST.TAnnotated (id, _59_481) -> begin
(let _59_487 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_59_487) with
| (env, _59_486) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _150_100 = (free_type_vars env t)
in (env, _150_100))
end))
and free_type_vars = (fun env t -> (match ((let _150_103 = (unparen t)
in _150_103.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env a)) with
| None -> begin
(a)::[]
end
| _59_496 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.Labeled (t, _, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_59_532, ts) -> begin
(FStar_List.collect (fun _59_539 -> (match (_59_539) with
| (t, _59_538) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_59_541, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _59_548) -> begin
(let _150_106 = (free_type_vars env t1)
in (let _150_105 = (free_type_vars env t2)
in (FStar_List.append _150_106 _150_105)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(let _59_557 = (free_type_vars_b env b)
in (match (_59_557) with
| (env, f) -> begin
(let _150_107 = (free_type_vars env t)
in (FStar_List.append f _150_107))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(let _59_573 = (FStar_List.fold_left (fun _59_566 binder -> (match (_59_566) with
| (env, free) -> begin
(let _59_570 = (free_type_vars_b env binder)
in (match (_59_570) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_59_573) with
| (env, free) -> begin
(let _150_110 = (free_type_vars env body)
in (FStar_List.append free _150_110))
end))
end
| FStar_Parser_AST.Project (t, _59_576) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
(FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.FStar_Parser_AST.range)
end))

let head_and_args = (fun t -> (let rec aux = (fun args t -> (match ((let _150_117 = (unparen t)
in _150_117.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _59_620 -> begin
(t, args)
end))
in (aux [] t)))

let close = (fun env t -> (let ftv = (let _150_122 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _150_122))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _150_126 = (let _150_125 = (let _150_124 = (kind_star x.FStar_Ident.idRange)
in (x, _150_124))
in FStar_Parser_AST.TAnnotated (_150_125))
in (FStar_Parser_AST.mk_binder _150_126 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

let close_fun = (fun env t -> (let ftv = (let _150_131 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _150_131))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _150_135 = (let _150_134 = (let _150_133 = (kind_star x.FStar_Ident.idRange)
in (x, _150_133))
in FStar_Parser_AST.TAnnotated (_150_134))
in (FStar_Parser_AST.mk_binder _150_135 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (let t = (match ((let _150_136 = (unlabel t)
in _150_136.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_59_633) -> begin
t
end
| _59_636 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))

let rec uncurry = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _59_646 -> begin
(bs, t)
end))

let rec is_app_pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _59_650) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_59_656); FStar_Parser_AST.prange = _59_654}, _59_660) -> begin
true
end
| _59_664 -> begin
false
end))

let rec destruct_app_pattern = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(let _59_676 = (destruct_app_pattern env is_top_level p)
in (match (_59_676) with
| (name, args, _59_675) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _59_681); FStar_Parser_AST.prange = _59_678}, args) when is_top_level -> begin
(let _150_150 = (let _150_149 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_150_149))
in (_150_150, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _59_692); FStar_Parser_AST.prange = _59_689}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _59_700 -> begin
(FStar_All.failwith "Not an app pattern")
end))

type bnd =
| TBinder of (FStar_Absyn_Syntax.btvdef * FStar_Absyn_Syntax.knd * FStar_Absyn_Syntax.aqual)
| VBinder of (FStar_Absyn_Syntax.bvvdef * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Absyn_Syntax.typ)

let is_TBinder = (fun _discr_ -> (match (_discr_) with
| TBinder (_) -> begin
true
end
| _ -> begin
false
end))

let is_VBinder = (fun _discr_ -> (match (_discr_) with
| VBinder (_) -> begin
true
end
| _ -> begin
false
end))

let is_LetBinder = (fun _discr_ -> (match (_discr_) with
| LetBinder (_) -> begin
true
end
| _ -> begin
false
end))

let ___TBinder____0 = (fun projectee -> (match (projectee) with
| TBinder (_59_703) -> begin
_59_703
end))

let ___VBinder____0 = (fun projectee -> (match (projectee) with
| VBinder (_59_706) -> begin
_59_706
end))

let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_59_709) -> begin
_59_709
end))

let binder_of_bnd = (fun _59_3 -> (match (_59_3) with
| TBinder (a, k, aq) -> begin
(FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), aq)
end
| VBinder (x, t, aq) -> begin
(FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), aq)
end
| _59_722 -> begin
(FStar_All.failwith "Impossible")
end))

let trans_aqual = (fun _59_4 -> (match (_59_4) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Absyn_Syntax.Implicit)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Absyn_Syntax.Equality)
end
| _59_729 -> begin
None
end))

let as_binder = (fun env imp _59_5 -> (match (_59_5) with
| FStar_Util.Inl (None, k) -> begin
((FStar_Absyn_Syntax.null_t_binder k), env)
end
| FStar_Util.Inr (None, t) -> begin
((FStar_Absyn_Syntax.null_v_binder t), env)
end
| FStar_Util.Inl (Some (a), k) -> begin
(let _59_748 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_59_748) with
| (env, a) -> begin
((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), (trans_aqual imp)), env)
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(let _59_756 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_59_756) with
| (env, x) -> begin
((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), (trans_aqual imp)), env)
end))
end))

type env_t =
FStar_Parser_DesugarEnv.env

type lenv_t =
(FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list

let label_conjuncts = (fun tag polarity label_opt f -> (let label = (fun f -> (let msg = (match (label_opt) with
| Some (l) -> begin
l
end
| _59_766 -> begin
(let _150_213 = (FStar_Range.string_of_range f.FStar_Parser_AST.range)
in (FStar_Util.format2 "%s at %s" tag _150_213))
end)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled ((f, msg, polarity))) f.FStar_Parser_AST.range f.FStar_Parser_AST.level)))
in (let rec aux = (fun f -> (match (f.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (g) -> begin
(let _150_217 = (let _150_216 = (aux g)
in FStar_Parser_AST.Paren (_150_216))
in (FStar_Parser_AST.mk_term _150_217 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("/\\", f1::f2::[]) -> begin
(let _150_223 = (let _150_222 = (let _150_221 = (let _150_220 = (aux f1)
in (let _150_219 = (let _150_218 = (aux f2)
in (_150_218)::[])
in (_150_220)::_150_219))
in ("/\\", _150_221))
in FStar_Parser_AST.Op (_150_222))
in (FStar_Parser_AST.mk_term _150_223 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _150_227 = (let _150_226 = (let _150_225 = (aux f2)
in (let _150_224 = (aux f3)
in (f1, _150_225, _150_224)))
in FStar_Parser_AST.If (_150_226))
in (FStar_Parser_AST.mk_term _150_227 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Abs (binders, g) -> begin
(let _150_230 = (let _150_229 = (let _150_228 = (aux g)
in (binders, _150_228))
in FStar_Parser_AST.Abs (_150_229))
in (FStar_Parser_AST.mk_term _150_230 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| _59_788 -> begin
(label f)
end))
in (aux f))))

let mk_lb = (fun _59_792 -> (match (_59_792) with
| (n, t, e) -> begin
{FStar_Absyn_Syntax.lbname = n; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = e}
end))

let rec desugar_data_pat = (fun env p -> (let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _59_6 -> (match (_59_6) with
| FStar_Util.Inr (y) -> begin
(y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText)
end
| _59_803 -> begin
false
end))))) with
| Some (FStar_Util.Inr (y)) -> begin
(l, e, y)
end
| _59_808 -> begin
(let _59_811 = (FStar_Parser_DesugarEnv.push_local_vbinding e x)
in (match (_59_811) with
| (e, x) -> begin
((FStar_Util.Inr (x))::l, e, x)
end))
end))
in (let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _59_7 -> (match (_59_7) with
| FStar_Util.Inl (b) -> begin
(b.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText)
end
| _59_820 -> begin
false
end))))) with
| Some (FStar_Util.Inl (b)) -> begin
(l, e, b)
end
| _59_825 -> begin
(let _59_828 = (FStar_Parser_DesugarEnv.push_local_tbinding e a)
in (match (_59_828) with
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
(let _59_850 = (aux loc env p)
in (match (_59_850) with
| (loc, env, var, p, _59_849) -> begin
(let _59_867 = (FStar_List.fold_left (fun _59_854 p -> (match (_59_854) with
| (loc, env, ps) -> begin
(let _59_863 = (aux loc env p)
in (match (_59_863) with
| (loc, env, _59_859, p, _59_862) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_59_867) with
| (loc, env, ps) -> begin
(let pat = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (let _59_869 = (let _150_302 = (FStar_Absyn_Syntax.pat_vars pat)
in (Prims.ignore _150_302))
in (loc, env, var, pat, false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(let p = if (is_kind env t) then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTvar (_59_876) -> begin
p
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(let _59_882 = p
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar ((x, imp)); FStar_Parser_AST.prange = _59_882.FStar_Parser_AST.prange})
end
| _59_885 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end)
end else begin
p
end
in (let _59_892 = (aux loc env p)
in (match (_59_892) with
| (loc, env', binder, p, imp) -> begin
(let binder = (match (binder) with
| LetBinder (_59_894) -> begin
(FStar_All.failwith "impossible")
end
| TBinder (x, _59_898, aq) -> begin
(let _150_304 = (let _150_303 = (desugar_kind env t)
in (x, _150_303, aq))
in TBinder (_150_304))
end
| VBinder (x, _59_904, aq) -> begin
(let t = (close_fun env t)
in (let _150_306 = (let _150_305 = (desugar_typ env t)
in (x, _150_305, aq))
in VBinder (_150_306)))
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
in (let _150_307 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_twild ((FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((a, FStar_Absyn_Syntax.kun, aq)), _150_307, imp)))
end else begin
(let _59_919 = (resolvea loc env a)
in (match (_59_919) with
| (loc, env, abvd) -> begin
(let _150_308 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_tvar ((FStar_Absyn_Util.bvd_to_bvar_s abvd FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((abvd, FStar_Absyn_Syntax.kun, aq)), _150_308, imp))
end))
end)
end
| FStar_Parser_AST.PatWild -> begin
(let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let y = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _150_309 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_wild ((FStar_Absyn_Util.bvd_to_bvar_s y FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _150_309, false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _150_310 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_constant (c)))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _150_310, false)))
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(let aq = if imp then begin
Some (FStar_Absyn_Syntax.Implicit)
end else begin
None
end
in (let _59_934 = (resolvex loc env x)
in (match (_59_934) with
| (loc, env, xbvd) -> begin
(let _150_311 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_var ((FStar_Absyn_Util.bvd_to_bvar_s xbvd FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((xbvd, FStar_Absyn_Syntax.tun, aq)), _150_311, imp))
end)))
end
| FStar_Parser_AST.PatName (l) -> begin
(let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _150_312 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), []))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _150_312, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _59_940}, args) -> begin
(let _59_962 = (FStar_List.fold_right (fun arg _59_951 -> (match (_59_951) with
| (loc, env, args) -> begin
(let _59_958 = (aux loc env arg)
in (match (_59_958) with
| (loc, env, _59_955, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_59_962) with
| (loc, env, args) -> begin
(let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _150_315 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _150_315, false))))
end))
end
| FStar_Parser_AST.PatApp (_59_966) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _59_986 = (FStar_List.fold_right (fun pat _59_974 -> (match (_59_974) with
| (loc, env, pats) -> begin
(let _59_982 = (aux loc env pat)
in (match (_59_982) with
| (loc, env, _59_978, pat, _59_981) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_59_986) with
| (loc, env, pats) -> begin
(let pat = (let _150_322 = (let _150_321 = (let _150_320 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _150_320))
in (FStar_All.pipe_left _150_321 (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv FStar_Absyn_Const.nil_lid), Some (FStar_Absyn_Syntax.Data_ctor), [])))))
in (FStar_List.fold_right (fun hd tl -> (let r = (FStar_Range.union_ranges hd.FStar_Absyn_Syntax.p tl.FStar_Absyn_Syntax.p)
in (FStar_All.pipe_left (pos_r r) (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv FStar_Absyn_Const.cons_lid), Some (FStar_Absyn_Syntax.Data_ctor), ((hd, false))::((tl, false))::[])))))) pats _150_322))
in (let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(let _59_1012 = (FStar_List.fold_left (fun _59_999 p -> (match (_59_999) with
| (loc, env, pats) -> begin
(let _59_1008 = (aux loc env p)
in (match (_59_1008) with
| (loc, env, _59_1004, pat, _59_1007) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_59_1012) with
| (loc, env, args) -> begin
(let args = (FStar_List.rev args)
in (let l = if dep then begin
(FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end else begin
(FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
in (let constr = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (let l = (match (constr.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (v, _59_1018) -> begin
v
end
| _59_1022 -> begin
(FStar_All.failwith "impossible")
end)
in (let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _150_325 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _150_325, false)))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(let _59_1032 = (FStar_List.hd fields)
in (match (_59_1032) with
| (f, _59_1031) -> begin
(let _59_1036 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_59_1036) with
| (record, _59_1035) -> begin
(let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _59_1039 -> (match (_59_1039) with
| (f, p) -> begin
(let _150_327 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in (_150_327, p))
end))))
in (let args = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _59_1044 -> (match (_59_1044) with
| (f, _59_1043) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _59_1048 -> (match (_59_1048) with
| (g, _59_1047) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_59_1051, p) -> begin
p
end)
end))))
in (let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_DesugarEnv.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (let _59_1063 = (aux loc env app)
in (match (_59_1063) with
| (env, e, b, p, _59_1062) -> begin
(let p = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, _59_1066, args) -> begin
(let _150_335 = (let _150_334 = (let _150_333 = (let _150_332 = (let _150_331 = (let _150_330 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_DesugarEnv.typename, _150_330))
in FStar_Absyn_Syntax.Record_ctor (_150_331))
in Some (_150_332))
in (fv, _150_333, args))
in FStar_Absyn_Syntax.Pat_cons (_150_334))
in (FStar_All.pipe_left pos _150_335))
end
| _59_1071 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (let _59_1080 = (aux [] env p)
in (match (_59_1080) with
| (_59_1074, env, b, p, _59_1079) -> begin
(env, b, p)
end))))))
and desugar_binding_pat_maybe_top = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _59_1086) -> begin
(let _150_341 = (let _150_340 = (let _150_339 = (FStar_Parser_DesugarEnv.qualify env x)
in (_150_339, FStar_Absyn_Syntax.tun))
in LetBinder (_150_340))
in (env, _150_341, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _59_1093); FStar_Parser_AST.prange = _59_1090}, t) -> begin
(let _150_345 = (let _150_344 = (let _150_343 = (FStar_Parser_DesugarEnv.qualify env x)
in (let _150_342 = (desugar_typ env t)
in (_150_343, _150_342)))
in LetBinder (_150_344))
in (env, _150_345, None))
end
| _59_1101 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(let _59_1105 = (desugar_data_pat env p)
in (match (_59_1105) with
| (env, binder, p) -> begin
(let p = (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) -> begin
None
end
| _59_1116 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top = (fun _59_1120 env pat -> (let _59_1128 = (desugar_data_pat env pat)
in (match (_59_1128) with
| (env, _59_1126, pat) -> begin
(env, pat)
end)))
and desugar_match_pat = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_typ_or_exp = (fun env t -> if (is_type env t) then begin
(let _150_355 = (desugar_typ env t)
in FStar_Util.Inl (_150_355))
end else begin
(let _150_356 = (desugar_exp env t)
in FStar_Util.Inr (_150_356))
end)
and desugar_exp = (fun env e -> (desugar_exp_maybe_top false env e))
and desugar_exp_maybe_top = (fun top_level env top -> (let pos = (fun e -> (e None top.FStar_Parser_AST.range))
in (let setpos = (fun e -> (let _59_1142 = e
in {FStar_Absyn_Syntax.n = _59_1142.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _59_1142.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _59_1142.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _59_1142.FStar_Absyn_Syntax.uvs}))
in (match ((let _150_376 = (unparen top)
in _150_376.FStar_Parser_AST.tm)) with
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
in (let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _150_380 = (desugar_typ_or_exp env t)
in (_150_380, None)))))
in (let _150_381 = (FStar_Absyn_Util.mk_exp_app op args)
in (FStar_All.pipe_left setpos _150_381))))
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
(let _150_382 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _150_382))
end
end
| FStar_Parser_AST.Construct (l, args) -> begin
(let dt = (let _150_387 = (let _150_386 = (let _150_385 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (_150_385, Some (FStar_Absyn_Syntax.Data_ctor)))
in (FStar_Absyn_Syntax.mk_Exp_fvar _150_386))
in (FStar_All.pipe_left pos _150_387))
in (match (args) with
| [] -> begin
dt
end
| _59_1169 -> begin
(let args = (FStar_List.map (fun _59_1172 -> (match (_59_1172) with
| (t, imp) -> begin
(let te = (desugar_typ_or_exp env t)
in (arg_withimp_e imp te))
end)) args)
in (let _150_392 = (let _150_391 = (let _150_390 = (let _150_389 = (FStar_Absyn_Util.mk_exp_app dt args)
in (_150_389, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_150_390))
in (FStar_Absyn_Syntax.mk_Exp_meta _150_391))
in (FStar_All.pipe_left setpos _150_392)))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(let _59_1209 = (FStar_List.fold_left (fun _59_1181 pat -> (match (_59_1181) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar (a, imp); FStar_Parser_AST.prange = _59_1184}, t) -> begin
(let ftvs = (let _150_395 = (free_type_vars env t)
in (FStar_List.append _150_395 ftvs))
in (let _150_397 = (let _150_396 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _150_396))
in (_150_397, ftvs)))
end
| FStar_Parser_AST.PatTvar (a, _59_1196) -> begin
(let _150_399 = (let _150_398 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _150_398))
in (_150_399, ftvs))
end
| FStar_Parser_AST.PatAscribed (_59_1200, t) -> begin
(let _150_401 = (let _150_400 = (free_type_vars env t)
in (FStar_List.append _150_400 ftvs))
in (env, _150_401))
end
| _59_1205 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_59_1209) with
| (_59_1207, ftv) -> begin
(let ftv = (sort_ftv ftv)
in (let binders = (let _150_403 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, true))) top.FStar_Parser_AST.range))))
in (FStar_List.append _150_403 binders))
in (let rec aux = (fun env bs sc_pat_opt _59_8 -> (match (_59_8) with
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
(let _59_1232 = (desugar_binding_pat env p)
in (match (_59_1232) with
| (env, b, pat) -> begin
(let _59_1292 = (match (b) with
| LetBinder (_59_1234) -> begin
(FStar_All.failwith "Impossible")
end
| TBinder (a, k, aq) -> begin
(let _150_412 = (binder_of_bnd b)
in (_150_412, sc_pat_opt))
end
| VBinder (x, t, aq) -> begin
(let b = (FStar_Absyn_Util.bvd_to_bvar_s x t)
in (let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _59_1249) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _150_414 = (let _150_413 = (FStar_Absyn_Util.bvar_to_exp b)
in (_150_413, p))
in Some (_150_414))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Absyn_Syntax.n, p'.FStar_Absyn_Syntax.v)) with
| (FStar_Absyn_Syntax.Exp_bvar (_59_1263), _59_1266) -> begin
(let tup = (FStar_Absyn_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (let sc = (let _150_420 = (let _150_419 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _150_418 = (let _150_417 = (let _150_416 = (let _150_415 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _150_415))
in (_150_416)::[])
in ((FStar_Absyn_Syntax.varg sc))::_150_417)
in (_150_419, _150_418)))
in (FStar_Absyn_Syntax.mk_Exp_app _150_420 None top.FStar_Parser_AST.range))
in (let p = (let _150_421 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv tup), Some (FStar_Absyn_Syntax.Data_ctor), ((p', false))::((p, false))::[]))) None _150_421))
in Some ((sc, p)))))
end
| (FStar_Absyn_Syntax.Exp_app (_59_1272, args), FStar_Absyn_Syntax.Pat_cons (_59_1277, _59_1279, pats)) -> begin
(let tup = (FStar_Absyn_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (let sc = (let _150_427 = (let _150_426 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _150_425 = (let _150_424 = (let _150_423 = (let _150_422 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _150_422))
in (_150_423)::[])
in (FStar_List.append args _150_424))
in (_150_426, _150_425)))
in (FStar_Absyn_Syntax.mk_Exp_app _150_427 None top.FStar_Parser_AST.range))
in (let p = (let _150_428 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv tup), Some (FStar_Absyn_Syntax.Data_ctor), (FStar_List.append pats (((p, false))::[]))))) None _150_428))
in Some ((sc, p)))))
end
| _59_1288 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((FStar_Util.Inr (b), aq), sc_pat_opt)))
end)
in (match (_59_1292) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _59_1296; FStar_Parser_AST.level = _59_1294}, arg, _59_1302) when ((FStar_Ident.lid_equals a FStar_Absyn_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Absyn_Const.assume_lid)) -> begin
(let phi = (desugar_formula env arg)
in (let _150_438 = (let _150_437 = (let _150_436 = (FStar_Absyn_Util.fvar None a (FStar_Ident.range_of_lid a))
in (let _150_435 = (let _150_434 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ phi)
in (let _150_433 = (let _150_432 = (let _150_431 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None top.FStar_Parser_AST.range)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _150_431))
in (_150_432)::[])
in (_150_434)::_150_433))
in (_150_436, _150_435)))
in (FStar_Absyn_Syntax.mk_Exp_app _150_437))
in (FStar_All.pipe_left pos _150_438)))
end
| FStar_Parser_AST.App (_59_1307) -> begin
(let rec aux = (fun args e -> (match ((let _150_443 = (unparen e)
in _150_443.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(let arg = (let _150_444 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _150_444))
in (aux ((arg)::args) e))
end
| _59_1319 -> begin
(let head = (desugar_exp env e)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_app (head, args))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _150_450 = (let _150_449 = (let _150_448 = (let _150_447 = (desugar_exp env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_150_447, FStar_Absyn_Syntax.Sequence))
in FStar_Absyn_Syntax.Meta_desugared (_150_448))
in (FStar_Absyn_Syntax.mk_Exp_meta _150_449))
in (FStar_All.pipe_left setpos _150_450))
end
| FStar_Parser_AST.Let (is_rec, (pat, _snd)::_tl, body) -> begin
(let ds_let_rec = (fun _59_1335 -> (match (()) with
| () -> begin
(let bindings = ((pat, _snd))::_tl
in (let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _59_1339 -> (match (_59_1339) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _150_454 = (destruct_app_pattern env top_level p)
in (_150_454, def))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _150_455 = (destruct_app_pattern env top_level p)
in (_150_455, def))
end
| _59_1345 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _59_1350); FStar_Parser_AST.prange = _59_1347}, t) -> begin
if top_level then begin
(let _150_458 = (let _150_457 = (let _150_456 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_150_456))
in (_150_457, [], Some (t)))
in (_150_458, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _59_1359) -> begin
if top_level then begin
(let _150_461 = (let _150_460 = (let _150_459 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_150_459))
in (_150_460, [], None))
in (_150_461, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _59_1363 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (let _59_1389 = (FStar_List.fold_left (fun _59_1367 _59_1376 -> (match ((_59_1367, _59_1376)) with
| ((env, fnames), ((f, _59_1370, _59_1372), _59_1375)) -> begin
(let _59_1386 = (match (f) with
| FStar_Util.Inl (x) -> begin
(let _59_1381 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_59_1381) with
| (env, xx) -> begin
(env, FStar_Util.Inl (xx))
end))
end
| FStar_Util.Inr (l) -> begin
(let _150_464 = (FStar_Parser_DesugarEnv.push_rec_binding env (FStar_Parser_DesugarEnv.Binding_let (l)))
in (_150_464, FStar_Util.Inr (l)))
end)
in (match (_59_1386) with
| (env, lbname) -> begin
(env, (lbname)::fnames)
end))
end)) (env, []) funs)
in (match (_59_1389) with
| (env', fnames) -> begin
(let fnames = (FStar_List.rev fnames)
in (let desugar_one_def = (fun env lbname _59_1400 -> (match (_59_1400) with
| ((_59_1395, args, result_t), def) -> begin
(let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _150_471 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _150_471 FStar_Parser_AST.Expr))
end)
in (let def = (match (args) with
| [] -> begin
def
end
| _59_1407 -> begin
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
in (let _59_1420 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_59_1420) with
| (env, binder, pat) -> begin
(match (binder) with
| TBinder (_59_1422) -> begin
(FStar_All.failwith "Unexpected type binder in let")
end
| LetBinder (l, t) -> begin
(let body = (desugar_exp env t2)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = t1})::[]), body))))
end
| VBinder (x, t, _59_1432) -> begin
(let body = (desugar_exp env t2)
in (let body = (match (pat) with
| (None) | (Some ({FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_wild (_); FStar_Absyn_Syntax.sort = _; FStar_Absyn_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _150_483 = (let _150_482 = (FStar_Absyn_Util.bvd_to_exp x t)
in (_150_482, ((pat, None, body))::[]))
in (FStar_Absyn_Syntax.mk_Exp_match _150_483 None body.FStar_Absyn_Syntax.pos))
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
(let _150_496 = (let _150_495 = (let _150_494 = (desugar_exp env t1)
in (let _150_493 = (let _150_492 = (let _150_488 = (desugar_exp env t2)
in ((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) None t2.FStar_Parser_AST.range), None, _150_488))
in (let _150_491 = (let _150_490 = (let _150_489 = (desugar_exp env t3)
in ((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) None t3.FStar_Parser_AST.range), None, _150_489))
in (_150_490)::[])
in (_150_492)::_150_491))
in (_150_494, _150_493)))
in (FStar_Absyn_Syntax.mk_Exp_match _150_495))
in (FStar_All.pipe_left pos _150_496))
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
(let desugar_branch = (fun _59_1471 -> (match (_59_1471) with
| (pat, wopt, b) -> begin
(let _59_1474 = (desugar_match_pat env pat)
in (match (_59_1474) with
| (env, pat) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _150_499 = (desugar_exp env e)
in Some (_150_499))
end)
in (let b = (desugar_exp env b)
in (pat, wopt, b)))
end))
end))
in (let _150_505 = (let _150_504 = (let _150_503 = (desugar_exp env e)
in (let _150_502 = (FStar_List.map desugar_branch branches)
in (_150_503, _150_502)))
in (FStar_Absyn_Syntax.mk_Exp_match _150_504))
in (FStar_All.pipe_left pos _150_505)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _150_511 = (let _150_510 = (let _150_509 = (desugar_exp env e)
in (let _150_508 = (desugar_typ env t)
in (_150_509, _150_508, None)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _150_510))
in (FStar_All.pipe_left pos _150_511))
end
| FStar_Parser_AST.Record (_59_1485, []) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(let _59_1496 = (FStar_List.hd fields)
in (match (_59_1496) with
| (f, _59_1495) -> begin
(let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (let _59_1502 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_59_1502) with
| (record, _59_1501) -> begin
(let get_field = (fun xopt f -> (let fn = f.FStar_Ident.ident
in (let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _59_1510 -> (match (_59_1510) with
| (g, _59_1509) -> begin
(let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_59_1514, e) -> begin
(let _150_519 = (qfn fn)
in (_150_519, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _150_522 = (let _150_521 = (let _150_520 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in (_150_520, top.FStar_Parser_AST.range))
in FStar_Absyn_Syntax.Error (_150_521))
in (Prims.raise _150_522))
end
| Some (x) -> begin
(let _150_523 = (qfn fn)
in (_150_523, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (let recterm = (match (eopt) with
| None -> begin
(let _150_528 = (let _150_527 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _59_1526 -> (match (_59_1526) with
| (f, _59_1525) -> begin
(let _150_526 = (let _150_525 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _150_525))
in (_150_526, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_DesugarEnv.constrname, _150_527))
in FStar_Parser_AST.Construct (_150_528))
end
| Some (e) -> begin
(let x = (FStar_Absyn_Util.genident (Some (e.FStar_Parser_AST.range)))
in (let xterm = (let _150_530 = (let _150_529 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_150_529))
in (FStar_Parser_AST.mk_term _150_530 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (let record = (let _150_533 = (let _150_532 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _59_1534 -> (match (_59_1534) with
| (f, _59_1533) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _150_532))
in FStar_Parser_AST.Record (_150_533))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, false))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (let e = (desugar_exp env recterm)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _59_1557); FStar_Absyn_Syntax.tk = _59_1554; FStar_Absyn_Syntax.pos = _59_1552; FStar_Absyn_Syntax.fvs = _59_1550; FStar_Absyn_Syntax.uvs = _59_1548}, args); FStar_Absyn_Syntax.tk = _59_1546; FStar_Absyn_Syntax.pos = _59_1544; FStar_Absyn_Syntax.fvs = _59_1542; FStar_Absyn_Syntax.uvs = _59_1540}, FStar_Absyn_Syntax.Data_app)) -> begin
(let e = (let _150_543 = (let _150_542 = (let _150_541 = (let _150_540 = (let _150_539 = (let _150_538 = (let _150_537 = (let _150_536 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_DesugarEnv.typename, _150_536))
in FStar_Absyn_Syntax.Record_ctor (_150_537))
in Some (_150_538))
in (fv, _150_539))
in (FStar_Absyn_Syntax.mk_Exp_fvar _150_540 None e.FStar_Absyn_Syntax.pos))
in (_150_541, args))
in (FStar_Absyn_Syntax.mk_Exp_app _150_542))
in (FStar_All.pipe_left pos _150_543))
in (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, FStar_Absyn_Syntax.Data_app)))))
end
| _59_1571 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(let _59_1578 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_projector_by_field_name env) f)
in (match (_59_1578) with
| (fieldname, is_rec) -> begin
(let e = (desugar_exp env e)
in (let fn = (let _59_1583 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_59_1583) with
| (ns, _59_1582) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (let qual = if is_rec then begin
Some (FStar_Absyn_Syntax.Record_projector (fn))
end else begin
None
end
in (let _150_548 = (let _150_547 = (let _150_546 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Record_projector (fn))) fieldname (FStar_Ident.range_of_lid f))
in (_150_546, ((FStar_Absyn_Syntax.varg e))::[]))
in (FStar_Absyn_Syntax.mk_Exp_app _150_547))
in (FStar_All.pipe_left pos _150_548)))))
end))
end
| FStar_Parser_AST.Paren (e) -> begin
(desugar_exp env e)
end
| _59_1589 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_typ = (fun env top -> (let wpos = (fun t -> (t None top.FStar_Parser_AST.range))
in (let setpos = (fun t -> (let _59_1596 = t
in {FStar_Absyn_Syntax.n = _59_1596.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _59_1596.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _59_1596.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _59_1596.FStar_Absyn_Syntax.uvs}))
in (let top = (unparen top)
in (let head_and_args = (fun t -> (let rec aux = (fun args t -> (match ((let _150_571 = (unparen t)
in _150_571.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _59_1614 -> begin
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
(let _150_572 = (desugar_exp env t)
in (FStar_All.pipe_right _150_572 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(let t = (label_conjuncts "post-condition" false lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(let _150_573 = (desugar_exp env t)
in (FStar_All.pipe_right _150_573 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Op ("*", t1::_59_1628::[]) -> begin
if (is_type env t1) then begin
(let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(let rest = (flatten t2)
in (t1)::rest)
end
| _59_1643 -> begin
(t)::[]
end))
in (let targs = (let _150_578 = (flatten top)
in (FStar_All.pipe_right _150_578 (FStar_List.map (fun t -> (let _150_577 = (desugar_typ env t)
in (FStar_Absyn_Syntax.targ _150_577))))))
in (let tup = (let _150_579 = (FStar_Absyn_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _150_579))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))))
end else begin
(let _150_585 = (let _150_584 = (let _150_583 = (let _150_582 = (FStar_Parser_AST.term_to_string t1)
in (FStar_Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _150_582))
in (_150_583, top.FStar_Parser_AST.range))
in FStar_Absyn_Syntax.Error (_150_584))
in (Prims.raise _150_585))
end
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_typ env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("~", ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("==", args))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[]))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_tylid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(let _150_586 = (desugar_exp env top)
in (FStar_All.pipe_right _150_586 FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(let args = (FStar_List.map (fun t -> (let _150_588 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _150_588))) args)
in (let _150_589 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _150_589 args)))
end)
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _150_590 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (FStar_All.pipe_left setpos _150_590))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = 0) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _150_591 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _150_591))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let l = (FStar_Absyn_Util.set_lid_range l top.FStar_Parser_AST.range)
in (let _150_592 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _150_592)))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(let t = (let _150_593 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _150_593))
in (let args = (FStar_List.map (fun _59_1679 -> (match (_59_1679) with
| (t, imp) -> begin
(let _150_595 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _150_595))
end)) args)
in (FStar_Absyn_Util.mk_typ_app t args)))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(let rec aux = (fun env bs _59_9 -> (match (_59_9) with
| [] -> begin
(let body = (desugar_typ env body)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_lam ((FStar_List.rev bs), body))))
end
| hd::tl -> begin
(let _59_1697 = (desugar_binding_pat env hd)
in (match (_59_1697) with
| (env, bnd, pat) -> begin
(match (pat) with
| Some (q) -> begin
(let _150_607 = (let _150_606 = (let _150_605 = (let _150_604 = (FStar_Absyn_Print.pat_to_string q)
in (FStar_Util.format1 "Pattern matching at the type level is not supported; got %s\n" _150_604))
in (_150_605, hd.FStar_Parser_AST.prange))
in FStar_Absyn_Syntax.Error (_150_606))
in (Prims.raise _150_607))
end
| None -> begin
(let b = (binder_of_bnd bnd)
in (aux env ((b)::bs) tl))
end)
end))
end))
in (aux env [] binders))
end
| FStar_Parser_AST.App (_59_1703) -> begin
(let rec aux = (fun args e -> (match ((let _150_612 = (unparen e)
in _150_612.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, arg, imp) -> begin
(let arg = (let _150_613 = (desugar_typ_or_exp env arg)
in (FStar_All.pipe_left (arg_withimp_t imp) _150_613))
in (aux ((arg)::args) e))
end
| _59_1715 -> begin
(let head = (desugar_typ env e)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (head, args))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Product ([], t) -> begin
(FStar_All.failwith "Impossible: product with no binders")
end
| FStar_Parser_AST.Product (binders, t) -> begin
(let _59_1727 = (uncurry binders t)
in (match (_59_1727) with
| (bs, t) -> begin
(let rec aux = (fun env bs _59_10 -> (match (_59_10) with
| [] -> begin
(let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_fun ((FStar_List.rev bs), cod))))
end
| hd::tl -> begin
(let mlenv = (FStar_Parser_DesugarEnv.default_ml env)
in (let bb = (desugar_binder mlenv hd)
in (let _59_1741 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_59_1741) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_exp_binder env b)) with
| (None, _59_1748) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(let _59_1762 = (match ((as_binder env None (FStar_Util.Inr (b)))) with
| ((FStar_Util.Inr (x), _59_1754), env) -> begin
(x, env)
end
| _59_1759 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_59_1762) with
| (b, env) -> begin
(let f = if (is_type env f) then begin
(desugar_formula env f)
end else begin
(let _150_624 = (desugar_exp env f)
in (FStar_All.pipe_right _150_624 FStar_Absyn_Util.b2t))
end
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_refine (b, f))))
end))
end)
end
| (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| FStar_Parser_AST.Ascribed (t, k) -> begin
(let _150_632 = (let _150_631 = (let _150_630 = (desugar_typ env t)
in (let _150_629 = (desugar_kind env k)
in (_150_630, _150_629)))
in (FStar_Absyn_Syntax.mk_Typ_ascribed' _150_631))
in (FStar_All.pipe_left wpos _150_632))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(let _59_1796 = (FStar_List.fold_left (fun _59_1781 b -> (match (_59_1781) with
| (env, tparams, typs) -> begin
(let _59_1785 = (desugar_exp_binder env b)
in (match (_59_1785) with
| (xopt, t) -> begin
(let _59_1791 = (match (xopt) with
| None -> begin
(let _150_635 = (FStar_Absyn_Util.new_bvd (Some (top.FStar_Parser_AST.range)))
in (env, _150_635))
end
| Some (x) -> begin
(FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_59_1791) with
| (env, x) -> begin
(let _150_639 = (let _150_638 = (let _150_637 = (let _150_636 = (FStar_Absyn_Util.close_with_lam tparams t)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _150_636))
in (_150_637)::[])
in (FStar_List.append typs _150_638))
in (env, (FStar_List.append tparams (((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), None))::[])), _150_639))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_59_1796) with
| (env, _59_1794, targs) -> begin
(let tup = (let _150_640 = (FStar_Absyn_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _150_640))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))
end))
end
| FStar_Parser_AST.Record (_59_1799) -> begin
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
| _59_1818 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _59_1820 -> begin
(FStar_Parser_AST.error "Expected a type" top top.FStar_Parser_AST.range)
end))))))
and desugar_comp = (fun r default_ok env t -> (let fail = (fun msg -> (Prims.raise (FStar_Absyn_Syntax.Error ((msg, r)))))
in (let pre_process_comp_typ = (fun t -> (let _59_1831 = (head_and_args t)
in (match (_59_1831) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(let unit = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (let nil_pat = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr), FStar_Parser_AST.Nothing)
in (let _59_1857 = (FStar_All.pipe_right args (FStar_List.partition (fun _59_1839 -> (match (_59_1839) with
| (arg, _59_1838) -> begin
(match ((let _150_652 = (unparen arg)
in _150_652.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _59_1843; FStar_Parser_AST.level = _59_1841}, _59_1848, _59_1850) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = "decreases")
end
| _59_1854 -> begin
false
end)
end))))
in (match (_59_1857) with
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
| FStar_Parser_AST.Name (tot) when (((tot.FStar_Ident.ident.FStar_Ident.idText = "Tot") && (not ((FStar_Parser_DesugarEnv.is_effect_name env FStar_Absyn_Const.effect_Tot_lid)))) && (let _150_653 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals _150_653 FStar_Absyn_Const.prims_lid))) -> begin
(let args = (FStar_List.map (fun _59_1872 -> (match (_59_1872) with
| (t, imp) -> begin
(let _150_655 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _150_655))
end)) args)
in (let _150_656 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.effect_Tot_lid FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _150_656 args)))
end
| _59_1875 -> begin
(desugar_typ env t)
end)
end)))
in (let t = (pre_process_comp_typ t)
in (let _59_1879 = (FStar_Absyn_Util.head_and_args t)
in (match (_59_1879) with
| (head, args) -> begin
(match ((let _150_658 = (let _150_657 = (FStar_Absyn_Util.compress_typ head)
in _150_657.FStar_Absyn_Syntax.n)
in (_150_658, args))) with
| (FStar_Absyn_Syntax.Typ_const (eff), (FStar_Util.Inl (result_typ), _59_1886)::rest) -> begin
(let _59_1926 = (FStar_All.pipe_right rest (FStar_List.partition (fun _59_11 -> (match (_59_11) with
| (FStar_Util.Inr (_59_1892), _59_1895) -> begin
false
end
| (FStar_Util.Inl (t), _59_1900) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _59_1909; FStar_Absyn_Syntax.pos = _59_1907; FStar_Absyn_Syntax.fvs = _59_1905; FStar_Absyn_Syntax.uvs = _59_1903}, (FStar_Util.Inr (_59_1914), _59_1917)::[]) -> begin
(FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.decreases_lid)
end
| _59_1923 -> begin
false
end)
end))))
in (match (_59_1926) with
| (dec, rest) -> begin
(let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _59_12 -> (match (_59_12) with
| (FStar_Util.Inl (t), _59_1931) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (_59_1934, (FStar_Util.Inr (arg), _59_1938)::[]) -> begin
FStar_Absyn_Syntax.DECREASES (arg)
end
| _59_1944 -> begin
(FStar_All.failwith "impos")
end)
end
| _59_1946 -> begin
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
(let _150_665 = (let _150_664 = (let _150_663 = (let _150_662 = (let _150_661 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((pat, FStar_Absyn_Syntax.Meta_smt_pat))))
in FStar_Util.Inr (_150_661))
in (_150_662, aq))
in (_150_663)::[])
in (ens)::_150_664)
in (req)::_150_665)
end
| _59_1957 -> begin
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
(let _150_667 = (let _150_666 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _150_666))
in (fail _150_667))
end
end)
end))
end
| _59_1960 -> begin
if default_ok then begin
(env.FStar_Parser_DesugarEnv.default_result_effect t r)
end else begin
(let _150_669 = (let _150_668 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _150_668))
in (fail _150_669))
end
end)
end))))))
and desugar_kind = (fun env k -> (let pos = (fun f -> (f k.FStar_Parser_AST.range))
in (let setpos = (fun kk -> (let _59_1967 = kk
in {FStar_Absyn_Syntax.n = _59_1967.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _59_1967.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = k.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _59_1967.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _59_1967.FStar_Absyn_Syntax.uvs}))
in (let k = (unparen k)
in (match (k.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _59_1976; FStar_Ident.ident = _59_1974; FStar_Ident.nsstr = _59_1972; FStar_Ident.str = "Type"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_type)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _59_1985; FStar_Ident.ident = _59_1983; FStar_Ident.nsstr = _59_1981; FStar_Ident.str = "Effect"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_effect)
end
| FStar_Parser_AST.Name (l) -> begin
(match ((let _150_681 = (FStar_Parser_DesugarEnv.qualify_lid env l)
in (FStar_Parser_DesugarEnv.find_kind_abbrev env _150_681))) with
| Some (l) -> begin
(FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, []), FStar_Absyn_Syntax.mk_Kind_unknown)))
end
| _59_1993 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)
end
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.kun)
end
| FStar_Parser_AST.Product (bs, k) -> begin
(let _59_2001 = (uncurry bs k)
in (match (_59_2001) with
| (bs, k) -> begin
(let rec aux = (fun env bs _59_13 -> (match (_59_13) with
| [] -> begin
(let _150_692 = (let _150_691 = (let _150_690 = (desugar_kind env k)
in ((FStar_List.rev bs), _150_690))
in (FStar_Absyn_Syntax.mk_Kind_arrow _150_691))
in (FStar_All.pipe_left pos _150_692))
end
| hd::tl -> begin
(let _59_2012 = (let _150_694 = (let _150_693 = (FStar_Parser_DesugarEnv.default_ml env)
in (desugar_binder _150_693 hd))
in (FStar_All.pipe_right _150_694 (as_binder env hd.FStar_Parser_AST.aqual)))
in (match (_59_2012) with
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
(let args = (FStar_List.map (fun _59_2022 -> (match (_59_2022) with
| (t, b) -> begin
(let qual = if (b = FStar_Parser_AST.Hash) then begin
Some (FStar_Absyn_Syntax.Implicit)
end else begin
None
end
in (let _150_696 = (desugar_typ_or_exp env t)
in (_150_696, qual)))
end)) args)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), FStar_Absyn_Syntax.mk_Kind_unknown))))
end)
end
| _59_2026 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)))))
and desugar_formula' = (fun env f -> (let connective = (fun s -> (match (s) with
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
| _59_2037 -> begin
None
end))
in (let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (let setpos = (fun t -> (let _59_2042 = t
in {FStar_Absyn_Syntax.n = _59_2042.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _59_2042.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = f.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _59_2042.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _59_2042.FStar_Absyn_Syntax.uvs}))
in (let desugar_quant = (fun q qt b pats body -> (let tk = (desugar_binder env (let _59_2050 = b
in {FStar_Parser_AST.b = _59_2050.FStar_Parser_AST.b; FStar_Parser_AST.brange = _59_2050.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _59_2050.FStar_Parser_AST.aqual}))
in (let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _150_732 = (desugar_typ_or_exp env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _150_732)))))) pats))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(let _59_2065 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_59_2065) with
| (env, a) -> begin
(let pats = (desugar_pats env pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _59_2070 -> begin
(let _150_733 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
in (FStar_All.pipe_left setpos _150_733))
end)
in (let body = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k)))::[], body)))
in (let _150_738 = (let _150_737 = (let _150_736 = (FStar_Ident.set_lid_range qt b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _150_736 FStar_Absyn_Syntax.kun))
in (FStar_Absyn_Util.mk_typ_app _150_737 (((FStar_Absyn_Syntax.targ body))::[])))
in (FStar_All.pipe_left setpos _150_738))))))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(let _59_2080 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_59_2080) with
| (env, x) -> begin
(let pats = (desugar_pats env pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _59_2085 -> begin
(FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
end)
in (let body = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t)))::[], body)))
in (let _150_743 = (let _150_742 = (let _150_741 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _150_741 FStar_Absyn_Syntax.kun))
in (FStar_Absyn_Util.mk_typ_app _150_742 (((FStar_Absyn_Syntax.targ body))::[])))
in (FStar_All.pipe_left setpos _150_743))))))
end))
end
| _59_2089 -> begin
(FStar_All.failwith "impossible")
end))))
in (let push_quant = (fun q binders pats body -> (match (binders) with
| b::b'::_rest -> begin
(let rest = (b')::_rest
in (let body = (let _150_758 = (q (rest, pats, body))
in (let _150_757 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _150_758 _150_757 FStar_Parser_AST.Formula)))
in (let _150_759 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _150_759 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _59_2103 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _150_760 = (unparen f)
in _150_760.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(let f = (desugar_formula env f)
in (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((f, l, FStar_Absyn_Syntax.dummyRange, p)))))
end
| FStar_Parser_AST.Op ("==", hd::_args) -> begin
(let args = (hd)::_args
in (let args = (FStar_List.map (fun t -> (let _150_762 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _150_762))) args)
in (let eq = if (is_type env hd) then begin
(let _150_763 = (FStar_Ident.set_lid_range FStar_Absyn_Const.eqT_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _150_763 FStar_Absyn_Syntax.kun))
end else begin
(let _150_764 = (FStar_Ident.set_lid_range FStar_Absyn_Const.eq2_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _150_764 FStar_Absyn_Syntax.kun))
end
in (FStar_Absyn_Util.mk_typ_app eq args))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match (((connective s), args)) with
| (Some (conn), _59_2129::_59_2127::[]) -> begin
(let _150_769 = (let _150_765 = (FStar_Ident.set_lid_range conn f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _150_765 FStar_Absyn_Syntax.kun))
in (let _150_768 = (FStar_List.map (fun x -> (let _150_767 = (desugar_formula env x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _150_767))) args)
in (FStar_Absyn_Util.mk_typ_app _150_769 _150_768)))
end
| _59_2134 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _150_770 = (desugar_exp env f)
in (FStar_All.pipe_right _150_770 FStar_Absyn_Util.b2t))
end
end)
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _150_775 = (let _150_771 = (FStar_Ident.set_lid_range FStar_Absyn_Const.ite_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _150_771 FStar_Absyn_Syntax.kun))
in (let _150_774 = (FStar_List.map (fun x -> (match ((desugar_typ_or_exp env x)) with
| FStar_Util.Inl (t) -> begin
(FStar_Absyn_Syntax.targ t)
end
| FStar_Util.Inr (v) -> begin
(let _150_773 = (FStar_Absyn_Util.b2t v)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _150_773))
end)) ((f1)::(f2)::(f3)::[]))
in (FStar_Absyn_Util.mk_typ_app _150_775 _150_774)))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall (_1::_2::_3, pats, body) -> begin
(let binders = (_1)::(_2)::_3
in (let _150_777 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _150_777)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(let binders = (_1)::(_2)::_3
in (let _150_779 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _150_779)))
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
| _59_2196 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _150_780 = (desugar_exp env f)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _150_780))
end
end)))))))
and desugar_formula = (fun env t -> (desugar_formula' (let _59_2199 = env
in {FStar_Parser_DesugarEnv.curmodule = _59_2199.FStar_Parser_DesugarEnv.curmodule; FStar_Parser_DesugarEnv.modules = _59_2199.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _59_2199.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _59_2199.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _59_2199.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _59_2199.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _59_2199.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = FStar_Parser_AST.Formula; FStar_Parser_DesugarEnv.sigmap = _59_2199.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _59_2199.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _59_2199.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _59_2199.FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder = (fun env b -> if (is_type_binder env b) then begin
(let _150_785 = (desugar_type_binder env b)
in FStar_Util.Inl (_150_785))
end else begin
(let _150_786 = (desugar_exp_binder env b)
in FStar_Util.Inr (_150_786))
end)
and typars_of_binders = (fun env bs -> (let _59_2232 = (FStar_List.fold_left (fun _59_2207 b -> (match (_59_2207) with
| (env, out) -> begin
(let tk = (desugar_binder env (let _59_2209 = b
in {FStar_Parser_AST.b = _59_2209.FStar_Parser_AST.b; FStar_Parser_AST.brange = _59_2209.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _59_2209.FStar_Parser_AST.aqual}))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(let _59_2219 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_59_2219) with
| (env, a) -> begin
(env, ((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), (trans_aqual b.FStar_Parser_AST.aqual)))::out)
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(let _59_2227 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_59_2227) with
| (env, x) -> begin
(env, ((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), (trans_aqual b.FStar_Parser_AST.aqual)))::out)
end))
end
| _59_2229 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_59_2232) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_exp_binder = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, t) -> begin
(let _150_793 = (desugar_typ env t)
in (Some (x), _150_793))
end
| FStar_Parser_AST.TVariable (t) -> begin
(let _150_794 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in (None, _150_794))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _150_795 = (desugar_typ env t)
in (None, _150_795))
end
| FStar_Parser_AST.Variable (x) -> begin
(Some (x), FStar_Absyn_Syntax.tun)
end
| _59_2246 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a type)", b.FStar_Parser_AST.brange))))
end))
and desugar_type_binder = (fun env b -> (let fail = (fun _59_2250 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a kind)", b.FStar_Parser_AST.brange))))
end))
in (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, t)) | (FStar_Parser_AST.TAnnotated (x, t)) -> begin
(let _150_800 = (desugar_kind env t)
in (Some (x), _150_800))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _150_801 = (desugar_kind env t)
in (None, _150_801))
end
| FStar_Parser_AST.TVariable (x) -> begin
(Some (x), (let _59_2261 = FStar_Absyn_Syntax.mk_Kind_type
in {FStar_Absyn_Syntax.n = _59_2261.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _59_2261.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = b.FStar_Parser_AST.brange; FStar_Absyn_Syntax.fvs = _59_2261.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _59_2261.FStar_Absyn_Syntax.uvs}))
end
| _59_2264 -> begin
(fail ())
end)))

let gather_tc_binders = (fun tps k -> (let rec aux = (fun bs k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(aux (FStar_List.append bs binders) k)
end
| FStar_Absyn_Syntax.Kind_abbrev (_59_2275, k) -> begin
(aux bs k)
end
| _59_2280 -> begin
bs
end))
in (let _150_810 = (aux tps k)
in (FStar_All.pipe_right _150_810 FStar_Absyn_Util.name_binders))))

let mk_data_discriminators = (fun quals env t tps k datas -> (let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_DesugarEnv.iface) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_List.append ((FStar_Absyn_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (let binders = (gather_tc_binders tps k)
in (let p = (FStar_Ident.range_of_lid t)
in (let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _59_2294 -> (match (_59_2294) with
| (x, _59_2293) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end))))
in (let binders = (let _150_831 = (let _150_830 = (let _150_829 = (let _150_828 = (let _150_827 = (FStar_Absyn_Util.ftv t FStar_Absyn_Syntax.kun)
in (let _150_826 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (_150_827, _150_826)))
in (FStar_Absyn_Syntax.mk_Typ_app' _150_828 None p))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder _150_829))
in (_150_830)::[])
in (FStar_List.append imp_binders _150_831))
in (let disc_type = (let _150_834 = (let _150_833 = (let _150_832 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.total_comp _150_832 p))
in (binders, _150_833))
in (FStar_Absyn_Syntax.mk_Typ_fun _150_834 None p))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (let disc_name = (FStar_Absyn_Util.mk_discriminator d)
in (let _150_837 = (let _150_836 = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Discriminator (d))::[]))
in (disc_name, disc_type, _150_836, (FStar_Ident.range_of_lid disc_name)))
in FStar_Absyn_Syntax.Sig_val_decl (_150_837)))))))))))))

let mk_indexed_projectors = (fun fvq refine_domain env _59_2306 lid formals t -> (match (_59_2306) with
| (tc, tps, k) -> begin
(let binders = (gather_tc_binders tps k)
in (let p = (FStar_Ident.range_of_lid lid)
in (let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p))
in (let projectee = (let _150_847 = (FStar_Absyn_Util.genident (Some (p)))
in {FStar_Absyn_Syntax.ppname = (FStar_Absyn_Syntax.mk_ident ("projectee", p)); FStar_Absyn_Syntax.realname = _150_847})
in (let arg_exp = (FStar_Absyn_Util.bvd_to_exp projectee FStar_Absyn_Syntax.tun)
in (let arg_binder = (let arg_typ = (let _150_850 = (let _150_849 = (FStar_Absyn_Util.ftv tc FStar_Absyn_Syntax.kun)
in (let _150_848 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (_150_849, _150_848)))
in (FStar_Absyn_Syntax.mk_Typ_app' _150_850 None p))
in if (not (refine_domain)) then begin
(FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end else begin
(let disc_name = (FStar_Absyn_Util.mk_discriminator lid)
in (let x = (FStar_Absyn_Util.gen_bvar arg_typ)
in (let _150_860 = (let _150_859 = (let _150_858 = (let _150_857 = (let _150_856 = (let _150_855 = (let _150_854 = (FStar_Absyn_Util.fvar None disc_name p)
in (let _150_853 = (let _150_852 = (let _150_851 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _150_851))
in (_150_852)::[])
in (_150_854, _150_853)))
in (FStar_Absyn_Syntax.mk_Exp_app _150_855 None p))
in (FStar_Absyn_Util.b2t _150_856))
in (x, _150_857))
in (FStar_Absyn_Syntax.mk_Typ_refine _150_858 None p))
in (FStar_All.pipe_left (FStar_Absyn_Util.bvd_to_bvar_s projectee) _150_859))
in (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder _150_860))))
end)
in (let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _59_2323 -> (match (_59_2323) with
| (x, _59_2322) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end))))
in (let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (let arg = (FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (let subst = (let _150_868 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i f -> (match ((Prims.fst f)) with
| FStar_Util.Inl (a) -> begin
(let _59_2334 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_59_2334) with
| (field_name, _59_2333) -> begin
(let proj = (let _150_865 = (let _150_864 = (FStar_Absyn_Util.ftv field_name FStar_Absyn_Syntax.kun)
in (_150_864, (arg)::[]))
in (FStar_Absyn_Syntax.mk_Typ_app _150_865 None p))
in (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, proj)))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(let _59_2341 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_59_2341) with
| (field_name, _59_2340) -> begin
(let proj = (let _150_867 = (let _150_866 = (FStar_Absyn_Util.fvar None field_name p)
in (_150_866, (arg)::[]))
in (FStar_Absyn_Syntax.mk_Exp_app _150_867 None p))
in (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, proj)))::[])
end))
end))))
in (FStar_All.pipe_right _150_868 FStar_List.flatten))
in (let ntps = (FStar_List.length tps)
in (let all_params = (let _150_870 = (FStar_All.pipe_right tps (FStar_List.map (fun _59_2348 -> (match (_59_2348) with
| (b, _59_2347) -> begin
(b, Some (FStar_Absyn_Syntax.Implicit))
end))))
in (FStar_List.append _150_870 formals))
in (let _150_898 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i ax -> (match ((Prims.fst ax)) with
| FStar_Util.Inl (a) -> begin
(let _59_2357 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_59_2357) with
| (field_name, _59_2356) -> begin
(let kk = (let _150_874 = (let _150_873 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (binders, _150_873))
in (FStar_Absyn_Syntax.mk_Kind_arrow _150_874 p))
in (FStar_Absyn_Syntax.Sig_tycon ((field_name, [], kk, [], [], (FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector ((lid, FStar_Util.Inl (a.FStar_Absyn_Syntax.v))))::[], (FStar_Ident.range_of_lid field_name))))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(let _59_2364 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_59_2364) with
| (field_name, _59_2363) -> begin
(let t = (let _150_877 = (let _150_876 = (let _150_875 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Absyn_Util.total_comp _150_875 p))
in (binders, _150_876))
in (FStar_Absyn_Syntax.mk_Typ_fun _150_877 None p))
in (let quals = (fun q -> if ((not (env.FStar_Parser_DesugarEnv.iface)) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_Absyn_Syntax.Assumption)::q
end else begin
q
end)
in (let quals = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector ((lid, FStar_Util.Inr (x.FStar_Absyn_Syntax.v))))::[]))
in (let impl = if (((let _150_880 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _150_880)) || (fvq <> FStar_Absyn_Syntax.Data_ctor)) || (let _150_882 = (let _150_881 = (FStar_Parser_DesugarEnv.current_module env)
in _150_881.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _150_882))) then begin
[]
end else begin
(let projection = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (let as_imp = (fun _59_14 -> (match (_59_14) with
| Some (FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _59_2374 -> begin
false
end))
in (let arg_pats = (let _150_895 = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j by -> (match (by) with
| (FStar_Util.Inl (_59_2379), imp) -> begin
if (j < ntps) then begin
[]
end else begin
(let _150_890 = (let _150_889 = (let _150_888 = (let _150_887 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.kun)
in FStar_Absyn_Syntax.Pat_tvar (_150_887))
in (pos _150_888))
in (_150_889, (as_imp imp)))
in (_150_890)::[])
end
end
| (FStar_Util.Inr (_59_2384), imp) -> begin
if ((i + ntps) = j) then begin
(((pos (FStar_Absyn_Syntax.Pat_var (projection))), (as_imp imp)))::[]
end else begin
(let _150_894 = (let _150_893 = (let _150_892 = (let _150_891 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in FStar_Absyn_Syntax.Pat_wild (_150_891))
in (pos _150_892))
in (_150_893, (as_imp imp)))
in (_150_894)::[])
end
end))))
in (FStar_All.pipe_right _150_895 FStar_List.flatten))
in (let pat = (let _150_897 = (FStar_All.pipe_right (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv lid), Some (fvq), arg_pats))) pos)
in (let _150_896 = (FStar_Absyn_Util.bvar_to_exp projection)
in (_150_897, None, _150_896)))
in (let body = (FStar_Absyn_Syntax.mk_Exp_match (arg_exp, (pat)::[]) None p)
in (let imp = (FStar_Absyn_Syntax.mk_Exp_abs (binders, body) None (FStar_Ident.range_of_lid field_name))
in (let lb = {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (field_name); FStar_Absyn_Syntax.lbtyp = FStar_Absyn_Syntax.tun; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_Tot_lid; FStar_Absyn_Syntax.lbdef = imp}
in (FStar_Absyn_Syntax.Sig_let (((false, (lb)::[]), p, [], quals)))::[])))))))
end
in (FStar_Absyn_Syntax.Sig_val_decl ((field_name, t, quals, (FStar_Ident.range_of_lid field_name))))::impl))))
end))
end))))
in (FStar_All.pipe_right _150_898 FStar_List.flatten))))))))))))))
end))

let mk_data_projectors = (fun env _59_17 -> (match (_59_17) with
| FStar_Absyn_Syntax.Sig_datacon (lid, t, tycon, quals, _59_2401, _59_2403) when (not ((FStar_Ident.lid_equals lid FStar_Absyn_Const.lexcons_lid))) -> begin
(let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _59_15 -> (match (_59_15) with
| FStar_Absyn_Syntax.RecordConstructor (_59_2408) -> begin
true
end
| _59_2411 -> begin
false
end)))) then begin
false
end else begin
(let _59_2417 = tycon
in (match (_59_2417) with
| (l, _59_2414, _59_2416) -> begin
(match ((FStar_Parser_DesugarEnv.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _59_2421 -> begin
true
end)
end))
end
in (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
(let cod = (FStar_Absyn_Util.comp_result cod)
in (let qual = (match ((FStar_Util.find_map quals (fun _59_16 -> (match (_59_16) with
| FStar_Absyn_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Absyn_Syntax.Record_ctor ((lid, fns)))
end
| _59_2432 -> begin
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
| _59_2438 -> begin
[]
end))
end
| _59_2440 -> begin
[]
end))

let rec desugar_tycon = (fun env rng quals tcs -> (let tycon_id = (fun _59_18 -> (match (_59_18) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _150_918 = (let _150_917 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_150_917))
in (FStar_Parser_AST.mk_term _150_918 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| _59_2505 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _150_931 = (let _150_930 = (let _150_929 = (binder_to_term b)
in (out, _150_929, (imp_of_aqual b)))
in FStar_Parser_AST.App (_150_930))
in (FStar_Parser_AST.mk_term _150_931 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (let tycon_record_as_variant = (fun _59_19 -> (match (_59_19) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (let mfields = (FStar_List.map (fun _59_2518 -> (match (_59_2518) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Absyn_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (let result = (let _150_937 = (let _150_936 = (let _150_935 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_150_935))
in (FStar_Parser_AST.mk_term _150_936 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _150_937 parms))
in (let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _150_939 = (FStar_All.pipe_right fields (FStar_List.map (fun _59_2525 -> (match (_59_2525) with
| (x, _59_2524) -> begin
(FStar_Parser_DesugarEnv.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _150_939))))))
end
| _59_2527 -> begin
(FStar_All.failwith "impossible")
end))
in (let desugar_abstract_tc = (fun quals _env mutuals _59_20 -> (match (_59_20) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(let _59_2541 = (typars_of_binders _env binders)
in (match (_59_2541) with
| (_env', typars) -> begin
(let k = (match (kopt) with
| None -> begin
FStar_Absyn_Syntax.kun
end
| Some (k) -> begin
(desugar_kind _env' k)
end)
in (let tconstr = (let _150_950 = (let _150_949 = (let _150_948 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_150_948))
in (FStar_Parser_AST.mk_term _150_949 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _150_950 binders))
in (let qlid = (FStar_Parser_DesugarEnv.qualify _env id)
in (let se = FStar_Absyn_Syntax.Sig_tycon ((qlid, typars, k, mutuals, [], quals, rng))
in (let _env = (FStar_Parser_DesugarEnv.push_rec_binding _env (FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (let _env2 = (FStar_Parser_DesugarEnv.push_rec_binding _env' (FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (_env, _env2, se, tconstr)))))))
end))
end
| _59_2552 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (let push_tparam = (fun env _59_21 -> (match (_59_21) with
| (FStar_Util.Inr (x), _59_2559) -> begin
(FStar_Parser_DesugarEnv.push_bvvdef env x.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inl (a), _59_2564) -> begin
(FStar_Parser_DesugarEnv.push_btvdef env a.FStar_Absyn_Syntax.v)
end))
in (let push_tparams = (FStar_List.fold_left push_tparam)
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (_59_2568)::[] -> begin
(let tc = (FStar_List.hd tcs)
in (let _59_2579 = (desugar_abstract_tc quals env [] tc)
in (match (_59_2579) with
| (_59_2573, _59_2575, se, _59_2578) -> begin
(let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))
end)))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t)::[] -> begin
(let _59_2590 = (typars_of_binders env binders)
in (match (_59_2590) with
| (env', typars) -> begin
(let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _59_22 -> (match (_59_22) with
| FStar_Absyn_Syntax.Effect -> begin
true
end
| _59_2595 -> begin
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
in (let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _59_23 -> (match (_59_23) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _59_2603 -> begin
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
in (let _150_962 = (let _150_961 = (FStar_Parser_DesugarEnv.qualify env id)
in (let _150_960 = (FStar_All.pipe_right quals (FStar_List.filter (fun _59_24 -> (match (_59_24) with
| FStar_Absyn_Syntax.Effect -> begin
false
end
| _59_2609 -> begin
true
end))))
in (_150_961, typars, c, _150_960, rng)))
in FStar_Absyn_Syntax.Sig_effect_abbrev (_150_962)))
end else begin
(let t = (desugar_typ env' t)
in (let _150_964 = (let _150_963 = (FStar_Parser_DesugarEnv.qualify env id)
in (_150_963, typars, k, t, quals, rng))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_150_964)))
end
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| FStar_Parser_AST.TyconRecord (_59_2614)::[] -> begin
(let trec = (FStar_List.hd tcs)
in (let _59_2620 = (tycon_record_as_variant trec)
in (match (_59_2620) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _59_2624::_59_2622 -> begin
(let env0 = env
in (let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (let rec collect_tcs = (fun quals et tc -> (let _59_2635 = et
in (match (_59_2635) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_59_2637) -> begin
(let trec = tc
in (let _59_2642 = (tycon_record_as_variant trec)
in (match (_59_2642) with
| (t, fs) -> begin
(collect_tcs ((FStar_Absyn_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(let _59_2654 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_59_2654) with
| (env, _59_2651, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(let _59_2666 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_59_2666) with
| (env, _59_2663, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _59_2668 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (let _59_2671 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_59_2671) with
| (env, tcs) -> begin
(let tcs = (FStar_List.rev tcs)
in (let sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _59_26 -> (match (_59_26) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (id, tpars, k, _59_2678, _59_2680, _59_2682, _59_2684), t, quals) -> begin
(let env_tps = (push_tparams env tpars)
in (let t = (desugar_typ env_tps t)
in (FStar_Absyn_Syntax.Sig_typ_abbrev ((id, tpars, k, t, [], rng)))::[]))
end
| FStar_Util.Inl (FStar_Absyn_Syntax.Sig_tycon (tname, tpars, k, mutuals, _59_2698, tags, _59_2701), constrs, tconstr, quals) -> begin
(let tycon = (tname, tpars, k)
in (let env_tps = (push_tparams env tpars)
in (let _59_2732 = (let _150_980 = (FStar_All.pipe_right constrs (FStar_List.map (fun _59_2714 -> (match (_59_2714) with
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
in (let t = (let _150_975 = (FStar_Parser_DesugarEnv.default_total env_tps)
in (let _150_974 = (close env_tps t)
in (desugar_typ _150_975 _150_974)))
in (let name = (FStar_Parser_DesugarEnv.qualify env id)
in (let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _59_25 -> (match (_59_25) with
| FStar_Absyn_Syntax.RecordType (fns) -> begin
(FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _59_2728 -> begin
[]
end))))
in (let _150_979 = (let _150_978 = (let _150_977 = (FStar_All.pipe_right t FStar_Absyn_Util.name_function_binders)
in (name, _150_977, tycon, quals, mutuals, rng))
in FStar_Absyn_Syntax.Sig_datacon (_150_978))
in (name, _150_979))))))
end))))
in (FStar_All.pipe_left FStar_List.split _150_980))
in (match (_59_2732) with
| (constrNames, constrs) -> begin
(FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, constrNames, tags, rng)))::constrs
end))))
end
| _59_2734 -> begin
(FStar_All.failwith "impossible")
end))))
in (let bundle = (let _150_982 = (let _150_981 = (FStar_List.collect FStar_Absyn_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _150_981, rng))
in FStar_Absyn_Syntax.Sig_bundle (_150_982))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (let data_ops = (FStar_All.pipe_right sigelts (FStar_List.collect (mk_data_projectors env)))
in (let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _59_27 -> (match (_59_27) with
| FStar_Absyn_Syntax.Sig_tycon (tname, tps, k, _59_2744, constrs, quals, _59_2748) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _59_2752 -> begin
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

let desugar_binders = (fun env binders -> (let _59_2783 = (FStar_List.fold_left (fun _59_2761 b -> (match (_59_2761) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| FStar_Util.Inl (Some (a), k) -> begin
(let _59_2770 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_59_2770) with
| (env, a) -> begin
(env, ((FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k)))::binders)
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(let _59_2778 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_59_2778) with
| (env, x) -> begin
(env, ((FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t)))::binders)
end))
end
| _59_2780 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_59_2783) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))

let trans_qual = (fun _59_28 -> (match (_59_28) with
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

let trans_pragma = (fun _59_29 -> (match (_59_29) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Absyn_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions -> begin
FStar_Absyn_Syntax.ResetOptions
end))

let trans_quals = (FStar_List.map trans_qual)

let rec desugar_decl = (fun env d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(let se = FStar_Absyn_Syntax.Sig_pragma (((trans_pragma p), d.FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| FStar_Parser_AST.Open (lid) -> begin
(let env = (FStar_Parser_DesugarEnv.push_namespace env lid)
in (env, []))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _150_999 = (FStar_Parser_DesugarEnv.push_module_abbrev env x l)
in (_150_999, []))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _150_1000 = (trans_quals qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _150_1000 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _150_1002 = (let _150_1001 = (desugar_exp_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Absyn_Util.compress_exp _150_1001))
in _150_1002.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let (lbs, _59_2819) -> begin
(let lids = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inr (l) -> begin
l
end
| _59_2826 -> begin
(FStar_All.failwith "impossible")
end))))
in (let quals = (match (quals) with
| _59_2831::_59_2829 -> begin
(trans_quals quals)
end
| _59_2834 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _59_30 -> (match (_59_30) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_59_2843); FStar_Absyn_Syntax.lbtyp = _59_2841; FStar_Absyn_Syntax.lbeff = _59_2839; FStar_Absyn_Syntax.lbdef = _59_2837} -> begin
[]
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = _59_2851; FStar_Absyn_Syntax.lbeff = _59_2849; FStar_Absyn_Syntax.lbdef = _59_2847} -> begin
(FStar_Parser_DesugarEnv.lookup_letbinding_quals env l)
end))))
end)
in (let s = FStar_Absyn_Syntax.Sig_let ((lbs, d.FStar_Parser_AST.drange, lids, quals))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env s)
in (env, (s)::[])))))
end
| _59_2859 -> begin
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
in (let _150_1008 = (let _150_1007 = (let _150_1006 = (let _150_1005 = (FStar_Parser_DesugarEnv.qualify env id)
in (_150_1005, f, (FStar_Absyn_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Sig_assume (_150_1006))
in (_150_1007)::[])
in (env, _150_1008)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(let t = (let _150_1009 = (close_fun env t)
in (desugar_typ env _150_1009))
in (let quals = if (env.FStar_Parser_DesugarEnv.iface && env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(let _150_1010 = (trans_quals quals)
in (FStar_Absyn_Syntax.Assumption)::_150_1010)
end else begin
(trans_quals quals)
end
in (let se = (let _150_1012 = (let _150_1011 = (FStar_Parser_DesugarEnv.qualify env id)
in (_150_1011, t, quals, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Sig_val_decl (_150_1012))
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
in (let t = (let _150_1015 = (let _150_1014 = (let _150_1013 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (FStar_Absyn_Syntax.mk_Total _150_1013))
in (((FStar_Absyn_Syntax.null_v_binder t))::[], _150_1014))
in (FStar_Absyn_Syntax.mk_Typ_fun _150_1015 None d.FStar_Parser_AST.drange))
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
(let _59_2912 = (desugar_binders env binders)
in (match (_59_2912) with
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
in (let _59_2928 = (desugar_binders env eff_binders)
in (match (_59_2928) with
| (env, binders) -> begin
(let defn = (desugar_typ env defn)
in (let _59_2932 = (FStar_Absyn_Util.head_and_args defn)
in (match (_59_2932) with
| (head, args) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (eff) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_effect_defn env eff.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _150_1020 = (let _150_1019 = (let _150_1018 = (let _150_1017 = (let _150_1016 = (FStar_Absyn_Print.sli eff.FStar_Absyn_Syntax.v)
in (Prims.strcat "Effect " _150_1016))
in (Prims.strcat _150_1017 " not found"))
in (_150_1018, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_150_1019))
in (Prims.raise _150_1020))
end
| Some (ed) -> begin
(let subst = (FStar_Absyn_Util.subst_of_list ed.FStar_Absyn_Syntax.binders args)
in (let sub = (FStar_Absyn_Util.subst_typ subst)
in (let ed = (let _150_1038 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _150_1037 = (trans_quals quals)
in (let _150_1036 = (FStar_Absyn_Util.subst_kind subst ed.FStar_Absyn_Syntax.signature)
in (let _150_1035 = (sub ed.FStar_Absyn_Syntax.ret)
in (let _150_1034 = (sub ed.FStar_Absyn_Syntax.bind_wp)
in (let _150_1033 = (sub ed.FStar_Absyn_Syntax.bind_wlp)
in (let _150_1032 = (sub ed.FStar_Absyn_Syntax.if_then_else)
in (let _150_1031 = (sub ed.FStar_Absyn_Syntax.ite_wp)
in (let _150_1030 = (sub ed.FStar_Absyn_Syntax.ite_wlp)
in (let _150_1029 = (sub ed.FStar_Absyn_Syntax.wp_binop)
in (let _150_1028 = (sub ed.FStar_Absyn_Syntax.wp_as_type)
in (let _150_1027 = (sub ed.FStar_Absyn_Syntax.close_wp)
in (let _150_1026 = (sub ed.FStar_Absyn_Syntax.close_wp_t)
in (let _150_1025 = (sub ed.FStar_Absyn_Syntax.assert_p)
in (let _150_1024 = (sub ed.FStar_Absyn_Syntax.assume_p)
in (let _150_1023 = (sub ed.FStar_Absyn_Syntax.null_wp)
in (let _150_1022 = (sub ed.FStar_Absyn_Syntax.trivial)
in {FStar_Absyn_Syntax.mname = _150_1038; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _150_1037; FStar_Absyn_Syntax.signature = _150_1036; FStar_Absyn_Syntax.ret = _150_1035; FStar_Absyn_Syntax.bind_wp = _150_1034; FStar_Absyn_Syntax.bind_wlp = _150_1033; FStar_Absyn_Syntax.if_then_else = _150_1032; FStar_Absyn_Syntax.ite_wp = _150_1031; FStar_Absyn_Syntax.ite_wlp = _150_1030; FStar_Absyn_Syntax.wp_binop = _150_1029; FStar_Absyn_Syntax.wp_as_type = _150_1028; FStar_Absyn_Syntax.close_wp = _150_1027; FStar_Absyn_Syntax.close_wp_t = _150_1026; FStar_Absyn_Syntax.assert_p = _150_1025; FStar_Absyn_Syntax.assume_p = _150_1024; FStar_Absyn_Syntax.null_wp = _150_1023; FStar_Absyn_Syntax.trivial = _150_1022})))))))))))))))))
in (let se = FStar_Absyn_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)
end
| _59_2944 -> begin
(let _150_1042 = (let _150_1041 = (let _150_1040 = (let _150_1039 = (FStar_Absyn_Print.typ_to_string head)
in (Prims.strcat _150_1039 " is not an effect"))
in (_150_1040, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_150_1041))
in (Prims.raise _150_1042))
end)
end)))
end)))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(let env0 = env
in (let env = (FStar_Parser_DesugarEnv.enter_monad_scope env eff_name)
in (let _59_2958 = (desugar_binders env eff_binders)
in (match (_59_2958) with
| (env, binders) -> begin
(let eff_k = (desugar_kind env eff_kind)
in (let _59_2969 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _59_2962 decl -> (match (_59_2962) with
| (env, out) -> begin
(let _59_2966 = (desugar_decl env decl)
in (match (_59_2966) with
| (env, ses) -> begin
(let _150_1046 = (let _150_1045 = (FStar_List.hd ses)
in (_150_1045)::out)
in (env, _150_1046))
end))
end)) (env, [])))
in (match (_59_2969) with
| (env, decls) -> begin
(let decls = (FStar_List.rev decls)
in (let lookup = (fun s -> (match ((let _150_1049 = (FStar_Parser_DesugarEnv.qualify env (FStar_Absyn_Syntax.mk_ident (s, d.FStar_Parser_AST.drange)))
in (FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _150_1049))) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat (Prims.strcat "Monad " eff_name.FStar_Ident.idText) " expects definition of ") s), d.FStar_Parser_AST.drange))))
end
| Some (t) -> begin
t
end))
in (let ed = (let _150_1065 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _150_1064 = (trans_quals quals)
in (let _150_1063 = (lookup "return")
in (let _150_1062 = (lookup "bind_wp")
in (let _150_1061 = (lookup "bind_wlp")
in (let _150_1060 = (lookup "if_then_else")
in (let _150_1059 = (lookup "ite_wp")
in (let _150_1058 = (lookup "ite_wlp")
in (let _150_1057 = (lookup "wp_binop")
in (let _150_1056 = (lookup "wp_as_type")
in (let _150_1055 = (lookup "close_wp")
in (let _150_1054 = (lookup "close_wp_t")
in (let _150_1053 = (lookup "assert_p")
in (let _150_1052 = (lookup "assume_p")
in (let _150_1051 = (lookup "null_wp")
in (let _150_1050 = (lookup "trivial")
in {FStar_Absyn_Syntax.mname = _150_1065; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _150_1064; FStar_Absyn_Syntax.signature = eff_k; FStar_Absyn_Syntax.ret = _150_1063; FStar_Absyn_Syntax.bind_wp = _150_1062; FStar_Absyn_Syntax.bind_wlp = _150_1061; FStar_Absyn_Syntax.if_then_else = _150_1060; FStar_Absyn_Syntax.ite_wp = _150_1059; FStar_Absyn_Syntax.ite_wlp = _150_1058; FStar_Absyn_Syntax.wp_binop = _150_1057; FStar_Absyn_Syntax.wp_as_type = _150_1056; FStar_Absyn_Syntax.close_wp = _150_1055; FStar_Absyn_Syntax.close_wp_t = _150_1054; FStar_Absyn_Syntax.assert_p = _150_1053; FStar_Absyn_Syntax.assume_p = _150_1052; FStar_Absyn_Syntax.null_wp = _150_1051; FStar_Absyn_Syntax.trivial = _150_1050}))))))))))))))))
in (let se = FStar_Absyn_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)))
end))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(let lookup = (fun l -> (match ((FStar_Parser_DesugarEnv.try_lookup_effect_name env l)) with
| None -> begin
(let _150_1072 = (let _150_1071 = (let _150_1070 = (let _150_1069 = (let _150_1068 = (FStar_Absyn_Print.sli l)
in (Prims.strcat "Effect name " _150_1068))
in (Prims.strcat _150_1069 " not found"))
in (_150_1070, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_150_1071))
in (Prims.raise _150_1072))
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

let desugar_decls = (fun env decls -> (FStar_List.fold_left (fun _59_2994 d -> (match (_59_2994) with
| (env, sigelts) -> begin
(let _59_2998 = (desugar_decl env d)
in (match (_59_2998) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))

let open_prims_all = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.prims_lid)) FStar_Absyn_Syntax.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.all_lid)) FStar_Absyn_Syntax.dummyRange))::[]

let desugar_modul_common = (fun curmod env m -> (let open_ns = (fun mname d -> (let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _150_1088 = (let _150_1087 = (let _150_1086 = (FStar_Absyn_Syntax.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_150_1086))
in (FStar_Parser_AST.mk_decl _150_1087 (FStar_Absyn_Syntax.range_of_lid mname)))
in (_150_1088)::d)
end else begin
d
end
in d))
in (let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod, _59_3009) -> begin
(FStar_Parser_DesugarEnv.finish_module_or_interface env prev_mod)
end)
in (let _59_3028 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _150_1090 = (FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _150_1089 = (open_ns mname decls)
in (_150_1090, mname, _150_1089, true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _150_1092 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _150_1091 = (open_ns mname decls)
in (_150_1092, mname, _150_1091, false)))
end)
in (match (_59_3028) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(let _59_3031 = (desugar_decls env decls)
in (match (_59_3031) with
| (env, sigelts) -> begin
(let modul = {FStar_Absyn_Syntax.name = mname; FStar_Absyn_Syntax.declarations = sigelts; FStar_Absyn_Syntax.exports = []; FStar_Absyn_Syntax.is_interface = intf; FStar_Absyn_Syntax.is_deserialized = false}
in (env, modul, pop_when_done))
end))
end)))))

let desugar_partial_modul = (fun curmod env m -> (let m = if (FStar_ST.read FStar_Options.interactive_fsi) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _150_1099 = (let _150_1098 = (let _150_1097 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_Util.for_some (fun m -> (m = mname.FStar_Ident.str)) _150_1097))
in (mname, decls, _150_1098))
in FStar_Parser_AST.Interface (_150_1099))
end
| FStar_Parser_AST.Interface (mname, _59_3043, _59_3045) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (let _59_3053 = (desugar_modul_common curmod env m)
in (match (_59_3053) with
| (x, y, _59_3052) -> begin
(x, y)
end))))

let desugar_modul = (fun env m -> (let _59_3059 = (desugar_modul_common None env m)
in (match (_59_3059) with
| (env, modul, pop_when_done) -> begin
(let env = (FStar_Parser_DesugarEnv.finish_module_or_interface env modul)
in (let _59_3061 = if (FStar_Options.should_dump modul.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _150_1104 = (FStar_Absyn_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _150_1104))
end else begin
()
end
in (let _150_1105 = if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface modul.FStar_Absyn_Syntax.name env)
end else begin
env
end
in (_150_1105, modul))))
end)))

let desugar_file = (fun env f -> (let _59_3074 = (FStar_List.fold_left (fun _59_3067 m -> (match (_59_3067) with
| (env, mods) -> begin
(let _59_3071 = (desugar_modul env m)
in (match (_59_3071) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_59_3074) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))

let add_modul_to_env = (fun m en -> (let _59_3079 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false en m.FStar_Absyn_Syntax.name)
in (match (_59_3079) with
| (en, pop_when_done) -> begin
(let en = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt (let _59_3080 = en
in {FStar_Parser_DesugarEnv.curmodule = Some (m.FStar_Absyn_Syntax.name); FStar_Parser_DesugarEnv.modules = _59_3080.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _59_3080.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _59_3080.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _59_3080.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _59_3080.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _59_3080.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = _59_3080.FStar_Parser_DesugarEnv.phase; FStar_Parser_DesugarEnv.sigmap = _59_3080.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _59_3080.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _59_3080.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _59_3080.FStar_Parser_DesugarEnv.admitted_iface}) m.FStar_Absyn_Syntax.exports)
in (let env = (FStar_Parser_DesugarEnv.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface m.FStar_Absyn_Syntax.name env)
end else begin
env
end))
end)))




