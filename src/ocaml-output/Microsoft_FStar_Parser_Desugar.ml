
let as_imp = (fun ( _43_1 ) -> (match (_43_1) with
| (Microsoft_FStar_Parser_AST.Hash) | (Microsoft_FStar_Parser_AST.FsTypApp) -> begin
Some (Microsoft_FStar_Absyn_Syntax.Implicit)
end
| _43_34 -> begin
None
end))

let arg_withimp_e = (fun ( imp ) ( t ) -> (t, (as_imp imp)))

let arg_withimp_t = (fun ( imp ) ( t ) -> (match (imp) with
| Microsoft_FStar_Parser_AST.Hash -> begin
(t, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end
| _43_41 -> begin
(t, None)
end))

let contains_binder = (fun ( binders ) -> (Support.All.pipe_right binders (Support.Microsoft.FStar.Util.for_some (fun ( b ) -> (match (b.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Annotated (_43_45) -> begin
true
end
| _43_48 -> begin
false
end)))))

let rec unparen = (fun ( t ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _43_53 -> begin
t
end))

let rec unlabel = (fun ( t ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (t) -> begin
(unlabel t)
end
| Microsoft_FStar_Parser_AST.Labeled ((t, _43_59, _43_61)) -> begin
(unlabel t)
end
| _43_65 -> begin
t
end))

let kind_star = (fun ( r ) -> (let _114_17 = (let _114_16 = (Microsoft_FStar_Absyn_Syntax.lid_of_path (("Type")::[]) r)
in Microsoft_FStar_Parser_AST.Name (_114_16))
in (Microsoft_FStar_Parser_AST.mk_term _114_17 r Microsoft_FStar_Parser_AST.Kind)))

let compile_op = (fun ( arity ) ( s ) -> (let name_of_char = (fun ( _43_2 ) -> (match (_43_2) with
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
| _43_88 -> begin
"UNKNOWN"
end))
in (let rec aux = (fun ( i ) -> (match ((i = (Support.String.length s))) with
| true -> begin
[]
end
| false -> begin
(let _114_28 = (let _114_26 = (Support.Microsoft.FStar.Util.char_at s i)
in (name_of_char _114_26))
in (let _114_27 = (aux (i + 1))
in (_114_28)::_114_27))
end))
in (let _114_30 = (let _114_29 = (aux 0)
in (Support.String.concat "_" _114_29))
in (Support.String.strcat "op_" _114_30)))))

let compile_op_lid = (fun ( n ) ( s ) ( r ) -> (let _114_40 = (let _114_39 = (let _114_38 = (let _114_37 = (compile_op n s)
in (_114_37, r))
in (Microsoft_FStar_Absyn_Syntax.mk_ident _114_38))
in (_114_39)::[])
in (Support.All.pipe_right _114_40 Microsoft_FStar_Absyn_Syntax.lid_of_ids)))

let op_as_vlid = (fun ( env ) ( arity ) ( rng ) ( s ) -> (let r = (fun ( l ) -> (let _114_51 = (Microsoft_FStar_Absyn_Util.set_lid_range l rng)
in Some (_114_51)))
in (let fallback = (fun ( _43_102 ) -> (match (()) with
| () -> begin
(match (s) with
| "=" -> begin
(r Microsoft_FStar_Absyn_Const.op_Eq)
end
| ":=" -> begin
(r Microsoft_FStar_Absyn_Const.op_ColonEq)
end
| "<" -> begin
(r Microsoft_FStar_Absyn_Const.op_LT)
end
| "<=" -> begin
(r Microsoft_FStar_Absyn_Const.op_LTE)
end
| ">" -> begin
(r Microsoft_FStar_Absyn_Const.op_GT)
end
| ">=" -> begin
(r Microsoft_FStar_Absyn_Const.op_GTE)
end
| "&&" -> begin
(r Microsoft_FStar_Absyn_Const.op_And)
end
| "||" -> begin
(r Microsoft_FStar_Absyn_Const.op_Or)
end
| "*" -> begin
(r Microsoft_FStar_Absyn_Const.op_Multiply)
end
| "+" -> begin
(r Microsoft_FStar_Absyn_Const.op_Addition)
end
| "-" when (arity = 1) -> begin
(r Microsoft_FStar_Absyn_Const.op_Minus)
end
| "-" -> begin
(r Microsoft_FStar_Absyn_Const.op_Subtraction)
end
| "/" -> begin
(r Microsoft_FStar_Absyn_Const.op_Division)
end
| "%" -> begin
(r Microsoft_FStar_Absyn_Const.op_Modulus)
end
| "!" -> begin
(r Microsoft_FStar_Absyn_Const.read_lid)
end
| "@" -> begin
(r Microsoft_FStar_Absyn_Const.list_append_lid)
end
| "^" -> begin
(r Microsoft_FStar_Absyn_Const.strcat_lid)
end
| "|>" -> begin
(r Microsoft_FStar_Absyn_Const.pipe_right_lid)
end
| "<|" -> begin
(r Microsoft_FStar_Absyn_Const.pipe_left_lid)
end
| "<>" -> begin
(r Microsoft_FStar_Absyn_Const.op_notEq)
end
| _43_124 -> begin
None
end)
end))
in (match ((let _114_54 = (compile_op_lid arity s rng)
in (Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env _114_54))) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _43_135)); Microsoft_FStar_Absyn_Syntax.tk = _43_132; Microsoft_FStar_Absyn_Syntax.pos = _43_130; Microsoft_FStar_Absyn_Syntax.fvs = _43_128; Microsoft_FStar_Absyn_Syntax.uvs = _43_126}) -> begin
Some (fv.Microsoft_FStar_Absyn_Syntax.v)
end
| _43_141 -> begin
(fallback ())
end))))

let op_as_tylid = (fun ( env ) ( arity ) ( rng ) ( s ) -> (let r = (fun ( l ) -> (let _114_65 = (Microsoft_FStar_Absyn_Util.set_lid_range l rng)
in Some (_114_65)))
in (match (s) with
| "~" -> begin
(r Microsoft_FStar_Absyn_Const.not_lid)
end
| "==" -> begin
(r Microsoft_FStar_Absyn_Const.eq2_lid)
end
| "=!=" -> begin
(r Microsoft_FStar_Absyn_Const.neq2_lid)
end
| "<<" -> begin
(r Microsoft_FStar_Absyn_Const.precedes_lid)
end
| "/\\" -> begin
(r Microsoft_FStar_Absyn_Const.and_lid)
end
| "\\/" -> begin
(r Microsoft_FStar_Absyn_Const.or_lid)
end
| "==>" -> begin
(r Microsoft_FStar_Absyn_Const.imp_lid)
end
| "<==>" -> begin
(r Microsoft_FStar_Absyn_Const.iff_lid)
end
| s -> begin
(match ((let _114_66 = (compile_op_lid arity s rng)
in (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env _114_66))) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (ftv); Microsoft_FStar_Absyn_Syntax.tk = _43_164; Microsoft_FStar_Absyn_Syntax.pos = _43_162; Microsoft_FStar_Absyn_Syntax.fvs = _43_160; Microsoft_FStar_Absyn_Syntax.uvs = _43_158}) -> begin
Some (ftv.Microsoft_FStar_Absyn_Syntax.v)
end
| _43_170 -> begin
None
end)
end)))

let rec is_type = (fun ( env ) ( t ) -> (match ((t.Microsoft_FStar_Parser_AST.level = Microsoft_FStar_Parser_AST.Type)) with
| true -> begin
true
end
| false -> begin
(match ((let _114_73 = (unparen t)
in _114_73.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Wild -> begin
true
end
| Microsoft_FStar_Parser_AST.Labeled (_43_175) -> begin
true
end
| Microsoft_FStar_Parser_AST.Op (("*", hd::_43_179)) -> begin
(is_type env hd)
end
| (Microsoft_FStar_Parser_AST.Op (("==", _))) | (Microsoft_FStar_Parser_AST.Op (("=!=", _))) | (Microsoft_FStar_Parser_AST.Op (("~", _))) | (Microsoft_FStar_Parser_AST.Op (("/\\", _))) | (Microsoft_FStar_Parser_AST.Op (("\\/", _))) | (Microsoft_FStar_Parser_AST.Op (("==>", _))) | (Microsoft_FStar_Parser_AST.Op (("<==>", _))) | (Microsoft_FStar_Parser_AST.Op (("<<", _))) -> begin
true
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match ((op_as_tylid env (Support.List.length args) t.Microsoft_FStar_Parser_AST.range s)) with
| None -> begin
false
end
| _43_230 -> begin
true
end)
end
| (Microsoft_FStar_Parser_AST.QForall (_)) | (Microsoft_FStar_Parser_AST.QExists (_)) | (Microsoft_FStar_Parser_AST.Sum (_)) | (Microsoft_FStar_Parser_AST.Refine (_)) | (Microsoft_FStar_Parser_AST.Tvar (_)) | (Microsoft_FStar_Parser_AST.NamedTyp (_)) -> begin
true
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) when ((Support.List.length l.Microsoft_FStar_Absyn_Syntax.ns) = 0) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env l.Microsoft_FStar_Absyn_Syntax.ident)) with
| Some (_43_253) -> begin
true
end
| _43_256 -> begin
(Microsoft_FStar_Parser_DesugarEnv.is_type_lid env l)
end)
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) | (Microsoft_FStar_Parser_AST.Construct ((l, _))) -> begin
(Microsoft_FStar_Parser_DesugarEnv.is_type_lid env l)
end
| (Microsoft_FStar_Parser_AST.App (({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Var (l); Microsoft_FStar_Parser_AST.range = _; Microsoft_FStar_Parser_AST.level = _}, arg, Microsoft_FStar_Parser_AST.Nothing))) | (Microsoft_FStar_Parser_AST.App (({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Name (l); Microsoft_FStar_Parser_AST.range = _; Microsoft_FStar_Parser_AST.level = _}, arg, Microsoft_FStar_Parser_AST.Nothing))) when (l.Microsoft_FStar_Absyn_Syntax.str = "ref") -> begin
(is_type env arg)
end
| (Microsoft_FStar_Parser_AST.App ((t, _, _))) | (Microsoft_FStar_Parser_AST.Paren (t)) | (Microsoft_FStar_Parser_AST.Ascribed ((t, _))) -> begin
(is_type env t)
end
| Microsoft_FStar_Parser_AST.Product ((_43_297, t)) -> begin
(not ((is_kind env t)))
end
| Microsoft_FStar_Parser_AST.If ((t, t1, t2)) -> begin
(((is_type env t) || (is_type env t1)) || (is_type env t2))
end
| Microsoft_FStar_Parser_AST.Abs ((pats, t)) -> begin
(let rec aux = (fun ( env ) ( pats ) -> (match (pats) with
| [] -> begin
(is_type env t)
end
| hd::pats -> begin
(match (hd.Microsoft_FStar_Parser_AST.pat) with
| (Microsoft_FStar_Parser_AST.PatWild) | (Microsoft_FStar_Parser_AST.PatVar (_)) -> begin
(aux env pats)
end
| Microsoft_FStar_Parser_AST.PatTvar ((id, _43_323)) -> begin
(let _43_329 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_43_329) with
| (env, _43_328) -> begin
(aux env pats)
end))
end
| Microsoft_FStar_Parser_AST.PatAscribed ((p, tm)) -> begin
(let env = (match ((is_kind env tm)) with
| true -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| (Microsoft_FStar_Parser_AST.PatVar ((id, _))) | (Microsoft_FStar_Parser_AST.PatTvar ((id, _))) -> begin
(let _114_78 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (Support.All.pipe_right _114_78 Support.Prims.fst))
end
| _43_344 -> begin
env
end)
end
| false -> begin
env
end)
in (aux env pats))
end
| _43_347 -> begin
false
end)
end))
in (aux env pats))
end
| _43_349 -> begin
false
end)
end))
and is_kind = (fun ( env ) ( t ) -> (match ((t.Microsoft_FStar_Parser_AST.level = Microsoft_FStar_Parser_AST.Kind)) with
| true -> begin
true
end
| false -> begin
(match ((let _114_81 = (unparen t)
in _114_81.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Name ({Microsoft_FStar_Absyn_Syntax.ns = _43_358; Microsoft_FStar_Absyn_Syntax.ident = _43_356; Microsoft_FStar_Absyn_Syntax.nsstr = _43_354; Microsoft_FStar_Absyn_Syntax.str = "Type"}) -> begin
true
end
| Microsoft_FStar_Parser_AST.Product ((_43_362, t)) -> begin
(is_kind env t)
end
| Microsoft_FStar_Parser_AST.Paren (t) -> begin
(is_kind env t)
end
| (Microsoft_FStar_Parser_AST.Construct ((l, _))) | (Microsoft_FStar_Parser_AST.Name (l)) -> begin
(Microsoft_FStar_Parser_DesugarEnv.is_kind_abbrev env l)
end
| _43_375 -> begin
false
end)
end))

let rec is_type_binder = (fun ( env ) ( b ) -> (match ((b.Microsoft_FStar_Parser_AST.blevel = Microsoft_FStar_Parser_AST.Formula)) with
| true -> begin
(match (b.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Variable (_43_379) -> begin
false
end
| (Microsoft_FStar_Parser_AST.TAnnotated (_)) | (Microsoft_FStar_Parser_AST.TVariable (_)) -> begin
true
end
| (Microsoft_FStar_Parser_AST.Annotated ((_, t))) | (Microsoft_FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end
| false -> begin
(match (b.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Variable (_43_394) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected binder without annotation", b.Microsoft_FStar_Parser_AST.brange))))
end
| Microsoft_FStar_Parser_AST.TVariable (_43_397) -> begin
false
end
| Microsoft_FStar_Parser_AST.TAnnotated (_43_400) -> begin
true
end
| (Microsoft_FStar_Parser_AST.Annotated ((_, t))) | (Microsoft_FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end))

let sort_ftv = (fun ( ftv ) -> (let _114_92 = (Support.Microsoft.FStar.Util.remove_dups (fun ( x ) ( y ) -> (x.Microsoft_FStar_Absyn_Syntax.idText = y.Microsoft_FStar_Absyn_Syntax.idText)) ftv)
in (Support.All.pipe_left (Support.Microsoft.FStar.Util.sort_with (fun ( x ) ( y ) -> (Support.String.compare x.Microsoft_FStar_Absyn_Syntax.idText y.Microsoft_FStar_Absyn_Syntax.idText))) _114_92)))

let rec free_type_vars_b = (fun ( env ) ( binder ) -> (match (binder.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Variable (_43_416) -> begin
(env, [])
end
| Microsoft_FStar_Parser_AST.TVariable (x) -> begin
(let _43_423 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env x)
in (match (_43_423) with
| (env, _43_422) -> begin
(env, (x)::[])
end))
end
| Microsoft_FStar_Parser_AST.Annotated ((_43_425, term)) -> begin
(let _114_99 = (free_type_vars env term)
in (env, _114_99))
end
| Microsoft_FStar_Parser_AST.TAnnotated ((id, _43_431)) -> begin
(let _43_437 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_43_437) with
| (env, _43_436) -> begin
(env, [])
end))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(let _114_100 = (free_type_vars env t)
in (env, _114_100))
end))
and free_type_vars = (fun ( env ) ( t ) -> (match ((let _114_103 = (unparen t)
in _114_103.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Tvar (a) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env a)) with
| None -> begin
(a)::[]
end
| _43_446 -> begin
[]
end)
end
| (Microsoft_FStar_Parser_AST.Wild) | (Microsoft_FStar_Parser_AST.Const (_)) | (Microsoft_FStar_Parser_AST.Var (_)) | (Microsoft_FStar_Parser_AST.Name (_)) -> begin
[]
end
| (Microsoft_FStar_Parser_AST.Requires ((t, _))) | (Microsoft_FStar_Parser_AST.Ensures ((t, _))) | (Microsoft_FStar_Parser_AST.Labeled ((t, _, _))) | (Microsoft_FStar_Parser_AST.NamedTyp ((_, t))) | (Microsoft_FStar_Parser_AST.Paren (t)) | (Microsoft_FStar_Parser_AST.Ascribed ((t, _))) -> begin
(free_type_vars env t)
end
| Microsoft_FStar_Parser_AST.Construct ((_43_482, ts)) -> begin
(Support.List.collect (fun ( _43_489 ) -> (match (_43_489) with
| (t, _43_488) -> begin
(free_type_vars env t)
end)) ts)
end
| Microsoft_FStar_Parser_AST.Op ((_43_491, ts)) -> begin
(Support.List.collect (free_type_vars env) ts)
end
| Microsoft_FStar_Parser_AST.App ((t1, t2, _43_498)) -> begin
(let _114_106 = (free_type_vars env t1)
in (let _114_105 = (free_type_vars env t2)
in (Support.List.append _114_106 _114_105)))
end
| Microsoft_FStar_Parser_AST.Refine ((b, t)) -> begin
(let _43_507 = (free_type_vars_b env b)
in (match (_43_507) with
| (env, f) -> begin
(let _114_107 = (free_type_vars env t)
in (Support.List.append f _114_107))
end))
end
| (Microsoft_FStar_Parser_AST.Product ((binders, body))) | (Microsoft_FStar_Parser_AST.Sum ((binders, body))) -> begin
(let _43_523 = (Support.List.fold_left (fun ( _43_516 ) ( binder ) -> (match (_43_516) with
| (env, free) -> begin
(let _43_520 = (free_type_vars_b env binder)
in (match (_43_520) with
| (env, f) -> begin
(env, (Support.List.append f free))
end))
end)) (env, []) binders)
in (match (_43_523) with
| (env, free) -> begin
(let _114_110 = (free_type_vars env body)
in (Support.List.append free _114_110))
end))
end
| Microsoft_FStar_Parser_AST.Project ((t, _43_526)) -> begin
(free_type_vars env t)
end
| (Microsoft_FStar_Parser_AST.Abs (_)) | (Microsoft_FStar_Parser_AST.If (_)) | (Microsoft_FStar_Parser_AST.QForall (_)) | (Microsoft_FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (Microsoft_FStar_Parser_AST.Let (_)) | (Microsoft_FStar_Parser_AST.Record (_)) | (Microsoft_FStar_Parser_AST.Match (_)) | (Microsoft_FStar_Parser_AST.TryWith (_)) | (Microsoft_FStar_Parser_AST.Seq (_)) -> begin
(Microsoft_FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.Microsoft_FStar_Parser_AST.range)
end))

let head_and_args = (fun ( t ) -> (let rec aux = (fun ( args ) ( t ) -> (match ((let _114_117 = (unparen t)
in _114_117.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((t, arg, imp)) -> begin
(aux (((arg, imp))::args) t)
end
| Microsoft_FStar_Parser_AST.Construct ((l, args')) -> begin
({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Name (l); Microsoft_FStar_Parser_AST.range = t.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Parser_AST.level = t.Microsoft_FStar_Parser_AST.level}, (Support.List.append args' args))
end
| _43_570 -> begin
(t, args)
end))
in (aux [] t)))

let close = (fun ( env ) ( t ) -> (let ftv = (let _114_122 = (free_type_vars env t)
in (Support.All.pipe_left sort_ftv _114_122))
in (match (((Support.List.length ftv) = 0)) with
| true -> begin
t
end
| false -> begin
(let binders = (Support.All.pipe_right ftv (Support.List.map (fun ( x ) -> (let _114_126 = (let _114_125 = (let _114_124 = (kind_star x.Microsoft_FStar_Absyn_Syntax.idRange)
in (x, _114_124))
in Microsoft_FStar_Parser_AST.TAnnotated (_114_125))
in (Microsoft_FStar_Parser_AST.mk_binder _114_126 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type (Some (Microsoft_FStar_Absyn_Syntax.Implicit)))))))
in (let result = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((binders, t))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
in result))
end)))

let close_fun = (fun ( env ) ( t ) -> (let ftv = (let _114_131 = (free_type_vars env t)
in (Support.All.pipe_left sort_ftv _114_131))
in (match (((Support.List.length ftv) = 0)) with
| true -> begin
t
end
| false -> begin
(let binders = (Support.All.pipe_right ftv (Support.List.map (fun ( x ) -> (let _114_135 = (let _114_134 = (let _114_133 = (kind_star x.Microsoft_FStar_Absyn_Syntax.idRange)
in (x, _114_133))
in Microsoft_FStar_Parser_AST.TAnnotated (_114_134))
in (Microsoft_FStar_Parser_AST.mk_binder _114_135 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type (Some (Microsoft_FStar_Absyn_Syntax.Implicit)))))))
in (let t = (match ((let _114_136 = (unlabel t)
in _114_136.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Product (_43_583) -> begin
t
end
| _43_586 -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.App (((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.effect_Tot_lid)) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level), t, Microsoft_FStar_Parser_AST.Nothing))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
end)
in (let result = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((binders, t))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
in result)))
end)))

let rec uncurry = (fun ( bs ) ( t ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Product ((binders, t)) -> begin
(uncurry (Support.List.append bs binders) t)
end
| _43_596 -> begin
(bs, t)
end))

let rec is_app_pattern = (fun ( p ) -> (match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed ((p, _43_600)) -> begin
(is_app_pattern p)
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar (_43_606); Microsoft_FStar_Parser_AST.prange = _43_604}, _43_610)) -> begin
true
end
| _43_614 -> begin
false
end))

let rec destruct_app_pattern = (fun ( env ) ( is_top_level ) ( p ) -> (match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed ((p, t)) -> begin
(let _43_626 = (destruct_app_pattern env is_top_level p)
in (match (_43_626) with
| (name, args, _43_625) -> begin
(name, args, Some (t))
end))
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((id, _43_631)); Microsoft_FStar_Parser_AST.prange = _43_628}, args)) when is_top_level -> begin
(let _114_150 = (let _114_149 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in Support.Microsoft.FStar.Util.Inr (_114_149))
in (_114_150, args, None))
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((id, _43_642)); Microsoft_FStar_Parser_AST.prange = _43_639}, args)) -> begin
(Support.Microsoft.FStar.Util.Inl (id), args, None)
end
| _43_650 -> begin
(Support.All.failwith "Not an app pattern")
end))

type bnd =
| TBinder of (Microsoft_FStar_Absyn_Syntax.btvdef * Microsoft_FStar_Absyn_Syntax.knd * Microsoft_FStar_Absyn_Syntax.aqual)
| VBinder of (Microsoft_FStar_Absyn_Syntax.bvvdef * Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.aqual)
| LetBinder of (Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Absyn_Syntax.typ)

let is_TBinder = (fun ( _discr_ ) -> (match (_discr_) with
| TBinder (_) -> begin
true
end
| _ -> begin
false
end))

let is_VBinder = (fun ( _discr_ ) -> (match (_discr_) with
| VBinder (_) -> begin
true
end
| _ -> begin
false
end))

let is_LetBinder = (fun ( _discr_ ) -> (match (_discr_) with
| LetBinder (_) -> begin
true
end
| _ -> begin
false
end))

let ___TBinder____0 = (fun ( projectee ) -> (match (projectee) with
| TBinder (_43_653) -> begin
_43_653
end))

let ___VBinder____0 = (fun ( projectee ) -> (match (projectee) with
| VBinder (_43_656) -> begin
_43_656
end))

let ___LetBinder____0 = (fun ( projectee ) -> (match (projectee) with
| LetBinder (_43_659) -> begin
_43_659
end))

let binder_of_bnd = (fun ( _43_3 ) -> (match (_43_3) with
| TBinder ((a, k, aq)) -> begin
(Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)), aq)
end
| VBinder ((x, t, aq)) -> begin
(Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)), aq)
end
| _43_672 -> begin
(Support.All.failwith "Impossible")
end))

let as_binder = (fun ( env ) ( imp ) ( _43_4 ) -> (match (_43_4) with
| Support.Microsoft.FStar.Util.Inl ((None, k)) -> begin
(let _114_201 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (_114_201, env))
end
| Support.Microsoft.FStar.Util.Inr ((None, t)) -> begin
(let _114_202 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_114_202, env))
end
| Support.Microsoft.FStar.Util.Inl ((Some (a), k)) -> begin
(let _43_691 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_43_691) with
| (env, a) -> begin
((Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)), imp), env)
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _43_699 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_43_699) with
| (env, x) -> begin
((Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)), imp), env)
end))
end))

type env_t =
Microsoft_FStar_Parser_DesugarEnv.env

type lenv_t =
(Microsoft_FStar_Absyn_Syntax.btvdef, Microsoft_FStar_Absyn_Syntax.bvvdef) Support.Microsoft.FStar.Util.either list

let label_conjuncts = (fun ( tag ) ( polarity ) ( label_opt ) ( f ) -> (let label = (fun ( f ) -> (let msg = (match (label_opt) with
| Some (l) -> begin
l
end
| _43_709 -> begin
(let _114_213 = (Support.Microsoft.FStar.Range.string_of_range f.Microsoft_FStar_Parser_AST.range)
in (Support.Microsoft.FStar.Util.format2 "%s at %s" tag _114_213))
end)
in (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Labeled ((f, msg, polarity))) f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level)))
in (let rec aux = (fun ( f ) -> (match (f.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (g) -> begin
(let _114_217 = (let _114_216 = (aux g)
in Microsoft_FStar_Parser_AST.Paren (_114_216))
in (Microsoft_FStar_Parser_AST.mk_term _114_217 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Op (("/\\", f1::f2::[])) -> begin
(let _114_223 = (let _114_222 = (let _114_221 = (let _114_220 = (aux f1)
in (let _114_219 = (let _114_218 = (aux f2)
in (_114_218)::[])
in (_114_220)::_114_219))
in ("/\\", _114_221))
in Microsoft_FStar_Parser_AST.Op (_114_222))
in (Microsoft_FStar_Parser_AST.mk_term _114_223 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.If ((f1, f2, f3)) -> begin
(let _114_227 = (let _114_226 = (let _114_225 = (aux f2)
in (let _114_224 = (aux f3)
in (f1, _114_225, _114_224)))
in Microsoft_FStar_Parser_AST.If (_114_226))
in (Microsoft_FStar_Parser_AST.mk_term _114_227 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Abs ((binders, g)) -> begin
(let _114_230 = (let _114_229 = (let _114_228 = (aux g)
in (binders, _114_228))
in Microsoft_FStar_Parser_AST.Abs (_114_229))
in (Microsoft_FStar_Parser_AST.mk_term _114_230 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| _43_731 -> begin
(label f)
end))
in (aux f))))

let mk_lb = (fun ( _43_735 ) -> (match (_43_735) with
| (n, t, e) -> begin
{Microsoft_FStar_Absyn_Syntax.lbname = n; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = Microsoft_FStar_Absyn_Const.effect_ALL_lid; Microsoft_FStar_Absyn_Syntax.lbdef = e}
end))

let rec desugar_data_pat = (fun ( env ) ( p ) -> (let resolvex = (fun ( l ) ( e ) ( x ) -> (match ((Support.All.pipe_right l (Support.Microsoft.FStar.Util.find_opt (fun ( _43_5 ) -> (match (_43_5) with
| Support.Microsoft.FStar.Util.Inr (y) -> begin
(y.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText = x.Microsoft_FStar_Absyn_Syntax.idText)
end
| _43_746 -> begin
false
end))))) with
| Some (Support.Microsoft.FStar.Util.Inr (y)) -> begin
(l, e, y)
end
| _43_751 -> begin
(let _43_754 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding e x)
in (match (_43_754) with
| (e, x) -> begin
((Support.Microsoft.FStar.Util.Inr (x))::l, e, x)
end))
end))
in (let resolvea = (fun ( l ) ( e ) ( a ) -> (match ((Support.All.pipe_right l (Support.Microsoft.FStar.Util.find_opt (fun ( _43_6 ) -> (match (_43_6) with
| Support.Microsoft.FStar.Util.Inl (b) -> begin
(b.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText = a.Microsoft_FStar_Absyn_Syntax.idText)
end
| _43_763 -> begin
false
end))))) with
| Some (Support.Microsoft.FStar.Util.Inl (b)) -> begin
(l, e, b)
end
| _43_768 -> begin
(let _43_771 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding e a)
in (match (_43_771) with
| (e, a) -> begin
((Support.Microsoft.FStar.Util.Inl (a))::l, e, a)
end))
end))
in (let rec aux = (fun ( loc ) ( env ) ( p ) -> (let pos = (fun ( q ) -> (Microsoft_FStar_Absyn_Syntax.withinfo q None p.Microsoft_FStar_Parser_AST.prange))
in (let pos_r = (fun ( r ) ( q ) -> (Microsoft_FStar_Absyn_Syntax.withinfo q None r))
in (match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatOr ([]) -> begin
(Support.All.failwith "impossible")
end
| Microsoft_FStar_Parser_AST.PatOr (p::ps) -> begin
(let _43_793 = (aux loc env p)
in (match (_43_793) with
| (loc, env, var, p, _43_792) -> begin
(let _43_810 = (Support.List.fold_left (fun ( _43_797 ) ( p ) -> (match (_43_797) with
| (loc, env, ps) -> begin
(let _43_806 = (aux loc env p)
in (match (_43_806) with
| (loc, env, _43_802, p, _43_805) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_43_810) with
| (loc, env, ps) -> begin
(let pat = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_disj ((p)::(Support.List.rev ps))))
in (let _43_812 = (let _114_302 = (Microsoft_FStar_Absyn_Syntax.pat_vars pat)
in (Support.Prims.ignore _114_302))
in (loc, env, var, pat, false)))
end))
end))
end
| Microsoft_FStar_Parser_AST.PatAscribed ((p, t)) -> begin
(let p = (match ((is_kind env t)) with
| true -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatTvar (_43_819) -> begin
p
end
| Microsoft_FStar_Parser_AST.PatVar ((x, imp)) -> begin
(let _43_825 = p
in {Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatTvar ((x, imp)); Microsoft_FStar_Parser_AST.prange = _43_825.Microsoft_FStar_Parser_AST.prange})
end
| _43_828 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern", p.Microsoft_FStar_Parser_AST.prange))))
end)
end
| false -> begin
p
end)
in (let _43_835 = (aux loc env p)
in (match (_43_835) with
| (loc, env', binder, p, imp) -> begin
(let binder = (match (binder) with
| LetBinder (_43_837) -> begin
(Support.All.failwith "impossible")
end
| TBinder ((x, _43_841, aq)) -> begin
(let _114_304 = (let _114_303 = (desugar_kind env t)
in (x, _114_303, aq))
in TBinder (_114_304))
end
| VBinder ((x, _43_847, aq)) -> begin
(let t = (close_fun env t)
in (let _114_306 = (let _114_305 = (desugar_typ env t)
in (x, _114_305, aq))
in VBinder (_114_306)))
end)
in (loc, env', binder, p, imp))
end)))
end
| Microsoft_FStar_Parser_AST.PatTvar ((a, imp)) -> begin
(let aq = (match (imp) with
| true -> begin
Some (Microsoft_FStar_Absyn_Syntax.Implicit)
end
| false -> begin
None
end)
in (match ((a.Microsoft_FStar_Absyn_Syntax.idText = "\'_")) with
| true -> begin
(let a = (Support.All.pipe_left Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _114_307 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_twild ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a Microsoft_FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((a, Microsoft_FStar_Absyn_Syntax.kun, aq)), _114_307, imp)))
end
| false -> begin
(let _43_862 = (resolvea loc env a)
in (match (_43_862) with
| (loc, env, abvd) -> begin
(let _114_308 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_tvar ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s abvd Microsoft_FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((abvd, Microsoft_FStar_Absyn_Syntax.kun, aq)), _114_308, imp))
end))
end))
end
| Microsoft_FStar_Parser_AST.PatWild -> begin
(let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let y = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _114_309 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_wild ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s y Microsoft_FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _114_309, false))))
end
| Microsoft_FStar_Parser_AST.PatConst (c) -> begin
(let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _114_310 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_constant (c)))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _114_310, false)))
end
| Microsoft_FStar_Parser_AST.PatVar ((x, imp)) -> begin
(let aq = (match (imp) with
| true -> begin
Some (Microsoft_FStar_Absyn_Syntax.Implicit)
end
| false -> begin
None
end)
in (let _43_877 = (resolvex loc env x)
in (match (_43_877) with
| (loc, env, xbvd) -> begin
(let _114_311 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_var ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s xbvd Microsoft_FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((xbvd, Microsoft_FStar_Absyn_Syntax.tun, aq)), _114_311, imp))
end)))
end
| Microsoft_FStar_Parser_AST.PatName (l) -> begin
(let l = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _114_312 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), []))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _114_312, false))))
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatName (l); Microsoft_FStar_Parser_AST.prange = _43_883}, args)) -> begin
(let _43_905 = (Support.List.fold_right (fun ( arg ) ( _43_894 ) -> (match (_43_894) with
| (loc, env, args) -> begin
(let _43_901 = (aux loc env arg)
in (match (_43_901) with
| (loc, env, _43_898, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_43_905) with
| (loc, env, args) -> begin
(let l = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _114_315 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _114_315, false))))
end))
end
| Microsoft_FStar_Parser_AST.PatApp (_43_909) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern", p.Microsoft_FStar_Parser_AST.prange))))
end
| Microsoft_FStar_Parser_AST.PatList (pats) -> begin
(let _43_929 = (Support.List.fold_right (fun ( pat ) ( _43_917 ) -> (match (_43_917) with
| (loc, env, pats) -> begin
(let _43_925 = (aux loc env pat)
in (match (_43_925) with
| (loc, env, _43_921, pat, _43_924) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_43_929) with
| (loc, env, pats) -> begin
(let pat = (let _114_328 = (let _114_327 = (let _114_323 = (Support.Microsoft.FStar.Range.end_range p.Microsoft_FStar_Parser_AST.prange)
in (pos_r _114_323))
in (let _114_326 = (let _114_325 = (let _114_324 = (Microsoft_FStar_Absyn_Util.fv Microsoft_FStar_Absyn_Const.nil_lid)
in (_114_324, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), []))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_114_325))
in (Support.All.pipe_left _114_327 _114_326)))
in (Support.List.fold_right (fun ( hd ) ( tl ) -> (let r = (Support.Microsoft.FStar.Range.union_ranges hd.Microsoft_FStar_Absyn_Syntax.p tl.Microsoft_FStar_Absyn_Syntax.p)
in (let _114_322 = (let _114_321 = (let _114_320 = (Microsoft_FStar_Absyn_Util.fv Microsoft_FStar_Absyn_Const.cons_lid)
in (_114_320, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), ((hd, false))::((tl, false))::[]))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_114_321))
in (Support.All.pipe_left (pos_r r) _114_322)))) pats _114_328))
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), pat, false)))
end))
end
| Microsoft_FStar_Parser_AST.PatTuple ((args, dep)) -> begin
(let _43_955 = (Support.List.fold_left (fun ( _43_942 ) ( p ) -> (match (_43_942) with
| (loc, env, pats) -> begin
(let _43_951 = (aux loc env p)
in (match (_43_951) with
| (loc, env, _43_947, pat, _43_950) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_43_955) with
| (loc, env, args) -> begin
(let args = (Support.List.rev args)
in (let l = (match (dep) with
| true -> begin
(Microsoft_FStar_Absyn_Util.mk_dtuple_data_lid (Support.List.length args) p.Microsoft_FStar_Parser_AST.prange)
end
| false -> begin
(Microsoft_FStar_Absyn_Util.mk_tuple_data_lid (Support.List.length args) p.Microsoft_FStar_Parser_AST.prange)
end)
in (let constr = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (let l = (match (constr.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, _43_961)) -> begin
v
end
| _43_965 -> begin
(Support.All.failwith "impossible")
end)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _114_331 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _114_331, false)))))))
end))
end
| Microsoft_FStar_Parser_AST.PatRecord ([]) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern", p.Microsoft_FStar_Parser_AST.prange))))
end
| Microsoft_FStar_Parser_AST.PatRecord (fields) -> begin
(let _43_975 = (Support.List.hd fields)
in (match (_43_975) with
| (f, _43_974) -> begin
(let _43_979 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_43_979) with
| (record, _43_978) -> begin
(let fields = (Support.All.pipe_right fields (Support.List.map (fun ( _43_982 ) -> (match (_43_982) with
| (f, p) -> begin
(let _114_333 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in (_114_333, p))
end))))
in (let args = (Support.All.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map (fun ( _43_987 ) -> (match (_43_987) with
| (f, _43_986) -> begin
(match ((Support.All.pipe_right fields (Support.List.tryFind (fun ( _43_991 ) -> (match (_43_991) with
| (g, _43_990) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals f g)
end))))) with
| None -> begin
(Microsoft_FStar_Parser_AST.mk_pattern Microsoft_FStar_Parser_AST.PatWild p.Microsoft_FStar_Parser_AST.prange)
end
| Some ((_43_994, p)) -> begin
p
end)
end))))
in (let app = (Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatApp (((Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatName (record.Microsoft_FStar_Parser_DesugarEnv.constrname)) p.Microsoft_FStar_Parser_AST.prange), args))) p.Microsoft_FStar_Parser_AST.prange)
in (let _43_1006 = (aux loc env app)
in (match (_43_1006) with
| (env, e, b, p, _43_1005) -> begin
(let p = (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, _43_1009, args)) -> begin
(let _114_341 = (let _114_340 = (let _114_339 = (let _114_338 = (let _114_337 = (let _114_336 = (Support.All.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map Support.Prims.fst))
in (record.Microsoft_FStar_Parser_DesugarEnv.typename, _114_336))
in Microsoft_FStar_Absyn_Syntax.Record_ctor (_114_337))
in Some (_114_338))
in (fv, _114_339, args))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_114_340))
in (Support.All.pipe_left pos _114_341))
end
| _43_1014 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (let _43_1023 = (aux [] env p)
in (match (_43_1023) with
| (_43_1017, env, b, p, _43_1022) -> begin
(env, b, p)
end))))))
and desugar_binding_pat_maybe_top = (fun ( top ) ( env ) ( p ) -> (match (top) with
| true -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatVar ((x, _43_1029)) -> begin
(let _114_347 = (let _114_346 = (let _114_345 = (Microsoft_FStar_Parser_DesugarEnv.qualify env x)
in (_114_345, Microsoft_FStar_Absyn_Syntax.tun))
in LetBinder (_114_346))
in (env, _114_347, None))
end
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((x, _43_1036)); Microsoft_FStar_Parser_AST.prange = _43_1033}, t)) -> begin
(let _114_351 = (let _114_350 = (let _114_349 = (Microsoft_FStar_Parser_DesugarEnv.qualify env x)
in (let _114_348 = (desugar_typ env t)
in (_114_349, _114_348)))
in LetBinder (_114_350))
in (env, _114_351, None))
end
| _43_1044 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern at the top-level", p.Microsoft_FStar_Parser_AST.prange))))
end)
end
| false -> begin
(let _43_1048 = (desugar_data_pat env p)
in (match (_43_1048) with
| (env, binder, p) -> begin
(let p = (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_var (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_wild (_)) -> begin
None
end
| _43_1059 -> begin
Some (p)
end)
in (env, binder, p))
end))
end))
and desugar_binding_pat = (fun ( env ) ( p ) -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top = (fun ( _43_1063 ) ( env ) ( pat ) -> (let _43_1071 = (desugar_data_pat env pat)
in (match (_43_1071) with
| (env, _43_1069, pat) -> begin
(env, pat)
end)))
and desugar_match_pat = (fun ( env ) ( p ) -> (desugar_match_pat_maybe_top false env p))
and desugar_typ_or_exp = (fun ( env ) ( t ) -> (match ((is_type env t)) with
| true -> begin
(let _114_361 = (desugar_typ env t)
in Support.Microsoft.FStar.Util.Inl (_114_361))
end
| false -> begin
(let _114_362 = (desugar_exp env t)
in Support.Microsoft.FStar.Util.Inr (_114_362))
end))
and desugar_exp = (fun ( env ) ( e ) -> (desugar_exp_maybe_top false env e))
and desugar_exp_maybe_top = (fun ( top_level ) ( env ) ( top ) -> (let pos = (fun ( e ) -> (e None top.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( e ) -> (let _43_1085 = e
in {Microsoft_FStar_Absyn_Syntax.n = _43_1085.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _43_1085.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = top.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _43_1085.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _43_1085.Microsoft_FStar_Absyn_Syntax.uvs}))
in (match ((let _114_382 = (unparen top)
in _114_382.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Const (c) -> begin
(Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match ((op_as_vlid env (Support.List.length args) top.Microsoft_FStar_Parser_AST.range s)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat "Unexpected operator: " s), top.Microsoft_FStar_Parser_AST.range))))
end
| Some (l) -> begin
(let op = (let _114_385 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (Microsoft_FStar_Absyn_Util.fvar None l _114_385))
in (let args = (Support.All.pipe_right args (Support.List.map (fun ( t ) -> (let _114_387 = (desugar_typ_or_exp env t)
in (_114_387, None)))))
in (let _114_388 = (Microsoft_FStar_Absyn_Util.mk_exp_app op args)
in (Support.All.pipe_left setpos _114_388))))
end)
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) -> begin
(match ((l.Microsoft_FStar_Absyn_Syntax.str = "ref")) with
| true -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env Microsoft_FStar_Absyn_Const.alloc_lid)) with
| None -> begin
(let _114_391 = (let _114_390 = (let _114_389 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in ("Identifier \'ref\' not found; include lib/st.fst in your path", _114_389))
in Microsoft_FStar_Absyn_Syntax.Error (_114_390))
in (raise (_114_391)))
end
| Some (e) -> begin
(setpos e)
end)
end
| false -> begin
(let _114_392 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (Support.All.pipe_left setpos _114_392))
end)
end
| Microsoft_FStar_Parser_AST.Construct ((l, args)) -> begin
(let dt = (let _114_397 = (let _114_396 = (let _114_395 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (_114_395, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _114_396))
in (Support.All.pipe_left pos _114_397))
in (match (args) with
| [] -> begin
dt
end
| _43_1112 -> begin
(let args = (Support.List.map (fun ( _43_1115 ) -> (match (_43_1115) with
| (t, imp) -> begin
(let te = (desugar_typ_or_exp env t)
in (arg_withimp_e imp te))
end)) args)
in (let _114_402 = (let _114_401 = (let _114_400 = (let _114_399 = (Microsoft_FStar_Absyn_Util.mk_exp_app dt args)
in (_114_399, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_114_400))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _114_401))
in (Support.All.pipe_left setpos _114_402)))
end))
end
| Microsoft_FStar_Parser_AST.Abs ((binders, body)) -> begin
(let _43_1152 = (Support.List.fold_left (fun ( _43_1124 ) ( pat ) -> (match (_43_1124) with
| (env, ftvs) -> begin
(match (pat.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatTvar ((a, imp)); Microsoft_FStar_Parser_AST.prange = _43_1127}, t)) -> begin
(let ftvs = (let _114_405 = (free_type_vars env t)
in (Support.List.append _114_405 ftvs))
in (let _114_407 = (let _114_406 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (Support.All.pipe_left Support.Prims.fst _114_406))
in (_114_407, ftvs)))
end
| Microsoft_FStar_Parser_AST.PatTvar ((a, _43_1139)) -> begin
(let _114_409 = (let _114_408 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (Support.All.pipe_left Support.Prims.fst _114_408))
in (_114_409, ftvs))
end
| Microsoft_FStar_Parser_AST.PatAscribed ((_43_1143, t)) -> begin
(let _114_411 = (let _114_410 = (free_type_vars env t)
in (Support.List.append _114_410 ftvs))
in (env, _114_411))
end
| _43_1148 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_43_1152) with
| (_43_1150, ftv) -> begin
(let ftv = (sort_ftv ftv)
in (let binders = (let _114_413 = (Support.All.pipe_right ftv (Support.List.map (fun ( a ) -> (Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatTvar ((a, true))) top.Microsoft_FStar_Parser_AST.range))))
in (Support.List.append _114_413 binders))
in (let rec aux = (fun ( env ) ( bs ) ( sc_pat_opt ) ( _43_7 ) -> (match (_43_7) with
| [] -> begin
(let body = (desugar_exp env body)
in (let body = (match (sc_pat_opt) with
| Some ((sc, pat)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_match (sc, ((pat, None, body))::[]) None body.Microsoft_FStar_Absyn_Syntax.pos)
end
| None -> begin
body
end)
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs' ((Support.List.rev bs), body) None top.Microsoft_FStar_Parser_AST.range)))
end
| p::rest -> begin
(let _43_1175 = (desugar_binding_pat env p)
in (match (_43_1175) with
| (env, b, pat) -> begin
(let _43_1235 = (match (b) with
| LetBinder (_43_1177) -> begin
(Support.All.failwith "Impossible")
end
| TBinder ((a, k, aq)) -> begin
(let _114_422 = (binder_of_bnd b)
in (_114_422, sc_pat_opt))
end
| VBinder ((x, t, aq)) -> begin
(let b = (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)
in (let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _43_1192) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _114_424 = (let _114_423 = (Microsoft_FStar_Absyn_Util.bvar_to_exp b)
in (_114_423, p))
in Some (_114_424))
end
| (Some (p), Some ((sc, p'))) -> begin
(match ((sc.Microsoft_FStar_Absyn_Syntax.n, p'.Microsoft_FStar_Absyn_Syntax.v)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_43_1206), _43_1209) -> begin
(let tup = (Microsoft_FStar_Absyn_Util.mk_tuple_data_lid 2 top.Microsoft_FStar_Parser_AST.range)
in (let sc = (let _114_431 = (let _114_430 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) tup top.Microsoft_FStar_Parser_AST.range)
in (let _114_429 = (let _114_428 = (Microsoft_FStar_Absyn_Syntax.varg sc)
in (let _114_427 = (let _114_426 = (let _114_425 = (Microsoft_FStar_Absyn_Util.bvar_to_exp b)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.varg _114_425))
in (_114_426)::[])
in (_114_428)::_114_427))
in (_114_430, _114_429)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _114_431 None top.Microsoft_FStar_Parser_AST.range))
in (let p = (let _114_435 = (let _114_433 = (let _114_432 = (Microsoft_FStar_Absyn_Util.fv tup)
in (_114_432, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), ((p', false))::((p, false))::[]))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_114_433))
in (let _114_434 = (Support.Microsoft.FStar.Range.union_ranges p'.Microsoft_FStar_Absyn_Syntax.p p.Microsoft_FStar_Absyn_Syntax.p)
in (Microsoft_FStar_Absyn_Util.withinfo _114_435 None _114_434)))
in Some ((sc, p)))))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app ((_43_1215, args)), Microsoft_FStar_Absyn_Syntax.Pat_cons ((_43_1220, _43_1222, pats))) -> begin
(let tup = (Microsoft_FStar_Absyn_Util.mk_tuple_data_lid (1 + (Support.List.length args)) top.Microsoft_FStar_Parser_AST.range)
in (let sc = (let _114_441 = (let _114_440 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) tup top.Microsoft_FStar_Parser_AST.range)
in (let _114_439 = (let _114_438 = (let _114_437 = (let _114_436 = (Microsoft_FStar_Absyn_Util.bvar_to_exp b)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.varg _114_436))
in (_114_437)::[])
in (Support.List.append args _114_438))
in (_114_440, _114_439)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _114_441 None top.Microsoft_FStar_Parser_AST.range))
in (let p = (let _114_445 = (let _114_443 = (let _114_442 = (Microsoft_FStar_Absyn_Util.fv tup)
in (_114_442, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), (Support.List.append pats (((p, false))::[]))))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_114_443))
in (let _114_444 = (Support.Microsoft.FStar.Range.union_ranges p'.Microsoft_FStar_Absyn_Syntax.p p.Microsoft_FStar_Absyn_Syntax.p)
in (Microsoft_FStar_Absyn_Util.withinfo _114_445 None _114_444)))
in Some ((sc, p)))))
end
| _43_1231 -> begin
(Support.All.failwith "Impossible")
end)
end)
in ((Support.Microsoft.FStar.Util.Inr (b), aq), sc_pat_opt)))
end)
in (match (_43_1235) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| Microsoft_FStar_Parser_AST.App (({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Var (a); Microsoft_FStar_Parser_AST.range = _43_1239; Microsoft_FStar_Parser_AST.level = _43_1237}, arg, _43_1245)) when ((Microsoft_FStar_Absyn_Syntax.lid_equals a Microsoft_FStar_Absyn_Const.assert_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals a Microsoft_FStar_Absyn_Const.assume_lid)) -> begin
(let phi = (desugar_formula env arg)
in (let _114_456 = (let _114_455 = (let _114_454 = (let _114_448 = (Microsoft_FStar_Absyn_Syntax.range_of_lid a)
in (Microsoft_FStar_Absyn_Util.fvar None a _114_448))
in (let _114_453 = (let _114_452 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ phi)
in (let _114_451 = (let _114_450 = (let _114_449 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant Microsoft_FStar_Absyn_Syntax.Const_unit None top.Microsoft_FStar_Parser_AST.range)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.varg _114_449))
in (_114_450)::[])
in (_114_452)::_114_451))
in (_114_454, _114_453)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _114_455))
in (Support.All.pipe_left pos _114_456)))
end
| Microsoft_FStar_Parser_AST.App (_43_1250) -> begin
(let rec aux = (fun ( args ) ( e ) -> (match ((let _114_461 = (unparen e)
in _114_461.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((e, t, imp)) -> begin
(let arg = (let _114_462 = (desugar_typ_or_exp env t)
in (Support.All.pipe_left (arg_withimp_e imp) _114_462))
in (aux ((arg)::args) e))
end
| _43_1262 -> begin
(let head = (desugar_exp env e)
in (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (head, args))))
end))
in (aux [] top))
end
| Microsoft_FStar_Parser_AST.Seq ((t1, t2)) -> begin
(let _114_468 = (let _114_467 = (let _114_466 = (let _114_465 = (desugar_exp env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Let ((false, (((Microsoft_FStar_Parser_AST.mk_pattern Microsoft_FStar_Parser_AST.PatWild t1.Microsoft_FStar_Parser_AST.range), t1))::[], t2))) top.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Expr))
in (_114_465, Microsoft_FStar_Absyn_Syntax.Sequence))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_114_466))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _114_467))
in (Support.All.pipe_left setpos _114_468))
end
| Microsoft_FStar_Parser_AST.Let ((is_rec, (pat, _snd)::_tl, body)) -> begin
(let ds_let_rec = (fun ( _43_1278 ) -> (match (()) with
| () -> begin
(let bindings = ((pat, _snd))::_tl
in (let funs = (Support.All.pipe_right bindings (Support.List.map (fun ( _43_1282 ) -> (match (_43_1282) with
| (p, def) -> begin
(match ((is_app_pattern p)) with
| true -> begin
(let _114_472 = (destruct_app_pattern env top_level p)
in (_114_472, def))
end
| false -> begin
(match ((Microsoft_FStar_Parser_AST.un_function p def)) with
| Some ((p, def)) -> begin
(let _114_473 = (destruct_app_pattern env top_level p)
in (_114_473, def))
end
| _43_1288 -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((id, _43_1293)); Microsoft_FStar_Parser_AST.prange = _43_1290}, t)) -> begin
(match (top_level) with
| true -> begin
(let _114_476 = (let _114_475 = (let _114_474 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in Support.Microsoft.FStar.Util.Inr (_114_474))
in (_114_475, [], Some (t)))
in (_114_476, def))
end
| false -> begin
((Support.Microsoft.FStar.Util.Inl (id), [], Some (t)), def)
end)
end
| Microsoft_FStar_Parser_AST.PatVar ((id, _43_1302)) -> begin
(match (top_level) with
| true -> begin
(let _114_479 = (let _114_478 = (let _114_477 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in Support.Microsoft.FStar.Util.Inr (_114_477))
in (_114_478, [], None))
in (_114_479, def))
end
| false -> begin
((Support.Microsoft.FStar.Util.Inl (id), [], None), def)
end)
end
| _43_1306 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected let binding", p.Microsoft_FStar_Parser_AST.prange))))
end)
end)
end)
end))))
in (let _43_1332 = (Support.List.fold_left (fun ( _43_1310 ) ( _43_1319 ) -> (match ((_43_1310, _43_1319)) with
| ((env, fnames), ((f, _43_1313, _43_1315), _43_1318)) -> begin
(let _43_1329 = (match (f) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(let _43_1324 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_43_1324) with
| (env, xx) -> begin
(env, Support.Microsoft.FStar.Util.Inl (xx))
end))
end
| Support.Microsoft.FStar.Util.Inr (l) -> begin
(let _114_482 = (Microsoft_FStar_Parser_DesugarEnv.push_rec_binding env (Microsoft_FStar_Parser_DesugarEnv.Binding_let (l)))
in (_114_482, Support.Microsoft.FStar.Util.Inr (l)))
end)
in (match (_43_1329) with
| (env, lbname) -> begin
(env, (lbname)::fnames)
end))
end)) (env, []) funs)
in (match (_43_1332) with
| (env', fnames) -> begin
(let fnames = (Support.List.rev fnames)
in (let desugar_one_def = (fun ( env ) ( lbname ) ( _43_1343 ) -> (match (_43_1343) with
| ((_43_1338, args, result_t), def) -> begin
(let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _114_489 = (Support.Microsoft.FStar.Range.union_ranges t.Microsoft_FStar_Parser_AST.range def.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Ascribed ((def, t))) _114_489 Microsoft_FStar_Parser_AST.Expr))
end)
in (let def = (match (args) with
| [] -> begin
def
end
| _43_1350 -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.un_curry_abs args def) top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level)
end)
in (let body = (desugar_exp env def)
in (mk_lb (lbname, Microsoft_FStar_Absyn_Syntax.tun, body)))))
end))
in (let lbs = (Support.List.map2 (desugar_one_def (match (is_rec) with
| true -> begin
env'
end
| false -> begin
env
end)) fnames funs)
in (let body = (desugar_exp env' body)
in (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), body)))))))
end))))
end))
in (let ds_non_rec = (fun ( pat ) ( t1 ) ( t2 ) -> (let t1 = (desugar_exp env t1)
in (let _43_1363 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_43_1363) with
| (env, binder, pat) -> begin
(match (binder) with
| TBinder (_43_1365) -> begin
(Support.All.failwith "Unexpected type binder in let")
end
| LetBinder ((l, t)) -> begin
(let body = (desugar_exp env t2)
in (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((false, ({Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = Microsoft_FStar_Absyn_Const.effect_ALL_lid; Microsoft_FStar_Absyn_Syntax.lbdef = t1})::[]), body))))
end
| VBinder ((x, t, _43_1375)) -> begin
(let body = (desugar_exp env t2)
in (let body = (match (pat) with
| (None) | (Some ({Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_wild (_); Microsoft_FStar_Absyn_Syntax.sort = _; Microsoft_FStar_Absyn_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _114_501 = (let _114_500 = (Microsoft_FStar_Absyn_Util.bvd_to_exp x t)
in (_114_500, ((pat, None, body))::[]))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _114_501 None body.Microsoft_FStar_Absyn_Syntax.pos))
end)
in (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((false, ((mk_lb (Support.Microsoft.FStar.Util.Inl (x), t, t1)))::[]), body)))))
end)
end))))
in (match ((is_rec || (is_app_pattern pat))) with
| true -> begin
(ds_let_rec ())
end
| false -> begin
(ds_non_rec pat _snd body)
end)))
end
| Microsoft_FStar_Parser_AST.If ((t1, t2, t3)) -> begin
(let _114_514 = (let _114_513 = (let _114_512 = (desugar_exp env t1)
in (let _114_511 = (let _114_510 = (let _114_506 = (desugar_exp env t2)
in ((Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (true))) None t2.Microsoft_FStar_Parser_AST.range), None, _114_506))
in (let _114_509 = (let _114_508 = (let _114_507 = (desugar_exp env t3)
in ((Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (false))) None t3.Microsoft_FStar_Parser_AST.range), None, _114_507))
in (_114_508)::[])
in (_114_510)::_114_509))
in (_114_512, _114_511)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _114_513))
in (Support.All.pipe_left pos _114_514))
end
| Microsoft_FStar_Parser_AST.TryWith ((e, branches)) -> begin
(let r = top.Microsoft_FStar_Parser_AST.range
in (let handler = (Microsoft_FStar_Parser_AST.mk_function branches r r)
in (let body = (Microsoft_FStar_Parser_AST.mk_function ((((Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatConst (Microsoft_FStar_Absyn_Syntax.Const_unit)) r), None, e))::[]) r r)
in (let a1 = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.App (((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Var (Microsoft_FStar_Absyn_Const.try_with_lid)) r top.Microsoft_FStar_Parser_AST.level), body, Microsoft_FStar_Parser_AST.Nothing))) r top.Microsoft_FStar_Parser_AST.level)
in (let a2 = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.App ((a1, handler, Microsoft_FStar_Parser_AST.Nothing))) r top.Microsoft_FStar_Parser_AST.level)
in (desugar_exp env a2))))))
end
| Microsoft_FStar_Parser_AST.Match ((e, branches)) -> begin
(let desugar_branch = (fun ( _43_1414 ) -> (match (_43_1414) with
| (pat, wopt, b) -> begin
(let _43_1417 = (desugar_match_pat env pat)
in (match (_43_1417) with
| (env, pat) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _114_517 = (desugar_exp env e)
in Some (_114_517))
end)
in (let b = (desugar_exp env b)
in (pat, wopt, b)))
end))
end))
in (let _114_523 = (let _114_522 = (let _114_521 = (desugar_exp env e)
in (let _114_520 = (Support.List.map desugar_branch branches)
in (_114_521, _114_520)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _114_522))
in (Support.All.pipe_left pos _114_523)))
end
| Microsoft_FStar_Parser_AST.Ascribed ((e, t)) -> begin
(let _114_529 = (let _114_528 = (let _114_527 = (desugar_exp env e)
in (let _114_526 = (desugar_typ env t)
in (_114_527, _114_526, None)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed _114_528))
in (Support.All.pipe_left pos _114_529))
end
| Microsoft_FStar_Parser_AST.Record ((_43_1428, [])) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected empty record", top.Microsoft_FStar_Parser_AST.range))))
end
| Microsoft_FStar_Parser_AST.Record ((eopt, fields)) -> begin
(let _43_1439 = (Support.List.hd fields)
in (match (_43_1439) with
| (f, _43_1438) -> begin
(let qfn = (fun ( g ) -> (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append f.Microsoft_FStar_Absyn_Syntax.ns ((g)::[]))))
in (let _43_1445 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_43_1445) with
| (record, _43_1444) -> begin
(let get_field = (fun ( xopt ) ( f ) -> (let fn = f.Microsoft_FStar_Absyn_Syntax.ident
in (let found = (Support.All.pipe_right fields (Support.Microsoft.FStar.Util.find_opt (fun ( _43_1453 ) -> (match (_43_1453) with
| (g, _43_1452) -> begin
(let gn = g.Microsoft_FStar_Absyn_Syntax.ident
in (fn.Microsoft_FStar_Absyn_Syntax.idText = gn.Microsoft_FStar_Absyn_Syntax.idText))
end))))
in (match (found) with
| Some ((_43_1457, e)) -> begin
(let _114_537 = (qfn fn)
in (_114_537, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _114_541 = (let _114_540 = (let _114_539 = (let _114_538 = (Microsoft_FStar_Absyn_Syntax.text_of_lid f)
in (Support.Microsoft.FStar.Util.format1 "Field %s is missing" _114_538))
in (_114_539, top.Microsoft_FStar_Parser_AST.range))
in Microsoft_FStar_Absyn_Syntax.Error (_114_540))
in (raise (_114_541)))
end
| Some (x) -> begin
(let _114_542 = (qfn fn)
in (_114_542, (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Project ((x, f))) x.Microsoft_FStar_Parser_AST.range x.Microsoft_FStar_Parser_AST.level)))
end)
end))))
in (let recterm = (match (eopt) with
| None -> begin
(let _114_547 = (let _114_546 = (Support.All.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map (fun ( _43_1469 ) -> (match (_43_1469) with
| (f, _43_1468) -> begin
(let _114_545 = (let _114_544 = (get_field None f)
in (Support.All.pipe_left Support.Prims.snd _114_544))
in (_114_545, Microsoft_FStar_Parser_AST.Nothing))
end))))
in (record.Microsoft_FStar_Parser_DesugarEnv.constrname, _114_546))
in Microsoft_FStar_Parser_AST.Construct (_114_547))
end
| Some (e) -> begin
(let x = (Microsoft_FStar_Absyn_Util.genident (Some (e.Microsoft_FStar_Parser_AST.range)))
in (let xterm = (let _114_549 = (let _114_548 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((x)::[]))
in Microsoft_FStar_Parser_AST.Var (_114_548))
in (Microsoft_FStar_Parser_AST.mk_term _114_549 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr))
in (let record = (let _114_552 = (let _114_551 = (Support.All.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map (fun ( _43_1477 ) -> (match (_43_1477) with
| (f, _43_1476) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _114_551))
in Microsoft_FStar_Parser_AST.Record (_114_552))
in Microsoft_FStar_Parser_AST.Let ((false, (((Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatVar ((x, false))) x.Microsoft_FStar_Absyn_Syntax.idRange), e))::[], (Microsoft_FStar_Parser_AST.mk_term record top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))))))
end)
in (let recterm = (Microsoft_FStar_Parser_AST.mk_term recterm top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level)
in (let e = (desugar_exp env recterm)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _43_1500)); Microsoft_FStar_Absyn_Syntax.tk = _43_1497; Microsoft_FStar_Absyn_Syntax.pos = _43_1495; Microsoft_FStar_Absyn_Syntax.fvs = _43_1493; Microsoft_FStar_Absyn_Syntax.uvs = _43_1491}, args)); Microsoft_FStar_Absyn_Syntax.tk = _43_1489; Microsoft_FStar_Absyn_Syntax.pos = _43_1487; Microsoft_FStar_Absyn_Syntax.fvs = _43_1485; Microsoft_FStar_Absyn_Syntax.uvs = _43_1483}, Microsoft_FStar_Absyn_Syntax.Data_app))) -> begin
(let e = (let _114_562 = (let _114_561 = (let _114_560 = (let _114_559 = (let _114_558 = (let _114_557 = (let _114_556 = (let _114_555 = (Support.All.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map Support.Prims.fst))
in (record.Microsoft_FStar_Parser_DesugarEnv.typename, _114_555))
in Microsoft_FStar_Absyn_Syntax.Record_ctor (_114_556))
in Some (_114_557))
in (fv, _114_558))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _114_559 None e.Microsoft_FStar_Absyn_Syntax.pos))
in (_114_560, args))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _114_561))
in (Support.All.pipe_left pos _114_562))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Data_app)))))
end
| _43_1514 -> begin
e
end)))))
end)))
end))
end
| Microsoft_FStar_Parser_AST.Project ((e, f)) -> begin
(let _43_1522 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_43_1522) with
| (_43_1520, fieldname) -> begin
(let e = (desugar_exp env e)
in (let fn = (let _43_1527 = (Support.Microsoft.FStar.Util.prefix fieldname.Microsoft_FStar_Absyn_Syntax.ns)
in (match (_43_1527) with
| (ns, _43_1526) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append ns ((f.Microsoft_FStar_Absyn_Syntax.ident)::[])))
end))
in (let _114_570 = (let _114_569 = (let _114_568 = (let _114_565 = (Microsoft_FStar_Absyn_Syntax.range_of_lid f)
in (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Record_projector (fn))) fieldname _114_565))
in (let _114_567 = (let _114_566 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_114_566)::[])
in (_114_568, _114_567)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _114_569))
in (Support.All.pipe_left pos _114_570))))
end))
end
| Microsoft_FStar_Parser_AST.Paren (e) -> begin
(desugar_exp env e)
end
| _43_1532 -> begin
(Microsoft_FStar_Parser_AST.error "Unexpected term" top top.Microsoft_FStar_Parser_AST.range)
end))))
and desugar_typ = (fun ( env ) ( top ) -> (let wpos = (fun ( t ) -> (t None top.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( t ) -> (let _43_1539 = t
in {Microsoft_FStar_Absyn_Syntax.n = _43_1539.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _43_1539.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = top.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _43_1539.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _43_1539.Microsoft_FStar_Absyn_Syntax.uvs}))
in (let top = (unparen top)
in (let head_and_args = (fun ( t ) -> (let rec aux = (fun ( args ) ( t ) -> (match ((let _114_593 = (unparen t)
in _114_593.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((t, arg, imp)) -> begin
(aux (((arg, imp))::args) t)
end
| Microsoft_FStar_Parser_AST.Construct ((l, args')) -> begin
({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Name (l); Microsoft_FStar_Parser_AST.range = t.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Parser_AST.level = t.Microsoft_FStar_Parser_AST.level}, (Support.List.append args' args))
end
| _43_1557 -> begin
(t, args)
end))
in (aux [] t)))
in (match (top.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Wild -> begin
(setpos Microsoft_FStar_Absyn_Syntax.tun)
end
| Microsoft_FStar_Parser_AST.Requires ((t, lopt)) -> begin
(let t = (label_conjuncts "pre-condition" true lopt t)
in (match ((is_type env t)) with
| true -> begin
(desugar_typ env t)
end
| false -> begin
(let _114_594 = (desugar_exp env t)
in (Support.All.pipe_right _114_594 Microsoft_FStar_Absyn_Util.b2t))
end))
end
| Microsoft_FStar_Parser_AST.Ensures ((t, lopt)) -> begin
(let t = (label_conjuncts "post-condition" false lopt t)
in (match ((is_type env t)) with
| true -> begin
(desugar_typ env t)
end
| false -> begin
(let _114_595 = (desugar_exp env t)
in (Support.All.pipe_right _114_595 Microsoft_FStar_Absyn_Util.b2t))
end))
end
| Microsoft_FStar_Parser_AST.Op (("*", t1::_43_1571::[])) -> begin
(match ((is_type env t1)) with
| true -> begin
(let rec flatten = (fun ( t ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Op (("*", t1::t2::[])) -> begin
(let rest = (flatten t2)
in (t1)::rest)
end
| _43_1586 -> begin
(t)::[]
end))
in (let targs = (let _114_600 = (flatten top)
in (Support.All.pipe_right _114_600 (Support.List.map (fun ( t ) -> (let _114_599 = (desugar_typ env t)
in (Microsoft_FStar_Absyn_Syntax.targ _114_599))))))
in (let tup = (let _114_601 = (Microsoft_FStar_Absyn_Util.mk_tuple_lid (Support.List.length targs) top.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) _114_601))
in (Support.All.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))))
end
| false -> begin
(let _114_607 = (let _114_606 = (let _114_605 = (let _114_604 = (Microsoft_FStar_Parser_AST.term_to_string t1)
in (Support.Microsoft.FStar.Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _114_604))
in (_114_605, top.Microsoft_FStar_Parser_AST.range))
in Microsoft_FStar_Absyn_Syntax.Error (_114_606))
in (raise (_114_607)))
end)
end
| Microsoft_FStar_Parser_AST.Op (("=!=", args)) -> begin
(desugar_typ env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Op (("~", ((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Op (("==", args))) top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))::[]))) top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match ((op_as_tylid env (Support.List.length args) top.Microsoft_FStar_Parser_AST.range s)) with
| None -> begin
(let _114_608 = (desugar_exp env top)
in (Support.All.pipe_right _114_608 Microsoft_FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(let args = (Support.List.map (fun ( t ) -> (let _114_610 = (desugar_typ_or_exp env t)
in (Support.All.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _114_610))) args)
in (let _114_611 = (Microsoft_FStar_Absyn_Util.ftv l Microsoft_FStar_Absyn_Syntax.kun)
in (Microsoft_FStar_Absyn_Util.mk_typ_app _114_611 args)))
end)
end
| Microsoft_FStar_Parser_AST.Tvar (a) -> begin
(let _114_612 = (Microsoft_FStar_Parser_DesugarEnv.fail_or2 (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (Support.All.pipe_left setpos _114_612))
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) when ((Support.List.length l.Microsoft_FStar_Absyn_Syntax.ns) = 0) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env l.Microsoft_FStar_Absyn_Syntax.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _114_613 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (Support.All.pipe_left setpos _114_613))
end)
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) -> begin
(let l = (Microsoft_FStar_Absyn_Util.set_lid_range l top.Microsoft_FStar_Parser_AST.range)
in (let _114_614 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (Support.All.pipe_left setpos _114_614)))
end
| Microsoft_FStar_Parser_AST.Construct ((l, args)) -> begin
(let t = (let _114_615 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (Support.All.pipe_left setpos _114_615))
in (let args = (Support.List.map (fun ( _43_1622 ) -> (match (_43_1622) with
| (t, imp) -> begin
(let _114_617 = (desugar_typ_or_exp env t)
in (Support.All.pipe_left (arg_withimp_t imp) _114_617))
end)) args)
in (Microsoft_FStar_Absyn_Util.mk_typ_app t args)))
end
| Microsoft_FStar_Parser_AST.Abs ((binders, body)) -> begin
(let rec aux = (fun ( env ) ( bs ) ( _43_8 ) -> (match (_43_8) with
| [] -> begin
(let body = (desugar_typ env body)
in (Support.All.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam ((Support.List.rev bs), body))))
end
| hd::tl -> begin
(let _43_1640 = (desugar_binding_pat env hd)
in (match (_43_1640) with
| (env, bnd, pat) -> begin
(match (pat) with
| Some (q) -> begin
(let _114_629 = (let _114_628 = (let _114_627 = (let _114_626 = (Microsoft_FStar_Absyn_Print.pat_to_string q)
in (Support.Microsoft.FStar.Util.format1 "Pattern matching at the type level is not supported; got %s\n" _114_626))
in (_114_627, hd.Microsoft_FStar_Parser_AST.prange))
in Microsoft_FStar_Absyn_Syntax.Error (_114_628))
in (raise (_114_629)))
end
| None -> begin
(let b = (binder_of_bnd bnd)
in (aux env ((b)::bs) tl))
end)
end))
end))
in (aux env [] binders))
end
| Microsoft_FStar_Parser_AST.App (_43_1646) -> begin
(let rec aux = (fun ( args ) ( e ) -> (match ((let _114_634 = (unparen e)
in _114_634.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((e, arg, imp)) -> begin
(let arg = (let _114_635 = (desugar_typ_or_exp env arg)
in (Support.All.pipe_left (arg_withimp_t imp) _114_635))
in (aux ((arg)::args) e))
end
| _43_1658 -> begin
(let head = (desugar_typ env e)
in (Support.All.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (head, args))))
end))
in (aux [] top))
end
| Microsoft_FStar_Parser_AST.Product (([], t)) -> begin
(Support.All.failwith "Impossible: product with no binders")
end
| Microsoft_FStar_Parser_AST.Product ((binders, t)) -> begin
(let _43_1670 = (uncurry binders t)
in (match (_43_1670) with
| (bs, t) -> begin
(let rec aux = (fun ( env ) ( bs ) ( _43_9 ) -> (match (_43_9) with
| [] -> begin
(let cod = (desugar_comp top.Microsoft_FStar_Parser_AST.range true env t)
in (Support.All.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun ((Support.List.rev bs), cod))))
end
| hd::tl -> begin
(let mlenv = (Microsoft_FStar_Parser_DesugarEnv.default_ml env)
in (let bb = (desugar_binder mlenv hd)
in (let _43_1684 = (as_binder env hd.Microsoft_FStar_Parser_AST.aqual bb)
in (match (_43_1684) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| Microsoft_FStar_Parser_AST.Refine ((b, f)) -> begin
(match ((desugar_exp_binder env b)) with
| (None, _43_1691) -> begin
(Support.All.failwith "Missing binder in refinement")
end
| b -> begin
(let _43_1705 = (match ((as_binder env None (Support.Microsoft.FStar.Util.Inr (b)))) with
| ((Support.Microsoft.FStar.Util.Inr (x), _43_1697), env) -> begin
(x, env)
end
| _43_1702 -> begin
(Support.All.failwith "impossible")
end)
in (match (_43_1705) with
| (b, env) -> begin
(let f = (match ((is_type env f)) with
| true -> begin
(desugar_formula env f)
end
| false -> begin
(let _114_646 = (desugar_exp env f)
in (Support.All.pipe_right _114_646 Microsoft_FStar_Absyn_Util.b2t))
end)
in (Support.All.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (b, f))))
end))
end)
end
| (Microsoft_FStar_Parser_AST.NamedTyp ((_, t))) | (Microsoft_FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| Microsoft_FStar_Parser_AST.Ascribed ((t, k)) -> begin
(let _114_654 = (let _114_653 = (let _114_652 = (desugar_typ env t)
in (let _114_651 = (desugar_kind env k)
in (_114_652, _114_651)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed' _114_653))
in (Support.All.pipe_left wpos _114_654))
end
| Microsoft_FStar_Parser_AST.Sum ((binders, t)) -> begin
(let _43_1739 = (Support.List.fold_left (fun ( _43_1724 ) ( b ) -> (match (_43_1724) with
| (env, tparams, typs) -> begin
(let _43_1728 = (desugar_exp_binder env b)
in (match (_43_1728) with
| (xopt, t) -> begin
(let _43_1734 = (match (xopt) with
| None -> begin
(let _114_657 = (Microsoft_FStar_Absyn_Util.new_bvd (Some (top.Microsoft_FStar_Parser_AST.range)))
in (env, _114_657))
end
| Some (x) -> begin
(Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_43_1734) with
| (env, x) -> begin
(let _114_661 = (let _114_660 = (let _114_659 = (let _114_658 = (Microsoft_FStar_Absyn_Util.close_with_lam tparams t)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _114_658))
in (_114_659)::[])
in (Support.List.append typs _114_660))
in (env, (Support.List.append tparams (((Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)), None))::[])), _114_661))
end))
end))
end)) (env, [], []) (Support.List.append binders (((Microsoft_FStar_Parser_AST.mk_binder (Microsoft_FStar_Parser_AST.NoName (t)) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Type None))::[])))
in (match (_43_1739) with
| (env, _43_1737, targs) -> begin
(let tup = (let _114_662 = (Microsoft_FStar_Absyn_Util.mk_dtuple_lid (Support.List.length targs) top.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) _114_662))
in (Support.All.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))
end))
end
| Microsoft_FStar_Parser_AST.Record (_43_1742) -> begin
(Support.All.failwith "Unexpected record type")
end
| (Microsoft_FStar_Parser_AST.If (_)) | (Microsoft_FStar_Parser_AST.Labeled (_)) -> begin
(desugar_formula env top)
end
| _43_1751 when (top.Microsoft_FStar_Parser_AST.level = Microsoft_FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _43_1753 -> begin
(Microsoft_FStar_Parser_AST.error "Expected a type" top top.Microsoft_FStar_Parser_AST.range)
end))))))
and desugar_comp = (fun ( r ) ( default_ok ) ( env ) ( t ) -> (let fail = (fun ( msg ) -> (raise (Microsoft_FStar_Absyn_Syntax.Error ((msg, r)))))
in (let pre_process_comp_typ = (fun ( t ) -> (let _43_1764 = (head_and_args t)
in (match (_43_1764) with
| (head, args) -> begin
(match (head.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Name (lemma) when (lemma.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "Lemma") -> begin
(let unit = ((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.unit_lid)) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Type), Microsoft_FStar_Parser_AST.Nothing)
in (let nil_pat = ((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.nil_lid)) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Expr), Microsoft_FStar_Parser_AST.Nothing)
in (let _43_1790 = (Support.All.pipe_right args (Support.List.partition (fun ( _43_1772 ) -> (match (_43_1772) with
| (arg, _43_1771) -> begin
(match ((let _114_674 = (unparen arg)
in _114_674.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App (({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Var (d); Microsoft_FStar_Parser_AST.range = _43_1776; Microsoft_FStar_Parser_AST.level = _43_1774}, _43_1781, _43_1783)) -> begin
(d.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "decreases")
end
| _43_1787 -> begin
false
end)
end))))
in (match (_43_1790) with
| (decreases_clause, args) -> begin
(let args = (match (args) with
| [] -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Not enough arguments to \'Lemma\'", t.Microsoft_FStar_Parser_AST.range))))
end
| ens::[] -> begin
(let req_true = ((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Requires (((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.true_lid)) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Formula), None))) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Type), Microsoft_FStar_Parser_AST.Nothing)
in (unit)::(req_true)::(ens)::(nil_pat)::[])
end
| req::ens::[] -> begin
(unit)::(req)::(ens)::(nil_pat)::[]
end
| more -> begin
(unit)::more
end)
in (let t = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Construct ((lemma, (Support.List.append args decreases_clause)))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
in (desugar_typ env t)))
end))))
end
| Microsoft_FStar_Parser_AST.Name (tot) when (((tot.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "Tot") && (not ((Microsoft_FStar_Parser_DesugarEnv.is_effect_name env Microsoft_FStar_Absyn_Const.effect_Tot_lid)))) && (let _114_675 = (Microsoft_FStar_Parser_DesugarEnv.current_module env)
in (Microsoft_FStar_Absyn_Syntax.lid_equals _114_675 Microsoft_FStar_Absyn_Const.prims_lid))) -> begin
(let args = (Support.List.map (fun ( _43_1805 ) -> (match (_43_1805) with
| (t, imp) -> begin
(let _114_677 = (desugar_typ_or_exp env t)
in (Support.All.pipe_left (arg_withimp_t imp) _114_677))
end)) args)
in (let _114_678 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.effect_Tot_lid Microsoft_FStar_Absyn_Syntax.kun)
in (Microsoft_FStar_Absyn_Util.mk_typ_app _114_678 args)))
end
| _43_1808 -> begin
(desugar_typ env t)
end)
end)))
in (let t = (pre_process_comp_typ t)
in (let _43_1812 = (Microsoft_FStar_Absyn_Util.head_and_args t)
in (match (_43_1812) with
| (head, args) -> begin
(match ((let _114_680 = (let _114_679 = (Microsoft_FStar_Absyn_Util.compress_typ head)
in _114_679.Microsoft_FStar_Absyn_Syntax.n)
in (_114_680, args))) with
| (Microsoft_FStar_Absyn_Syntax.Typ_const (eff), (Support.Microsoft.FStar.Util.Inl (result_typ), _43_1819)::rest) -> begin
(let _43_1859 = (Support.All.pipe_right rest (Support.List.partition (fun ( _43_10 ) -> (match (_43_10) with
| (Support.Microsoft.FStar.Util.Inr (_43_1825), _43_1828) -> begin
false
end
| (Support.Microsoft.FStar.Util.Inl (t), _43_1833) -> begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (fv); Microsoft_FStar_Absyn_Syntax.tk = _43_1842; Microsoft_FStar_Absyn_Syntax.pos = _43_1840; Microsoft_FStar_Absyn_Syntax.fvs = _43_1838; Microsoft_FStar_Absyn_Syntax.uvs = _43_1836}, (Support.Microsoft.FStar.Util.Inr (_43_1847), _43_1850)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.decreases_lid)
end
| _43_1856 -> begin
false
end)
end))))
in (match (_43_1859) with
| (dec, rest) -> begin
(let decreases_clause = (Support.All.pipe_right dec (Support.List.map (fun ( _43_11 ) -> (match (_43_11) with
| (Support.Microsoft.FStar.Util.Inl (t), _43_1864) -> begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((_43_1867, (Support.Microsoft.FStar.Util.Inr (arg), _43_1871)::[])) -> begin
Microsoft_FStar_Absyn_Syntax.DECREASES (arg)
end
| _43_1877 -> begin
(Support.All.failwith "impos")
end)
end
| _43_1879 -> begin
(Support.All.failwith "impos")
end))))
in (match (((Microsoft_FStar_Parser_DesugarEnv.is_effect_name env eff.Microsoft_FStar_Absyn_Syntax.v) || (Microsoft_FStar_Absyn_Syntax.lid_equals eff.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.effect_Tot_lid))) with
| true -> begin
(match (((Microsoft_FStar_Absyn_Syntax.lid_equals eff.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.effect_Tot_lid) && ((Support.List.length decreases_clause) = 0))) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Total result_typ)
end
| false -> begin
(let flags = (match ((Microsoft_FStar_Absyn_Syntax.lid_equals eff.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.effect_Lemma_lid)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.LEMMA)::[]
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals eff.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.effect_Tot_lid)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.TOTAL)::[]
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals eff.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.effect_ML_lid)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.MLEFFECT)::[]
end
| false -> begin
[]
end)
end)
end)
in (Microsoft_FStar_Absyn_Syntax.mk_Comp {Microsoft_FStar_Absyn_Syntax.effect_name = eff.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.result_typ = result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = rest; Microsoft_FStar_Absyn_Syntax.flags = (Support.List.append flags decreases_clause)}))
end)
end
| false -> begin
(match (default_ok) with
| true -> begin
(env.Microsoft_FStar_Parser_DesugarEnv.default_result_effect t r)
end
| false -> begin
(let _114_684 = (let _114_683 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "%s is not an effect" _114_683))
in (fail _114_684))
end)
end))
end))
end
| _43_1883 -> begin
(match (default_ok) with
| true -> begin
(env.Microsoft_FStar_Parser_DesugarEnv.default_result_effect t r)
end
| false -> begin
(let _114_686 = (let _114_685 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "%s is not an effect" _114_685))
in (fail _114_686))
end)
end)
end))))))
and desugar_kind = (fun ( env ) ( k ) -> (let pos = (fun ( f ) -> (f k.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( kk ) -> (let _43_1890 = kk
in {Microsoft_FStar_Absyn_Syntax.n = _43_1890.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _43_1890.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = k.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _43_1890.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _43_1890.Microsoft_FStar_Absyn_Syntax.uvs}))
in (let k = (unparen k)
in (match (k.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Name ({Microsoft_FStar_Absyn_Syntax.ns = _43_1899; Microsoft_FStar_Absyn_Syntax.ident = _43_1897; Microsoft_FStar_Absyn_Syntax.nsstr = _43_1895; Microsoft_FStar_Absyn_Syntax.str = "Type"}) -> begin
(setpos Microsoft_FStar_Absyn_Syntax.mk_Kind_type)
end
| Microsoft_FStar_Parser_AST.Name ({Microsoft_FStar_Absyn_Syntax.ns = _43_1908; Microsoft_FStar_Absyn_Syntax.ident = _43_1906; Microsoft_FStar_Absyn_Syntax.nsstr = _43_1904; Microsoft_FStar_Absyn_Syntax.str = "Effect"}) -> begin
(setpos Microsoft_FStar_Absyn_Syntax.mk_Kind_effect)
end
| Microsoft_FStar_Parser_AST.Name (l) -> begin
(match ((let _114_698 = (Microsoft_FStar_Parser_DesugarEnv.qualify_lid env l)
in (Microsoft_FStar_Parser_DesugarEnv.find_kind_abbrev env _114_698))) with
| Some (l) -> begin
(Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev ((l, []), Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown)))
end
| _43_1916 -> begin
(Microsoft_FStar_Parser_AST.error "Unexpected term where kind was expected" k k.Microsoft_FStar_Parser_AST.range)
end)
end
| Microsoft_FStar_Parser_AST.Wild -> begin
(setpos Microsoft_FStar_Absyn_Syntax.kun)
end
| Microsoft_FStar_Parser_AST.Product ((bs, k)) -> begin
(let _43_1924 = (uncurry bs k)
in (match (_43_1924) with
| (bs, k) -> begin
(let rec aux = (fun ( env ) ( bs ) ( _43_12 ) -> (match (_43_12) with
| [] -> begin
(let _114_709 = (let _114_708 = (let _114_707 = (desugar_kind env k)
in ((Support.List.rev bs), _114_707))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _114_708))
in (Support.All.pipe_left pos _114_709))
end
| hd::tl -> begin
(let _43_1935 = (let _114_711 = (let _114_710 = (Microsoft_FStar_Parser_DesugarEnv.default_ml env)
in (desugar_binder _114_710 hd))
in (Support.All.pipe_right _114_711 (as_binder env hd.Microsoft_FStar_Parser_AST.aqual)))
in (match (_43_1935) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))
end))
in (aux env [] bs))
end))
end
| Microsoft_FStar_Parser_AST.Construct ((l, args)) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.find_kind_abbrev env l)) with
| None -> begin
(Microsoft_FStar_Parser_AST.error "Unexpected term where kind was expected" k k.Microsoft_FStar_Parser_AST.range)
end
| Some (l) -> begin
(let args = (Support.List.map (fun ( _43_1945 ) -> (match (_43_1945) with
| (t, b) -> begin
(let qual = (match ((b = Microsoft_FStar_Parser_AST.Hash)) with
| true -> begin
Some (Microsoft_FStar_Absyn_Syntax.Implicit)
end
| false -> begin
None
end)
in (let _114_713 = (desugar_typ_or_exp env t)
in (_114_713, qual)))
end)) args)
in (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown))))
end)
end
| _43_1949 -> begin
(Microsoft_FStar_Parser_AST.error "Unexpected term where kind was expected" k k.Microsoft_FStar_Parser_AST.range)
end)))))
and desugar_formula' = (fun ( env ) ( f ) -> (let connective = (fun ( s ) -> (match (s) with
| "/\\" -> begin
Some (Microsoft_FStar_Absyn_Const.and_lid)
end
| "\\/" -> begin
Some (Microsoft_FStar_Absyn_Const.or_lid)
end
| "==>" -> begin
Some (Microsoft_FStar_Absyn_Const.imp_lid)
end
| "<==>" -> begin
Some (Microsoft_FStar_Absyn_Const.iff_lid)
end
| "~" -> begin
Some (Microsoft_FStar_Absyn_Const.not_lid)
end
| _43_1960 -> begin
None
end))
in (let pos = (fun ( t ) -> (t None f.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( t ) -> (let _43_1965 = t
in {Microsoft_FStar_Absyn_Syntax.n = _43_1965.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _43_1965.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = f.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _43_1965.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _43_1965.Microsoft_FStar_Absyn_Syntax.uvs}))
in (let desugar_quant = (fun ( q ) ( qt ) ( b ) ( pats ) ( body ) -> (let tk = (desugar_binder env (let _43_1973 = b
in {Microsoft_FStar_Parser_AST.b = _43_1973.Microsoft_FStar_Parser_AST.b; Microsoft_FStar_Parser_AST.brange = _43_1973.Microsoft_FStar_Parser_AST.brange; Microsoft_FStar_Parser_AST.blevel = Microsoft_FStar_Parser_AST.Formula; Microsoft_FStar_Parser_AST.aqual = _43_1973.Microsoft_FStar_Parser_AST.aqual}))
in (match (tk) with
| Support.Microsoft.FStar.Util.Inl ((Some (a), k)) -> begin
(let _43_1983 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_43_1983) with
| (env, a) -> begin
(let pats = (Support.List.map (fun ( e ) -> (let _114_744 = (desugar_typ_or_exp env e)
in (Support.All.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _114_744))) pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _43_1989 -> begin
(let _114_745 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
in (Support.All.pipe_left setpos _114_745))
end)
in (let body = (let _114_751 = (let _114_750 = (let _114_749 = (let _114_748 = (Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_114_748)::[])
in (_114_749, body))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _114_750))
in (Support.All.pipe_left pos _114_751))
in (let _114_756 = (let _114_755 = (let _114_752 = (Microsoft_FStar_Absyn_Util.set_lid_range qt b.Microsoft_FStar_Parser_AST.brange)
in (Microsoft_FStar_Absyn_Util.ftv _114_752 Microsoft_FStar_Absyn_Syntax.kun))
in (let _114_754 = (let _114_753 = (Microsoft_FStar_Absyn_Syntax.targ body)
in (_114_753)::[])
in (Microsoft_FStar_Absyn_Util.mk_typ_app _114_755 _114_754)))
in (Support.All.pipe_left setpos _114_756))))))
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _43_1999 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_43_1999) with
| (env, x) -> begin
(let pats = (Support.List.map (fun ( e ) -> (let _114_758 = (desugar_typ_or_exp env e)
in (Support.All.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _114_758))) pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _43_2005 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
end)
in (let body = (let _114_764 = (let _114_763 = (let _114_762 = (let _114_761 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_114_761)::[])
in (_114_762, body))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _114_763))
in (Support.All.pipe_left pos _114_764))
in (let _114_769 = (let _114_768 = (let _114_765 = (Microsoft_FStar_Absyn_Util.set_lid_range q b.Microsoft_FStar_Parser_AST.brange)
in (Microsoft_FStar_Absyn_Util.ftv _114_765 Microsoft_FStar_Absyn_Syntax.kun))
in (let _114_767 = (let _114_766 = (Microsoft_FStar_Absyn_Syntax.targ body)
in (_114_766)::[])
in (Microsoft_FStar_Absyn_Util.mk_typ_app _114_768 _114_767)))
in (Support.All.pipe_left setpos _114_769))))))
end))
end
| _43_2009 -> begin
(Support.All.failwith "impossible")
end)))
in (let push_quant = (fun ( q ) ( binders ) ( pats ) ( body ) -> (match (binders) with
| b::b'::_rest -> begin
(let rest = (b')::_rest
in (let body = (let _114_784 = (q (rest, pats, body))
in (let _114_783 = (Support.Microsoft.FStar.Range.union_ranges b'.Microsoft_FStar_Parser_AST.brange body.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_AST.mk_term _114_784 _114_783 Microsoft_FStar_Parser_AST.Formula)))
in (let _114_785 = (q ((b)::[], [], body))
in (Microsoft_FStar_Parser_AST.mk_term _114_785 f.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Formula))))
end
| _43_2023 -> begin
(Support.All.failwith "impossible")
end))
in (match ((let _114_786 = (unparen f)
in _114_786.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Labeled ((f, l, p)) -> begin
(let f = (desugar_formula env f)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((f, l, Microsoft_FStar_Absyn_Syntax.dummyRange, p)))))
end
| Microsoft_FStar_Parser_AST.Op (("==", hd::_args)) -> begin
(let args = (hd)::_args
in (let args = (Support.List.map (fun ( t ) -> (let _114_788 = (desugar_typ_or_exp env t)
in (Support.All.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _114_788))) args)
in (let eq = (match ((is_type env hd)) with
| true -> begin
(let _114_789 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.eqT_lid f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _114_789 Microsoft_FStar_Absyn_Syntax.kun))
end
| false -> begin
(let _114_790 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.eq2_lid f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _114_790 Microsoft_FStar_Absyn_Syntax.kun))
end)
in (Microsoft_FStar_Absyn_Util.mk_typ_app eq args))))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match (((connective s), args)) with
| (Some (conn), _43_2049::_43_2047::[]) -> begin
(let _114_795 = (let _114_791 = (Microsoft_FStar_Absyn_Util.set_lid_range conn f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _114_791 Microsoft_FStar_Absyn_Syntax.kun))
in (let _114_794 = (Support.List.map (fun ( x ) -> (let _114_793 = (desugar_formula env x)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _114_793))) args)
in (Microsoft_FStar_Absyn_Util.mk_typ_app _114_795 _114_794)))
end
| _43_2054 -> begin
(match ((is_type env f)) with
| true -> begin
(desugar_typ env f)
end
| false -> begin
(let _114_796 = (desugar_exp env f)
in (Support.All.pipe_right _114_796 Microsoft_FStar_Absyn_Util.b2t))
end)
end)
end
| Microsoft_FStar_Parser_AST.If ((f1, f2, f3)) -> begin
(let _114_801 = (let _114_797 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.ite_lid f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _114_797 Microsoft_FStar_Absyn_Syntax.kun))
in (let _114_800 = (Support.List.map (fun ( x ) -> (match ((desugar_typ_or_exp env x)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| Support.Microsoft.FStar.Util.Inr (v) -> begin
(let _114_799 = (Microsoft_FStar_Absyn_Util.b2t v)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _114_799))
end)) ((f1)::(f2)::(f3)::[]))
in (Microsoft_FStar_Absyn_Util.mk_typ_app _114_801 _114_800)))
end
| Microsoft_FStar_Parser_AST.QForall ((_1::_2::_3, pats, body)) -> begin
(let binders = (_1)::(_2)::_3
in (let _114_803 = (push_quant (fun ( x ) -> Microsoft_FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _114_803)))
end
| Microsoft_FStar_Parser_AST.QExists ((_1::_2::_3, pats, body)) -> begin
(let binders = (_1)::(_2)::_3
in (let _114_805 = (push_quant (fun ( x ) -> Microsoft_FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _114_805)))
end
| Microsoft_FStar_Parser_AST.QForall ((b::[], pats, body)) -> begin
(desugar_quant Microsoft_FStar_Absyn_Const.forall_lid Microsoft_FStar_Absyn_Const.allTyp_lid b pats body)
end
| Microsoft_FStar_Parser_AST.QExists ((b::[], pats, body)) -> begin
(desugar_quant Microsoft_FStar_Absyn_Const.exists_lid Microsoft_FStar_Absyn_Const.allTyp_lid b pats body)
end
| Microsoft_FStar_Parser_AST.Paren (f) -> begin
(desugar_formula env f)
end
| _43_2102 -> begin
(match ((is_type env f)) with
| true -> begin
(desugar_typ env f)
end
| false -> begin
(let _114_806 = (desugar_exp env f)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Util.b2t _114_806))
end)
end)))))))
and desugar_formula = (fun ( env ) ( t ) -> (desugar_formula' (let _43_2105 = env
in {Microsoft_FStar_Parser_DesugarEnv.curmodule = _43_2105.Microsoft_FStar_Parser_DesugarEnv.curmodule; Microsoft_FStar_Parser_DesugarEnv.modules = _43_2105.Microsoft_FStar_Parser_DesugarEnv.modules; Microsoft_FStar_Parser_DesugarEnv.open_namespaces = _43_2105.Microsoft_FStar_Parser_DesugarEnv.open_namespaces; Microsoft_FStar_Parser_DesugarEnv.sigaccum = _43_2105.Microsoft_FStar_Parser_DesugarEnv.sigaccum; Microsoft_FStar_Parser_DesugarEnv.localbindings = _43_2105.Microsoft_FStar_Parser_DesugarEnv.localbindings; Microsoft_FStar_Parser_DesugarEnv.recbindings = _43_2105.Microsoft_FStar_Parser_DesugarEnv.recbindings; Microsoft_FStar_Parser_DesugarEnv.phase = Microsoft_FStar_Parser_AST.Formula; Microsoft_FStar_Parser_DesugarEnv.sigmap = _43_2105.Microsoft_FStar_Parser_DesugarEnv.sigmap; Microsoft_FStar_Parser_DesugarEnv.default_result_effect = _43_2105.Microsoft_FStar_Parser_DesugarEnv.default_result_effect; Microsoft_FStar_Parser_DesugarEnv.iface = _43_2105.Microsoft_FStar_Parser_DesugarEnv.iface; Microsoft_FStar_Parser_DesugarEnv.admitted_iface = _43_2105.Microsoft_FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder = (fun ( env ) ( b ) -> (match ((is_type_binder env b)) with
| true -> begin
(let _114_811 = (desugar_type_binder env b)
in Support.Microsoft.FStar.Util.Inl (_114_811))
end
| false -> begin
(let _114_812 = (desugar_exp_binder env b)
in Support.Microsoft.FStar.Util.Inr (_114_812))
end))
and typars_of_binders = (fun ( env ) ( bs ) -> (let _43_2138 = (Support.List.fold_left (fun ( _43_2113 ) ( b ) -> (match (_43_2113) with
| (env, out) -> begin
(let tk = (desugar_binder env (let _43_2115 = b
in {Microsoft_FStar_Parser_AST.b = _43_2115.Microsoft_FStar_Parser_AST.b; Microsoft_FStar_Parser_AST.brange = _43_2115.Microsoft_FStar_Parser_AST.brange; Microsoft_FStar_Parser_AST.blevel = Microsoft_FStar_Parser_AST.Formula; Microsoft_FStar_Parser_AST.aqual = _43_2115.Microsoft_FStar_Parser_AST.aqual}))
in (match (tk) with
| Support.Microsoft.FStar.Util.Inl ((Some (a), k)) -> begin
(let _43_2125 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_43_2125) with
| (env, a) -> begin
(env, ((Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)), b.Microsoft_FStar_Parser_AST.aqual))::out)
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _43_2133 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_43_2133) with
| (env, x) -> begin
(env, ((Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)), b.Microsoft_FStar_Parser_AST.aqual))::out)
end))
end
| _43_2135 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected binder", b.Microsoft_FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_43_2138) with
| (env, tpars) -> begin
(env, (Support.List.rev tpars))
end)))
and desugar_exp_binder = (fun ( env ) ( b ) -> (match (b.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Annotated ((x, t)) -> begin
(let _114_819 = (desugar_typ env t)
in (Some (x), _114_819))
end
| Microsoft_FStar_Parser_AST.TVariable (t) -> begin
(let _114_820 = (Microsoft_FStar_Parser_DesugarEnv.fail_or2 (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in (None, _114_820))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(let _114_821 = (desugar_typ env t)
in (None, _114_821))
end
| Microsoft_FStar_Parser_AST.Variable (x) -> begin
(Some (x), Microsoft_FStar_Absyn_Syntax.tun)
end
| _43_2152 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a type)", b.Microsoft_FStar_Parser_AST.brange))))
end))
and desugar_type_binder = (fun ( env ) ( b ) -> (let fail = (fun ( _43_2156 ) -> (match (()) with
| () -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a kind)", b.Microsoft_FStar_Parser_AST.brange))))
end))
in (match (b.Microsoft_FStar_Parser_AST.b) with
| (Microsoft_FStar_Parser_AST.Annotated ((x, t))) | (Microsoft_FStar_Parser_AST.TAnnotated ((x, t))) -> begin
(let _114_826 = (desugar_kind env t)
in (Some (x), _114_826))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(let _114_827 = (desugar_kind env t)
in (None, _114_827))
end
| Microsoft_FStar_Parser_AST.TVariable (x) -> begin
(Some (x), (let _43_2167 = Microsoft_FStar_Absyn_Syntax.mk_Kind_type
in {Microsoft_FStar_Absyn_Syntax.n = _43_2167.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _43_2167.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = b.Microsoft_FStar_Parser_AST.brange; Microsoft_FStar_Absyn_Syntax.fvs = _43_2167.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _43_2167.Microsoft_FStar_Absyn_Syntax.uvs}))
end
| _43_2170 -> begin
(fail ())
end)))

let gather_tc_binders = (fun ( tps ) ( k ) -> (let rec aux = (fun ( bs ) ( k ) -> (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((binders, k)) -> begin
(aux (Support.List.append bs binders) k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_43_2181, k)) -> begin
(aux bs k)
end
| _43_2186 -> begin
bs
end))
in (let _114_836 = (aux tps k)
in (Support.All.pipe_right _114_836 Microsoft_FStar_Absyn_Util.name_binders))))

let mk_data_discriminators = (fun ( quals ) ( env ) ( t ) ( tps ) ( k ) ( datas ) -> (let quals = (fun ( q ) -> (match (((Support.All.pipe_left Support.Prims.op_Negation env.Microsoft_FStar_Parser_DesugarEnv.iface) || env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface)) with
| true -> begin
(Support.List.append ((Microsoft_FStar_Absyn_Syntax.Assumption)::q) quals)
end
| false -> begin
(Support.List.append q quals)
end))
in (let binders = (gather_tc_binders tps k)
in (let p = (Microsoft_FStar_Absyn_Syntax.range_of_lid t)
in (let imp_binders = (Support.All.pipe_right binders (Support.List.map (fun ( _43_2200 ) -> (match (_43_2200) with
| (x, _43_2199) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end))))
in (let binders = (let _114_857 = (let _114_856 = (let _114_855 = (let _114_854 = (let _114_853 = (Microsoft_FStar_Absyn_Util.ftv t Microsoft_FStar_Absyn_Syntax.kun)
in (let _114_852 = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (_114_853, _114_852)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' _114_854 None p))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.null_v_binder _114_855))
in (_114_856)::[])
in (Support.List.append imp_binders _114_857))
in (let disc_type = (let _114_860 = (let _114_859 = (let _114_858 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.bool_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.total_comp _114_858 p))
in (binders, _114_859))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _114_860 None p))
in (Support.All.pipe_right datas (Support.List.map (fun ( d ) -> (let disc_name = (Microsoft_FStar_Absyn_Util.mk_discriminator d)
in (let _114_864 = (let _114_863 = (quals ((Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Discriminator (d))::[]))
in (let _114_862 = (Microsoft_FStar_Absyn_Syntax.range_of_lid disc_name)
in (disc_name, disc_type, _114_863, _114_862)))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_114_864)))))))))))))

let mk_indexed_projectors = (fun ( fvq ) ( refine_domain ) ( env ) ( _43_2212 ) ( lid ) ( formals ) ( t ) -> (match (_43_2212) with
| (tc, tps, k) -> begin
(let binders = (gather_tc_binders tps k)
in (let p = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (let pos = (fun ( q ) -> (Microsoft_FStar_Absyn_Syntax.withinfo q None p))
in (let projectee = (let _114_875 = (Microsoft_FStar_Absyn_Syntax.mk_ident ("projectee", p))
in (let _114_874 = (Microsoft_FStar_Absyn_Util.genident (Some (p)))
in {Microsoft_FStar_Absyn_Syntax.ppname = _114_875; Microsoft_FStar_Absyn_Syntax.realname = _114_874}))
in (let arg_exp = (Microsoft_FStar_Absyn_Util.bvd_to_exp projectee Microsoft_FStar_Absyn_Syntax.tun)
in (let arg_binder = (let arg_typ = (let _114_878 = (let _114_877 = (Microsoft_FStar_Absyn_Util.ftv tc Microsoft_FStar_Absyn_Syntax.kun)
in (let _114_876 = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (_114_877, _114_876)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' _114_878 None p))
in (match ((not (refine_domain))) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end
| false -> begin
(let disc_name = (Microsoft_FStar_Absyn_Util.mk_discriminator lid)
in (let x = (Microsoft_FStar_Absyn_Util.gen_bvar arg_typ)
in (let _114_888 = (let _114_887 = (let _114_886 = (let _114_885 = (let _114_884 = (let _114_883 = (let _114_882 = (Microsoft_FStar_Absyn_Util.fvar None disc_name p)
in (let _114_881 = (let _114_880 = (let _114_879 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.varg _114_879))
in (_114_880)::[])
in (_114_882, _114_881)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _114_883 None p))
in (Microsoft_FStar_Absyn_Util.b2t _114_884))
in (x, _114_885))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _114_886 None p))
in (Support.All.pipe_left (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s projectee) _114_887))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.v_binder _114_888))))
end))
in (let imp_binders = (Support.All.pipe_right binders (Support.List.map (fun ( _43_2229 ) -> (match (_43_2229) with
| (x, _43_2228) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end))))
in (let binders = (Support.List.append imp_binders ((arg_binder)::[]))
in (let arg = (Microsoft_FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (let subst = (let _114_898 = (Support.All.pipe_right formals (Support.List.mapi (fun ( i ) ( f ) -> (match ((Support.Prims.fst f)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(match ((Support.All.pipe_right binders (Support.Microsoft.FStar.Util.for_some (fun ( _43_13 ) -> (match (_43_13) with
| (Support.Microsoft.FStar.Util.Inl (b), _43_2241) -> begin
(Microsoft_FStar_Absyn_Util.bvd_eq a.Microsoft_FStar_Absyn_Syntax.v b.Microsoft_FStar_Absyn_Syntax.v)
end
| _43_2244 -> begin
false
end))))) with
| true -> begin
[]
end
| false -> begin
(let _43_2248 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_43_2248) with
| (field_name, _43_2247) -> begin
(let proj = (let _114_894 = (let _114_893 = (Microsoft_FStar_Absyn_Util.ftv field_name Microsoft_FStar_Absyn_Syntax.kun)
in (_114_893, (arg)::[]))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _114_894 None p))
in (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, proj)))::[])
end))
end)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(match ((Support.All.pipe_right binders (Support.Microsoft.FStar.Util.for_some (fun ( _43_14 ) -> (match (_43_14) with
| (Support.Microsoft.FStar.Util.Inr (y), _43_2256) -> begin
(Microsoft_FStar_Absyn_Util.bvd_eq x.Microsoft_FStar_Absyn_Syntax.v y.Microsoft_FStar_Absyn_Syntax.v)
end
| _43_2259 -> begin
false
end))))) with
| true -> begin
[]
end
| false -> begin
(let _43_2263 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_43_2263) with
| (field_name, _43_2262) -> begin
(let proj = (let _114_897 = (let _114_896 = (Microsoft_FStar_Absyn_Util.fvar None field_name p)
in (_114_896, (arg)::[]))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _114_897 None p))
in (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, proj)))::[])
end))
end)
end))))
in (Support.All.pipe_right _114_898 Support.List.flatten))
in (let ntps = (Support.List.length tps)
in (let _114_936 = (Support.All.pipe_right formals (Support.List.mapi (fun ( i ) ( ax ) -> (match ((Support.Prims.fst ax)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _43_2274 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_43_2274) with
| (field_name, _43_2273) -> begin
(let kk = (let _114_902 = (let _114_901 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (binders, _114_901))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _114_902 p))
in (let _114_905 = (let _114_904 = (let _114_903 = (Microsoft_FStar_Absyn_Syntax.range_of_lid field_name)
in (field_name, [], kk, [], [], (Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Projector ((lid, Support.Microsoft.FStar.Util.Inl (a.Microsoft_FStar_Absyn_Syntax.v))))::[], _114_903))
in Microsoft_FStar_Absyn_Syntax.Sig_tycon (_114_904))
in (_114_905)::[]))
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _43_2281 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_43_2281) with
| (field_name, _43_2280) -> begin
(let t = (let _114_908 = (let _114_907 = (let _114_906 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Absyn_Util.total_comp _114_906 p))
in (binders, _114_907))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _114_908 None p))
in (let quals = (fun ( q ) -> (match (((not (env.Microsoft_FStar_Parser_DesugarEnv.iface)) || env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.Assumption)::q
end
| false -> begin
q
end))
in (let quals = (quals ((Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Projector ((lid, Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.v))))::[]))
in (let impl = (match ((((let _114_911 = (Microsoft_FStar_Parser_DesugarEnv.current_module env)
in (Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.prims_lid _114_911)) || (fvq <> Microsoft_FStar_Absyn_Syntax.Data_ctor)) || (Support.ST.read Microsoft_FStar_Options.__temp_no_proj))) with
| true -> begin
[]
end
| false -> begin
(let projection = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in (let as_imp = (fun ( _43_15 ) -> (match (_43_15) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _43_2291 -> begin
false
end))
in (let arg_pats = (let _114_926 = (Support.All.pipe_right formals (Support.List.mapi (fun ( j ) ( by ) -> (match (by) with
| (Support.Microsoft.FStar.Util.Inl (_43_2296), imp) -> begin
(match ((j < ntps)) with
| true -> begin
[]
end
| false -> begin
(let _114_919 = (let _114_918 = (let _114_917 = (let _114_916 = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.kun)
in Microsoft_FStar_Absyn_Syntax.Pat_tvar (_114_916))
in (pos _114_917))
in (_114_918, (as_imp imp)))
in (_114_919)::[])
end)
end
| (Support.Microsoft.FStar.Util.Inr (_43_2301), imp) -> begin
(match ((i = j)) with
| true -> begin
(let _114_921 = (let _114_920 = (pos (Microsoft_FStar_Absyn_Syntax.Pat_var (projection)))
in (_114_920, (as_imp imp)))
in (_114_921)::[])
end
| false -> begin
(let _114_925 = (let _114_924 = (let _114_923 = (let _114_922 = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in Microsoft_FStar_Absyn_Syntax.Pat_wild (_114_922))
in (pos _114_923))
in (_114_924, (as_imp imp)))
in (_114_925)::[])
end)
end))))
in (Support.All.pipe_right _114_926 Support.List.flatten))
in (let pat = (let _114_931 = (let _114_929 = (let _114_928 = (let _114_927 = (Microsoft_FStar_Absyn_Util.fv lid)
in (_114_927, Some (fvq), arg_pats))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_114_928))
in (Support.All.pipe_right _114_929 pos))
in (let _114_930 = (Microsoft_FStar_Absyn_Util.bvar_to_exp projection)
in (_114_931, None, _114_930)))
in (let body = (Microsoft_FStar_Absyn_Syntax.mk_Exp_match (arg_exp, (pat)::[]) None p)
in (let imp = (let _114_932 = (Microsoft_FStar_Absyn_Syntax.range_of_lid field_name)
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (binders, body) None _114_932))
in (let lb = {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (field_name); Microsoft_FStar_Absyn_Syntax.lbtyp = Microsoft_FStar_Absyn_Syntax.tun; Microsoft_FStar_Absyn_Syntax.lbeff = Microsoft_FStar_Absyn_Const.effect_Tot_lid; Microsoft_FStar_Absyn_Syntax.lbdef = imp}
in (Microsoft_FStar_Absyn_Syntax.Sig_let (((false, (lb)::[]), p, [], quals)))::[])))))))
end)
in (let _114_935 = (let _114_934 = (let _114_933 = (Microsoft_FStar_Absyn_Syntax.range_of_lid field_name)
in (field_name, t, quals, _114_933))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_114_934))
in (_114_935)::impl)))))
end))
end))))
in (Support.All.pipe_right _114_936 Support.List.flatten)))))))))))))
end))

let mk_data_projectors = (fun ( env ) ( _43_18 ) -> (match (_43_18) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, _43_2318, _43_2320)) when (not ((Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.lexcons_lid))) -> begin
(let refine_domain = (match ((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _43_16 ) -> (match (_43_16) with
| Microsoft_FStar_Absyn_Syntax.RecordConstructor (_43_2325) -> begin
true
end
| _43_2328 -> begin
false
end))))) with
| true -> begin
false
end
| false -> begin
(let _43_2334 = tycon
in (match (_43_2334) with
| (l, _43_2331, _43_2333) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.find_all_datacons env l)) with
| Some (l) -> begin
((Support.List.length l) > 1)
end
| _43_2338 -> begin
true
end)
end))
end)
in (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((formals, cod)) -> begin
(let cod = (Microsoft_FStar_Absyn_Util.comp_result cod)
in (let qual = (match ((Support.Microsoft.FStar.Util.find_map quals (fun ( _43_17 ) -> (match (_43_17) with
| Microsoft_FStar_Absyn_Syntax.RecordConstructor (fns) -> begin
Some (Microsoft_FStar_Absyn_Syntax.Record_ctor ((lid, fns)))
end
| _43_2349 -> begin
None
end)))) with
| None -> begin
Microsoft_FStar_Absyn_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)
in (mk_indexed_projectors qual refine_domain env tycon lid formals cod)))
end
| _43_2355 -> begin
[]
end))
end
| _43_2357 -> begin
[]
end))

let rec desugar_tycon = (fun ( env ) ( rng ) ( quals ) ( tcs ) -> (let tycon_id = (fun ( _43_19 ) -> (match (_43_19) with
| (Microsoft_FStar_Parser_AST.TyconAbstract ((id, _, _))) | (Microsoft_FStar_Parser_AST.TyconAbbrev ((id, _, _, _))) | (Microsoft_FStar_Parser_AST.TyconRecord ((id, _, _, _))) | (Microsoft_FStar_Parser_AST.TyconVariant ((id, _, _, _))) -> begin
id
end))
in (let binder_to_term = (fun ( b ) -> (match (b.Microsoft_FStar_Parser_AST.b) with
| (Microsoft_FStar_Parser_AST.Annotated ((x, _))) | (Microsoft_FStar_Parser_AST.Variable (x)) -> begin
(let _114_956 = (let _114_955 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((x)::[]))
in Microsoft_FStar_Parser_AST.Var (_114_955))
in (Microsoft_FStar_Parser_AST.mk_term _114_956 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr))
end
| (Microsoft_FStar_Parser_AST.TAnnotated ((a, _))) | (Microsoft_FStar_Parser_AST.TVariable (a)) -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Tvar (a)) a.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type)
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
t
end))
in (let tot = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.effect_Tot_lid)) rng Microsoft_FStar_Parser_AST.Expr)
in (let with_constructor_effect = (fun ( t ) -> (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.App ((tot, t, Microsoft_FStar_Parser_AST.Nothing))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level))
in (let apply_binders = (fun ( t ) ( binders ) -> (Support.List.fold_left (fun ( out ) ( b ) -> (let _114_967 = (let _114_966 = (let _114_965 = (binder_to_term b)
in (out, _114_965, Microsoft_FStar_Parser_AST.Nothing))
in Microsoft_FStar_Parser_AST.App (_114_966))
in (Microsoft_FStar_Parser_AST.mk_term _114_967 out.Microsoft_FStar_Parser_AST.range out.Microsoft_FStar_Parser_AST.level))) t binders))
in (let tycon_record_as_variant = (fun ( _43_20 ) -> (match (_43_20) with
| Microsoft_FStar_Parser_AST.TyconRecord ((id, parms, kopt, fields)) -> begin
(let constrName = (Microsoft_FStar_Absyn_Syntax.mk_ident ((Support.String.strcat "Mk" id.Microsoft_FStar_Absyn_Syntax.idText), id.Microsoft_FStar_Absyn_Syntax.idRange))
in (let mfields = (Support.List.map (fun ( _43_2429 ) -> (match (_43_2429) with
| (x, t) -> begin
(let _114_973 = (let _114_972 = (let _114_971 = (Microsoft_FStar_Absyn_Util.mangle_field_name x)
in (_114_971, t))
in Microsoft_FStar_Parser_AST.Annotated (_114_972))
in (Microsoft_FStar_Parser_AST.mk_binder _114_973 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr None))
end)) fields)
in (let result = (let _114_976 = (let _114_975 = (let _114_974 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id)::[]))
in Microsoft_FStar_Parser_AST.Var (_114_974))
in (Microsoft_FStar_Parser_AST.mk_term _114_975 id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type))
in (apply_binders _114_976 parms))
in (let constrTyp = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type)
in (let _114_978 = (Support.All.pipe_right fields (Support.List.map (fun ( _43_2436 ) -> (match (_43_2436) with
| (x, _43_2435) -> begin
(Microsoft_FStar_Parser_DesugarEnv.qualify env x)
end))))
in (Microsoft_FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _114_978))))))
end
| _43_2438 -> begin
(Support.All.failwith "impossible")
end))
in (let desugar_abstract_tc = (fun ( quals ) ( _env ) ( mutuals ) ( _43_21 ) -> (match (_43_21) with
| Microsoft_FStar_Parser_AST.TyconAbstract ((id, binders, kopt)) -> begin
(let _43_2452 = (typars_of_binders _env binders)
in (match (_43_2452) with
| (_env', typars) -> begin
(let k = (match (kopt) with
| None -> begin
Microsoft_FStar_Absyn_Syntax.kun
end
| Some (k) -> begin
(desugar_kind _env' k)
end)
in (let tconstr = (let _114_989 = (let _114_988 = (let _114_987 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id)::[]))
in Microsoft_FStar_Parser_AST.Var (_114_987))
in (Microsoft_FStar_Parser_AST.mk_term _114_988 id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type))
in (apply_binders _114_989 binders))
in (let qlid = (Microsoft_FStar_Parser_DesugarEnv.qualify _env id)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_tycon ((qlid, typars, k, mutuals, [], quals, rng))
in (let _env = (Microsoft_FStar_Parser_DesugarEnv.push_rec_binding _env (Microsoft_FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (let _env2 = (Microsoft_FStar_Parser_DesugarEnv.push_rec_binding _env' (Microsoft_FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (_env, (_env2, typars), se, tconstr)))))))
end))
end
| _43_2463 -> begin
(Support.All.failwith "Unexpected tycon")
end))
in (let push_tparam = (fun ( env ) ( _43_22 ) -> (match (_43_22) with
| (Support.Microsoft.FStar.Util.Inr (x), _43_2470) -> begin
(Microsoft_FStar_Parser_DesugarEnv.push_bvvdef env x.Microsoft_FStar_Absyn_Syntax.v)
end
| (Support.Microsoft.FStar.Util.Inl (a), _43_2475) -> begin
(Microsoft_FStar_Parser_DesugarEnv.push_btvdef env a.Microsoft_FStar_Absyn_Syntax.v)
end))
in (let push_tparams = (Support.List.fold_left push_tparam)
in (match (tcs) with
| Microsoft_FStar_Parser_AST.TyconAbstract (_43_2479)::[] -> begin
(let tc = (Support.List.hd tcs)
in (let _43_2490 = (desugar_abstract_tc quals env [] tc)
in (match (_43_2490) with
| (_43_2484, _43_2486, se, _43_2489) -> begin
(let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))
end)))
end
| Microsoft_FStar_Parser_AST.TyconAbbrev ((id, binders, kopt, t))::[] -> begin
(let _43_2501 = (typars_of_binders env binders)
in (match (_43_2501) with
| (env', typars) -> begin
(let k = (match (kopt) with
| None -> begin
(match ((Support.Microsoft.FStar.Util.for_some (fun ( _43_23 ) -> (match (_43_23) with
| Microsoft_FStar_Absyn_Syntax.Effect -> begin
true
end
| _43_2506 -> begin
false
end)) quals)) with
| true -> begin
Microsoft_FStar_Absyn_Syntax.mk_Kind_effect
end
| false -> begin
Microsoft_FStar_Absyn_Syntax.kun
end)
end
| Some (k) -> begin
(desugar_kind env' k)
end)
in (let t0 = t
in (let quals = (match ((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _43_24 ) -> (match (_43_24) with
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
true
end
| _43_2514 -> begin
false
end))))) with
| true -> begin
quals
end
| false -> begin
(match ((t0.Microsoft_FStar_Parser_AST.level = Microsoft_FStar_Parser_AST.Formula)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.Logic)::quals
end
| false -> begin
quals
end)
end)
in (let se = (match ((Support.All.pipe_right quals (Support.List.contains Microsoft_FStar_Absyn_Syntax.Effect))) with
| true -> begin
(let c = (desugar_comp t.Microsoft_FStar_Parser_AST.range false env' t)
in (let _114_1001 = (let _114_1000 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (let _114_999 = (Support.All.pipe_right quals (Support.List.filter (fun ( _43_25 ) -> (match (_43_25) with
| Microsoft_FStar_Absyn_Syntax.Effect -> begin
false
end
| _43_2520 -> begin
true
end))))
in (_114_1000, typars, c, _114_999, rng)))
in Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_114_1001)))
end
| false -> begin
(let t = (desugar_typ env' t)
in (let _114_1003 = (let _114_1002 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (_114_1002, typars, k, t, quals, rng))
in Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_114_1003)))
end)
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| Microsoft_FStar_Parser_AST.TyconRecord (_43_2525)::[] -> begin
(let trec = (Support.List.hd tcs)
in (let _43_2531 = (tycon_record_as_variant trec)
in (match (_43_2531) with
| (t, fs) -> begin
(desugar_tycon env rng ((Microsoft_FStar_Absyn_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _43_2535::_43_2533 -> begin
(let env0 = env
in (let mutuals = (Support.List.map (fun ( x ) -> (Support.All.pipe_left (Microsoft_FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (let rec collect_tcs = (fun ( quals ) ( et ) ( tc ) -> (let _43_2546 = et
in (match (_43_2546) with
| (env, tcs) -> begin
(match (tc) with
| Microsoft_FStar_Parser_AST.TyconRecord (_43_2548) -> begin
(let trec = tc
in (let _43_2553 = (tycon_record_as_variant trec)
in (match (_43_2553) with
| (t, fs) -> begin
(collect_tcs ((Microsoft_FStar_Absyn_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| Microsoft_FStar_Parser_AST.TyconVariant ((id, binders, kopt, constructors)) -> begin
(let _43_2567 = (desugar_abstract_tc quals env mutuals (Microsoft_FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_43_2567) with
| (env, (_43_2562, tps), se, tconstr) -> begin
(env, (Support.Microsoft.FStar.Util.Inl ((se, tps, constructors, tconstr, quals)))::tcs)
end))
end
| Microsoft_FStar_Parser_AST.TyconAbbrev ((id, binders, kopt, t)) -> begin
(let _43_2581 = (desugar_abstract_tc quals env mutuals (Microsoft_FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_43_2581) with
| (env, (_43_2576, tps), se, tconstr) -> begin
(env, (Support.Microsoft.FStar.Util.Inr ((se, tps, t, quals)))::tcs)
end))
end
| _43_2583 -> begin
(Support.All.failwith "Unrecognized mutual type definition")
end)
end)))
in (let _43_2586 = (Support.List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_43_2586) with
| (env, tcs) -> begin
(let tcs = (Support.List.rev tcs)
in (let sigelts = (Support.All.pipe_right tcs (Support.List.collect (fun ( _43_27 ) -> (match (_43_27) with
| Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Syntax.Sig_tycon ((id, tpars, k, _43_2593, _43_2595, _43_2597, _43_2599)), tps, t, quals)) -> begin
(let env_tps = (push_tparams env tps)
in (let t = (desugar_typ env_tps t)
in (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((id, tpars, k, t, [], rng)))::[]))
end
| Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, _43_2614, tags, _43_2617)), tps, constrs, tconstr, quals)) -> begin
(let tycon = (tname, tpars, k)
in (let env_tps = (push_tparams env tps)
in (let _43_2653 = (let _114_1022 = (Support.All.pipe_right constrs (Support.List.map (fun ( _43_2631 ) -> (match (_43_2631) with
| (id, topt, of_notation) -> begin
(let t = (match (of_notation) with
| true -> begin
(match (topt) with
| Some (t) -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((((Microsoft_FStar_Parser_AST.mk_binder (Microsoft_FStar_Parser_AST.NoName (t)) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level None))::[], tconstr))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
end
| None -> begin
tconstr
end)
end
| false -> begin
(match (topt) with
| None -> begin
(Support.All.failwith "Impossible")
end
| Some (t) -> begin
t
end)
end)
in (let t = (let _114_1014 = (Microsoft_FStar_Parser_DesugarEnv.default_total env_tps)
in (let _114_1013 = (close env_tps t)
in (desugar_typ _114_1014 _114_1013)))
in (let name = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (let quals = (Support.All.pipe_right tags (Support.List.collect (fun ( _43_26 ) -> (match (_43_26) with
| Microsoft_FStar_Absyn_Syntax.RecordType (fns) -> begin
(Microsoft_FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _43_2645 -> begin
[]
end))))
in (let _114_1021 = (let _114_1020 = (let _114_1019 = (let _114_1018 = (let _114_1017 = (Support.List.map (fun ( _43_2650 ) -> (match (_43_2650) with
| (x, _43_2649) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end)) tps)
in (Microsoft_FStar_Absyn_Util.close_typ _114_1017 t))
in (Support.All.pipe_right _114_1018 Microsoft_FStar_Absyn_Util.name_function_binders))
in (name, _114_1019, tycon, quals, mutuals, rng))
in Microsoft_FStar_Absyn_Syntax.Sig_datacon (_114_1020))
in (name, _114_1021))))))
end))))
in (Support.All.pipe_left Support.List.split _114_1022))
in (match (_43_2653) with
| (constrNames, constrs) -> begin
(Microsoft_FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, constrNames, tags, rng)))::constrs
end))))
end
| _43_2655 -> begin
(Support.All.failwith "impossible")
end))))
in (let bundle = (let _114_1024 = (let _114_1023 = (Support.List.collect Microsoft_FStar_Absyn_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _114_1023, rng))
in Microsoft_FStar_Absyn_Syntax.Sig_bundle (_114_1024))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (let data_ops = (Support.All.pipe_right sigelts (Support.List.collect (mk_data_projectors env)))
in (let discs = (Support.All.pipe_right sigelts (Support.List.collect (fun ( _43_28 ) -> (match (_43_28) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((tname, tps, k, _43_2665, constrs, quals, _43_2669)) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _43_2673 -> begin
[]
end))))
in (let ops = (Support.List.append discs data_ops)
in (let env = (Support.List.fold_left Microsoft_FStar_Parser_DesugarEnv.push_sigelt env ops)
in (env, (Support.List.append ((bundle)::[]) ops))))))))))
end)))))
end
| [] -> begin
(Support.All.failwith "impossible")
end)))))))))))

let desugar_binders = (fun ( env ) ( binders ) -> (let _43_2704 = (Support.List.fold_left (fun ( _43_2682 ) ( b ) -> (match (_43_2682) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| Support.Microsoft.FStar.Util.Inl ((Some (a), k)) -> begin
(let _43_2691 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_43_2691) with
| (env, a) -> begin
(let _114_1033 = (let _114_1032 = (Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_114_1032)::binders)
in (env, _114_1033))
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _43_2699 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_43_2699) with
| (env, x) -> begin
(let _114_1035 = (let _114_1034 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_114_1034)::binders)
in (env, _114_1035))
end))
end
| _43_2701 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Missing name in binder", b.Microsoft_FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_43_2704) with
| (env, binders) -> begin
(env, (Support.List.rev binders))
end)))

let rec desugar_decl = (fun ( env ) ( d ) -> (match (d.Microsoft_FStar_Parser_AST.d) with
| Microsoft_FStar_Parser_AST.Pragma (p) -> begin
(let se = Microsoft_FStar_Absyn_Syntax.Sig_pragma ((p, d.Microsoft_FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| Microsoft_FStar_Parser_AST.Open (lid) -> begin
(let env = (Microsoft_FStar_Parser_DesugarEnv.push_namespace env lid)
in (env, []))
end
| Microsoft_FStar_Parser_AST.Tycon ((qual, tcs)) -> begin
(desugar_tycon env d.Microsoft_FStar_Parser_AST.drange qual tcs)
end
| Microsoft_FStar_Parser_AST.ToplevelLet ((isrec, lets)) -> begin
(match ((let _114_1041 = (let _114_1040 = (desugar_exp_maybe_top true env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Let ((isrec, lets, (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Const (Microsoft_FStar_Absyn_Syntax.Const_unit)) d.Microsoft_FStar_Parser_AST.drange Microsoft_FStar_Parser_AST.Expr)))) d.Microsoft_FStar_Parser_AST.drange Microsoft_FStar_Parser_AST.Expr))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Util.compress_exp _114_1040))
in _114_1041.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, _43_2723)) -> begin
(let lids = (Support.All.pipe_right (Support.Prims.snd lbs) (Support.List.map (fun ( lb ) -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inr (l) -> begin
l
end
| _43_2730 -> begin
(Support.All.failwith "impossible")
end))))
in (let quals = (Support.All.pipe_right (Support.Prims.snd lbs) (Support.List.collect (fun ( _43_29 ) -> (match (_43_29) with
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (_43_2740); Microsoft_FStar_Absyn_Syntax.lbtyp = _43_2738; Microsoft_FStar_Absyn_Syntax.lbeff = _43_2736; Microsoft_FStar_Absyn_Syntax.lbdef = _43_2734} -> begin
[]
end
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = _43_2748; Microsoft_FStar_Absyn_Syntax.lbeff = _43_2746; Microsoft_FStar_Absyn_Syntax.lbdef = _43_2744} -> begin
(Microsoft_FStar_Parser_DesugarEnv.lookup_letbinding_quals env l)
end))))
in (let s = Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, d.Microsoft_FStar_Parser_AST.drange, lids, quals))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env s)
in (env, (s)::[])))))
end
| _43_2756 -> begin
(Support.All.failwith "Desugaring a let did not produce a let")
end)
end
| Microsoft_FStar_Parser_AST.Main (t) -> begin
(let e = (desugar_exp env t)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_main ((e, d.Microsoft_FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| Microsoft_FStar_Parser_AST.Assume ((atag, id, t)) -> begin
(let f = (desugar_formula env t)
in (let _114_1047 = (let _114_1046 = (let _114_1045 = (let _114_1044 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (_114_1044, f, (Microsoft_FStar_Absyn_Syntax.Assumption)::[], d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Sig_assume (_114_1045))
in (_114_1046)::[])
in (env, _114_1047)))
end
| Microsoft_FStar_Parser_AST.Val ((quals, id, t)) -> begin
(let t = (let _114_1048 = (close_fun env t)
in (desugar_typ env _114_1048))
in (let quals = (match ((env.Microsoft_FStar_Parser_DesugarEnv.iface && env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.Assumption)::quals
end
| false -> begin
quals
end)
in (let se = (let _114_1050 = (let _114_1049 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (_114_1049, t, quals, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_114_1050))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[])))))
end
| Microsoft_FStar_Parser_AST.Exception ((id, None)) -> begin
(let t = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) Microsoft_FStar_Absyn_Const.exn_lid)
in (let l = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_datacon ((l, t, (Microsoft_FStar_Absyn_Const.exn_lid, [], Microsoft_FStar_Absyn_Syntax.ktype), (Microsoft_FStar_Absyn_Syntax.ExceptionConstructor)::[], (Microsoft_FStar_Absyn_Const.exn_lid)::[], d.Microsoft_FStar_Parser_AST.drange))
in (let se' = Microsoft_FStar_Absyn_Syntax.Sig_bundle (((se)::[], (Microsoft_FStar_Absyn_Syntax.ExceptionConstructor)::[], (l)::[], d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env se')
in (let data_ops = (mk_data_projectors env se)
in (let discs = (mk_data_discriminators [] env Microsoft_FStar_Absyn_Const.exn_lid [] Microsoft_FStar_Absyn_Syntax.ktype ((l)::[]))
in (let env = (Support.List.fold_left Microsoft_FStar_Parser_DesugarEnv.push_sigelt env (Support.List.append discs data_ops))
in (env, (Support.List.append ((se')::discs) data_ops))))))))))
end
| Microsoft_FStar_Parser_AST.Exception ((id, Some (term))) -> begin
(let t = (desugar_typ env term)
in (let t = (let _114_1055 = (let _114_1054 = (let _114_1051 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_114_1051)::[])
in (let _114_1053 = (let _114_1052 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) Microsoft_FStar_Absyn_Const.exn_lid)
in (Microsoft_FStar_Absyn_Syntax.mk_Total _114_1052))
in (_114_1054, _114_1053)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _114_1055 None d.Microsoft_FStar_Parser_AST.drange))
in (let l = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_datacon ((l, t, (Microsoft_FStar_Absyn_Const.exn_lid, [], Microsoft_FStar_Absyn_Syntax.ktype), (Microsoft_FStar_Absyn_Syntax.ExceptionConstructor)::[], (Microsoft_FStar_Absyn_Const.exn_lid)::[], d.Microsoft_FStar_Parser_AST.drange))
in (let se' = Microsoft_FStar_Absyn_Syntax.Sig_bundle (((se)::[], (Microsoft_FStar_Absyn_Syntax.ExceptionConstructor)::[], (l)::[], d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env se')
in (let data_ops = (mk_data_projectors env se)
in (let discs = (mk_data_discriminators [] env Microsoft_FStar_Absyn_Const.exn_lid [] Microsoft_FStar_Absyn_Syntax.ktype ((l)::[]))
in (let env = (Support.List.fold_left Microsoft_FStar_Parser_DesugarEnv.push_sigelt env (Support.List.append discs data_ops))
in (env, (Support.List.append ((se')::discs) data_ops)))))))))))
end
| Microsoft_FStar_Parser_AST.KindAbbrev ((id, binders, k)) -> begin
(let _43_2809 = (desugar_binders env binders)
in (match (_43_2809) with
| (env_k, binders) -> begin
(let k = (desugar_kind env_k k)
in (let name = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev ((name, binders, k, d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[])))))
end))
end
| Microsoft_FStar_Parser_AST.NewEffect ((quals, Microsoft_FStar_Parser_AST.RedefineEffect ((eff_name, eff_binders, defn)))) -> begin
(let env0 = env
in (let _43_2825 = (desugar_binders env eff_binders)
in (match (_43_2825) with
| (env, binders) -> begin
(let defn = (desugar_typ env defn)
in (let _43_2829 = (Microsoft_FStar_Absyn_Util.head_and_args defn)
in (match (_43_2829) with
| (head, args) -> begin
(match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (eff) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_effect_defn env eff.Microsoft_FStar_Absyn_Syntax.v)) with
| None -> begin
(let _114_1060 = (let _114_1059 = (let _114_1058 = (let _114_1057 = (let _114_1056 = (Microsoft_FStar_Absyn_Print.sli eff.Microsoft_FStar_Absyn_Syntax.v)
in (Support.String.strcat "Effect " _114_1056))
in (Support.String.strcat _114_1057 " not found"))
in (_114_1058, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Error (_114_1059))
in (raise (_114_1060)))
end
| Some (ed) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.subst_of_list ed.Microsoft_FStar_Absyn_Syntax.binders args)
in (let sub = (Microsoft_FStar_Absyn_Util.subst_typ subst)
in (let ed = (let _114_1077 = (Microsoft_FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _114_1076 = (Microsoft_FStar_Absyn_Util.subst_kind subst ed.Microsoft_FStar_Absyn_Syntax.signature)
in (let _114_1075 = (sub ed.Microsoft_FStar_Absyn_Syntax.ret)
in (let _114_1074 = (sub ed.Microsoft_FStar_Absyn_Syntax.bind_wp)
in (let _114_1073 = (sub ed.Microsoft_FStar_Absyn_Syntax.bind_wlp)
in (let _114_1072 = (sub ed.Microsoft_FStar_Absyn_Syntax.if_then_else)
in (let _114_1071 = (sub ed.Microsoft_FStar_Absyn_Syntax.ite_wp)
in (let _114_1070 = (sub ed.Microsoft_FStar_Absyn_Syntax.ite_wlp)
in (let _114_1069 = (sub ed.Microsoft_FStar_Absyn_Syntax.wp_binop)
in (let _114_1068 = (sub ed.Microsoft_FStar_Absyn_Syntax.wp_as_type)
in (let _114_1067 = (sub ed.Microsoft_FStar_Absyn_Syntax.close_wp)
in (let _114_1066 = (sub ed.Microsoft_FStar_Absyn_Syntax.close_wp_t)
in (let _114_1065 = (sub ed.Microsoft_FStar_Absyn_Syntax.assert_p)
in (let _114_1064 = (sub ed.Microsoft_FStar_Absyn_Syntax.assume_p)
in (let _114_1063 = (sub ed.Microsoft_FStar_Absyn_Syntax.null_wp)
in (let _114_1062 = (sub ed.Microsoft_FStar_Absyn_Syntax.trivial)
in {Microsoft_FStar_Absyn_Syntax.mname = _114_1077; Microsoft_FStar_Absyn_Syntax.binders = binders; Microsoft_FStar_Absyn_Syntax.qualifiers = quals; Microsoft_FStar_Absyn_Syntax.signature = _114_1076; Microsoft_FStar_Absyn_Syntax.ret = _114_1075; Microsoft_FStar_Absyn_Syntax.bind_wp = _114_1074; Microsoft_FStar_Absyn_Syntax.bind_wlp = _114_1073; Microsoft_FStar_Absyn_Syntax.if_then_else = _114_1072; Microsoft_FStar_Absyn_Syntax.ite_wp = _114_1071; Microsoft_FStar_Absyn_Syntax.ite_wlp = _114_1070; Microsoft_FStar_Absyn_Syntax.wp_binop = _114_1069; Microsoft_FStar_Absyn_Syntax.wp_as_type = _114_1068; Microsoft_FStar_Absyn_Syntax.close_wp = _114_1067; Microsoft_FStar_Absyn_Syntax.close_wp_t = _114_1066; Microsoft_FStar_Absyn_Syntax.assert_p = _114_1065; Microsoft_FStar_Absyn_Syntax.assume_p = _114_1064; Microsoft_FStar_Absyn_Syntax.null_wp = _114_1063; Microsoft_FStar_Absyn_Syntax.trivial = _114_1062}))))))))))))))))
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ed, d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)
end
| _43_2841 -> begin
(let _114_1081 = (let _114_1080 = (let _114_1079 = (let _114_1078 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (Support.String.strcat _114_1078 " is not an effect"))
in (_114_1079, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Error (_114_1080))
in (raise (_114_1081)))
end)
end)))
end)))
end
| Microsoft_FStar_Parser_AST.NewEffect ((quals, Microsoft_FStar_Parser_AST.DefineEffect ((eff_name, eff_binders, eff_kind, eff_decls)))) -> begin
(let env0 = env
in (let env = (Microsoft_FStar_Parser_DesugarEnv.enter_monad_scope env eff_name)
in (let _43_2855 = (desugar_binders env eff_binders)
in (match (_43_2855) with
| (env, binders) -> begin
(let eff_k = (desugar_kind env eff_kind)
in (let _43_2866 = (Support.All.pipe_right eff_decls (Support.List.fold_left (fun ( _43_2859 ) ( decl ) -> (match (_43_2859) with
| (env, out) -> begin
(let _43_2863 = (desugar_decl env decl)
in (match (_43_2863) with
| (env, ses) -> begin
(let _114_1085 = (let _114_1084 = (Support.List.hd ses)
in (_114_1084)::out)
in (env, _114_1085))
end))
end)) (env, [])))
in (match (_43_2866) with
| (env, decls) -> begin
(let decls = (Support.List.rev decls)
in (let lookup = (fun ( s ) -> (match ((let _114_1089 = (let _114_1088 = (Microsoft_FStar_Absyn_Syntax.mk_ident (s, d.Microsoft_FStar_Parser_AST.drange))
in (Microsoft_FStar_Parser_DesugarEnv.qualify env _114_1088))
in (Microsoft_FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _114_1089))) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat (Support.String.strcat (Support.String.strcat "Monad " eff_name.Microsoft_FStar_Absyn_Syntax.idText) " expects definition of ") s), d.Microsoft_FStar_Parser_AST.drange))))
end
| Some (t) -> begin
t
end))
in (let ed = (let _114_1104 = (Microsoft_FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _114_1103 = (lookup "return")
in (let _114_1102 = (lookup "bind_wp")
in (let _114_1101 = (lookup "bind_wlp")
in (let _114_1100 = (lookup "if_then_else")
in (let _114_1099 = (lookup "ite_wp")
in (let _114_1098 = (lookup "ite_wlp")
in (let _114_1097 = (lookup "wp_binop")
in (let _114_1096 = (lookup "wp_as_type")
in (let _114_1095 = (lookup "close_wp")
in (let _114_1094 = (lookup "close_wp_t")
in (let _114_1093 = (lookup "assert_p")
in (let _114_1092 = (lookup "assume_p")
in (let _114_1091 = (lookup "null_wp")
in (let _114_1090 = (lookup "trivial")
in {Microsoft_FStar_Absyn_Syntax.mname = _114_1104; Microsoft_FStar_Absyn_Syntax.binders = binders; Microsoft_FStar_Absyn_Syntax.qualifiers = quals; Microsoft_FStar_Absyn_Syntax.signature = eff_k; Microsoft_FStar_Absyn_Syntax.ret = _114_1103; Microsoft_FStar_Absyn_Syntax.bind_wp = _114_1102; Microsoft_FStar_Absyn_Syntax.bind_wlp = _114_1101; Microsoft_FStar_Absyn_Syntax.if_then_else = _114_1100; Microsoft_FStar_Absyn_Syntax.ite_wp = _114_1099; Microsoft_FStar_Absyn_Syntax.ite_wlp = _114_1098; Microsoft_FStar_Absyn_Syntax.wp_binop = _114_1097; Microsoft_FStar_Absyn_Syntax.wp_as_type = _114_1096; Microsoft_FStar_Absyn_Syntax.close_wp = _114_1095; Microsoft_FStar_Absyn_Syntax.close_wp_t = _114_1094; Microsoft_FStar_Absyn_Syntax.assert_p = _114_1093; Microsoft_FStar_Absyn_Syntax.assume_p = _114_1092; Microsoft_FStar_Absyn_Syntax.null_wp = _114_1091; Microsoft_FStar_Absyn_Syntax.trivial = _114_1090})))))))))))))))
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ed, d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)))
end))))
end
| Microsoft_FStar_Parser_AST.SubEffect (l) -> begin
(let lookup = (fun ( l ) -> (match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_effect_name env l)) with
| None -> begin
(let _114_1111 = (let _114_1110 = (let _114_1109 = (let _114_1108 = (let _114_1107 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.String.strcat "Effect name " _114_1107))
in (Support.String.strcat _114_1108 " not found"))
in (_114_1109, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Error (_114_1110))
in (raise (_114_1111)))
end
| Some (l) -> begin
l
end))
in (let src = (lookup l.Microsoft_FStar_Parser_AST.msource)
in (let dst = (lookup l.Microsoft_FStar_Parser_AST.mdest)
in (let lift = (desugar_typ env l.Microsoft_FStar_Parser_AST.lift_op)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (({Microsoft_FStar_Absyn_Syntax.source = src; Microsoft_FStar_Absyn_Syntax.target = dst; Microsoft_FStar_Absyn_Syntax.lift = lift}, d.Microsoft_FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end))

let desugar_decls = (fun ( env ) ( decls ) -> (Support.List.fold_left (fun ( _43_2891 ) ( d ) -> (match (_43_2891) with
| (env, sigelts) -> begin
(let _43_2895 = (desugar_decl env d)
in (match (_43_2895) with
| (env, se) -> begin
(env, (Support.List.append sigelts se))
end))
end)) (env, []) decls))

let open_prims_all = ((Microsoft_FStar_Parser_AST.mk_decl (Microsoft_FStar_Parser_AST.Open (Microsoft_FStar_Absyn_Const.prims_lid)) Microsoft_FStar_Absyn_Syntax.dummyRange))::((Microsoft_FStar_Parser_AST.mk_decl (Microsoft_FStar_Parser_AST.Open (Microsoft_FStar_Absyn_Const.all_lid)) Microsoft_FStar_Absyn_Syntax.dummyRange))::[]

let desugar_modul_common = (fun ( curmod ) ( env ) ( m ) -> (let open_ns = (fun ( mname ) ( d ) -> (let d = (match (((Support.List.length mname.Microsoft_FStar_Absyn_Syntax.ns) <> 0)) with
| true -> begin
(let _114_1128 = (let _114_1127 = (let _114_1125 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids mname.Microsoft_FStar_Absyn_Syntax.ns)
in Microsoft_FStar_Parser_AST.Open (_114_1125))
in (let _114_1126 = (Microsoft_FStar_Absyn_Syntax.range_of_lid mname)
in (Microsoft_FStar_Parser_AST.mk_decl _114_1127 _114_1126)))
in (_114_1128)::d)
end
| false -> begin
d
end)
in d))
in (let env = (match (curmod) with
| None -> begin
env
end
| Some ((prev_mod, _43_2906)) -> begin
(Microsoft_FStar_Parser_DesugarEnv.finish_module_or_interface env prev_mod)
end)
in (let _43_2923 = (match (m) with
| Microsoft_FStar_Parser_AST.Interface ((mname, decls, admitted)) -> begin
(let _114_1130 = (Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _114_1129 = (open_ns mname decls)
in (_114_1130, mname, _114_1129, true)))
end
| Microsoft_FStar_Parser_AST.Module ((mname, decls)) -> begin
(let _114_1132 = (Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _114_1131 = (open_ns mname decls)
in (_114_1132, mname, _114_1131, false)))
end)
in (match (_43_2923) with
| (env, mname, decls, intf) -> begin
(let _43_2926 = (desugar_decls env decls)
in (match (_43_2926) with
| (env, sigelts) -> begin
(let modul = {Microsoft_FStar_Absyn_Syntax.name = mname; Microsoft_FStar_Absyn_Syntax.declarations = sigelts; Microsoft_FStar_Absyn_Syntax.exports = []; Microsoft_FStar_Absyn_Syntax.is_interface = intf; Microsoft_FStar_Absyn_Syntax.is_deserialized = false}
in (env, modul))
end))
end)))))

let desugar_partial_modul = (fun ( curmod ) ( env ) ( m ) -> (let m = (match ((Support.ST.read Microsoft_FStar_Options.interactive_fsi)) with
| true -> begin
(match (m) with
| Microsoft_FStar_Parser_AST.Module ((mname, decls)) -> begin
(let _114_1139 = (let _114_1138 = (let _114_1137 = (Support.ST.read Microsoft_FStar_Options.admit_fsi)
in (Support.Microsoft.FStar.Util.for_some (fun ( m ) -> (m = mname.Microsoft_FStar_Absyn_Syntax.str)) _114_1137))
in (mname, decls, _114_1138))
in Microsoft_FStar_Parser_AST.Interface (_114_1139))
end
| Microsoft_FStar_Parser_AST.Interface ((mname, _43_2938, _43_2940)) -> begin
(Support.All.failwith (Support.String.strcat "Impossible: " mname.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText))
end)
end
| false -> begin
m
end)
in (desugar_modul_common curmod env m)))

let desugar_modul = (fun ( env ) ( m ) -> (let _43_2948 = (desugar_modul_common None env m)
in (match (_43_2948) with
| (env, modul) -> begin
(let env = (Microsoft_FStar_Parser_DesugarEnv.finish_module_or_interface env modul)
in (let _43_2950 = (match ((Microsoft_FStar_Options.should_dump modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(let _114_1144 = (Microsoft_FStar_Absyn_Print.modul_to_string modul)
in (Support.Microsoft.FStar.Util.fprint1 "%s\n" _114_1144))
end
| false -> begin
()
end)
in (env, modul)))
end)))

let desugar_file = (fun ( env ) ( f ) -> (let _43_2963 = (Support.List.fold_left (fun ( _43_2956 ) ( m ) -> (match (_43_2956) with
| (env, mods) -> begin
(let _43_2960 = (desugar_modul env m)
in (match (_43_2960) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_43_2963) with
| (env, mods) -> begin
(env, (Support.List.rev mods))
end)))

let add_modul_to_env = (fun ( m ) ( en ) -> (let en = (Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface false false en m.Microsoft_FStar_Absyn_Syntax.name)
in (let en = (Support.List.fold_left Microsoft_FStar_Parser_DesugarEnv.push_sigelt (let _43_2967 = en
in {Microsoft_FStar_Parser_DesugarEnv.curmodule = Some (m.Microsoft_FStar_Absyn_Syntax.name); Microsoft_FStar_Parser_DesugarEnv.modules = _43_2967.Microsoft_FStar_Parser_DesugarEnv.modules; Microsoft_FStar_Parser_DesugarEnv.open_namespaces = _43_2967.Microsoft_FStar_Parser_DesugarEnv.open_namespaces; Microsoft_FStar_Parser_DesugarEnv.sigaccum = _43_2967.Microsoft_FStar_Parser_DesugarEnv.sigaccum; Microsoft_FStar_Parser_DesugarEnv.localbindings = _43_2967.Microsoft_FStar_Parser_DesugarEnv.localbindings; Microsoft_FStar_Parser_DesugarEnv.recbindings = _43_2967.Microsoft_FStar_Parser_DesugarEnv.recbindings; Microsoft_FStar_Parser_DesugarEnv.phase = _43_2967.Microsoft_FStar_Parser_DesugarEnv.phase; Microsoft_FStar_Parser_DesugarEnv.sigmap = _43_2967.Microsoft_FStar_Parser_DesugarEnv.sigmap; Microsoft_FStar_Parser_DesugarEnv.default_result_effect = _43_2967.Microsoft_FStar_Parser_DesugarEnv.default_result_effect; Microsoft_FStar_Parser_DesugarEnv.iface = _43_2967.Microsoft_FStar_Parser_DesugarEnv.iface; Microsoft_FStar_Parser_DesugarEnv.admitted_iface = _43_2967.Microsoft_FStar_Parser_DesugarEnv.admitted_iface}) m.Microsoft_FStar_Absyn_Syntax.exports)
in (Microsoft_FStar_Parser_DesugarEnv.finish_module_or_interface en m))))




