
let as_imp = (fun ( _43_1 ) -> (match (_43_1) with
| (Microsoft_FStar_Parser_AST.Hash) | (Microsoft_FStar_Parser_AST.FsTypApp) -> begin
Some (Microsoft_FStar_Absyn_Syntax.Implicit)
end
| _43_32 -> begin
None
end))

let arg_withimp_e = (fun ( imp ) ( t ) -> (t, (as_imp imp)))

let arg_withimp_t = (fun ( imp ) ( t ) -> (match (imp) with
| Microsoft_FStar_Parser_AST.Hash -> begin
(t, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end
| _43_39 -> begin
(t, None)
end))

let contains_binder = (fun ( binders ) -> (Support.All.pipe_right binders (Support.Microsoft.FStar.Util.for_some (fun ( b ) -> (match (b.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Annotated (_43_43) -> begin
true
end
| _43_46 -> begin
false
end)))))

let rec unparen = (fun ( t ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _43_51 -> begin
t
end))

let rec unlabel = (fun ( t ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (t) -> begin
(unlabel t)
end
| Microsoft_FStar_Parser_AST.Labeled ((t, _43_57, _43_59)) -> begin
(unlabel t)
end
| _43_63 -> begin
t
end))

let kind_star = (fun ( r ) -> (let _70_18819 = (let _70_18818 = (Microsoft_FStar_Absyn_Syntax.lid_of_path (("Type")::[]) r)
in Microsoft_FStar_Parser_AST.Name (_70_18818))
in (Microsoft_FStar_Parser_AST.mk_term _70_18819 r Microsoft_FStar_Parser_AST.Kind)))

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
| _43_86 -> begin
"UNKNOWN"
end))
in (let rec aux = (fun ( i ) -> (match ((i = (Support.String.length s))) with
| true -> begin
[]
end
| false -> begin
(let _70_18830 = (let _70_18828 = (Support.Microsoft.FStar.Util.char_at s i)
in (name_of_char _70_18828))
in (let _70_18829 = (aux (i + 1))
in (_70_18830)::_70_18829))
end))
in (let _70_18832 = (let _70_18831 = (aux 0)
in (Support.String.concat "_" _70_18831))
in (Support.String.strcat "op_" _70_18832)))))

let compile_op_lid = (fun ( n ) ( s ) ( r ) -> (let _70_18842 = (let _70_18841 = (let _70_18840 = (let _70_18839 = (compile_op n s)
in (_70_18839, r))
in (Microsoft_FStar_Absyn_Syntax.mk_ident _70_18840))
in (_70_18841)::[])
in (Support.All.pipe_right _70_18842 Microsoft_FStar_Absyn_Syntax.lid_of_ids)))

let op_as_vlid = (fun ( env ) ( arity ) ( rng ) ( s ) -> (let r = (fun ( l ) -> (let _70_18853 = (Microsoft_FStar_Absyn_Util.set_lid_range l rng)
in Some (_70_18853)))
in (let fallback = (fun ( _43_100 ) -> (match (()) with
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
| _43_122 -> begin
None
end)
end))
in (match ((let _70_18856 = (compile_op_lid arity s rng)
in (Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env _70_18856))) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _43_133)); Microsoft_FStar_Absyn_Syntax.tk = _43_130; Microsoft_FStar_Absyn_Syntax.pos = _43_128; Microsoft_FStar_Absyn_Syntax.fvs = _43_126; Microsoft_FStar_Absyn_Syntax.uvs = _43_124}) -> begin
Some (fv.Microsoft_FStar_Absyn_Syntax.v)
end
| _43_139 -> begin
(fallback ())
end))))

let op_as_tylid = (fun ( env ) ( arity ) ( rng ) ( s ) -> (let r = (fun ( l ) -> (let _70_18867 = (Microsoft_FStar_Absyn_Util.set_lid_range l rng)
in Some (_70_18867)))
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
(match ((let _70_18868 = (compile_op_lid arity s rng)
in (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env _70_18868))) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (ftv); Microsoft_FStar_Absyn_Syntax.tk = _43_162; Microsoft_FStar_Absyn_Syntax.pos = _43_160; Microsoft_FStar_Absyn_Syntax.fvs = _43_158; Microsoft_FStar_Absyn_Syntax.uvs = _43_156}) -> begin
Some (ftv.Microsoft_FStar_Absyn_Syntax.v)
end
| _43_168 -> begin
None
end)
end)))

let rec is_type = (fun ( env ) ( t ) -> (match ((t.Microsoft_FStar_Parser_AST.level = Microsoft_FStar_Parser_AST.Type)) with
| true -> begin
true
end
| false -> begin
(match ((let _70_18875 = (unparen t)
in _70_18875.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Wild -> begin
true
end
| Microsoft_FStar_Parser_AST.Labeled (_43_173) -> begin
true
end
| Microsoft_FStar_Parser_AST.Op (("*", hd::_43_177)) -> begin
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
| _43_228 -> begin
true
end)
end
| (Microsoft_FStar_Parser_AST.QForall (_)) | (Microsoft_FStar_Parser_AST.QExists (_)) | (Microsoft_FStar_Parser_AST.Sum (_)) | (Microsoft_FStar_Parser_AST.Refine (_)) | (Microsoft_FStar_Parser_AST.Tvar (_)) | (Microsoft_FStar_Parser_AST.NamedTyp (_)) -> begin
true
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) when ((Support.List.length l.Microsoft_FStar_Absyn_Syntax.ns) = 0) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env l.Microsoft_FStar_Absyn_Syntax.ident)) with
| Some (_43_251) -> begin
true
end
| _43_254 -> begin
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
| Microsoft_FStar_Parser_AST.Product ((_43_295, t)) -> begin
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
| Microsoft_FStar_Parser_AST.PatTvar ((id, _43_321)) -> begin
(let _43_327 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_43_327) with
| (env, _43_326) -> begin
(aux env pats)
end))
end
| Microsoft_FStar_Parser_AST.PatAscribed ((p, tm)) -> begin
(let env = (match ((is_kind env tm)) with
| true -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| (Microsoft_FStar_Parser_AST.PatVar ((id, _))) | (Microsoft_FStar_Parser_AST.PatTvar ((id, _))) -> begin
(let _70_18880 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (Support.All.pipe_right _70_18880 Support.Prims.fst))
end
| _43_342 -> begin
env
end)
end
| false -> begin
env
end)
in (aux env pats))
end
| _43_345 -> begin
false
end)
end))
in (aux env pats))
end
| _43_347 -> begin
false
end)
end))
and is_kind = (fun ( env ) ( t ) -> (match ((t.Microsoft_FStar_Parser_AST.level = Microsoft_FStar_Parser_AST.Kind)) with
| true -> begin
true
end
| false -> begin
(match ((let _70_18883 = (unparen t)
in _70_18883.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Name ({Microsoft_FStar_Absyn_Syntax.ns = _43_356; Microsoft_FStar_Absyn_Syntax.ident = _43_354; Microsoft_FStar_Absyn_Syntax.nsstr = _43_352; Microsoft_FStar_Absyn_Syntax.str = "Type"}) -> begin
true
end
| Microsoft_FStar_Parser_AST.Product ((_43_360, t)) -> begin
(is_kind env t)
end
| Microsoft_FStar_Parser_AST.Paren (t) -> begin
(is_kind env t)
end
| (Microsoft_FStar_Parser_AST.Construct ((l, _))) | (Microsoft_FStar_Parser_AST.Name (l)) -> begin
(Microsoft_FStar_Parser_DesugarEnv.is_kind_abbrev env l)
end
| _43_373 -> begin
false
end)
end))

let rec is_type_binder = (fun ( env ) ( b ) -> (match ((b.Microsoft_FStar_Parser_AST.blevel = Microsoft_FStar_Parser_AST.Formula)) with
| true -> begin
(match (b.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Variable (_43_377) -> begin
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
| Microsoft_FStar_Parser_AST.Variable (_43_392) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected binder without annotation", b.Microsoft_FStar_Parser_AST.brange))))
end
| Microsoft_FStar_Parser_AST.TVariable (_43_395) -> begin
false
end
| Microsoft_FStar_Parser_AST.TAnnotated (_43_398) -> begin
true
end
| (Microsoft_FStar_Parser_AST.Annotated ((_, t))) | (Microsoft_FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end))

let sort_ftv = (fun ( ftv ) -> (let _70_18894 = (Support.Microsoft.FStar.Util.remove_dups (fun ( x ) ( y ) -> (x.Microsoft_FStar_Absyn_Syntax.idText = y.Microsoft_FStar_Absyn_Syntax.idText)) ftv)
in (Support.All.pipe_left (Support.Microsoft.FStar.Util.sort_with (fun ( x ) ( y ) -> (Support.String.compare x.Microsoft_FStar_Absyn_Syntax.idText y.Microsoft_FStar_Absyn_Syntax.idText))) _70_18894)))

let rec free_type_vars_b = (fun ( env ) ( binder ) -> (match (binder.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Variable (_43_414) -> begin
(env, [])
end
| Microsoft_FStar_Parser_AST.TVariable (x) -> begin
(let _43_421 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env x)
in (match (_43_421) with
| (env, _43_420) -> begin
(env, (x)::[])
end))
end
| Microsoft_FStar_Parser_AST.Annotated ((_43_423, term)) -> begin
(let _70_18901 = (free_type_vars env term)
in (env, _70_18901))
end
| Microsoft_FStar_Parser_AST.TAnnotated ((id, _43_429)) -> begin
(let _43_435 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_43_435) with
| (env, _43_434) -> begin
(env, [])
end))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(let _70_18902 = (free_type_vars env t)
in (env, _70_18902))
end))
and free_type_vars = (fun ( env ) ( t ) -> (match ((let _70_18905 = (unparen t)
in _70_18905.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Tvar (a) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env a)) with
| None -> begin
(a)::[]
end
| _43_444 -> begin
[]
end)
end
| (Microsoft_FStar_Parser_AST.Wild) | (Microsoft_FStar_Parser_AST.Const (_)) | (Microsoft_FStar_Parser_AST.Var (_)) | (Microsoft_FStar_Parser_AST.Name (_)) -> begin
[]
end
| (Microsoft_FStar_Parser_AST.Requires ((t, _))) | (Microsoft_FStar_Parser_AST.Ensures ((t, _))) | (Microsoft_FStar_Parser_AST.Labeled ((t, _, _))) | (Microsoft_FStar_Parser_AST.NamedTyp ((_, t))) | (Microsoft_FStar_Parser_AST.Paren (t)) | (Microsoft_FStar_Parser_AST.Ascribed ((t, _))) -> begin
(free_type_vars env t)
end
| Microsoft_FStar_Parser_AST.Construct ((_43_480, ts)) -> begin
(Support.List.collect (fun ( _43_487 ) -> (match (_43_487) with
| (t, _43_486) -> begin
(free_type_vars env t)
end)) ts)
end
| Microsoft_FStar_Parser_AST.Op ((_43_489, ts)) -> begin
(Support.List.collect (free_type_vars env) ts)
end
| Microsoft_FStar_Parser_AST.App ((t1, t2, _43_496)) -> begin
(let _70_18908 = (free_type_vars env t1)
in (let _70_18907 = (free_type_vars env t2)
in (Support.List.append _70_18908 _70_18907)))
end
| Microsoft_FStar_Parser_AST.Refine ((b, t)) -> begin
(let _43_505 = (free_type_vars_b env b)
in (match (_43_505) with
| (env, f) -> begin
(let _70_18909 = (free_type_vars env t)
in (Support.List.append f _70_18909))
end))
end
| (Microsoft_FStar_Parser_AST.Product ((binders, body))) | (Microsoft_FStar_Parser_AST.Sum ((binders, body))) -> begin
(let _43_521 = (Support.List.fold_left (fun ( _43_514 ) ( binder ) -> (match (_43_514) with
| (env, free) -> begin
(let _43_518 = (free_type_vars_b env binder)
in (match (_43_518) with
| (env, f) -> begin
(env, (Support.List.append f free))
end))
end)) (env, []) binders)
in (match (_43_521) with
| (env, free) -> begin
(let _70_18912 = (free_type_vars env body)
in (Support.List.append free _70_18912))
end))
end
| Microsoft_FStar_Parser_AST.Project ((t, _43_524)) -> begin
(free_type_vars env t)
end
| (Microsoft_FStar_Parser_AST.Abs (_)) | (Microsoft_FStar_Parser_AST.If (_)) | (Microsoft_FStar_Parser_AST.QForall (_)) | (Microsoft_FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (Microsoft_FStar_Parser_AST.Let (_)) | (Microsoft_FStar_Parser_AST.Record (_)) | (Microsoft_FStar_Parser_AST.Match (_)) | (Microsoft_FStar_Parser_AST.TryWith (_)) | (Microsoft_FStar_Parser_AST.Seq (_)) -> begin
(Microsoft_FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.Microsoft_FStar_Parser_AST.range)
end))

let head_and_args = (fun ( t ) -> (let rec aux = (fun ( args ) ( t ) -> (match ((let _70_18919 = (unparen t)
in _70_18919.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((t, arg, imp)) -> begin
(aux (((arg, imp))::args) t)
end
| Microsoft_FStar_Parser_AST.Construct ((l, args')) -> begin
({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Name (l); Microsoft_FStar_Parser_AST.range = t.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Parser_AST.level = t.Microsoft_FStar_Parser_AST.level}, (Support.List.append args' args))
end
| _43_568 -> begin
(t, args)
end))
in (aux [] t)))

let close = (fun ( env ) ( t ) -> (let ftv = (let _70_18924 = (free_type_vars env t)
in (Support.All.pipe_left sort_ftv _70_18924))
in (match (((Support.List.length ftv) = 0)) with
| true -> begin
t
end
| false -> begin
(let binders = (Support.All.pipe_right ftv (Support.List.map (fun ( x ) -> (let _70_18928 = (let _70_18927 = (let _70_18926 = (kind_star x.Microsoft_FStar_Absyn_Syntax.idRange)
in (x, _70_18926))
in Microsoft_FStar_Parser_AST.TAnnotated (_70_18927))
in (Microsoft_FStar_Parser_AST.mk_binder _70_18928 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type (Some (Microsoft_FStar_Absyn_Syntax.Implicit)))))))
in (let result = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((binders, t))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
in result))
end)))

let close_fun = (fun ( env ) ( t ) -> (let ftv = (let _70_18933 = (free_type_vars env t)
in (Support.All.pipe_left sort_ftv _70_18933))
in (match (((Support.List.length ftv) = 0)) with
| true -> begin
t
end
| false -> begin
(let binders = (Support.All.pipe_right ftv (Support.List.map (fun ( x ) -> (let _70_18937 = (let _70_18936 = (let _70_18935 = (kind_star x.Microsoft_FStar_Absyn_Syntax.idRange)
in (x, _70_18935))
in Microsoft_FStar_Parser_AST.TAnnotated (_70_18936))
in (Microsoft_FStar_Parser_AST.mk_binder _70_18937 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type (Some (Microsoft_FStar_Absyn_Syntax.Implicit)))))))
in (let t = (match ((let _70_18938 = (unlabel t)
in _70_18938.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Product (_43_581) -> begin
t
end
| _43_584 -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.App (((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.effect_Tot_lid)) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level), t, Microsoft_FStar_Parser_AST.Nothing))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
end)
in (let result = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((binders, t))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
in result)))
end)))

let rec uncurry = (fun ( bs ) ( t ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Product ((binders, t)) -> begin
(uncurry (Support.List.append bs binders) t)
end
| _43_594 -> begin
(bs, t)
end))

let rec is_app_pattern = (fun ( p ) -> (match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed ((p, _43_598)) -> begin
(is_app_pattern p)
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar (_43_604); Microsoft_FStar_Parser_AST.prange = _43_602}, _43_608)) -> begin
true
end
| _43_612 -> begin
false
end))

let rec destruct_app_pattern = (fun ( env ) ( is_top_level ) ( p ) -> (match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed ((p, t)) -> begin
(let _43_624 = (destruct_app_pattern env is_top_level p)
in (match (_43_624) with
| (name, args, _43_623) -> begin
(name, args, Some (t))
end))
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((id, _43_629)); Microsoft_FStar_Parser_AST.prange = _43_626}, args)) when is_top_level -> begin
(let _70_18952 = (let _70_18951 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in Support.Microsoft.FStar.Util.Inr (_70_18951))
in (_70_18952, args, None))
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((id, _43_640)); Microsoft_FStar_Parser_AST.prange = _43_637}, args)) -> begin
(Support.Microsoft.FStar.Util.Inl (id), args, None)
end
| _43_648 -> begin
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

let binder_of_bnd = (fun ( _43_3 ) -> (match (_43_3) with
| TBinder ((a, k, aq)) -> begin
(Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)), aq)
end
| VBinder ((x, t, aq)) -> begin
(Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)), aq)
end
| _43_667 -> begin
(Support.All.failwith "Impossible")
end))

let as_binder = (fun ( env ) ( imp ) ( _43_4 ) -> (match (_43_4) with
| Support.Microsoft.FStar.Util.Inl ((None, k)) -> begin
(let _70_18982 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (_70_18982, env))
end
| Support.Microsoft.FStar.Util.Inr ((None, t)) -> begin
(let _70_18983 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_70_18983, env))
end
| Support.Microsoft.FStar.Util.Inl ((Some (a), k)) -> begin
(let _43_686 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_43_686) with
| (env, a) -> begin
((Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)), imp), env)
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _43_694 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_43_694) with
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
| _43_704 -> begin
(let _70_18994 = (Support.Microsoft.FStar.Range.string_of_range f.Microsoft_FStar_Parser_AST.range)
in (Support.Microsoft.FStar.Util.format2 "%s at %s" tag _70_18994))
end)
in (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Labeled ((f, msg, polarity))) f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level)))
in (let rec aux = (fun ( f ) -> (match (f.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (g) -> begin
(let _70_18998 = (let _70_18997 = (aux g)
in Microsoft_FStar_Parser_AST.Paren (_70_18997))
in (Microsoft_FStar_Parser_AST.mk_term _70_18998 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Op (("/\\", f1::f2::[])) -> begin
(let _70_19004 = (let _70_19003 = (let _70_19002 = (let _70_19001 = (aux f1)
in (let _70_19000 = (let _70_18999 = (aux f2)
in (_70_18999)::[])
in (_70_19001)::_70_19000))
in ("/\\", _70_19002))
in Microsoft_FStar_Parser_AST.Op (_70_19003))
in (Microsoft_FStar_Parser_AST.mk_term _70_19004 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.If ((f1, f2, f3)) -> begin
(let _70_19008 = (let _70_19007 = (let _70_19006 = (aux f2)
in (let _70_19005 = (aux f3)
in (f1, _70_19006, _70_19005)))
in Microsoft_FStar_Parser_AST.If (_70_19007))
in (Microsoft_FStar_Parser_AST.mk_term _70_19008 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Abs ((binders, g)) -> begin
(let _70_19011 = (let _70_19010 = (let _70_19009 = (aux g)
in (binders, _70_19009))
in Microsoft_FStar_Parser_AST.Abs (_70_19010))
in (Microsoft_FStar_Parser_AST.mk_term _70_19011 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| _43_726 -> begin
(label f)
end))
in (aux f))))

let mk_lb = (fun ( _43_730 ) -> (match (_43_730) with
| (n, t, e) -> begin
{Microsoft_FStar_Absyn_Syntax.lbname = n; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = Microsoft_FStar_Absyn_Const.effect_ALL_lid; Microsoft_FStar_Absyn_Syntax.lbdef = e}
end))

let rec desugar_data_pat = (fun ( env ) ( p ) -> (let resolvex = (fun ( l ) ( e ) ( x ) -> (match ((Support.All.pipe_right l (Support.Microsoft.FStar.Util.find_opt (fun ( _43_5 ) -> (match (_43_5) with
| Support.Microsoft.FStar.Util.Inr (y) -> begin
(y.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText = x.Microsoft_FStar_Absyn_Syntax.idText)
end
| _43_741 -> begin
false
end))))) with
| Some (Support.Microsoft.FStar.Util.Inr (y)) -> begin
(l, e, y)
end
| _43_746 -> begin
(let _43_749 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding e x)
in (match (_43_749) with
| (e, x) -> begin
((Support.Microsoft.FStar.Util.Inr (x))::l, e, x)
end))
end))
in (let resolvea = (fun ( l ) ( e ) ( a ) -> (match ((Support.All.pipe_right l (Support.Microsoft.FStar.Util.find_opt (fun ( _43_6 ) -> (match (_43_6) with
| Support.Microsoft.FStar.Util.Inl (b) -> begin
(b.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText = a.Microsoft_FStar_Absyn_Syntax.idText)
end
| _43_758 -> begin
false
end))))) with
| Some (Support.Microsoft.FStar.Util.Inl (b)) -> begin
(l, e, b)
end
| _43_763 -> begin
(let _43_766 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding e a)
in (match (_43_766) with
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
(let _43_786 = (aux loc env p)
in (match (_43_786) with
| (loc, env, var, p) -> begin
(let _43_801 = (Support.List.fold_left (fun ( _43_790 ) ( p ) -> (match (_43_790) with
| (loc, env, ps) -> begin
(let _43_797 = (aux loc env p)
in (match (_43_797) with
| (loc, env, _43_795, p) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_43_801) with
| (loc, env, ps) -> begin
(let pat = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_disj ((p)::(Support.List.rev ps))))
in (let _43_803 = (let _70_19083 = (Microsoft_FStar_Absyn_Syntax.pat_vars pat)
in (Support.Prims.ignore _70_19083))
in (loc, env, var, pat)))
end))
end))
end
| Microsoft_FStar_Parser_AST.PatAscribed ((p, t)) -> begin
(let p = (match ((is_kind env t)) with
| true -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatTvar (_43_810) -> begin
p
end
| Microsoft_FStar_Parser_AST.PatVar ((x, imp)) -> begin
(let _43_816 = p
in {Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatTvar ((x, imp)); Microsoft_FStar_Parser_AST.prange = _43_816.Microsoft_FStar_Parser_AST.prange})
end
| _43_819 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern", p.Microsoft_FStar_Parser_AST.prange))))
end)
end
| false -> begin
p
end)
in (let _43_825 = (aux loc env p)
in (match (_43_825) with
| (loc, env', binder, p) -> begin
(let binder = (match (binder) with
| LetBinder (_43_827) -> begin
(Support.All.failwith "impossible")
end
| TBinder ((x, _43_831, aq)) -> begin
(let _70_19085 = (let _70_19084 = (desugar_kind env t)
in (x, _70_19084, aq))
in TBinder (_70_19085))
end
| VBinder ((x, _43_837, aq)) -> begin
(let t = (close_fun env t)
in (let _70_19087 = (let _70_19086 = (desugar_typ env t)
in (x, _70_19086, aq))
in VBinder (_70_19087)))
end)
in (loc, env', binder, p))
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
in (let _70_19088 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_twild ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a Microsoft_FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((a, Microsoft_FStar_Absyn_Syntax.kun, aq)), _70_19088)))
end
| false -> begin
(let _43_852 = (resolvea loc env a)
in (match (_43_852) with
| (loc, env, abvd) -> begin
(let _70_19089 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_tvar ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s abvd Microsoft_FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((abvd, Microsoft_FStar_Absyn_Syntax.kun, aq)), _70_19089))
end))
end))
end
| Microsoft_FStar_Parser_AST.PatWild -> begin
(let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let y = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _70_19090 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_wild ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s y Microsoft_FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _70_19090))))
end
| Microsoft_FStar_Parser_AST.PatConst (c) -> begin
(let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _70_19091 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_constant (c)))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _70_19091)))
end
| Microsoft_FStar_Parser_AST.PatVar ((x, imp)) -> begin
(let aq = (match (imp) with
| true -> begin
Some (Microsoft_FStar_Absyn_Syntax.Implicit)
end
| false -> begin
None
end)
in (let _43_867 = (resolvex loc env x)
in (match (_43_867) with
| (loc, env, xbvd) -> begin
(let _70_19092 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_var (((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s xbvd Microsoft_FStar_Absyn_Syntax.tun), imp))))
in (loc, env, VBinder ((xbvd, Microsoft_FStar_Absyn_Syntax.tun, aq)), _70_19092))
end)))
end
| Microsoft_FStar_Parser_AST.PatName (l) -> begin
(let l = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _70_19093 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), []))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _70_19093))))
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatName (l); Microsoft_FStar_Parser_AST.prange = _43_873}, args)) -> begin
(let _43_894 = (Support.List.fold_right (fun ( arg ) ( _43_884 ) -> (match (_43_884) with
| (loc, env, args) -> begin
(let _43_890 = (aux loc env arg)
in (match (_43_890) with
| (loc, env, _43_888, arg) -> begin
(loc, env, (arg)::args)
end))
end)) args (loc, env, []))
in (match (_43_894) with
| (loc, env, args) -> begin
(let l = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _70_19096 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _70_19096))))
end))
end
| Microsoft_FStar_Parser_AST.PatApp (_43_898) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern", p.Microsoft_FStar_Parser_AST.prange))))
end
| Microsoft_FStar_Parser_AST.PatList (pats) -> begin
(let _43_916 = (Support.List.fold_right (fun ( pat ) ( _43_906 ) -> (match (_43_906) with
| (loc, env, pats) -> begin
(let _43_912 = (aux loc env pat)
in (match (_43_912) with
| (loc, env, _43_910, pat) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_43_916) with
| (loc, env, pats) -> begin
(let pat = (let _70_19109 = (let _70_19108 = (let _70_19104 = (Support.Microsoft.FStar.Range.end_range p.Microsoft_FStar_Parser_AST.prange)
in (pos_r _70_19104))
in (let _70_19107 = (let _70_19106 = (let _70_19105 = (Microsoft_FStar_Absyn_Util.fv Microsoft_FStar_Absyn_Const.nil_lid)
in (_70_19105, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), []))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_70_19106))
in (Support.All.pipe_left _70_19108 _70_19107)))
in (Support.List.fold_right (fun ( hd ) ( tl ) -> (let r = (Support.Microsoft.FStar.Range.union_ranges hd.Microsoft_FStar_Absyn_Syntax.p tl.Microsoft_FStar_Absyn_Syntax.p)
in (let _70_19103 = (let _70_19102 = (let _70_19101 = (Microsoft_FStar_Absyn_Util.fv Microsoft_FStar_Absyn_Const.cons_lid)
in (_70_19101, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), (hd)::(tl)::[]))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_70_19102))
in (Support.All.pipe_left (pos_r r) _70_19103)))) pats _70_19109))
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), pat)))
end))
end
| Microsoft_FStar_Parser_AST.PatTuple ((args, dep)) -> begin
(let _43_940 = (Support.List.fold_left (fun ( _43_929 ) ( p ) -> (match (_43_929) with
| (loc, env, pats) -> begin
(let _43_936 = (aux loc env p)
in (match (_43_936) with
| (loc, env, _43_934, pat) -> begin
(loc, env, (pat)::pats)
end))
end)) (loc, env, []) args)
in (match (_43_940) with
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
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, _43_946)) -> begin
v
end
| _43_950 -> begin
(Support.All.failwith "impossible")
end)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _70_19112 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _70_19112)))))))
end))
end
| Microsoft_FStar_Parser_AST.PatRecord ([]) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern", p.Microsoft_FStar_Parser_AST.prange))))
end
| Microsoft_FStar_Parser_AST.PatRecord (fields) -> begin
(let _43_960 = (Support.List.hd fields)
in (match (_43_960) with
| (f, _43_959) -> begin
(let _43_964 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_43_964) with
| (record, _43_963) -> begin
(let fields = (Support.All.pipe_right fields (Support.List.map (fun ( _43_967 ) -> (match (_43_967) with
| (f, p) -> begin
(let _70_19114 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in (_70_19114, p))
end))))
in (let args = (Support.All.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map (fun ( _43_972 ) -> (match (_43_972) with
| (f, _43_971) -> begin
(match ((Support.All.pipe_right fields (Support.List.tryFind (fun ( _43_976 ) -> (match (_43_976) with
| (g, _43_975) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals f g)
end))))) with
| None -> begin
(Microsoft_FStar_Parser_AST.mk_pattern Microsoft_FStar_Parser_AST.PatWild p.Microsoft_FStar_Parser_AST.prange)
end
| Some ((_43_979, p)) -> begin
p
end)
end))))
in (let app = (Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatApp (((Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatName (record.Microsoft_FStar_Parser_DesugarEnv.constrname)) p.Microsoft_FStar_Parser_AST.prange), args))) p.Microsoft_FStar_Parser_AST.prange)
in (let _43_989 = (aux loc env app)
in (match (_43_989) with
| (env, e, b, p) -> begin
(let p = (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, _43_992, args)) -> begin
(let _70_19122 = (let _70_19121 = (let _70_19120 = (let _70_19119 = (let _70_19118 = (let _70_19117 = (Support.All.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map Support.Prims.fst))
in (record.Microsoft_FStar_Parser_DesugarEnv.typename, _70_19117))
in Microsoft_FStar_Absyn_Syntax.Record_ctor (_70_19118))
in Some (_70_19119))
in (fv, _70_19120, args))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_70_19121))
in (Support.All.pipe_left pos _70_19122))
end
| _43_997 -> begin
p
end)
in (env, e, b, p))
end)))))
end))
end))
end))))
in (let _43_1004 = (aux [] env p)
in (match (_43_1004) with
| (_43_1000, env, b, p) -> begin
(env, b, p)
end))))))
and desugar_binding_pat_maybe_top = (fun ( top ) ( env ) ( p ) -> (match (top) with
| true -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatVar ((x, _43_1010)) -> begin
(let _70_19128 = (let _70_19127 = (let _70_19126 = (Microsoft_FStar_Parser_DesugarEnv.qualify env x)
in (_70_19126, Microsoft_FStar_Absyn_Syntax.tun))
in LetBinder (_70_19127))
in (env, _70_19128, None))
end
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((x, _43_1017)); Microsoft_FStar_Parser_AST.prange = _43_1014}, t)) -> begin
(let _70_19132 = (let _70_19131 = (let _70_19130 = (Microsoft_FStar_Parser_DesugarEnv.qualify env x)
in (let _70_19129 = (desugar_typ env t)
in (_70_19130, _70_19129)))
in LetBinder (_70_19131))
in (env, _70_19132, None))
end
| _43_1025 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern at the top-level", p.Microsoft_FStar_Parser_AST.prange))))
end)
end
| false -> begin
(let _43_1029 = (desugar_data_pat env p)
in (match (_43_1029) with
| (env, binder, p) -> begin
(let p = (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_var (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_wild (_)) -> begin
None
end
| _43_1040 -> begin
Some (p)
end)
in (env, binder, p))
end))
end))
and desugar_binding_pat = (fun ( env ) ( p ) -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top = (fun ( _43_1044 ) ( env ) ( pat ) -> (let _43_1052 = (desugar_data_pat env pat)
in (match (_43_1052) with
| (env, _43_1050, pat) -> begin
(env, pat)
end)))
and desugar_match_pat = (fun ( env ) ( p ) -> (desugar_match_pat_maybe_top false env p))
and desugar_typ_or_exp = (fun ( env ) ( t ) -> (match ((is_type env t)) with
| true -> begin
(let _70_19142 = (desugar_typ env t)
in Support.Microsoft.FStar.Util.Inl (_70_19142))
end
| false -> begin
(let _70_19143 = (desugar_exp env t)
in Support.Microsoft.FStar.Util.Inr (_70_19143))
end))
and desugar_exp = (fun ( env ) ( e ) -> (desugar_exp_maybe_top false env e))
and desugar_exp_maybe_top = (fun ( top_level ) ( env ) ( top ) -> (let pos = (fun ( e ) -> (e None top.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( e ) -> (let _43_1066 = e
in {Microsoft_FStar_Absyn_Syntax.n = _43_1066.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _43_1066.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = top.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _43_1066.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _43_1066.Microsoft_FStar_Absyn_Syntax.uvs}))
in (match ((let _70_19163 = (unparen top)
in _70_19163.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Const (c) -> begin
(Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match ((op_as_vlid env (Support.List.length args) top.Microsoft_FStar_Parser_AST.range s)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat "Unexpected operator: " s), top.Microsoft_FStar_Parser_AST.range))))
end
| Some (l) -> begin
(let op = (let _70_19166 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (Microsoft_FStar_Absyn_Util.fvar None l _70_19166))
in (let args = (Support.All.pipe_right args (Support.List.map (fun ( t ) -> (let _70_19168 = (desugar_typ_or_exp env t)
in (_70_19168, None)))))
in (let _70_19169 = (Microsoft_FStar_Absyn_Util.mk_exp_app op args)
in (Support.All.pipe_left setpos _70_19169))))
end)
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) -> begin
(match ((l.Microsoft_FStar_Absyn_Syntax.str = "ref")) with
| true -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env Microsoft_FStar_Absyn_Const.alloc_lid)) with
| None -> begin
(let _70_19172 = (let _70_19171 = (let _70_19170 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in ("Identifier \'ref\' not found; include lib/st.fst in your path", _70_19170))
in Microsoft_FStar_Absyn_Syntax.Error (_70_19171))
in (raise (_70_19172)))
end
| Some (e) -> begin
(setpos e)
end)
end
| false -> begin
(let _70_19173 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (Support.All.pipe_left setpos _70_19173))
end)
end
| Microsoft_FStar_Parser_AST.Construct ((l, args)) -> begin
(let dt = (let _70_19178 = (let _70_19177 = (let _70_19176 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (_70_19176, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _70_19177))
in (Support.All.pipe_left pos _70_19178))
in (match (args) with
| [] -> begin
dt
end
| _43_1093 -> begin
(let args = (Support.List.map (fun ( _43_1096 ) -> (match (_43_1096) with
| (t, imp) -> begin
(let te = (desugar_typ_or_exp env t)
in (arg_withimp_e imp te))
end)) args)
in (let _70_19183 = (let _70_19182 = (let _70_19181 = (let _70_19180 = (Microsoft_FStar_Absyn_Util.mk_exp_app dt args)
in (_70_19180, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_70_19181))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _70_19182))
in (Support.All.pipe_left setpos _70_19183)))
end))
end
| Microsoft_FStar_Parser_AST.Abs ((binders, body)) -> begin
(let _43_1133 = (Support.List.fold_left (fun ( _43_1105 ) ( pat ) -> (match (_43_1105) with
| (env, ftvs) -> begin
(match (pat.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatTvar ((a, imp)); Microsoft_FStar_Parser_AST.prange = _43_1108}, t)) -> begin
(let ftvs = (let _70_19186 = (free_type_vars env t)
in (Support.List.append _70_19186 ftvs))
in (let _70_19188 = (let _70_19187 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (Support.All.pipe_left Support.Prims.fst _70_19187))
in (_70_19188, ftvs)))
end
| Microsoft_FStar_Parser_AST.PatTvar ((a, _43_1120)) -> begin
(let _70_19190 = (let _70_19189 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (Support.All.pipe_left Support.Prims.fst _70_19189))
in (_70_19190, ftvs))
end
| Microsoft_FStar_Parser_AST.PatAscribed ((_43_1124, t)) -> begin
(let _70_19192 = (let _70_19191 = (free_type_vars env t)
in (Support.List.append _70_19191 ftvs))
in (env, _70_19192))
end
| _43_1129 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_43_1133) with
| (_43_1131, ftv) -> begin
(let ftv = (sort_ftv ftv)
in (let binders = (let _70_19194 = (Support.All.pipe_right ftv (Support.List.map (fun ( a ) -> (Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatTvar ((a, true))) top.Microsoft_FStar_Parser_AST.range))))
in (Support.List.append _70_19194 binders))
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
(let _43_1156 = (desugar_binding_pat env p)
in (match (_43_1156) with
| (env, b, pat) -> begin
(let _43_1216 = (match (b) with
| LetBinder (_43_1158) -> begin
(Support.All.failwith "Impossible")
end
| TBinder ((a, k, aq)) -> begin
(let _70_19203 = (binder_of_bnd b)
in (_70_19203, sc_pat_opt))
end
| VBinder ((x, t, aq)) -> begin
(let b = (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)
in (let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _43_1173) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _70_19205 = (let _70_19204 = (Microsoft_FStar_Absyn_Util.bvar_to_exp b)
in (_70_19204, p))
in Some (_70_19205))
end
| (Some (p), Some ((sc, p'))) -> begin
(match ((sc.Microsoft_FStar_Absyn_Syntax.n, p'.Microsoft_FStar_Absyn_Syntax.v)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_43_1187), _43_1190) -> begin
(let tup = (Microsoft_FStar_Absyn_Util.mk_tuple_data_lid 2 top.Microsoft_FStar_Parser_AST.range)
in (let sc = (let _70_19212 = (let _70_19211 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) tup top.Microsoft_FStar_Parser_AST.range)
in (let _70_19210 = (let _70_19209 = (Microsoft_FStar_Absyn_Syntax.varg sc)
in (let _70_19208 = (let _70_19207 = (let _70_19206 = (Microsoft_FStar_Absyn_Util.bvar_to_exp b)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.varg _70_19206))
in (_70_19207)::[])
in (_70_19209)::_70_19208))
in (_70_19211, _70_19210)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _70_19212 None top.Microsoft_FStar_Parser_AST.range))
in (let p = (let _70_19216 = (let _70_19214 = (let _70_19213 = (Microsoft_FStar_Absyn_Util.fv tup)
in (_70_19213, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), (p')::(p)::[]))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_70_19214))
in (let _70_19215 = (Support.Microsoft.FStar.Range.union_ranges p'.Microsoft_FStar_Absyn_Syntax.p p.Microsoft_FStar_Absyn_Syntax.p)
in (Microsoft_FStar_Absyn_Util.withinfo _70_19216 None _70_19215)))
in Some ((sc, p)))))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app ((_43_1196, args)), Microsoft_FStar_Absyn_Syntax.Pat_cons ((_43_1201, _43_1203, pats))) -> begin
(let tup = (Microsoft_FStar_Absyn_Util.mk_tuple_data_lid (1 + (Support.List.length args)) top.Microsoft_FStar_Parser_AST.range)
in (let sc = (let _70_19222 = (let _70_19221 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) tup top.Microsoft_FStar_Parser_AST.range)
in (let _70_19220 = (let _70_19219 = (let _70_19218 = (let _70_19217 = (Microsoft_FStar_Absyn_Util.bvar_to_exp b)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.varg _70_19217))
in (_70_19218)::[])
in (Support.List.append args _70_19219))
in (_70_19221, _70_19220)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _70_19222 None top.Microsoft_FStar_Parser_AST.range))
in (let p = (let _70_19226 = (let _70_19224 = (let _70_19223 = (Microsoft_FStar_Absyn_Util.fv tup)
in (_70_19223, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), (Support.List.append pats ((p)::[]))))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_70_19224))
in (let _70_19225 = (Support.Microsoft.FStar.Range.union_ranges p'.Microsoft_FStar_Absyn_Syntax.p p.Microsoft_FStar_Absyn_Syntax.p)
in (Microsoft_FStar_Absyn_Util.withinfo _70_19226 None _70_19225)))
in Some ((sc, p)))))
end
| _43_1212 -> begin
(Support.All.failwith "Impossible")
end)
end)
in ((Support.Microsoft.FStar.Util.Inr (b), aq), sc_pat_opt)))
end)
in (match (_43_1216) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| Microsoft_FStar_Parser_AST.App (({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Var (a); Microsoft_FStar_Parser_AST.range = _43_1220; Microsoft_FStar_Parser_AST.level = _43_1218}, arg, _43_1226)) when ((Microsoft_FStar_Absyn_Syntax.lid_equals a Microsoft_FStar_Absyn_Const.assert_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals a Microsoft_FStar_Absyn_Const.assume_lid)) -> begin
(let phi = (desugar_formula env arg)
in (let _70_19237 = (let _70_19236 = (let _70_19235 = (let _70_19229 = (Microsoft_FStar_Absyn_Syntax.range_of_lid a)
in (Microsoft_FStar_Absyn_Util.fvar None a _70_19229))
in (let _70_19234 = (let _70_19233 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ phi)
in (let _70_19232 = (let _70_19231 = (let _70_19230 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant Microsoft_FStar_Absyn_Syntax.Const_unit None top.Microsoft_FStar_Parser_AST.range)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.varg _70_19230))
in (_70_19231)::[])
in (_70_19233)::_70_19232))
in (_70_19235, _70_19234)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _70_19236))
in (Support.All.pipe_left pos _70_19237)))
end
| Microsoft_FStar_Parser_AST.App (_43_1231) -> begin
(let rec aux = (fun ( args ) ( e ) -> (match ((let _70_19242 = (unparen e)
in _70_19242.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((e, t, imp)) -> begin
(let arg = (let _70_19243 = (desugar_typ_or_exp env t)
in (Support.All.pipe_left (arg_withimp_e imp) _70_19243))
in (aux ((arg)::args) e))
end
| _43_1243 -> begin
(let head = (desugar_exp env e)
in (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (head, args))))
end))
in (aux [] top))
end
| Microsoft_FStar_Parser_AST.Seq ((t1, t2)) -> begin
(let _70_19249 = (let _70_19248 = (let _70_19247 = (let _70_19246 = (desugar_exp env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Let ((false, (((Microsoft_FStar_Parser_AST.mk_pattern Microsoft_FStar_Parser_AST.PatWild t1.Microsoft_FStar_Parser_AST.range), t1))::[], t2))) top.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Expr))
in (_70_19246, Microsoft_FStar_Absyn_Syntax.Sequence))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_70_19247))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _70_19248))
in (Support.All.pipe_left setpos _70_19249))
end
| Microsoft_FStar_Parser_AST.Let ((is_rec, (pat, _snd)::_tl, body)) -> begin
(let ds_let_rec = (fun ( _43_1259 ) -> (match (()) with
| () -> begin
(let bindings = ((pat, _snd))::_tl
in (let funs = (Support.All.pipe_right bindings (Support.List.map (fun ( _43_1263 ) -> (match (_43_1263) with
| (p, def) -> begin
(match ((is_app_pattern p)) with
| true -> begin
(let _70_19253 = (destruct_app_pattern env top_level p)
in (_70_19253, def))
end
| false -> begin
(match ((Microsoft_FStar_Parser_AST.un_function p def)) with
| Some ((p, def)) -> begin
(let _70_19254 = (destruct_app_pattern env top_level p)
in (_70_19254, def))
end
| _43_1269 -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((id, _43_1274)); Microsoft_FStar_Parser_AST.prange = _43_1271}, t)) -> begin
(match (top_level) with
| true -> begin
(let _70_19257 = (let _70_19256 = (let _70_19255 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in Support.Microsoft.FStar.Util.Inr (_70_19255))
in (_70_19256, [], Some (t)))
in (_70_19257, def))
end
| false -> begin
((Support.Microsoft.FStar.Util.Inl (id), [], Some (t)), def)
end)
end
| Microsoft_FStar_Parser_AST.PatVar ((id, _43_1283)) -> begin
(match (top_level) with
| true -> begin
(let _70_19260 = (let _70_19259 = (let _70_19258 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in Support.Microsoft.FStar.Util.Inr (_70_19258))
in (_70_19259, [], None))
in (_70_19260, def))
end
| false -> begin
((Support.Microsoft.FStar.Util.Inl (id), [], None), def)
end)
end
| _43_1287 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected let binding", p.Microsoft_FStar_Parser_AST.prange))))
end)
end)
end)
end))))
in (let _43_1313 = (Support.List.fold_left (fun ( _43_1291 ) ( _43_1300 ) -> (match ((_43_1291, _43_1300)) with
| ((env, fnames), ((f, _43_1294, _43_1296), _43_1299)) -> begin
(let _43_1310 = (match (f) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(let _43_1305 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_43_1305) with
| (env, xx) -> begin
(env, Support.Microsoft.FStar.Util.Inl (xx))
end))
end
| Support.Microsoft.FStar.Util.Inr (l) -> begin
(let _70_19263 = (Microsoft_FStar_Parser_DesugarEnv.push_rec_binding env (Microsoft_FStar_Parser_DesugarEnv.Binding_let (l)))
in (_70_19263, Support.Microsoft.FStar.Util.Inr (l)))
end)
in (match (_43_1310) with
| (env, lbname) -> begin
(env, (lbname)::fnames)
end))
end)) (env, []) funs)
in (match (_43_1313) with
| (env', fnames) -> begin
(let fnames = (Support.List.rev fnames)
in (let desugar_one_def = (fun ( env ) ( lbname ) ( _43_1324 ) -> (match (_43_1324) with
| ((_43_1319, args, result_t), def) -> begin
(let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _70_19270 = (Support.Microsoft.FStar.Range.union_ranges t.Microsoft_FStar_Parser_AST.range def.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Ascribed ((def, t))) _70_19270 Microsoft_FStar_Parser_AST.Expr))
end)
in (let def = (match (args) with
| [] -> begin
def
end
| _43_1331 -> begin
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
in (let _43_1344 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_43_1344) with
| (env, binder, pat) -> begin
(match (binder) with
| TBinder (_43_1346) -> begin
(Support.All.failwith "Unexpected type binder in let")
end
| LetBinder ((l, t)) -> begin
(let body = (desugar_exp env t2)
in (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((false, ({Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = Microsoft_FStar_Absyn_Const.effect_ALL_lid; Microsoft_FStar_Absyn_Syntax.lbdef = t1})::[]), body))))
end
| VBinder ((x, t, _43_1356)) -> begin
(let body = (desugar_exp env t2)
in (let body = (match (pat) with
| (None) | (Some ({Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_wild (_); Microsoft_FStar_Absyn_Syntax.sort = _; Microsoft_FStar_Absyn_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _70_19282 = (let _70_19281 = (Microsoft_FStar_Absyn_Util.bvd_to_exp x t)
in (_70_19281, ((pat, None, body))::[]))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _70_19282 None body.Microsoft_FStar_Absyn_Syntax.pos))
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
(let _70_19295 = (let _70_19294 = (let _70_19293 = (desugar_exp env t1)
in (let _70_19292 = (let _70_19291 = (let _70_19287 = (desugar_exp env t2)
in ((Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (true))) None t2.Microsoft_FStar_Parser_AST.range), None, _70_19287))
in (let _70_19290 = (let _70_19289 = (let _70_19288 = (desugar_exp env t3)
in ((Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (false))) None t3.Microsoft_FStar_Parser_AST.range), None, _70_19288))
in (_70_19289)::[])
in (_70_19291)::_70_19290))
in (_70_19293, _70_19292)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _70_19294))
in (Support.All.pipe_left pos _70_19295))
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
(let desugar_branch = (fun ( _43_1395 ) -> (match (_43_1395) with
| (pat, wopt, b) -> begin
(let _43_1398 = (desugar_match_pat env pat)
in (match (_43_1398) with
| (env, pat) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _70_19298 = (desugar_exp env e)
in Some (_70_19298))
end)
in (let b = (desugar_exp env b)
in (pat, wopt, b)))
end))
end))
in (let _70_19304 = (let _70_19303 = (let _70_19302 = (desugar_exp env e)
in (let _70_19301 = (Support.List.map desugar_branch branches)
in (_70_19302, _70_19301)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _70_19303))
in (Support.All.pipe_left pos _70_19304)))
end
| Microsoft_FStar_Parser_AST.Ascribed ((e, t)) -> begin
(let _70_19310 = (let _70_19309 = (let _70_19308 = (desugar_exp env e)
in (let _70_19307 = (desugar_typ env t)
in (_70_19308, _70_19307, None)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed _70_19309))
in (Support.All.pipe_left pos _70_19310))
end
| Microsoft_FStar_Parser_AST.Record ((_43_1409, [])) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected empty record", top.Microsoft_FStar_Parser_AST.range))))
end
| Microsoft_FStar_Parser_AST.Record ((eopt, fields)) -> begin
(let _43_1420 = (Support.List.hd fields)
in (match (_43_1420) with
| (f, _43_1419) -> begin
(let qfn = (fun ( g ) -> (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append f.Microsoft_FStar_Absyn_Syntax.ns ((g)::[]))))
in (let _43_1426 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_43_1426) with
| (record, _43_1425) -> begin
(let get_field = (fun ( xopt ) ( f ) -> (let fn = f.Microsoft_FStar_Absyn_Syntax.ident
in (let found = (Support.All.pipe_right fields (Support.Microsoft.FStar.Util.find_opt (fun ( _43_1434 ) -> (match (_43_1434) with
| (g, _43_1433) -> begin
(let gn = g.Microsoft_FStar_Absyn_Syntax.ident
in (fn.Microsoft_FStar_Absyn_Syntax.idText = gn.Microsoft_FStar_Absyn_Syntax.idText))
end))))
in (match (found) with
| Some ((_43_1438, e)) -> begin
(let _70_19318 = (qfn fn)
in (_70_19318, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _70_19322 = (let _70_19321 = (let _70_19320 = (let _70_19319 = (Microsoft_FStar_Absyn_Syntax.text_of_lid f)
in (Support.Microsoft.FStar.Util.format1 "Field %s is missing" _70_19319))
in (_70_19320, top.Microsoft_FStar_Parser_AST.range))
in Microsoft_FStar_Absyn_Syntax.Error (_70_19321))
in (raise (_70_19322)))
end
| Some (x) -> begin
(let _70_19323 = (qfn fn)
in (_70_19323, (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Project ((x, f))) x.Microsoft_FStar_Parser_AST.range x.Microsoft_FStar_Parser_AST.level)))
end)
end))))
in (let recterm = (match (eopt) with
| None -> begin
(let _70_19328 = (let _70_19327 = (Support.All.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map (fun ( _43_1450 ) -> (match (_43_1450) with
| (f, _43_1449) -> begin
(let _70_19326 = (let _70_19325 = (get_field None f)
in (Support.All.pipe_left Support.Prims.snd _70_19325))
in (_70_19326, Microsoft_FStar_Parser_AST.Nothing))
end))))
in (record.Microsoft_FStar_Parser_DesugarEnv.constrname, _70_19327))
in Microsoft_FStar_Parser_AST.Construct (_70_19328))
end
| Some (e) -> begin
(let x = (Microsoft_FStar_Absyn_Util.genident (Some (e.Microsoft_FStar_Parser_AST.range)))
in (let xterm = (let _70_19330 = (let _70_19329 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((x)::[]))
in Microsoft_FStar_Parser_AST.Var (_70_19329))
in (Microsoft_FStar_Parser_AST.mk_term _70_19330 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr))
in (let record = (let _70_19333 = (let _70_19332 = (Support.All.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map (fun ( _43_1458 ) -> (match (_43_1458) with
| (f, _43_1457) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _70_19332))
in Microsoft_FStar_Parser_AST.Record (_70_19333))
in Microsoft_FStar_Parser_AST.Let ((false, (((Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatVar ((x, false))) x.Microsoft_FStar_Absyn_Syntax.idRange), e))::[], (Microsoft_FStar_Parser_AST.mk_term record top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))))))
end)
in (let recterm = (Microsoft_FStar_Parser_AST.mk_term recterm top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level)
in (let e = (desugar_exp env recterm)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _43_1481)); Microsoft_FStar_Absyn_Syntax.tk = _43_1478; Microsoft_FStar_Absyn_Syntax.pos = _43_1476; Microsoft_FStar_Absyn_Syntax.fvs = _43_1474; Microsoft_FStar_Absyn_Syntax.uvs = _43_1472}, args)); Microsoft_FStar_Absyn_Syntax.tk = _43_1470; Microsoft_FStar_Absyn_Syntax.pos = _43_1468; Microsoft_FStar_Absyn_Syntax.fvs = _43_1466; Microsoft_FStar_Absyn_Syntax.uvs = _43_1464}, Microsoft_FStar_Absyn_Syntax.Data_app))) -> begin
(let e = (let _70_19343 = (let _70_19342 = (let _70_19341 = (let _70_19340 = (let _70_19339 = (let _70_19338 = (let _70_19337 = (let _70_19336 = (Support.All.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map Support.Prims.fst))
in (record.Microsoft_FStar_Parser_DesugarEnv.typename, _70_19336))
in Microsoft_FStar_Absyn_Syntax.Record_ctor (_70_19337))
in Some (_70_19338))
in (fv, _70_19339))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _70_19340 None e.Microsoft_FStar_Absyn_Syntax.pos))
in (_70_19341, args))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _70_19342))
in (Support.All.pipe_left pos _70_19343))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Data_app)))))
end
| _43_1495 -> begin
e
end)))))
end)))
end))
end
| Microsoft_FStar_Parser_AST.Project ((e, f)) -> begin
(let _43_1503 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_43_1503) with
| (_43_1501, fieldname) -> begin
(let e = (desugar_exp env e)
in (let fn = (let _43_1508 = (Support.Microsoft.FStar.Util.prefix fieldname.Microsoft_FStar_Absyn_Syntax.ns)
in (match (_43_1508) with
| (ns, _43_1507) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append ns ((f.Microsoft_FStar_Absyn_Syntax.ident)::[])))
end))
in (let _70_19351 = (let _70_19350 = (let _70_19349 = (let _70_19346 = (Microsoft_FStar_Absyn_Syntax.range_of_lid f)
in (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Record_projector (fn))) fieldname _70_19346))
in (let _70_19348 = (let _70_19347 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_70_19347)::[])
in (_70_19349, _70_19348)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _70_19350))
in (Support.All.pipe_left pos _70_19351))))
end))
end
| Microsoft_FStar_Parser_AST.Paren (e) -> begin
(desugar_exp env e)
end
| _43_1513 -> begin
(Microsoft_FStar_Parser_AST.error "Unexpected term" top top.Microsoft_FStar_Parser_AST.range)
end))))
and desugar_typ = (fun ( env ) ( top ) -> (let wpos = (fun ( t ) -> (t None top.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( t ) -> (let _43_1520 = t
in {Microsoft_FStar_Absyn_Syntax.n = _43_1520.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _43_1520.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = top.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _43_1520.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _43_1520.Microsoft_FStar_Absyn_Syntax.uvs}))
in (let top = (unparen top)
in (let head_and_args = (fun ( t ) -> (let rec aux = (fun ( args ) ( t ) -> (match ((let _70_19374 = (unparen t)
in _70_19374.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((t, arg, imp)) -> begin
(aux (((arg, imp))::args) t)
end
| Microsoft_FStar_Parser_AST.Construct ((l, args')) -> begin
({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Name (l); Microsoft_FStar_Parser_AST.range = t.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Parser_AST.level = t.Microsoft_FStar_Parser_AST.level}, (Support.List.append args' args))
end
| _43_1538 -> begin
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
(let _70_19375 = (desugar_exp env t)
in (Support.All.pipe_right _70_19375 Microsoft_FStar_Absyn_Util.b2t))
end))
end
| Microsoft_FStar_Parser_AST.Ensures ((t, lopt)) -> begin
(let t = (label_conjuncts "post-condition" false lopt t)
in (match ((is_type env t)) with
| true -> begin
(desugar_typ env t)
end
| false -> begin
(let _70_19376 = (desugar_exp env t)
in (Support.All.pipe_right _70_19376 Microsoft_FStar_Absyn_Util.b2t))
end))
end
| Microsoft_FStar_Parser_AST.Op (("*", t1::_43_1552::[])) -> begin
(match ((is_type env t1)) with
| true -> begin
(let rec flatten = (fun ( t ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Op (("*", t1::t2::[])) -> begin
(let rest = (flatten t2)
in (t1)::rest)
end
| _43_1567 -> begin
(t)::[]
end))
in (let targs = (let _70_19381 = (flatten top)
in (Support.All.pipe_right _70_19381 (Support.List.map (fun ( t ) -> (let _70_19380 = (desugar_typ env t)
in (Microsoft_FStar_Absyn_Syntax.targ _70_19380))))))
in (let tup = (let _70_19382 = (Microsoft_FStar_Absyn_Util.mk_tuple_lid (Support.List.length targs) top.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) _70_19382))
in (Support.All.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))))
end
| false -> begin
(let _70_19388 = (let _70_19387 = (let _70_19386 = (let _70_19385 = (Microsoft_FStar_Parser_AST.term_to_string t1)
in (Support.Microsoft.FStar.Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _70_19385))
in (_70_19386, top.Microsoft_FStar_Parser_AST.range))
in Microsoft_FStar_Absyn_Syntax.Error (_70_19387))
in (raise (_70_19388)))
end)
end
| Microsoft_FStar_Parser_AST.Op (("=!=", args)) -> begin
(desugar_typ env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Op (("~", ((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Op (("==", args))) top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))::[]))) top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match ((op_as_tylid env (Support.List.length args) top.Microsoft_FStar_Parser_AST.range s)) with
| None -> begin
(let _70_19389 = (desugar_exp env top)
in (Support.All.pipe_right _70_19389 Microsoft_FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(let args = (Support.List.map (fun ( t ) -> (let _70_19391 = (desugar_typ_or_exp env t)
in (Support.All.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _70_19391))) args)
in (let _70_19392 = (Microsoft_FStar_Absyn_Util.ftv l Microsoft_FStar_Absyn_Syntax.kun)
in (Microsoft_FStar_Absyn_Util.mk_typ_app _70_19392 args)))
end)
end
| Microsoft_FStar_Parser_AST.Tvar (a) -> begin
(let _70_19393 = (Microsoft_FStar_Parser_DesugarEnv.fail_or2 (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (Support.All.pipe_left setpos _70_19393))
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) when ((Support.List.length l.Microsoft_FStar_Absyn_Syntax.ns) = 0) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env l.Microsoft_FStar_Absyn_Syntax.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _70_19394 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (Support.All.pipe_left setpos _70_19394))
end)
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) -> begin
(let l = (Microsoft_FStar_Absyn_Util.set_lid_range l top.Microsoft_FStar_Parser_AST.range)
in (let _70_19395 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (Support.All.pipe_left setpos _70_19395)))
end
| Microsoft_FStar_Parser_AST.Construct ((l, args)) -> begin
(let t = (let _70_19396 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (Support.All.pipe_left setpos _70_19396))
in (let args = (Support.List.map (fun ( _43_1603 ) -> (match (_43_1603) with
| (t, imp) -> begin
(let _70_19398 = (desugar_typ_or_exp env t)
in (Support.All.pipe_left (arg_withimp_t imp) _70_19398))
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
(let _43_1621 = (desugar_binding_pat env hd)
in (match (_43_1621) with
| (env, bnd, pat) -> begin
(match (pat) with
| Some (q) -> begin
(let _70_19410 = (let _70_19409 = (let _70_19408 = (let _70_19407 = (Microsoft_FStar_Absyn_Print.pat_to_string q)
in (Support.Microsoft.FStar.Util.format1 "Pattern matching at the type level is not supported; got %s\n" _70_19407))
in (_70_19408, hd.Microsoft_FStar_Parser_AST.prange))
in Microsoft_FStar_Absyn_Syntax.Error (_70_19409))
in (raise (_70_19410)))
end
| None -> begin
(let b = (binder_of_bnd bnd)
in (aux env ((b)::bs) tl))
end)
end))
end))
in (aux env [] binders))
end
| Microsoft_FStar_Parser_AST.App (_43_1627) -> begin
(let rec aux = (fun ( args ) ( e ) -> (match ((let _70_19415 = (unparen e)
in _70_19415.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((e, arg, imp)) -> begin
(let arg = (let _70_19416 = (desugar_typ_or_exp env arg)
in (Support.All.pipe_left (arg_withimp_t imp) _70_19416))
in (aux ((arg)::args) e))
end
| _43_1639 -> begin
(let head = (desugar_typ env e)
in (Support.All.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (head, args))))
end))
in (aux [] top))
end
| Microsoft_FStar_Parser_AST.Product (([], t)) -> begin
(Support.All.failwith "Impossible: product with no binders")
end
| Microsoft_FStar_Parser_AST.Product ((binders, t)) -> begin
(let _43_1651 = (uncurry binders t)
in (match (_43_1651) with
| (bs, t) -> begin
(let rec aux = (fun ( env ) ( bs ) ( _43_9 ) -> (match (_43_9) with
| [] -> begin
(let cod = (desugar_comp top.Microsoft_FStar_Parser_AST.range true env t)
in (Support.All.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun ((Support.List.rev bs), cod))))
end
| hd::tl -> begin
(let mlenv = (Microsoft_FStar_Parser_DesugarEnv.default_ml env)
in (let bb = (desugar_binder mlenv hd)
in (let _43_1665 = (as_binder env hd.Microsoft_FStar_Parser_AST.aqual bb)
in (match (_43_1665) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| Microsoft_FStar_Parser_AST.Refine ((b, f)) -> begin
(match ((desugar_exp_binder env b)) with
| (None, _43_1672) -> begin
(Support.All.failwith "Missing binder in refinement")
end
| b -> begin
(let _43_1686 = (match ((as_binder env None (Support.Microsoft.FStar.Util.Inr (b)))) with
| ((Support.Microsoft.FStar.Util.Inr (x), _43_1678), env) -> begin
(x, env)
end
| _43_1683 -> begin
(Support.All.failwith "impossible")
end)
in (match (_43_1686) with
| (b, env) -> begin
(let f = (match ((is_type env f)) with
| true -> begin
(desugar_formula env f)
end
| false -> begin
(let _70_19427 = (desugar_exp env f)
in (Support.All.pipe_right _70_19427 Microsoft_FStar_Absyn_Util.b2t))
end)
in (Support.All.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (b, f))))
end))
end)
end
| (Microsoft_FStar_Parser_AST.NamedTyp ((_, t))) | (Microsoft_FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| Microsoft_FStar_Parser_AST.Ascribed ((t, k)) -> begin
(let _70_19435 = (let _70_19434 = (let _70_19433 = (desugar_typ env t)
in (let _70_19432 = (desugar_kind env k)
in (_70_19433, _70_19432)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed' _70_19434))
in (Support.All.pipe_left wpos _70_19435))
end
| Microsoft_FStar_Parser_AST.Sum ((binders, t)) -> begin
(let _43_1720 = (Support.List.fold_left (fun ( _43_1705 ) ( b ) -> (match (_43_1705) with
| (env, tparams, typs) -> begin
(let _43_1709 = (desugar_exp_binder env b)
in (match (_43_1709) with
| (xopt, t) -> begin
(let _43_1715 = (match (xopt) with
| None -> begin
(let _70_19438 = (Microsoft_FStar_Absyn_Util.new_bvd (Some (top.Microsoft_FStar_Parser_AST.range)))
in (env, _70_19438))
end
| Some (x) -> begin
(Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_43_1715) with
| (env, x) -> begin
(let _70_19442 = (let _70_19441 = (let _70_19440 = (let _70_19439 = (Microsoft_FStar_Absyn_Util.close_with_lam tparams t)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _70_19439))
in (_70_19440)::[])
in (Support.List.append typs _70_19441))
in (env, (Support.List.append tparams (((Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)), None))::[])), _70_19442))
end))
end))
end)) (env, [], []) (Support.List.append binders (((Microsoft_FStar_Parser_AST.mk_binder (Microsoft_FStar_Parser_AST.NoName (t)) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Type None))::[])))
in (match (_43_1720) with
| (env, _43_1718, targs) -> begin
(let tup = (let _70_19443 = (Microsoft_FStar_Absyn_Util.mk_dtuple_lid (Support.List.length targs) top.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) _70_19443))
in (Support.All.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))
end))
end
| Microsoft_FStar_Parser_AST.Record (_43_1723) -> begin
(Support.All.failwith "Unexpected record type")
end
| (Microsoft_FStar_Parser_AST.If (_)) | (Microsoft_FStar_Parser_AST.Labeled (_)) -> begin
(desugar_formula env top)
end
| _43_1732 when (top.Microsoft_FStar_Parser_AST.level = Microsoft_FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _43_1734 -> begin
(Microsoft_FStar_Parser_AST.error "Expected a type" top top.Microsoft_FStar_Parser_AST.range)
end))))))
and desugar_comp = (fun ( r ) ( default_ok ) ( env ) ( t ) -> (let fail = (fun ( msg ) -> (raise (Microsoft_FStar_Absyn_Syntax.Error ((msg, r)))))
in (let pre_process_comp_typ = (fun ( t ) -> (let _43_1745 = (head_and_args t)
in (match (_43_1745) with
| (head, args) -> begin
(match (head.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Name (lemma) when (lemma.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "Lemma") -> begin
(let unit = ((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.unit_lid)) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Type), Microsoft_FStar_Parser_AST.Nothing)
in (let nil_pat = ((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.nil_lid)) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Expr), Microsoft_FStar_Parser_AST.Nothing)
in (let _43_1771 = (Support.All.pipe_right args (Support.List.partition (fun ( _43_1753 ) -> (match (_43_1753) with
| (arg, _43_1752) -> begin
(match ((let _70_19455 = (unparen arg)
in _70_19455.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App (({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Var (d); Microsoft_FStar_Parser_AST.range = _43_1757; Microsoft_FStar_Parser_AST.level = _43_1755}, _43_1762, _43_1764)) -> begin
(d.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "decreases")
end
| _43_1768 -> begin
false
end)
end))))
in (match (_43_1771) with
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
| Microsoft_FStar_Parser_AST.Name (tot) when (((tot.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "Tot") && (not ((Microsoft_FStar_Parser_DesugarEnv.is_effect_name env Microsoft_FStar_Absyn_Const.effect_Tot_lid)))) && (let _70_19456 = (Microsoft_FStar_Parser_DesugarEnv.current_module env)
in (Microsoft_FStar_Absyn_Syntax.lid_equals _70_19456 Microsoft_FStar_Absyn_Const.prims_lid))) -> begin
(let args = (Support.List.map (fun ( _43_1786 ) -> (match (_43_1786) with
| (t, imp) -> begin
(let _70_19458 = (desugar_typ_or_exp env t)
in (Support.All.pipe_left (arg_withimp_t imp) _70_19458))
end)) args)
in (let _70_19459 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.effect_Tot_lid Microsoft_FStar_Absyn_Syntax.kun)
in (Microsoft_FStar_Absyn_Util.mk_typ_app _70_19459 args)))
end
| _43_1789 -> begin
(desugar_typ env t)
end)
end)))
in (let t = (pre_process_comp_typ t)
in (let _43_1793 = (Microsoft_FStar_Absyn_Util.head_and_args t)
in (match (_43_1793) with
| (head, args) -> begin
(match ((let _70_19461 = (let _70_19460 = (Microsoft_FStar_Absyn_Util.compress_typ head)
in _70_19460.Microsoft_FStar_Absyn_Syntax.n)
in (_70_19461, args))) with
| (Microsoft_FStar_Absyn_Syntax.Typ_const (eff), (Support.Microsoft.FStar.Util.Inl (result_typ), _43_1800)::rest) -> begin
(let _43_1840 = (Support.All.pipe_right rest (Support.List.partition (fun ( _43_10 ) -> (match (_43_10) with
| (Support.Microsoft.FStar.Util.Inr (_43_1806), _43_1809) -> begin
false
end
| (Support.Microsoft.FStar.Util.Inl (t), _43_1814) -> begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (fv); Microsoft_FStar_Absyn_Syntax.tk = _43_1823; Microsoft_FStar_Absyn_Syntax.pos = _43_1821; Microsoft_FStar_Absyn_Syntax.fvs = _43_1819; Microsoft_FStar_Absyn_Syntax.uvs = _43_1817}, (Support.Microsoft.FStar.Util.Inr (_43_1828), _43_1831)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.decreases_lid)
end
| _43_1837 -> begin
false
end)
end))))
in (match (_43_1840) with
| (dec, rest) -> begin
(let decreases_clause = (Support.All.pipe_right dec (Support.List.map (fun ( _43_11 ) -> (match (_43_11) with
| (Support.Microsoft.FStar.Util.Inl (t), _43_1845) -> begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((_43_1848, (Support.Microsoft.FStar.Util.Inr (arg), _43_1852)::[])) -> begin
Microsoft_FStar_Absyn_Syntax.DECREASES (arg)
end
| _43_1858 -> begin
(Support.All.failwith "impos")
end)
end
| _43_1860 -> begin
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
(let _70_19465 = (let _70_19464 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "%s is not an effect" _70_19464))
in (fail _70_19465))
end)
end))
end))
end
| _43_1864 -> begin
(match (default_ok) with
| true -> begin
(env.Microsoft_FStar_Parser_DesugarEnv.default_result_effect t r)
end
| false -> begin
(let _70_19467 = (let _70_19466 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "%s is not an effect" _70_19466))
in (fail _70_19467))
end)
end)
end))))))
and desugar_kind = (fun ( env ) ( k ) -> (let pos = (fun ( f ) -> (f k.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( kk ) -> (let _43_1871 = kk
in {Microsoft_FStar_Absyn_Syntax.n = _43_1871.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _43_1871.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = k.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _43_1871.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _43_1871.Microsoft_FStar_Absyn_Syntax.uvs}))
in (let k = (unparen k)
in (match (k.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Name ({Microsoft_FStar_Absyn_Syntax.ns = _43_1880; Microsoft_FStar_Absyn_Syntax.ident = _43_1878; Microsoft_FStar_Absyn_Syntax.nsstr = _43_1876; Microsoft_FStar_Absyn_Syntax.str = "Type"}) -> begin
(setpos Microsoft_FStar_Absyn_Syntax.mk_Kind_type)
end
| Microsoft_FStar_Parser_AST.Name ({Microsoft_FStar_Absyn_Syntax.ns = _43_1889; Microsoft_FStar_Absyn_Syntax.ident = _43_1887; Microsoft_FStar_Absyn_Syntax.nsstr = _43_1885; Microsoft_FStar_Absyn_Syntax.str = "Effect"}) -> begin
(setpos Microsoft_FStar_Absyn_Syntax.mk_Kind_effect)
end
| Microsoft_FStar_Parser_AST.Name (l) -> begin
(match ((let _70_19479 = (Microsoft_FStar_Parser_DesugarEnv.qualify_lid env l)
in (Microsoft_FStar_Parser_DesugarEnv.find_kind_abbrev env _70_19479))) with
| Some (l) -> begin
(Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev ((l, []), Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown)))
end
| _43_1897 -> begin
(Microsoft_FStar_Parser_AST.error "Unexpected term where kind was expected" k k.Microsoft_FStar_Parser_AST.range)
end)
end
| Microsoft_FStar_Parser_AST.Wild -> begin
(setpos Microsoft_FStar_Absyn_Syntax.kun)
end
| Microsoft_FStar_Parser_AST.Product ((bs, k)) -> begin
(let _43_1905 = (uncurry bs k)
in (match (_43_1905) with
| (bs, k) -> begin
(let rec aux = (fun ( env ) ( bs ) ( _43_12 ) -> (match (_43_12) with
| [] -> begin
(let _70_19490 = (let _70_19489 = (let _70_19488 = (desugar_kind env k)
in ((Support.List.rev bs), _70_19488))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _70_19489))
in (Support.All.pipe_left pos _70_19490))
end
| hd::tl -> begin
(let _43_1916 = (let _70_19492 = (let _70_19491 = (Microsoft_FStar_Parser_DesugarEnv.default_ml env)
in (desugar_binder _70_19491 hd))
in (Support.All.pipe_right _70_19492 (as_binder env hd.Microsoft_FStar_Parser_AST.aqual)))
in (match (_43_1916) with
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
(let args = (Support.List.map (fun ( _43_1926 ) -> (match (_43_1926) with
| (t, b) -> begin
(let qual = (match ((b = Microsoft_FStar_Parser_AST.Hash)) with
| true -> begin
Some (Microsoft_FStar_Absyn_Syntax.Implicit)
end
| false -> begin
None
end)
in (let _70_19494 = (desugar_typ_or_exp env t)
in (_70_19494, qual)))
end)) args)
in (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown))))
end)
end
| _43_1930 -> begin
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
| _43_1941 -> begin
None
end))
in (let pos = (fun ( t ) -> (t None f.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( t ) -> (let _43_1946 = t
in {Microsoft_FStar_Absyn_Syntax.n = _43_1946.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _43_1946.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = f.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _43_1946.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _43_1946.Microsoft_FStar_Absyn_Syntax.uvs}))
in (let desugar_quant = (fun ( q ) ( qt ) ( b ) ( pats ) ( body ) -> (let tk = (desugar_binder env (let _43_1954 = b
in {Microsoft_FStar_Parser_AST.b = _43_1954.Microsoft_FStar_Parser_AST.b; Microsoft_FStar_Parser_AST.brange = _43_1954.Microsoft_FStar_Parser_AST.brange; Microsoft_FStar_Parser_AST.blevel = Microsoft_FStar_Parser_AST.Formula; Microsoft_FStar_Parser_AST.aqual = _43_1954.Microsoft_FStar_Parser_AST.aqual}))
in (match (tk) with
| Support.Microsoft.FStar.Util.Inl ((Some (a), k)) -> begin
(let _43_1964 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_43_1964) with
| (env, a) -> begin
(let pats = (Support.List.map (fun ( e ) -> (let _70_19525 = (desugar_typ_or_exp env e)
in (Support.All.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _70_19525))) pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _43_1970 -> begin
(let _70_19526 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
in (Support.All.pipe_left setpos _70_19526))
end)
in (let body = (let _70_19532 = (let _70_19531 = (let _70_19530 = (let _70_19529 = (Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_70_19529)::[])
in (_70_19530, body))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_19531))
in (Support.All.pipe_left pos _70_19532))
in (let _70_19537 = (let _70_19536 = (let _70_19533 = (Microsoft_FStar_Absyn_Util.set_lid_range qt b.Microsoft_FStar_Parser_AST.brange)
in (Microsoft_FStar_Absyn_Util.ftv _70_19533 Microsoft_FStar_Absyn_Syntax.kun))
in (let _70_19535 = (let _70_19534 = (Microsoft_FStar_Absyn_Syntax.targ body)
in (_70_19534)::[])
in (Microsoft_FStar_Absyn_Util.mk_typ_app _70_19536 _70_19535)))
in (Support.All.pipe_left setpos _70_19537))))))
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _43_1980 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_43_1980) with
| (env, x) -> begin
(let pats = (Support.List.map (fun ( e ) -> (let _70_19539 = (desugar_typ_or_exp env e)
in (Support.All.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _70_19539))) pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _43_1986 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
end)
in (let body = (let _70_19545 = (let _70_19544 = (let _70_19543 = (let _70_19542 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_70_19542)::[])
in (_70_19543, body))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_19544))
in (Support.All.pipe_left pos _70_19545))
in (let _70_19550 = (let _70_19549 = (let _70_19546 = (Microsoft_FStar_Absyn_Util.set_lid_range q b.Microsoft_FStar_Parser_AST.brange)
in (Microsoft_FStar_Absyn_Util.ftv _70_19546 Microsoft_FStar_Absyn_Syntax.kun))
in (let _70_19548 = (let _70_19547 = (Microsoft_FStar_Absyn_Syntax.targ body)
in (_70_19547)::[])
in (Microsoft_FStar_Absyn_Util.mk_typ_app _70_19549 _70_19548)))
in (Support.All.pipe_left setpos _70_19550))))))
end))
end
| _43_1990 -> begin
(Support.All.failwith "impossible")
end)))
in (let push_quant = (fun ( q ) ( binders ) ( pats ) ( body ) -> (match (binders) with
| b::b'::_rest -> begin
(let rest = (b')::_rest
in (let body = (let _70_19565 = (q (rest, pats, body))
in (let _70_19564 = (Support.Microsoft.FStar.Range.union_ranges b'.Microsoft_FStar_Parser_AST.brange body.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_AST.mk_term _70_19565 _70_19564 Microsoft_FStar_Parser_AST.Formula)))
in (let _70_19566 = (q ((b)::[], [], body))
in (Microsoft_FStar_Parser_AST.mk_term _70_19566 f.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Formula))))
end
| _43_2004 -> begin
(Support.All.failwith "impossible")
end))
in (match ((let _70_19567 = (unparen f)
in _70_19567.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Labeled ((f, l, p)) -> begin
(let f = (desugar_formula env f)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((f, l, Microsoft_FStar_Absyn_Syntax.dummyRange, p)))))
end
| Microsoft_FStar_Parser_AST.Op (("==", hd::_args)) -> begin
(let args = (hd)::_args
in (let args = (Support.List.map (fun ( t ) -> (let _70_19569 = (desugar_typ_or_exp env t)
in (Support.All.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _70_19569))) args)
in (let eq = (match ((is_type env hd)) with
| true -> begin
(let _70_19570 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.eqT_lid f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _70_19570 Microsoft_FStar_Absyn_Syntax.kun))
end
| false -> begin
(let _70_19571 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.eq2_lid f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _70_19571 Microsoft_FStar_Absyn_Syntax.kun))
end)
in (Microsoft_FStar_Absyn_Util.mk_typ_app eq args))))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match (((connective s), args)) with
| (Some (conn), _43_2030::_43_2028::[]) -> begin
(let _70_19576 = (let _70_19572 = (Microsoft_FStar_Absyn_Util.set_lid_range conn f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _70_19572 Microsoft_FStar_Absyn_Syntax.kun))
in (let _70_19575 = (Support.List.map (fun ( x ) -> (let _70_19574 = (desugar_formula env x)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _70_19574))) args)
in (Microsoft_FStar_Absyn_Util.mk_typ_app _70_19576 _70_19575)))
end
| _43_2035 -> begin
(match ((is_type env f)) with
| true -> begin
(desugar_typ env f)
end
| false -> begin
(let _70_19577 = (desugar_exp env f)
in (Support.All.pipe_right _70_19577 Microsoft_FStar_Absyn_Util.b2t))
end)
end)
end
| Microsoft_FStar_Parser_AST.If ((f1, f2, f3)) -> begin
(let _70_19582 = (let _70_19578 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.ite_lid f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _70_19578 Microsoft_FStar_Absyn_Syntax.kun))
in (let _70_19581 = (Support.List.map (fun ( x ) -> (match ((desugar_typ_or_exp env x)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| Support.Microsoft.FStar.Util.Inr (v) -> begin
(let _70_19580 = (Microsoft_FStar_Absyn_Util.b2t v)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _70_19580))
end)) ((f1)::(f2)::(f3)::[]))
in (Microsoft_FStar_Absyn_Util.mk_typ_app _70_19582 _70_19581)))
end
| Microsoft_FStar_Parser_AST.QForall ((_1::_2::_3, pats, body)) -> begin
(let binders = (_1)::(_2)::_3
in (let _70_19584 = (push_quant (fun ( x ) -> Microsoft_FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _70_19584)))
end
| Microsoft_FStar_Parser_AST.QExists ((_1::_2::_3, pats, body)) -> begin
(let binders = (_1)::(_2)::_3
in (let _70_19586 = (push_quant (fun ( x ) -> Microsoft_FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _70_19586)))
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
| _43_2083 -> begin
(match ((is_type env f)) with
| true -> begin
(desugar_typ env f)
end
| false -> begin
(let _70_19587 = (desugar_exp env f)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Util.b2t _70_19587))
end)
end)))))))
and desugar_formula = (fun ( env ) ( t ) -> (desugar_formula' (let _43_2086 = env
in {Microsoft_FStar_Parser_DesugarEnv.curmodule = _43_2086.Microsoft_FStar_Parser_DesugarEnv.curmodule; Microsoft_FStar_Parser_DesugarEnv.modules = _43_2086.Microsoft_FStar_Parser_DesugarEnv.modules; Microsoft_FStar_Parser_DesugarEnv.open_namespaces = _43_2086.Microsoft_FStar_Parser_DesugarEnv.open_namespaces; Microsoft_FStar_Parser_DesugarEnv.sigaccum = _43_2086.Microsoft_FStar_Parser_DesugarEnv.sigaccum; Microsoft_FStar_Parser_DesugarEnv.localbindings = _43_2086.Microsoft_FStar_Parser_DesugarEnv.localbindings; Microsoft_FStar_Parser_DesugarEnv.recbindings = _43_2086.Microsoft_FStar_Parser_DesugarEnv.recbindings; Microsoft_FStar_Parser_DesugarEnv.phase = Microsoft_FStar_Parser_AST.Formula; Microsoft_FStar_Parser_DesugarEnv.sigmap = _43_2086.Microsoft_FStar_Parser_DesugarEnv.sigmap; Microsoft_FStar_Parser_DesugarEnv.default_result_effect = _43_2086.Microsoft_FStar_Parser_DesugarEnv.default_result_effect; Microsoft_FStar_Parser_DesugarEnv.iface = _43_2086.Microsoft_FStar_Parser_DesugarEnv.iface; Microsoft_FStar_Parser_DesugarEnv.admitted_iface = _43_2086.Microsoft_FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder = (fun ( env ) ( b ) -> (match ((is_type_binder env b)) with
| true -> begin
(let _70_19592 = (desugar_type_binder env b)
in Support.Microsoft.FStar.Util.Inl (_70_19592))
end
| false -> begin
(let _70_19593 = (desugar_exp_binder env b)
in Support.Microsoft.FStar.Util.Inr (_70_19593))
end))
and typars_of_binders = (fun ( env ) ( bs ) -> (let _43_2119 = (Support.List.fold_left (fun ( _43_2094 ) ( b ) -> (match (_43_2094) with
| (env, out) -> begin
(let tk = (desugar_binder env (let _43_2096 = b
in {Microsoft_FStar_Parser_AST.b = _43_2096.Microsoft_FStar_Parser_AST.b; Microsoft_FStar_Parser_AST.brange = _43_2096.Microsoft_FStar_Parser_AST.brange; Microsoft_FStar_Parser_AST.blevel = Microsoft_FStar_Parser_AST.Formula; Microsoft_FStar_Parser_AST.aqual = _43_2096.Microsoft_FStar_Parser_AST.aqual}))
in (match (tk) with
| Support.Microsoft.FStar.Util.Inl ((Some (a), k)) -> begin
(let _43_2106 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_43_2106) with
| (env, a) -> begin
(env, ((Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)), b.Microsoft_FStar_Parser_AST.aqual))::out)
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _43_2114 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_43_2114) with
| (env, x) -> begin
(env, ((Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)), b.Microsoft_FStar_Parser_AST.aqual))::out)
end))
end
| _43_2116 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected binder", b.Microsoft_FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_43_2119) with
| (env, tpars) -> begin
(env, (Support.List.rev tpars))
end)))
and desugar_exp_binder = (fun ( env ) ( b ) -> (match (b.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Annotated ((x, t)) -> begin
(let _70_19600 = (desugar_typ env t)
in (Some (x), _70_19600))
end
| Microsoft_FStar_Parser_AST.TVariable (t) -> begin
(let _70_19601 = (Microsoft_FStar_Parser_DesugarEnv.fail_or2 (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in (None, _70_19601))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(let _70_19602 = (desugar_typ env t)
in (None, _70_19602))
end
| Microsoft_FStar_Parser_AST.Variable (x) -> begin
(Some (x), Microsoft_FStar_Absyn_Syntax.tun)
end
| _43_2133 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a type)", b.Microsoft_FStar_Parser_AST.brange))))
end))
and desugar_type_binder = (fun ( env ) ( b ) -> (let fail = (fun ( _43_2137 ) -> (match (()) with
| () -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a kind)", b.Microsoft_FStar_Parser_AST.brange))))
end))
in (match (b.Microsoft_FStar_Parser_AST.b) with
| (Microsoft_FStar_Parser_AST.Annotated ((x, t))) | (Microsoft_FStar_Parser_AST.TAnnotated ((x, t))) -> begin
(let _70_19607 = (desugar_kind env t)
in (Some (x), _70_19607))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(let _70_19608 = (desugar_kind env t)
in (None, _70_19608))
end
| Microsoft_FStar_Parser_AST.TVariable (x) -> begin
(Some (x), (let _43_2148 = Microsoft_FStar_Absyn_Syntax.mk_Kind_type
in {Microsoft_FStar_Absyn_Syntax.n = _43_2148.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _43_2148.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = b.Microsoft_FStar_Parser_AST.brange; Microsoft_FStar_Absyn_Syntax.fvs = _43_2148.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _43_2148.Microsoft_FStar_Absyn_Syntax.uvs}))
end
| _43_2151 -> begin
(fail ())
end)))

let gather_tc_binders = (fun ( tps ) ( k ) -> (let rec aux = (fun ( bs ) ( k ) -> (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((binders, k)) -> begin
(aux (Support.List.append bs binders) k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_43_2162, k)) -> begin
(aux bs k)
end
| _43_2167 -> begin
bs
end))
in (let _70_19617 = (aux tps k)
in (Support.All.pipe_right _70_19617 Microsoft_FStar_Absyn_Util.name_binders))))

let mk_data_discriminators = (fun ( quals ) ( env ) ( t ) ( tps ) ( k ) ( datas ) -> (let quals = (fun ( q ) -> (match (((Support.All.pipe_left Support.Prims.op_Negation env.Microsoft_FStar_Parser_DesugarEnv.iface) || env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface)) with
| true -> begin
(Support.List.append ((Microsoft_FStar_Absyn_Syntax.Assumption)::q) quals)
end
| false -> begin
(Support.List.append q quals)
end))
in (let binders = (gather_tc_binders tps k)
in (let p = (Microsoft_FStar_Absyn_Syntax.range_of_lid t)
in (let imp_binders = (Support.All.pipe_right binders (Support.List.map (fun ( _43_2181 ) -> (match (_43_2181) with
| (x, _43_2180) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end))))
in (let binders = (let _70_19638 = (let _70_19637 = (let _70_19636 = (let _70_19635 = (let _70_19634 = (Microsoft_FStar_Absyn_Util.ftv t Microsoft_FStar_Absyn_Syntax.kun)
in (let _70_19633 = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (_70_19634, _70_19633)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' _70_19635 None p))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.null_v_binder _70_19636))
in (_70_19637)::[])
in (Support.List.append imp_binders _70_19638))
in (let disc_type = (let _70_19641 = (let _70_19640 = (let _70_19639 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.bool_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.total_comp _70_19639 p))
in (binders, _70_19640))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _70_19641 None p))
in (Support.All.pipe_right datas (Support.List.map (fun ( d ) -> (let disc_name = (Microsoft_FStar_Absyn_Util.mk_discriminator d)
in (let _70_19645 = (let _70_19644 = (quals ((Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Discriminator (d))::[]))
in (let _70_19643 = (Microsoft_FStar_Absyn_Syntax.range_of_lid disc_name)
in (disc_name, disc_type, _70_19644, _70_19643)))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_70_19645)))))))))))))

let mk_indexed_projectors = (fun ( refine_domain ) ( env ) ( _43_2192 ) ( lid ) ( formals ) ( t ) -> (match (_43_2192) with
| (tc, tps, k) -> begin
(let binders = (gather_tc_binders tps k)
in (let p = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (let arg_binder = (let arg_typ = (let _70_19654 = (let _70_19653 = (Microsoft_FStar_Absyn_Util.ftv tc Microsoft_FStar_Absyn_Syntax.kun)
in (let _70_19652 = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (_70_19653, _70_19652)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' _70_19654 None p))
in (let projectee = (let _70_19656 = (Microsoft_FStar_Absyn_Syntax.mk_ident ("projectee", p))
in (let _70_19655 = (Microsoft_FStar_Absyn_Util.genident (Some (p)))
in {Microsoft_FStar_Absyn_Syntax.ppname = _70_19656; Microsoft_FStar_Absyn_Syntax.realname = _70_19655}))
in (match ((not (refine_domain))) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end
| false -> begin
(let disc_name = (Microsoft_FStar_Absyn_Util.mk_discriminator lid)
in (let x = (Microsoft_FStar_Absyn_Util.gen_bvar arg_typ)
in (let _70_19666 = (let _70_19665 = (let _70_19664 = (let _70_19663 = (let _70_19662 = (let _70_19661 = (let _70_19660 = (Microsoft_FStar_Absyn_Util.fvar None disc_name p)
in (let _70_19659 = (let _70_19658 = (let _70_19657 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.varg _70_19657))
in (_70_19658)::[])
in (_70_19660, _70_19659)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _70_19661 None p))
in (Microsoft_FStar_Absyn_Util.b2t _70_19662))
in (x, _70_19663))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _70_19664 None p))
in (Support.All.pipe_left (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s projectee) _70_19665))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.v_binder _70_19666))))
end)))
in (let imp_binders = (Support.All.pipe_right binders (Support.List.map (fun ( _43_2206 ) -> (match (_43_2206) with
| (x, _43_2205) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end))))
in (let binders = (Support.List.append imp_binders ((arg_binder)::[]))
in (let arg = (Microsoft_FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (let subst = (let _70_19676 = (Support.All.pipe_right formals (Support.List.mapi (fun ( i ) ( f ) -> (match ((Support.Prims.fst f)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(match ((Support.All.pipe_right binders (Support.Microsoft.FStar.Util.for_some (fun ( _43_13 ) -> (match (_43_13) with
| (Support.Microsoft.FStar.Util.Inl (b), _43_2218) -> begin
(Microsoft_FStar_Absyn_Util.bvd_eq a.Microsoft_FStar_Absyn_Syntax.v b.Microsoft_FStar_Absyn_Syntax.v)
end
| _43_2221 -> begin
false
end))))) with
| true -> begin
[]
end
| false -> begin
(let _43_2225 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_43_2225) with
| (field_name, _43_2224) -> begin
(let proj = (let _70_19672 = (let _70_19671 = (Microsoft_FStar_Absyn_Util.ftv field_name Microsoft_FStar_Absyn_Syntax.kun)
in (_70_19671, (arg)::[]))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_19672 None p))
in (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, proj)))::[])
end))
end)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(match ((Support.All.pipe_right binders (Support.Microsoft.FStar.Util.for_some (fun ( _43_14 ) -> (match (_43_14) with
| (Support.Microsoft.FStar.Util.Inr (y), _43_2233) -> begin
(Microsoft_FStar_Absyn_Util.bvd_eq x.Microsoft_FStar_Absyn_Syntax.v y.Microsoft_FStar_Absyn_Syntax.v)
end
| _43_2236 -> begin
false
end))))) with
| true -> begin
[]
end
| false -> begin
(let _43_2240 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_43_2240) with
| (field_name, _43_2239) -> begin
(let proj = (let _70_19675 = (let _70_19674 = (Microsoft_FStar_Absyn_Util.fvar None field_name p)
in (_70_19674, (arg)::[]))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _70_19675 None p))
in (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, proj)))::[])
end))
end)
end))))
in (Support.All.pipe_right _70_19676 Support.List.flatten))
in (Support.All.pipe_right formals (Support.List.mapi (fun ( i ) ( ax ) -> (match ((Support.Prims.fst ax)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _43_2250 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_43_2250) with
| (field_name, _43_2249) -> begin
(let kk = (let _70_19680 = (let _70_19679 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (binders, _70_19679))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _70_19680 p))
in (let _70_19682 = (let _70_19681 = (Microsoft_FStar_Absyn_Syntax.range_of_lid field_name)
in (field_name, [], kk, [], [], (Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Projector ((lid, Support.Microsoft.FStar.Util.Inl (a.Microsoft_FStar_Absyn_Syntax.v))))::[], _70_19681))
in Microsoft_FStar_Absyn_Syntax.Sig_tycon (_70_19682)))
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _43_2257 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_43_2257) with
| (field_name, _43_2256) -> begin
(let t = (let _70_19685 = (let _70_19684 = (let _70_19683 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Absyn_Util.total_comp _70_19683 p))
in (binders, _70_19684))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _70_19685 None p))
in (let quals = (fun ( q ) -> (match (((not (env.Microsoft_FStar_Parser_DesugarEnv.iface)) || env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.Assumption)::q
end
| false -> begin
q
end))
in (let _70_19689 = (let _70_19688 = (Microsoft_FStar_Absyn_Syntax.range_of_lid field_name)
in (field_name, t, (quals ((Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Projector ((lid, Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.v))))::[])), _70_19688))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_70_19689))))
end))
end)))))))))))
end))

let mk_data_projectors = (fun ( env ) ( _43_16 ) -> (match (_43_16) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, _43_2268, _43_2270)) when (not ((Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.lexcons_lid))) -> begin
(let refine_domain = (match ((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _43_15 ) -> (match (_43_15) with
| Microsoft_FStar_Absyn_Syntax.RecordConstructor (_43_2275) -> begin
true
end
| _43_2278 -> begin
false
end))))) with
| true -> begin
false
end
| false -> begin
(let _43_2284 = tycon
in (match (_43_2284) with
| (l, _43_2281, _43_2283) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.find_all_datacons env l)) with
| Some (l) -> begin
((Support.List.length l) > 1)
end
| _43_2288 -> begin
true
end)
end))
end)
in (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((formals, cod)) -> begin
(let cod = (Microsoft_FStar_Absyn_Util.comp_result cod)
in (mk_indexed_projectors refine_domain env tycon lid formals cod))
end
| _43_2296 -> begin
[]
end))
end
| _43_2298 -> begin
[]
end))

let rec desugar_tycon = (fun ( env ) ( rng ) ( quals ) ( tcs ) -> (let tycon_id = (fun ( _43_17 ) -> (match (_43_17) with
| (Microsoft_FStar_Parser_AST.TyconAbstract ((id, _, _))) | (Microsoft_FStar_Parser_AST.TyconAbbrev ((id, _, _, _))) | (Microsoft_FStar_Parser_AST.TyconRecord ((id, _, _, _))) | (Microsoft_FStar_Parser_AST.TyconVariant ((id, _, _, _))) -> begin
id
end))
in (let binder_to_term = (fun ( b ) -> (match (b.Microsoft_FStar_Parser_AST.b) with
| (Microsoft_FStar_Parser_AST.Annotated ((x, _))) | (Microsoft_FStar_Parser_AST.Variable (x)) -> begin
(let _70_19708 = (let _70_19707 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((x)::[]))
in Microsoft_FStar_Parser_AST.Var (_70_19707))
in (Microsoft_FStar_Parser_AST.mk_term _70_19708 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr))
end
| (Microsoft_FStar_Parser_AST.TAnnotated ((a, _))) | (Microsoft_FStar_Parser_AST.TVariable (a)) -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Tvar (a)) a.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type)
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
t
end))
in (let tot = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.effect_Tot_lid)) rng Microsoft_FStar_Parser_AST.Expr)
in (let with_constructor_effect = (fun ( t ) -> (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.App ((tot, t, Microsoft_FStar_Parser_AST.Nothing))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level))
in (let apply_binders = (fun ( t ) ( binders ) -> (Support.List.fold_left (fun ( out ) ( b ) -> (let _70_19719 = (let _70_19718 = (let _70_19717 = (binder_to_term b)
in (out, _70_19717, Microsoft_FStar_Parser_AST.Nothing))
in Microsoft_FStar_Parser_AST.App (_70_19718))
in (Microsoft_FStar_Parser_AST.mk_term _70_19719 out.Microsoft_FStar_Parser_AST.range out.Microsoft_FStar_Parser_AST.level))) t binders))
in (let tycon_record_as_variant = (fun ( _43_18 ) -> (match (_43_18) with
| Microsoft_FStar_Parser_AST.TyconRecord ((id, parms, kopt, fields)) -> begin
(let constrName = (Microsoft_FStar_Absyn_Syntax.mk_ident ((Support.String.strcat "Mk" id.Microsoft_FStar_Absyn_Syntax.idText), id.Microsoft_FStar_Absyn_Syntax.idRange))
in (let mfields = (Support.List.map (fun ( _43_2370 ) -> (match (_43_2370) with
| (x, t) -> begin
(let _70_19725 = (let _70_19724 = (let _70_19723 = (Microsoft_FStar_Absyn_Util.mangle_field_name x)
in (_70_19723, t))
in Microsoft_FStar_Parser_AST.Annotated (_70_19724))
in (Microsoft_FStar_Parser_AST.mk_binder _70_19725 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr None))
end)) fields)
in (let result = (let _70_19728 = (let _70_19727 = (let _70_19726 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id)::[]))
in Microsoft_FStar_Parser_AST.Var (_70_19726))
in (Microsoft_FStar_Parser_AST.mk_term _70_19727 id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type))
in (apply_binders _70_19728 parms))
in (let constrTyp = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type)
in (let _70_19730 = (Support.All.pipe_right fields (Support.List.map (fun ( _43_2377 ) -> (match (_43_2377) with
| (x, _43_2376) -> begin
(Microsoft_FStar_Parser_DesugarEnv.qualify env x)
end))))
in (Microsoft_FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _70_19730))))))
end
| _43_2379 -> begin
(Support.All.failwith "impossible")
end))
in (let desugar_abstract_tc = (fun ( quals ) ( _env ) ( mutuals ) ( _43_19 ) -> (match (_43_19) with
| Microsoft_FStar_Parser_AST.TyconAbstract ((id, binders, kopt)) -> begin
(let _43_2393 = (typars_of_binders _env binders)
in (match (_43_2393) with
| (_env', typars) -> begin
(let k = (match (kopt) with
| None -> begin
Microsoft_FStar_Absyn_Syntax.kun
end
| Some (k) -> begin
(desugar_kind _env' k)
end)
in (let tconstr = (let _70_19741 = (let _70_19740 = (let _70_19739 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id)::[]))
in Microsoft_FStar_Parser_AST.Var (_70_19739))
in (Microsoft_FStar_Parser_AST.mk_term _70_19740 id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type))
in (apply_binders _70_19741 binders))
in (let qlid = (Microsoft_FStar_Parser_DesugarEnv.qualify _env id)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_tycon ((qlid, typars, k, mutuals, [], quals, rng))
in (let _env = (Microsoft_FStar_Parser_DesugarEnv.push_rec_binding _env (Microsoft_FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (let _env2 = (Microsoft_FStar_Parser_DesugarEnv.push_rec_binding _env' (Microsoft_FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (_env, (_env2, typars), se, tconstr)))))))
end))
end
| _43_2404 -> begin
(Support.All.failwith "Unexpected tycon")
end))
in (let push_tparam = (fun ( env ) ( _43_20 ) -> (match (_43_20) with
| (Support.Microsoft.FStar.Util.Inr (x), _43_2411) -> begin
(Microsoft_FStar_Parser_DesugarEnv.push_bvvdef env x.Microsoft_FStar_Absyn_Syntax.v)
end
| (Support.Microsoft.FStar.Util.Inl (a), _43_2416) -> begin
(Microsoft_FStar_Parser_DesugarEnv.push_btvdef env a.Microsoft_FStar_Absyn_Syntax.v)
end))
in (let push_tparams = (Support.List.fold_left push_tparam)
in (match (tcs) with
| Microsoft_FStar_Parser_AST.TyconAbstract (_43_2420)::[] -> begin
(let tc = (Support.List.hd tcs)
in (let _43_2431 = (desugar_abstract_tc quals env [] tc)
in (match (_43_2431) with
| (_43_2425, _43_2427, se, _43_2430) -> begin
(let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))
end)))
end
| Microsoft_FStar_Parser_AST.TyconAbbrev ((id, binders, kopt, t))::[] -> begin
(let _43_2442 = (typars_of_binders env binders)
in (match (_43_2442) with
| (env', typars) -> begin
(let k = (match (kopt) with
| None -> begin
(match ((Support.Microsoft.FStar.Util.for_some (fun ( _43_21 ) -> (match (_43_21) with
| Microsoft_FStar_Absyn_Syntax.Effect -> begin
true
end
| _43_2447 -> begin
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
in (let quals = (match ((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _43_22 ) -> (match (_43_22) with
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
true
end
| _43_2455 -> begin
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
in (let _70_19753 = (let _70_19752 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (let _70_19751 = (Support.All.pipe_right quals (Support.List.filter (fun ( _43_23 ) -> (match (_43_23) with
| Microsoft_FStar_Absyn_Syntax.Effect -> begin
false
end
| _43_2461 -> begin
true
end))))
in (_70_19752, typars, c, _70_19751, rng)))
in Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_70_19753)))
end
| false -> begin
(let t = (desugar_typ env' t)
in (let _70_19755 = (let _70_19754 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (_70_19754, typars, k, t, quals, rng))
in Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_70_19755)))
end)
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| Microsoft_FStar_Parser_AST.TyconRecord (_43_2466)::[] -> begin
(let trec = (Support.List.hd tcs)
in (let _43_2472 = (tycon_record_as_variant trec)
in (match (_43_2472) with
| (t, fs) -> begin
(desugar_tycon env rng ((Microsoft_FStar_Absyn_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _43_2476::_43_2474 -> begin
(let env0 = env
in (let mutuals = (Support.List.map (fun ( x ) -> (Support.All.pipe_left (Microsoft_FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (let rec collect_tcs = (fun ( quals ) ( et ) ( tc ) -> (let _43_2487 = et
in (match (_43_2487) with
| (env, tcs) -> begin
(match (tc) with
| Microsoft_FStar_Parser_AST.TyconRecord (_43_2489) -> begin
(let trec = tc
in (let _43_2494 = (tycon_record_as_variant trec)
in (match (_43_2494) with
| (t, fs) -> begin
(collect_tcs ((Microsoft_FStar_Absyn_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| Microsoft_FStar_Parser_AST.TyconVariant ((id, binders, kopt, constructors)) -> begin
(let _43_2508 = (desugar_abstract_tc quals env mutuals (Microsoft_FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_43_2508) with
| (env, (_43_2503, tps), se, tconstr) -> begin
(env, (Support.Microsoft.FStar.Util.Inl ((se, tps, constructors, tconstr, quals)))::tcs)
end))
end
| Microsoft_FStar_Parser_AST.TyconAbbrev ((id, binders, kopt, t)) -> begin
(let _43_2522 = (desugar_abstract_tc quals env mutuals (Microsoft_FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_43_2522) with
| (env, (_43_2517, tps), se, tconstr) -> begin
(env, (Support.Microsoft.FStar.Util.Inr ((se, tps, t, quals)))::tcs)
end))
end
| _43_2524 -> begin
(Support.All.failwith "Unrecognized mutual type definition")
end)
end)))
in (let _43_2527 = (Support.List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_43_2527) with
| (env, tcs) -> begin
(let tcs = (Support.List.rev tcs)
in (let sigelts = (Support.All.pipe_right tcs (Support.List.collect (fun ( _43_25 ) -> (match (_43_25) with
| Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Syntax.Sig_tycon ((id, tpars, k, _43_2534, _43_2536, _43_2538, _43_2540)), tps, t, quals)) -> begin
(let env_tps = (push_tparams env tps)
in (let t = (desugar_typ env_tps t)
in (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((id, tpars, k, t, [], rng)))::[]))
end
| Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, _43_2555, tags, _43_2558)), tps, constrs, tconstr, quals)) -> begin
(let tycon = (tname, tpars, k)
in (let env_tps = (push_tparams env tps)
in (let _43_2594 = (let _70_19774 = (Support.All.pipe_right constrs (Support.List.map (fun ( _43_2572 ) -> (match (_43_2572) with
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
in (let t = (let _70_19766 = (Microsoft_FStar_Parser_DesugarEnv.default_total env_tps)
in (let _70_19765 = (close env_tps t)
in (desugar_typ _70_19766 _70_19765)))
in (let name = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (let quals = (Support.All.pipe_right tags (Support.List.collect (fun ( _43_24 ) -> (match (_43_24) with
| Microsoft_FStar_Absyn_Syntax.RecordType (fns) -> begin
(Microsoft_FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _43_2586 -> begin
[]
end))))
in (let _70_19773 = (let _70_19772 = (let _70_19771 = (let _70_19770 = (let _70_19769 = (Support.List.map (fun ( _43_2591 ) -> (match (_43_2591) with
| (x, _43_2590) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end)) tps)
in (Microsoft_FStar_Absyn_Util.close_typ _70_19769 t))
in (Support.All.pipe_right _70_19770 Microsoft_FStar_Absyn_Util.name_function_binders))
in (name, _70_19771, tycon, quals, mutuals, rng))
in Microsoft_FStar_Absyn_Syntax.Sig_datacon (_70_19772))
in (name, _70_19773))))))
end))))
in (Support.All.pipe_left Support.List.split _70_19774))
in (match (_43_2594) with
| (constrNames, constrs) -> begin
(Microsoft_FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, constrNames, tags, rng)))::constrs
end))))
end
| _43_2596 -> begin
(Support.All.failwith "impossible")
end))))
in (let bundle = (let _70_19776 = (let _70_19775 = (Support.List.collect Microsoft_FStar_Absyn_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _70_19775, rng))
in Microsoft_FStar_Absyn_Syntax.Sig_bundle (_70_19776))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (let data_ops = (Support.All.pipe_right sigelts (Support.List.collect (mk_data_projectors env)))
in (let discs = (Support.All.pipe_right sigelts (Support.List.collect (fun ( _43_26 ) -> (match (_43_26) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((tname, tps, k, _43_2606, constrs, quals, _43_2610)) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _43_2614 -> begin
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

let desugar_binders = (fun ( env ) ( binders ) -> (let _43_2645 = (Support.List.fold_left (fun ( _43_2623 ) ( b ) -> (match (_43_2623) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| Support.Microsoft.FStar.Util.Inl ((Some (a), k)) -> begin
(let _43_2632 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_43_2632) with
| (env, a) -> begin
(let _70_19785 = (let _70_19784 = (Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_70_19784)::binders)
in (env, _70_19785))
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _43_2640 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_43_2640) with
| (env, x) -> begin
(let _70_19787 = (let _70_19786 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_70_19786)::binders)
in (env, _70_19787))
end))
end
| _43_2642 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Missing name in binder", b.Microsoft_FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_43_2645) with
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
(match ((let _70_19793 = (let _70_19792 = (desugar_exp_maybe_top true env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Let ((isrec, lets, (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Const (Microsoft_FStar_Absyn_Syntax.Const_unit)) d.Microsoft_FStar_Parser_AST.drange Microsoft_FStar_Parser_AST.Expr)))) d.Microsoft_FStar_Parser_AST.drange Microsoft_FStar_Parser_AST.Expr))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Util.compress_exp _70_19792))
in _70_19793.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, _43_2664)) -> begin
(let lids = (Support.All.pipe_right (Support.Prims.snd lbs) (Support.List.map (fun ( lb ) -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inr (l) -> begin
l
end
| _43_2671 -> begin
(Support.All.failwith "impossible")
end))))
in (let quals = (Support.All.pipe_right (Support.Prims.snd lbs) (Support.List.collect (fun ( _43_27 ) -> (match (_43_27) with
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (_43_2681); Microsoft_FStar_Absyn_Syntax.lbtyp = _43_2679; Microsoft_FStar_Absyn_Syntax.lbeff = _43_2677; Microsoft_FStar_Absyn_Syntax.lbdef = _43_2675} -> begin
[]
end
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = _43_2689; Microsoft_FStar_Absyn_Syntax.lbeff = _43_2687; Microsoft_FStar_Absyn_Syntax.lbdef = _43_2685} -> begin
(Microsoft_FStar_Parser_DesugarEnv.lookup_letbinding_quals env l)
end))))
in (let s = Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, d.Microsoft_FStar_Parser_AST.drange, lids, quals))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env s)
in (env, (s)::[])))))
end
| _43_2697 -> begin
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
in (let _70_19799 = (let _70_19798 = (let _70_19797 = (let _70_19796 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (_70_19796, f, (Microsoft_FStar_Absyn_Syntax.Assumption)::[], d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Sig_assume (_70_19797))
in (_70_19798)::[])
in (env, _70_19799)))
end
| Microsoft_FStar_Parser_AST.Val ((quals, id, t)) -> begin
(let t = (let _70_19800 = (close_fun env t)
in (desugar_typ env _70_19800))
in (let quals = (match ((env.Microsoft_FStar_Parser_DesugarEnv.iface && env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.Assumption)::quals
end
| false -> begin
quals
end)
in (let se = (let _70_19802 = (let _70_19801 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (_70_19801, t, quals, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_70_19802))
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
in (let t = (let _70_19807 = (let _70_19806 = (let _70_19803 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_70_19803)::[])
in (let _70_19805 = (let _70_19804 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) Microsoft_FStar_Absyn_Const.exn_lid)
in (Microsoft_FStar_Absyn_Syntax.mk_Total _70_19804))
in (_70_19806, _70_19805)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _70_19807 None d.Microsoft_FStar_Parser_AST.drange))
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
(let _43_2750 = (desugar_binders env binders)
in (match (_43_2750) with
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
in (let _43_2766 = (desugar_binders env eff_binders)
in (match (_43_2766) with
| (env, binders) -> begin
(let defn = (desugar_typ env defn)
in (let _43_2770 = (Microsoft_FStar_Absyn_Util.head_and_args defn)
in (match (_43_2770) with
| (head, args) -> begin
(match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (eff) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_effect_defn env eff.Microsoft_FStar_Absyn_Syntax.v)) with
| None -> begin
(let _70_19812 = (let _70_19811 = (let _70_19810 = (let _70_19809 = (let _70_19808 = (Microsoft_FStar_Absyn_Print.sli eff.Microsoft_FStar_Absyn_Syntax.v)
in (Support.String.strcat "Effect " _70_19808))
in (Support.String.strcat _70_19809 " not found"))
in (_70_19810, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Error (_70_19811))
in (raise (_70_19812)))
end
| Some (ed) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.subst_of_list ed.Microsoft_FStar_Absyn_Syntax.binders args)
in (let sub = (Microsoft_FStar_Absyn_Util.subst_typ subst)
in (let ed = (let _70_19829 = (Microsoft_FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _70_19828 = (Microsoft_FStar_Absyn_Util.subst_kind subst ed.Microsoft_FStar_Absyn_Syntax.signature)
in (let _70_19827 = (sub ed.Microsoft_FStar_Absyn_Syntax.ret)
in (let _70_19826 = (sub ed.Microsoft_FStar_Absyn_Syntax.bind_wp)
in (let _70_19825 = (sub ed.Microsoft_FStar_Absyn_Syntax.bind_wlp)
in (let _70_19824 = (sub ed.Microsoft_FStar_Absyn_Syntax.if_then_else)
in (let _70_19823 = (sub ed.Microsoft_FStar_Absyn_Syntax.ite_wp)
in (let _70_19822 = (sub ed.Microsoft_FStar_Absyn_Syntax.ite_wlp)
in (let _70_19821 = (sub ed.Microsoft_FStar_Absyn_Syntax.wp_binop)
in (let _70_19820 = (sub ed.Microsoft_FStar_Absyn_Syntax.wp_as_type)
in (let _70_19819 = (sub ed.Microsoft_FStar_Absyn_Syntax.close_wp)
in (let _70_19818 = (sub ed.Microsoft_FStar_Absyn_Syntax.close_wp_t)
in (let _70_19817 = (sub ed.Microsoft_FStar_Absyn_Syntax.assert_p)
in (let _70_19816 = (sub ed.Microsoft_FStar_Absyn_Syntax.assume_p)
in (let _70_19815 = (sub ed.Microsoft_FStar_Absyn_Syntax.null_wp)
in (let _70_19814 = (sub ed.Microsoft_FStar_Absyn_Syntax.trivial)
in {Microsoft_FStar_Absyn_Syntax.mname = _70_19829; Microsoft_FStar_Absyn_Syntax.binders = binders; Microsoft_FStar_Absyn_Syntax.qualifiers = quals; Microsoft_FStar_Absyn_Syntax.signature = _70_19828; Microsoft_FStar_Absyn_Syntax.ret = _70_19827; Microsoft_FStar_Absyn_Syntax.bind_wp = _70_19826; Microsoft_FStar_Absyn_Syntax.bind_wlp = _70_19825; Microsoft_FStar_Absyn_Syntax.if_then_else = _70_19824; Microsoft_FStar_Absyn_Syntax.ite_wp = _70_19823; Microsoft_FStar_Absyn_Syntax.ite_wlp = _70_19822; Microsoft_FStar_Absyn_Syntax.wp_binop = _70_19821; Microsoft_FStar_Absyn_Syntax.wp_as_type = _70_19820; Microsoft_FStar_Absyn_Syntax.close_wp = _70_19819; Microsoft_FStar_Absyn_Syntax.close_wp_t = _70_19818; Microsoft_FStar_Absyn_Syntax.assert_p = _70_19817; Microsoft_FStar_Absyn_Syntax.assume_p = _70_19816; Microsoft_FStar_Absyn_Syntax.null_wp = _70_19815; Microsoft_FStar_Absyn_Syntax.trivial = _70_19814}))))))))))))))))
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ed, d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)
end
| _43_2782 -> begin
(let _70_19833 = (let _70_19832 = (let _70_19831 = (let _70_19830 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (Support.String.strcat _70_19830 " is not an effect"))
in (_70_19831, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Error (_70_19832))
in (raise (_70_19833)))
end)
end)))
end)))
end
| Microsoft_FStar_Parser_AST.NewEffect ((quals, Microsoft_FStar_Parser_AST.DefineEffect ((eff_name, eff_binders, eff_kind, eff_decls)))) -> begin
(let env0 = env
in (let env = (Microsoft_FStar_Parser_DesugarEnv.enter_monad_scope env eff_name)
in (let _43_2796 = (desugar_binders env eff_binders)
in (match (_43_2796) with
| (env, binders) -> begin
(let eff_k = (desugar_kind env eff_kind)
in (let _43_2807 = (Support.All.pipe_right eff_decls (Support.List.fold_left (fun ( _43_2800 ) ( decl ) -> (match (_43_2800) with
| (env, out) -> begin
(let _43_2804 = (desugar_decl env decl)
in (match (_43_2804) with
| (env, ses) -> begin
(let _70_19837 = (let _70_19836 = (Support.List.hd ses)
in (_70_19836)::out)
in (env, _70_19837))
end))
end)) (env, [])))
in (match (_43_2807) with
| (env, decls) -> begin
(let decls = (Support.List.rev decls)
in (let lookup = (fun ( s ) -> (match ((let _70_19841 = (let _70_19840 = (Microsoft_FStar_Absyn_Syntax.mk_ident (s, d.Microsoft_FStar_Parser_AST.drange))
in (Microsoft_FStar_Parser_DesugarEnv.qualify env _70_19840))
in (Microsoft_FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _70_19841))) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat (Support.String.strcat (Support.String.strcat "Monad " eff_name.Microsoft_FStar_Absyn_Syntax.idText) " expects definition of ") s), d.Microsoft_FStar_Parser_AST.drange))))
end
| Some (t) -> begin
t
end))
in (let ed = (let _70_19856 = (Microsoft_FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _70_19855 = (lookup "return")
in (let _70_19854 = (lookup "bind_wp")
in (let _70_19853 = (lookup "bind_wlp")
in (let _70_19852 = (lookup "if_then_else")
in (let _70_19851 = (lookup "ite_wp")
in (let _70_19850 = (lookup "ite_wlp")
in (let _70_19849 = (lookup "wp_binop")
in (let _70_19848 = (lookup "wp_as_type")
in (let _70_19847 = (lookup "close_wp")
in (let _70_19846 = (lookup "close_wp_t")
in (let _70_19845 = (lookup "assert_p")
in (let _70_19844 = (lookup "assume_p")
in (let _70_19843 = (lookup "null_wp")
in (let _70_19842 = (lookup "trivial")
in {Microsoft_FStar_Absyn_Syntax.mname = _70_19856; Microsoft_FStar_Absyn_Syntax.binders = binders; Microsoft_FStar_Absyn_Syntax.qualifiers = quals; Microsoft_FStar_Absyn_Syntax.signature = eff_k; Microsoft_FStar_Absyn_Syntax.ret = _70_19855; Microsoft_FStar_Absyn_Syntax.bind_wp = _70_19854; Microsoft_FStar_Absyn_Syntax.bind_wlp = _70_19853; Microsoft_FStar_Absyn_Syntax.if_then_else = _70_19852; Microsoft_FStar_Absyn_Syntax.ite_wp = _70_19851; Microsoft_FStar_Absyn_Syntax.ite_wlp = _70_19850; Microsoft_FStar_Absyn_Syntax.wp_binop = _70_19849; Microsoft_FStar_Absyn_Syntax.wp_as_type = _70_19848; Microsoft_FStar_Absyn_Syntax.close_wp = _70_19847; Microsoft_FStar_Absyn_Syntax.close_wp_t = _70_19846; Microsoft_FStar_Absyn_Syntax.assert_p = _70_19845; Microsoft_FStar_Absyn_Syntax.assume_p = _70_19844; Microsoft_FStar_Absyn_Syntax.null_wp = _70_19843; Microsoft_FStar_Absyn_Syntax.trivial = _70_19842})))))))))))))))
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ed, d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)))
end))))
end
| Microsoft_FStar_Parser_AST.SubEffect (l) -> begin
(let lookup = (fun ( l ) -> (match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_effect_name env l)) with
| None -> begin
(let _70_19863 = (let _70_19862 = (let _70_19861 = (let _70_19860 = (let _70_19859 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.String.strcat "Effect name " _70_19859))
in (Support.String.strcat _70_19860 " not found"))
in (_70_19861, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Error (_70_19862))
in (raise (_70_19863)))
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

let desugar_decls = (fun ( env ) ( decls ) -> (Support.List.fold_left (fun ( _43_2832 ) ( d ) -> (match (_43_2832) with
| (env, sigelts) -> begin
(let _43_2836 = (desugar_decl env d)
in (match (_43_2836) with
| (env, se) -> begin
(env, (Support.List.append sigelts se))
end))
end)) (env, []) decls))

let open_prims_all = ((Microsoft_FStar_Parser_AST.mk_decl (Microsoft_FStar_Parser_AST.Open (Microsoft_FStar_Absyn_Const.prims_lid)) Microsoft_FStar_Absyn_Syntax.dummyRange))::((Microsoft_FStar_Parser_AST.mk_decl (Microsoft_FStar_Parser_AST.Open (Microsoft_FStar_Absyn_Const.all_lid)) Microsoft_FStar_Absyn_Syntax.dummyRange))::[]

let desugar_modul_common = (fun ( curmod ) ( env ) ( m ) -> (let open_ns = (fun ( mname ) ( d ) -> (let d = (match (((Support.List.length mname.Microsoft_FStar_Absyn_Syntax.ns) <> 0)) with
| true -> begin
(let _70_19880 = (let _70_19879 = (let _70_19877 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids mname.Microsoft_FStar_Absyn_Syntax.ns)
in Microsoft_FStar_Parser_AST.Open (_70_19877))
in (let _70_19878 = (Microsoft_FStar_Absyn_Syntax.range_of_lid mname)
in (Microsoft_FStar_Parser_AST.mk_decl _70_19879 _70_19878)))
in (_70_19880)::d)
end
| false -> begin
d
end)
in d))
in (let env = (match (curmod) with
| None -> begin
env
end
| Some ((prev_mod, _43_2847)) -> begin
(Microsoft_FStar_Parser_DesugarEnv.finish_module_or_interface env prev_mod)
end)
in (let _43_2864 = (match (m) with
| Microsoft_FStar_Parser_AST.Interface ((mname, decls, admitted)) -> begin
(let _70_19882 = (Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _70_19881 = (open_ns mname decls)
in (_70_19882, mname, _70_19881, true)))
end
| Microsoft_FStar_Parser_AST.Module ((mname, decls)) -> begin
(let _70_19884 = (Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _70_19883 = (open_ns mname decls)
in (_70_19884, mname, _70_19883, false)))
end)
in (match (_43_2864) with
| (env, mname, decls, intf) -> begin
(let _43_2867 = (desugar_decls env decls)
in (match (_43_2867) with
| (env, sigelts) -> begin
(let modul = {Microsoft_FStar_Absyn_Syntax.name = mname; Microsoft_FStar_Absyn_Syntax.declarations = sigelts; Microsoft_FStar_Absyn_Syntax.exports = []; Microsoft_FStar_Absyn_Syntax.is_interface = intf; Microsoft_FStar_Absyn_Syntax.is_deserialized = false}
in (env, modul))
end))
end)))))

let desugar_partial_modul = (fun ( curmod ) ( env ) ( m ) -> (let m = (match ((Support.ST.read Microsoft_FStar_Options.interactive_fsi)) with
| true -> begin
(match (m) with
| Microsoft_FStar_Parser_AST.Module ((mname, decls)) -> begin
(let _70_19891 = (let _70_19890 = (let _70_19889 = (Support.ST.read Microsoft_FStar_Options.admit_fsi)
in (Support.Microsoft.FStar.Util.for_some (fun ( m ) -> (m = mname.Microsoft_FStar_Absyn_Syntax.str)) _70_19889))
in (mname, decls, _70_19890))
in Microsoft_FStar_Parser_AST.Interface (_70_19891))
end
| Microsoft_FStar_Parser_AST.Interface ((mname, _43_2879, _43_2881)) -> begin
(Support.All.failwith (Support.String.strcat "Impossible: " mname.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText))
end)
end
| false -> begin
m
end)
in (desugar_modul_common curmod env m)))

let desugar_modul = (fun ( env ) ( m ) -> (let _43_2889 = (desugar_modul_common None env m)
in (match (_43_2889) with
| (env, modul) -> begin
(let env = (Microsoft_FStar_Parser_DesugarEnv.finish_module_or_interface env modul)
in (let _43_2891 = (match ((Microsoft_FStar_Options.should_dump modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(let _70_19896 = (Microsoft_FStar_Absyn_Print.modul_to_string modul)
in (Support.Microsoft.FStar.Util.fprint1 "%s\n" _70_19896))
end
| false -> begin
()
end)
in (env, modul)))
end)))

let desugar_file = (fun ( env ) ( f ) -> (let _43_2904 = (Support.List.fold_left (fun ( _43_2897 ) ( m ) -> (match (_43_2897) with
| (env, mods) -> begin
(let _43_2901 = (desugar_modul env m)
in (match (_43_2901) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_43_2904) with
| (env, mods) -> begin
(env, (Support.List.rev mods))
end)))

let add_modul_to_env = (fun ( m ) ( en ) -> (let en = (Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface false false en m.Microsoft_FStar_Absyn_Syntax.name)
in (let en = (Support.List.fold_left Microsoft_FStar_Parser_DesugarEnv.push_sigelt (let _43_2908 = en
in {Microsoft_FStar_Parser_DesugarEnv.curmodule = Some (m.Microsoft_FStar_Absyn_Syntax.name); Microsoft_FStar_Parser_DesugarEnv.modules = _43_2908.Microsoft_FStar_Parser_DesugarEnv.modules; Microsoft_FStar_Parser_DesugarEnv.open_namespaces = _43_2908.Microsoft_FStar_Parser_DesugarEnv.open_namespaces; Microsoft_FStar_Parser_DesugarEnv.sigaccum = _43_2908.Microsoft_FStar_Parser_DesugarEnv.sigaccum; Microsoft_FStar_Parser_DesugarEnv.localbindings = _43_2908.Microsoft_FStar_Parser_DesugarEnv.localbindings; Microsoft_FStar_Parser_DesugarEnv.recbindings = _43_2908.Microsoft_FStar_Parser_DesugarEnv.recbindings; Microsoft_FStar_Parser_DesugarEnv.phase = _43_2908.Microsoft_FStar_Parser_DesugarEnv.phase; Microsoft_FStar_Parser_DesugarEnv.sigmap = _43_2908.Microsoft_FStar_Parser_DesugarEnv.sigmap; Microsoft_FStar_Parser_DesugarEnv.default_result_effect = _43_2908.Microsoft_FStar_Parser_DesugarEnv.default_result_effect; Microsoft_FStar_Parser_DesugarEnv.iface = _43_2908.Microsoft_FStar_Parser_DesugarEnv.iface; Microsoft_FStar_Parser_DesugarEnv.admitted_iface = _43_2908.Microsoft_FStar_Parser_DesugarEnv.admitted_iface}) m.Microsoft_FStar_Absyn_Syntax.exports)
in (Microsoft_FStar_Parser_DesugarEnv.finish_module_or_interface en m))))




