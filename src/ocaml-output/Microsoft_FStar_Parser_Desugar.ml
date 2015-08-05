
let as_imp = (fun ( _41_1 ) -> (match (_41_1) with
| (Microsoft_FStar_Parser_AST.Hash) | (Microsoft_FStar_Parser_AST.FsTypApp) -> begin
Some (Microsoft_FStar_Absyn_Syntax.Implicit)
end
| _41_32 -> begin
None
end))

let arg_withimp_e = (fun ( imp ) ( t ) -> (t, (as_imp imp)))

let arg_withimp_t = (fun ( imp ) ( t ) -> (match (imp) with
| Microsoft_FStar_Parser_AST.Hash -> begin
(t, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end
| _41_39 -> begin
(t, None)
end))

let contains_binder = (fun ( binders ) -> (Support.Prims.pipe_right binders (Support.Microsoft.FStar.Util.for_some (fun ( b ) -> (match (b.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Annotated (_41_43) -> begin
true
end
| _41_46 -> begin
false
end)))))

let rec unparen = (fun ( t ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _41_51 -> begin
t
end))

let rec unlabel = (fun ( t ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (t) -> begin
(unlabel t)
end
| Microsoft_FStar_Parser_AST.Labeled ((t, _41_57, _41_59)) -> begin
(unlabel t)
end
| _41_63 -> begin
t
end))

let kind_star = (fun ( r ) -> (let _68_18697 = (let _68_18696 = (Microsoft_FStar_Absyn_Syntax.lid_of_path (("Type")::[]) r)
in Microsoft_FStar_Parser_AST.Name (_68_18696))
in (Microsoft_FStar_Parser_AST.mk_term _68_18697 r Microsoft_FStar_Parser_AST.Kind)))

let compile_op = (fun ( arity ) ( s ) -> (let name_of_char = (fun ( _41_2 ) -> (match (_41_2) with
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
| _41_86 -> begin
"UNKNOWN"
end))
in (let rec aux = (fun ( i ) -> (match ((i = (Support.String.length s))) with
| true -> begin
[]
end
| false -> begin
(let _68_18708 = (let _68_18706 = (Support.Microsoft.FStar.Util.char_at s i)
in (name_of_char _68_18706))
in (let _68_18707 = (aux (i + 1))
in (_68_18708)::_68_18707))
end))
in (let _68_18710 = (let _68_18709 = (aux 0)
in (Support.String.concat "_" _68_18709))
in (Support.String.strcat "op_" _68_18710)))))

let compile_op_lid = (fun ( n ) ( s ) ( r ) -> (let _68_18720 = (let _68_18719 = (let _68_18718 = (let _68_18717 = (compile_op n s)
in (_68_18717, r))
in (Microsoft_FStar_Absyn_Syntax.mk_ident _68_18718))
in (_68_18719)::[])
in (Support.Prims.pipe_right _68_18720 Microsoft_FStar_Absyn_Syntax.lid_of_ids)))

let op_as_vlid = (fun ( env ) ( arity ) ( rng ) ( s ) -> (let r = (fun ( l ) -> (let _68_18731 = (Microsoft_FStar_Absyn_Util.set_lid_range l rng)
in Some (_68_18731)))
in (let fallback = (fun ( _41_100 ) -> (match (()) with
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
| _41_122 -> begin
None
end)
end))
in (match ((let _68_18734 = (compile_op_lid arity s rng)
in (Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env _68_18734))) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _41_133)); Microsoft_FStar_Absyn_Syntax.tk = _41_130; Microsoft_FStar_Absyn_Syntax.pos = _41_128; Microsoft_FStar_Absyn_Syntax.fvs = _41_126; Microsoft_FStar_Absyn_Syntax.uvs = _41_124}) -> begin
Some (fv.Microsoft_FStar_Absyn_Syntax.v)
end
| _41_139 -> begin
(fallback ())
end))))

let op_as_tylid = (fun ( env ) ( arity ) ( rng ) ( s ) -> (let r = (fun ( l ) -> (let _68_18745 = (Microsoft_FStar_Absyn_Util.set_lid_range l rng)
in Some (_68_18745)))
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
(match ((let _68_18746 = (compile_op_lid arity s rng)
in (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env _68_18746))) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (ftv); Microsoft_FStar_Absyn_Syntax.tk = _41_162; Microsoft_FStar_Absyn_Syntax.pos = _41_160; Microsoft_FStar_Absyn_Syntax.fvs = _41_158; Microsoft_FStar_Absyn_Syntax.uvs = _41_156}) -> begin
Some (ftv.Microsoft_FStar_Absyn_Syntax.v)
end
| _41_168 -> begin
None
end)
end)))

let rec is_type = (fun ( env ) ( t ) -> (match ((t.Microsoft_FStar_Parser_AST.level = Microsoft_FStar_Parser_AST.Type)) with
| true -> begin
true
end
| false -> begin
(match ((let _68_18753 = (unparen t)
in _68_18753.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Wild -> begin
true
end
| Microsoft_FStar_Parser_AST.Labeled (_41_173) -> begin
true
end
| Microsoft_FStar_Parser_AST.Op (("*", hd::_41_177)) -> begin
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
| _41_228 -> begin
true
end)
end
| (Microsoft_FStar_Parser_AST.QForall (_)) | (Microsoft_FStar_Parser_AST.QExists (_)) | (Microsoft_FStar_Parser_AST.Sum (_)) | (Microsoft_FStar_Parser_AST.Refine (_)) | (Microsoft_FStar_Parser_AST.Tvar (_)) | (Microsoft_FStar_Parser_AST.NamedTyp (_)) -> begin
true
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) when ((Support.List.length l.Microsoft_FStar_Absyn_Syntax.ns) = 0) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env l.Microsoft_FStar_Absyn_Syntax.ident)) with
| Some (_41_251) -> begin
true
end
| _41_254 -> begin
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
| Microsoft_FStar_Parser_AST.Product ((_41_295, t)) -> begin
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
| Microsoft_FStar_Parser_AST.PatTvar ((id, _41_321)) -> begin
(let _41_327 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_41_327) with
| (env, _41_326) -> begin
(aux env pats)
end))
end
| Microsoft_FStar_Parser_AST.PatAscribed ((p, tm)) -> begin
(let env = (match ((is_kind env tm)) with
| true -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| (Microsoft_FStar_Parser_AST.PatVar ((id, _))) | (Microsoft_FStar_Parser_AST.PatTvar ((id, _))) -> begin
(let _68_18758 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (Support.Prims.pipe_right _68_18758 Support.Prims.fst))
end
| _41_342 -> begin
env
end)
end
| false -> begin
env
end)
in (aux env pats))
end
| _41_345 -> begin
false
end)
end))
in (aux env pats))
end
| _41_347 -> begin
false
end)
end))
and is_kind = (fun ( env ) ( t ) -> (match ((t.Microsoft_FStar_Parser_AST.level = Microsoft_FStar_Parser_AST.Kind)) with
| true -> begin
true
end
| false -> begin
(match ((let _68_18761 = (unparen t)
in _68_18761.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Name ({Microsoft_FStar_Absyn_Syntax.ns = _41_356; Microsoft_FStar_Absyn_Syntax.ident = _41_354; Microsoft_FStar_Absyn_Syntax.nsstr = _41_352; Microsoft_FStar_Absyn_Syntax.str = "Type"}) -> begin
true
end
| Microsoft_FStar_Parser_AST.Product ((_41_360, t)) -> begin
(is_kind env t)
end
| Microsoft_FStar_Parser_AST.Paren (t) -> begin
(is_kind env t)
end
| (Microsoft_FStar_Parser_AST.Construct ((l, _))) | (Microsoft_FStar_Parser_AST.Name (l)) -> begin
(Microsoft_FStar_Parser_DesugarEnv.is_kind_abbrev env l)
end
| _41_373 -> begin
false
end)
end))

let rec is_type_binder = (fun ( env ) ( b ) -> (match ((b.Microsoft_FStar_Parser_AST.blevel = Microsoft_FStar_Parser_AST.Formula)) with
| true -> begin
(match (b.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Variable (_41_377) -> begin
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
| Microsoft_FStar_Parser_AST.Variable (_41_392) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected binder without annotation", b.Microsoft_FStar_Parser_AST.brange))))
end
| Microsoft_FStar_Parser_AST.TVariable (_41_395) -> begin
false
end
| Microsoft_FStar_Parser_AST.TAnnotated (_41_398) -> begin
true
end
| (Microsoft_FStar_Parser_AST.Annotated ((_, t))) | (Microsoft_FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end))

let sort_ftv = (fun ( ftv ) -> (let _68_18772 = (Support.Microsoft.FStar.Util.remove_dups (fun ( x ) ( y ) -> (x.Microsoft_FStar_Absyn_Syntax.idText = y.Microsoft_FStar_Absyn_Syntax.idText)) ftv)
in (Support.Prims.pipe_left (Support.Microsoft.FStar.Util.sort_with (fun ( x ) ( y ) -> (Support.String.compare x.Microsoft_FStar_Absyn_Syntax.idText y.Microsoft_FStar_Absyn_Syntax.idText))) _68_18772)))

let rec free_type_vars_b = (fun ( env ) ( binder ) -> (match (binder.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Variable (_41_414) -> begin
(env, [])
end
| Microsoft_FStar_Parser_AST.TVariable (x) -> begin
(let _41_421 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env x)
in (match (_41_421) with
| (env, _41_420) -> begin
(env, (x)::[])
end))
end
| Microsoft_FStar_Parser_AST.Annotated ((_41_423, term)) -> begin
(let _68_18779 = (free_type_vars env term)
in (env, _68_18779))
end
| Microsoft_FStar_Parser_AST.TAnnotated ((id, _41_429)) -> begin
(let _41_435 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_41_435) with
| (env, _41_434) -> begin
(env, [])
end))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(let _68_18780 = (free_type_vars env t)
in (env, _68_18780))
end))
and free_type_vars = (fun ( env ) ( t ) -> (match ((let _68_18783 = (unparen t)
in _68_18783.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Tvar (a) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env a)) with
| None -> begin
(a)::[]
end
| _41_444 -> begin
[]
end)
end
| (Microsoft_FStar_Parser_AST.Wild) | (Microsoft_FStar_Parser_AST.Const (_)) | (Microsoft_FStar_Parser_AST.Var (_)) | (Microsoft_FStar_Parser_AST.Name (_)) -> begin
[]
end
| (Microsoft_FStar_Parser_AST.Requires ((t, _))) | (Microsoft_FStar_Parser_AST.Ensures ((t, _))) | (Microsoft_FStar_Parser_AST.Labeled ((t, _, _))) | (Microsoft_FStar_Parser_AST.NamedTyp ((_, t))) | (Microsoft_FStar_Parser_AST.Paren (t)) | (Microsoft_FStar_Parser_AST.Ascribed ((t, _))) -> begin
(free_type_vars env t)
end
| Microsoft_FStar_Parser_AST.Construct ((_41_480, ts)) -> begin
(Support.List.collect (fun ( _41_487 ) -> (match (_41_487) with
| (t, _41_486) -> begin
(free_type_vars env t)
end)) ts)
end
| Microsoft_FStar_Parser_AST.Op ((_41_489, ts)) -> begin
(Support.List.collect (free_type_vars env) ts)
end
| Microsoft_FStar_Parser_AST.App ((t1, t2, _41_496)) -> begin
(let _68_18786 = (free_type_vars env t1)
in (let _68_18785 = (free_type_vars env t2)
in (Support.List.append _68_18786 _68_18785)))
end
| Microsoft_FStar_Parser_AST.Refine ((b, t)) -> begin
(let _41_505 = (free_type_vars_b env b)
in (match (_41_505) with
| (env, f) -> begin
(let _68_18787 = (free_type_vars env t)
in (Support.List.append f _68_18787))
end))
end
| (Microsoft_FStar_Parser_AST.Product ((binders, body))) | (Microsoft_FStar_Parser_AST.Sum ((binders, body))) -> begin
(let _41_521 = (Support.List.fold_left (fun ( _41_514 ) ( binder ) -> (match (_41_514) with
| (env, free) -> begin
(let _41_518 = (free_type_vars_b env binder)
in (match (_41_518) with
| (env, f) -> begin
(env, (Support.List.append f free))
end))
end)) (env, []) binders)
in (match (_41_521) with
| (env, free) -> begin
(let _68_18790 = (free_type_vars env body)
in (Support.List.append free _68_18790))
end))
end
| Microsoft_FStar_Parser_AST.Project ((t, _41_524)) -> begin
(free_type_vars env t)
end
| (Microsoft_FStar_Parser_AST.Abs (_)) | (Microsoft_FStar_Parser_AST.If (_)) | (Microsoft_FStar_Parser_AST.QForall (_)) | (Microsoft_FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (Microsoft_FStar_Parser_AST.Let (_)) | (Microsoft_FStar_Parser_AST.Record (_)) | (Microsoft_FStar_Parser_AST.Match (_)) | (Microsoft_FStar_Parser_AST.TryWith (_)) | (Microsoft_FStar_Parser_AST.Seq (_)) -> begin
(Microsoft_FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.Microsoft_FStar_Parser_AST.range)
end))

let head_and_args = (fun ( t ) -> (let rec aux = (fun ( args ) ( t ) -> (match ((let _68_18797 = (unparen t)
in _68_18797.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((t, arg, imp)) -> begin
(aux (((arg, imp))::args) t)
end
| Microsoft_FStar_Parser_AST.Construct ((l, args')) -> begin
({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Name (l); Microsoft_FStar_Parser_AST.range = t.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Parser_AST.level = t.Microsoft_FStar_Parser_AST.level}, (Support.List.append args' args))
end
| _41_568 -> begin
(t, args)
end))
in (aux [] t)))

let close = (fun ( env ) ( t ) -> (let ftv = (let _68_18802 = (free_type_vars env t)
in (Support.Prims.pipe_left sort_ftv _68_18802))
in (match (((Support.List.length ftv) = 0)) with
| true -> begin
t
end
| false -> begin
(let binders = (Support.Prims.pipe_right ftv (Support.List.map (fun ( x ) -> (let _68_18806 = (let _68_18805 = (let _68_18804 = (kind_star x.Microsoft_FStar_Absyn_Syntax.idRange)
in (x, _68_18804))
in Microsoft_FStar_Parser_AST.TAnnotated (_68_18805))
in (Microsoft_FStar_Parser_AST.mk_binder _68_18806 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type (Some (Microsoft_FStar_Absyn_Syntax.Implicit)))))))
in (let result = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((binders, t))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
in result))
end)))

let close_fun = (fun ( env ) ( t ) -> (let ftv = (let _68_18811 = (free_type_vars env t)
in (Support.Prims.pipe_left sort_ftv _68_18811))
in (match (((Support.List.length ftv) = 0)) with
| true -> begin
t
end
| false -> begin
(let binders = (Support.Prims.pipe_right ftv (Support.List.map (fun ( x ) -> (let _68_18815 = (let _68_18814 = (let _68_18813 = (kind_star x.Microsoft_FStar_Absyn_Syntax.idRange)
in (x, _68_18813))
in Microsoft_FStar_Parser_AST.TAnnotated (_68_18814))
in (Microsoft_FStar_Parser_AST.mk_binder _68_18815 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type (Some (Microsoft_FStar_Absyn_Syntax.Implicit)))))))
in (let t = (match ((let _68_18816 = (unlabel t)
in _68_18816.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Product (_41_581) -> begin
t
end
| _41_584 -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.App (((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.effect_Tot_lid)) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level), t, Microsoft_FStar_Parser_AST.Nothing))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
end)
in (let result = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((binders, t))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
in result)))
end)))

let rec uncurry = (fun ( bs ) ( t ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Product ((binders, t)) -> begin
(uncurry (Support.List.append bs binders) t)
end
| _41_594 -> begin
(bs, t)
end))

let rec is_app_pattern = (fun ( p ) -> (match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed ((p, _41_598)) -> begin
(is_app_pattern p)
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar (_41_604); Microsoft_FStar_Parser_AST.prange = _41_602}, _41_608)) -> begin
true
end
| _41_612 -> begin
false
end))

let rec destruct_app_pattern = (fun ( env ) ( is_top_level ) ( p ) -> (match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed ((p, t)) -> begin
(let _41_624 = (destruct_app_pattern env is_top_level p)
in (match (_41_624) with
| (name, args, _41_623) -> begin
(name, args, Some (t))
end))
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((id, _41_629)); Microsoft_FStar_Parser_AST.prange = _41_626}, args)) when is_top_level -> begin
(let _68_18830 = (let _68_18829 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in Support.Microsoft.FStar.Util.Inr (_68_18829))
in (_68_18830, args, None))
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((id, _41_640)); Microsoft_FStar_Parser_AST.prange = _41_637}, args)) -> begin
(Support.Microsoft.FStar.Util.Inl (id), args, None)
end
| _41_648 -> begin
(failwith ("Not an app pattern"))
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

let binder_of_bnd = (fun ( _41_3 ) -> (match (_41_3) with
| TBinder ((a, k, aq)) -> begin
(Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)), aq)
end
| VBinder ((x, t, aq)) -> begin
(Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)), aq)
end
| _41_667 -> begin
(failwith ("Impossible"))
end))

let as_binder = (fun ( env ) ( imp ) ( _41_4 ) -> (match (_41_4) with
| Support.Microsoft.FStar.Util.Inl ((None, k)) -> begin
(let _68_18860 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (_68_18860, env))
end
| Support.Microsoft.FStar.Util.Inr ((None, t)) -> begin
(let _68_18861 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_68_18861, env))
end
| Support.Microsoft.FStar.Util.Inl ((Some (a), k)) -> begin
(let _41_686 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_41_686) with
| (env, a) -> begin
((Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)), imp), env)
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _41_694 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_41_694) with
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
| _41_704 -> begin
(let _68_18872 = (Support.Microsoft.FStar.Range.string_of_range f.Microsoft_FStar_Parser_AST.range)
in (Support.Microsoft.FStar.Util.format2 "%s at %s" tag _68_18872))
end)
in (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Labeled ((f, msg, polarity))) f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level)))
in (let rec aux = (fun ( f ) -> (match (f.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (g) -> begin
(let _68_18876 = (let _68_18875 = (aux g)
in Microsoft_FStar_Parser_AST.Paren (_68_18875))
in (Microsoft_FStar_Parser_AST.mk_term _68_18876 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Op (("/\\", f1::f2::[])) -> begin
(let _68_18882 = (let _68_18881 = (let _68_18880 = (let _68_18879 = (aux f1)
in (let _68_18878 = (let _68_18877 = (aux f2)
in (_68_18877)::[])
in (_68_18879)::_68_18878))
in ("/\\", _68_18880))
in Microsoft_FStar_Parser_AST.Op (_68_18881))
in (Microsoft_FStar_Parser_AST.mk_term _68_18882 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.If ((f1, f2, f3)) -> begin
(let _68_18886 = (let _68_18885 = (let _68_18884 = (aux f2)
in (let _68_18883 = (aux f3)
in (f1, _68_18884, _68_18883)))
in Microsoft_FStar_Parser_AST.If (_68_18885))
in (Microsoft_FStar_Parser_AST.mk_term _68_18886 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Abs ((binders, g)) -> begin
(let _68_18889 = (let _68_18888 = (let _68_18887 = (aux g)
in (binders, _68_18887))
in Microsoft_FStar_Parser_AST.Abs (_68_18888))
in (Microsoft_FStar_Parser_AST.mk_term _68_18889 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| _41_726 -> begin
(label f)
end))
in (aux f))))

let mk_lb = (fun ( _41_730 ) -> (match (_41_730) with
| (n, t, e) -> begin
{Microsoft_FStar_Absyn_Syntax.lbname = n; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = Microsoft_FStar_Absyn_Const.effect_ALL_lid; Microsoft_FStar_Absyn_Syntax.lbdef = e}
end))

let rec desugar_data_pat = (fun ( env ) ( p ) -> (let resolvex = (fun ( l ) ( e ) ( x ) -> (match ((Support.Prims.pipe_right l (Support.Microsoft.FStar.Util.find_opt (fun ( _41_5 ) -> (match (_41_5) with
| Support.Microsoft.FStar.Util.Inr (y) -> begin
(y.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText = x.Microsoft_FStar_Absyn_Syntax.idText)
end
| _41_741 -> begin
false
end))))) with
| Some (Support.Microsoft.FStar.Util.Inr (y)) -> begin
(l, e, y)
end
| _41_746 -> begin
(let _41_749 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding e x)
in (match (_41_749) with
| (e, x) -> begin
((Support.Microsoft.FStar.Util.Inr (x))::l, e, x)
end))
end))
in (let resolvea = (fun ( l ) ( e ) ( a ) -> (match ((Support.Prims.pipe_right l (Support.Microsoft.FStar.Util.find_opt (fun ( _41_6 ) -> (match (_41_6) with
| Support.Microsoft.FStar.Util.Inl (b) -> begin
(b.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText = a.Microsoft_FStar_Absyn_Syntax.idText)
end
| _41_758 -> begin
false
end))))) with
| Some (Support.Microsoft.FStar.Util.Inl (b)) -> begin
(l, e, b)
end
| _41_763 -> begin
(let _41_766 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding e a)
in (match (_41_766) with
| (e, a) -> begin
((Support.Microsoft.FStar.Util.Inl (a))::l, e, a)
end))
end))
in (let rec aux = (fun ( loc ) ( env ) ( p ) -> (let pos = (fun ( q ) -> (Microsoft_FStar_Absyn_Syntax.withinfo q None p.Microsoft_FStar_Parser_AST.prange))
in (let pos_r = (fun ( r ) ( q ) -> (Microsoft_FStar_Absyn_Syntax.withinfo q None r))
in (match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatOr ([]) -> begin
(failwith ("impossible"))
end
| Microsoft_FStar_Parser_AST.PatOr (p::ps) -> begin
(let _41_786 = (aux loc env p)
in (match (_41_786) with
| (loc, env, var, p) -> begin
(let _41_801 = (Support.List.fold_left (fun ( _41_790 ) ( p ) -> (match (_41_790) with
| (loc, env, ps) -> begin
(let _41_797 = (aux loc env p)
in (match (_41_797) with
| (loc, env, _41_795, p) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_41_801) with
| (loc, env, ps) -> begin
(let pat = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_disj ((p)::(Support.List.rev ps))))
in (let _41_803 = (let _68_18961 = (Microsoft_FStar_Absyn_Syntax.pat_vars pat)
in (Support.Prims.ignore _68_18961))
in (loc, env, var, pat)))
end))
end))
end
| Microsoft_FStar_Parser_AST.PatAscribed ((p, t)) -> begin
(let p = (match ((is_kind env t)) with
| true -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatTvar (_41_810) -> begin
p
end
| Microsoft_FStar_Parser_AST.PatVar ((x, imp)) -> begin
(let _41_816 = p
in {Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatTvar ((x, imp)); Microsoft_FStar_Parser_AST.prange = _41_816.Microsoft_FStar_Parser_AST.prange})
end
| _41_819 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern", p.Microsoft_FStar_Parser_AST.prange))))
end)
end
| false -> begin
p
end)
in (let _41_825 = (aux loc env p)
in (match (_41_825) with
| (loc, env', binder, p) -> begin
(let binder = (match (binder) with
| LetBinder (_41_827) -> begin
(failwith ("impossible"))
end
| TBinder ((x, _41_831, aq)) -> begin
(let _68_18963 = (let _68_18962 = (desugar_kind env t)
in (x, _68_18962, aq))
in TBinder (_68_18963))
end
| VBinder ((x, _41_837, aq)) -> begin
(let t = (close_fun env t)
in (let _68_18965 = (let _68_18964 = (desugar_typ env t)
in (x, _68_18964, aq))
in VBinder (_68_18965)))
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
(let a = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _68_18966 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_twild ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a Microsoft_FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((a, Microsoft_FStar_Absyn_Syntax.kun, aq)), _68_18966)))
end
| false -> begin
(let _41_852 = (resolvea loc env a)
in (match (_41_852) with
| (loc, env, abvd) -> begin
(let _68_18967 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_tvar ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s abvd Microsoft_FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((abvd, Microsoft_FStar_Absyn_Syntax.kun, aq)), _68_18967))
end))
end))
end
| Microsoft_FStar_Parser_AST.PatWild -> begin
(let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let y = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _68_18968 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_wild ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s y Microsoft_FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _68_18968))))
end
| Microsoft_FStar_Parser_AST.PatConst (c) -> begin
(let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _68_18969 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_constant (c)))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _68_18969)))
end
| Microsoft_FStar_Parser_AST.PatVar ((x, imp)) -> begin
(let aq = (match (imp) with
| true -> begin
Some (Microsoft_FStar_Absyn_Syntax.Implicit)
end
| false -> begin
None
end)
in (let _41_867 = (resolvex loc env x)
in (match (_41_867) with
| (loc, env, xbvd) -> begin
(let _68_18970 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_var (((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s xbvd Microsoft_FStar_Absyn_Syntax.tun), imp))))
in (loc, env, VBinder ((xbvd, Microsoft_FStar_Absyn_Syntax.tun, aq)), _68_18970))
end)))
end
| Microsoft_FStar_Parser_AST.PatName (l) -> begin
(let l = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _68_18971 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), []))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _68_18971))))
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatName (l); Microsoft_FStar_Parser_AST.prange = _41_873}, args)) -> begin
(let _41_894 = (Support.List.fold_right (fun ( arg ) ( _41_884 ) -> (match (_41_884) with
| (loc, env, args) -> begin
(let _41_890 = (aux loc env arg)
in (match (_41_890) with
| (loc, env, _41_888, arg) -> begin
(loc, env, (arg)::args)
end))
end)) args (loc, env, []))
in (match (_41_894) with
| (loc, env, args) -> begin
(let l = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _68_18974 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _68_18974))))
end))
end
| Microsoft_FStar_Parser_AST.PatApp (_41_898) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern", p.Microsoft_FStar_Parser_AST.prange))))
end
| Microsoft_FStar_Parser_AST.PatList (pats) -> begin
(let _41_916 = (Support.List.fold_right (fun ( pat ) ( _41_906 ) -> (match (_41_906) with
| (loc, env, pats) -> begin
(let _41_912 = (aux loc env pat)
in (match (_41_912) with
| (loc, env, _41_910, pat) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_41_916) with
| (loc, env, pats) -> begin
(let pat = (let _68_18987 = (let _68_18986 = (let _68_18982 = (Support.Microsoft.FStar.Range.end_range p.Microsoft_FStar_Parser_AST.prange)
in (pos_r _68_18982))
in (let _68_18985 = (let _68_18984 = (let _68_18983 = (Microsoft_FStar_Absyn_Util.fv Microsoft_FStar_Absyn_Const.nil_lid)
in (_68_18983, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), []))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_68_18984))
in (Support.Prims.pipe_left _68_18986 _68_18985)))
in (Support.List.fold_right (fun ( hd ) ( tl ) -> (let r = (Support.Microsoft.FStar.Range.union_ranges hd.Microsoft_FStar_Absyn_Syntax.p tl.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_18981 = (let _68_18980 = (let _68_18979 = (Microsoft_FStar_Absyn_Util.fv Microsoft_FStar_Absyn_Const.cons_lid)
in (_68_18979, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), (hd)::(tl)::[]))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_68_18980))
in (Support.Prims.pipe_left (pos_r r) _68_18981)))) pats _68_18987))
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), pat)))
end))
end
| Microsoft_FStar_Parser_AST.PatTuple ((args, dep)) -> begin
(let _41_940 = (Support.List.fold_left (fun ( _41_929 ) ( p ) -> (match (_41_929) with
| (loc, env, pats) -> begin
(let _41_936 = (aux loc env p)
in (match (_41_936) with
| (loc, env, _41_934, pat) -> begin
(loc, env, (pat)::pats)
end))
end)) (loc, env, []) args)
in (match (_41_940) with
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
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, _41_946)) -> begin
v
end
| _41_950 -> begin
(failwith ("impossible"))
end)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _68_18990 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _68_18990)))))))
end))
end
| Microsoft_FStar_Parser_AST.PatRecord ([]) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern", p.Microsoft_FStar_Parser_AST.prange))))
end
| Microsoft_FStar_Parser_AST.PatRecord (fields) -> begin
(let _41_960 = (Support.List.hd fields)
in (match (_41_960) with
| (f, _41_959) -> begin
(let _41_964 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_41_964) with
| (record, _41_963) -> begin
(let fields = (Support.Prims.pipe_right fields (Support.List.map (fun ( _41_967 ) -> (match (_41_967) with
| (f, p) -> begin
(let _68_18992 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in (_68_18992, p))
end))))
in (let args = (Support.Prims.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map (fun ( _41_972 ) -> (match (_41_972) with
| (f, _41_971) -> begin
(match ((Support.Prims.pipe_right fields (Support.List.tryFind (fun ( _41_976 ) -> (match (_41_976) with
| (g, _41_975) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals f g)
end))))) with
| None -> begin
(Microsoft_FStar_Parser_AST.mk_pattern Microsoft_FStar_Parser_AST.PatWild p.Microsoft_FStar_Parser_AST.prange)
end
| Some ((_41_979, p)) -> begin
p
end)
end))))
in (let app = (Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatApp (((Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatName (record.Microsoft_FStar_Parser_DesugarEnv.constrname)) p.Microsoft_FStar_Parser_AST.prange), args))) p.Microsoft_FStar_Parser_AST.prange)
in (let _41_989 = (aux loc env app)
in (match (_41_989) with
| (env, e, b, p) -> begin
(let p = (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, _41_992, args)) -> begin
(let _68_19000 = (let _68_18999 = (let _68_18998 = (let _68_18997 = (let _68_18996 = (let _68_18995 = (Support.Prims.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map Support.Prims.fst))
in (record.Microsoft_FStar_Parser_DesugarEnv.typename, _68_18995))
in Microsoft_FStar_Absyn_Syntax.Record_ctor (_68_18996))
in Some (_68_18997))
in (fv, _68_18998, args))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_68_18999))
in (Support.Prims.pipe_left pos _68_19000))
end
| _41_997 -> begin
p
end)
in (env, e, b, p))
end)))))
end))
end))
end))))
in (let _41_1004 = (aux [] env p)
in (match (_41_1004) with
| (_41_1000, env, b, p) -> begin
(env, b, p)
end))))))
and desugar_binding_pat_maybe_top = (fun ( top ) ( env ) ( p ) -> (match (top) with
| true -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatVar ((x, _41_1010)) -> begin
(let _68_19006 = (let _68_19005 = (let _68_19004 = (Microsoft_FStar_Parser_DesugarEnv.qualify env x)
in (_68_19004, Microsoft_FStar_Absyn_Syntax.tun))
in LetBinder (_68_19005))
in (env, _68_19006, None))
end
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((x, _41_1017)); Microsoft_FStar_Parser_AST.prange = _41_1014}, t)) -> begin
(let _68_19010 = (let _68_19009 = (let _68_19008 = (Microsoft_FStar_Parser_DesugarEnv.qualify env x)
in (let _68_19007 = (desugar_typ env t)
in (_68_19008, _68_19007)))
in LetBinder (_68_19009))
in (env, _68_19010, None))
end
| _41_1025 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern at the top-level", p.Microsoft_FStar_Parser_AST.prange))))
end)
end
| false -> begin
(let _41_1029 = (desugar_data_pat env p)
in (match (_41_1029) with
| (env, binder, p) -> begin
(let p = (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_var (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_wild (_)) -> begin
None
end
| _41_1040 -> begin
Some (p)
end)
in (env, binder, p))
end))
end))
and desugar_binding_pat = (fun ( env ) ( p ) -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top = (fun ( _41_1044 ) ( env ) ( pat ) -> (let _41_1052 = (desugar_data_pat env pat)
in (match (_41_1052) with
| (env, _41_1050, pat) -> begin
(env, pat)
end)))
and desugar_match_pat = (fun ( env ) ( p ) -> (desugar_match_pat_maybe_top false env p))
and desugar_typ_or_exp = (fun ( env ) ( t ) -> (match ((is_type env t)) with
| true -> begin
(let _68_19020 = (desugar_typ env t)
in Support.Microsoft.FStar.Util.Inl (_68_19020))
end
| false -> begin
(let _68_19021 = (desugar_exp env t)
in Support.Microsoft.FStar.Util.Inr (_68_19021))
end))
and desugar_exp = (fun ( env ) ( e ) -> (desugar_exp_maybe_top false env e))
and desugar_exp_maybe_top = (fun ( top_level ) ( env ) ( top ) -> (let pos = (fun ( e ) -> (e None top.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( e ) -> (let _41_1066 = e
in {Microsoft_FStar_Absyn_Syntax.n = _41_1066.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _41_1066.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = top.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _41_1066.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _41_1066.Microsoft_FStar_Absyn_Syntax.uvs}))
in (match ((let _68_19041 = (unparen top)
in _68_19041.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Const (c) -> begin
(Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match ((op_as_vlid env (Support.List.length args) top.Microsoft_FStar_Parser_AST.range s)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat "Unexpected operator: " s), top.Microsoft_FStar_Parser_AST.range))))
end
| Some (l) -> begin
(let op = (let _68_19044 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (Microsoft_FStar_Absyn_Util.fvar None l _68_19044))
in (let args = (Support.Prims.pipe_right args (Support.List.map (fun ( t ) -> (let _68_19046 = (desugar_typ_or_exp env t)
in (_68_19046, None)))))
in (let _68_19047 = (Microsoft_FStar_Absyn_Util.mk_exp_app op args)
in (Support.Prims.pipe_left setpos _68_19047))))
end)
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) -> begin
(match ((l.Microsoft_FStar_Absyn_Syntax.str = "ref")) with
| true -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env Microsoft_FStar_Absyn_Const.alloc_lid)) with
| None -> begin
(let _68_19050 = (let _68_19049 = (let _68_19048 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in ("Identifier \'ref\' not found; include lib/st.fst in your path", _68_19048))
in Microsoft_FStar_Absyn_Syntax.Error (_68_19049))
in (raise (_68_19050)))
end
| Some (e) -> begin
(setpos e)
end)
end
| false -> begin
(let _68_19051 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (Support.Prims.pipe_left setpos _68_19051))
end)
end
| Microsoft_FStar_Parser_AST.Construct ((l, args)) -> begin
(let dt = (let _68_19056 = (let _68_19055 = (let _68_19054 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (_68_19054, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _68_19055))
in (Support.Prims.pipe_left pos _68_19056))
in (match (args) with
| [] -> begin
dt
end
| _41_1093 -> begin
(let args = (Support.List.map (fun ( _41_1096 ) -> (match (_41_1096) with
| (t, imp) -> begin
(let te = (desugar_typ_or_exp env t)
in (arg_withimp_e imp te))
end)) args)
in (let _68_19061 = (let _68_19060 = (let _68_19059 = (let _68_19058 = (Microsoft_FStar_Absyn_Util.mk_exp_app dt args)
in (_68_19058, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_68_19059))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _68_19060))
in (Support.Prims.pipe_left setpos _68_19061)))
end))
end
| Microsoft_FStar_Parser_AST.Abs ((binders, body)) -> begin
(let _41_1133 = (Support.List.fold_left (fun ( _41_1105 ) ( pat ) -> (match (_41_1105) with
| (env, ftvs) -> begin
(match (pat.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatTvar ((a, imp)); Microsoft_FStar_Parser_AST.prange = _41_1108}, t)) -> begin
(let ftvs = (let _68_19064 = (free_type_vars env t)
in (Support.List.append _68_19064 ftvs))
in (let _68_19066 = (let _68_19065 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (Support.Prims.pipe_left Support.Prims.fst _68_19065))
in (_68_19066, ftvs)))
end
| Microsoft_FStar_Parser_AST.PatTvar ((a, _41_1120)) -> begin
(let _68_19068 = (let _68_19067 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (Support.Prims.pipe_left Support.Prims.fst _68_19067))
in (_68_19068, ftvs))
end
| Microsoft_FStar_Parser_AST.PatAscribed ((_41_1124, t)) -> begin
(let _68_19070 = (let _68_19069 = (free_type_vars env t)
in (Support.List.append _68_19069 ftvs))
in (env, _68_19070))
end
| _41_1129 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_41_1133) with
| (_41_1131, ftv) -> begin
(let ftv = (sort_ftv ftv)
in (let binders = (let _68_19072 = (Support.Prims.pipe_right ftv (Support.List.map (fun ( a ) -> (Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatTvar ((a, true))) top.Microsoft_FStar_Parser_AST.range))))
in (Support.List.append _68_19072 binders))
in (let rec aux = (fun ( env ) ( bs ) ( sc_pat_opt ) ( _41_7 ) -> (match (_41_7) with
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
(let _41_1156 = (desugar_binding_pat env p)
in (match (_41_1156) with
| (env, b, pat) -> begin
(let _41_1216 = (match (b) with
| LetBinder (_41_1158) -> begin
(failwith ("Impossible"))
end
| TBinder ((a, k, aq)) -> begin
(let _68_19081 = (binder_of_bnd b)
in (_68_19081, sc_pat_opt))
end
| VBinder ((x, t, aq)) -> begin
(let b = (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)
in (let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _41_1173) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _68_19083 = (let _68_19082 = (Microsoft_FStar_Absyn_Util.bvar_to_exp b)
in (_68_19082, p))
in Some (_68_19083))
end
| (Some (p), Some ((sc, p'))) -> begin
(match ((sc.Microsoft_FStar_Absyn_Syntax.n, p'.Microsoft_FStar_Absyn_Syntax.v)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_41_1187), _41_1190) -> begin
(let tup = (Microsoft_FStar_Absyn_Util.mk_tuple_data_lid 2 top.Microsoft_FStar_Parser_AST.range)
in (let sc = (let _68_19090 = (let _68_19089 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) tup top.Microsoft_FStar_Parser_AST.range)
in (let _68_19088 = (let _68_19087 = (Microsoft_FStar_Absyn_Syntax.varg sc)
in (let _68_19086 = (let _68_19085 = (let _68_19084 = (Microsoft_FStar_Absyn_Util.bvar_to_exp b)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg _68_19084))
in (_68_19085)::[])
in (_68_19087)::_68_19086))
in (_68_19089, _68_19088)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _68_19090 None top.Microsoft_FStar_Parser_AST.range))
in (let p = (let _68_19094 = (let _68_19092 = (let _68_19091 = (Microsoft_FStar_Absyn_Util.fv tup)
in (_68_19091, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), (p')::(p)::[]))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_68_19092))
in (let _68_19093 = (Support.Microsoft.FStar.Range.union_ranges p'.Microsoft_FStar_Absyn_Syntax.p p.Microsoft_FStar_Absyn_Syntax.p)
in (Microsoft_FStar_Absyn_Util.withinfo _68_19094 None _68_19093)))
in Some ((sc, p)))))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app ((_41_1196, args)), Microsoft_FStar_Absyn_Syntax.Pat_cons ((_41_1201, _41_1203, pats))) -> begin
(let tup = (Microsoft_FStar_Absyn_Util.mk_tuple_data_lid (1 + (Support.List.length args)) top.Microsoft_FStar_Parser_AST.range)
in (let sc = (let _68_19100 = (let _68_19099 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) tup top.Microsoft_FStar_Parser_AST.range)
in (let _68_19098 = (let _68_19097 = (let _68_19096 = (let _68_19095 = (Microsoft_FStar_Absyn_Util.bvar_to_exp b)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg _68_19095))
in (_68_19096)::[])
in (Support.List.append args _68_19097))
in (_68_19099, _68_19098)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _68_19100 None top.Microsoft_FStar_Parser_AST.range))
in (let p = (let _68_19104 = (let _68_19102 = (let _68_19101 = (Microsoft_FStar_Absyn_Util.fv tup)
in (_68_19101, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), (Support.List.append pats ((p)::[]))))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_68_19102))
in (let _68_19103 = (Support.Microsoft.FStar.Range.union_ranges p'.Microsoft_FStar_Absyn_Syntax.p p.Microsoft_FStar_Absyn_Syntax.p)
in (Microsoft_FStar_Absyn_Util.withinfo _68_19104 None _68_19103)))
in Some ((sc, p)))))
end
| _41_1212 -> begin
(failwith ("Impossible"))
end)
end)
in ((Support.Microsoft.FStar.Util.Inr (b), aq), sc_pat_opt)))
end)
in (match (_41_1216) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| Microsoft_FStar_Parser_AST.App (({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Var (a); Microsoft_FStar_Parser_AST.range = _41_1220; Microsoft_FStar_Parser_AST.level = _41_1218}, arg, _41_1226)) when ((Microsoft_FStar_Absyn_Syntax.lid_equals a Microsoft_FStar_Absyn_Const.assert_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals a Microsoft_FStar_Absyn_Const.assume_lid)) -> begin
(let phi = (desugar_formula env arg)
in (let _68_19115 = (let _68_19114 = (let _68_19113 = (let _68_19107 = (Microsoft_FStar_Absyn_Syntax.range_of_lid a)
in (Microsoft_FStar_Absyn_Util.fvar None a _68_19107))
in (let _68_19112 = (let _68_19111 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ phi)
in (let _68_19110 = (let _68_19109 = (let _68_19108 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant Microsoft_FStar_Absyn_Syntax.Const_unit None top.Microsoft_FStar_Parser_AST.range)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg _68_19108))
in (_68_19109)::[])
in (_68_19111)::_68_19110))
in (_68_19113, _68_19112)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _68_19114))
in (Support.Prims.pipe_left pos _68_19115)))
end
| Microsoft_FStar_Parser_AST.App (_41_1231) -> begin
(let rec aux = (fun ( args ) ( e ) -> (match ((let _68_19120 = (unparen e)
in _68_19120.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((e, t, imp)) -> begin
(let arg = (let _68_19121 = (desugar_typ_or_exp env t)
in (Support.Prims.pipe_left (arg_withimp_e imp) _68_19121))
in (aux ((arg)::args) e))
end
| _41_1243 -> begin
(let head = (desugar_exp env e)
in (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (head, args))))
end))
in (aux [] top))
end
| Microsoft_FStar_Parser_AST.Seq ((t1, t2)) -> begin
(let _68_19127 = (let _68_19126 = (let _68_19125 = (let _68_19124 = (desugar_exp env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Let ((false, (((Microsoft_FStar_Parser_AST.mk_pattern Microsoft_FStar_Parser_AST.PatWild t1.Microsoft_FStar_Parser_AST.range), t1))::[], t2))) top.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Expr))
in (_68_19124, Microsoft_FStar_Absyn_Syntax.Sequence))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_68_19125))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _68_19126))
in (Support.Prims.pipe_left setpos _68_19127))
end
| Microsoft_FStar_Parser_AST.Let ((is_rec, (pat, _snd)::_tl, body)) -> begin
(let ds_let_rec = (fun ( _41_1259 ) -> (match (()) with
| () -> begin
(let bindings = ((pat, _snd))::_tl
in (let funs = (Support.Prims.pipe_right bindings (Support.List.map (fun ( _41_1263 ) -> (match (_41_1263) with
| (p, def) -> begin
(match ((is_app_pattern p)) with
| true -> begin
(let _68_19131 = (destruct_app_pattern env top_level p)
in (_68_19131, def))
end
| false -> begin
(match ((Microsoft_FStar_Parser_AST.un_function p def)) with
| Some ((p, def)) -> begin
(let _68_19132 = (destruct_app_pattern env top_level p)
in (_68_19132, def))
end
| _41_1269 -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((id, _41_1274)); Microsoft_FStar_Parser_AST.prange = _41_1271}, t)) -> begin
(match (top_level) with
| true -> begin
(let _68_19135 = (let _68_19134 = (let _68_19133 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in Support.Microsoft.FStar.Util.Inr (_68_19133))
in (_68_19134, [], Some (t)))
in (_68_19135, def))
end
| false -> begin
((Support.Microsoft.FStar.Util.Inl (id), [], Some (t)), def)
end)
end
| Microsoft_FStar_Parser_AST.PatVar ((id, _41_1283)) -> begin
(match (top_level) with
| true -> begin
(let _68_19138 = (let _68_19137 = (let _68_19136 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in Support.Microsoft.FStar.Util.Inr (_68_19136))
in (_68_19137, [], None))
in (_68_19138, def))
end
| false -> begin
((Support.Microsoft.FStar.Util.Inl (id), [], None), def)
end)
end
| _41_1287 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected let binding", p.Microsoft_FStar_Parser_AST.prange))))
end)
end)
end)
end))))
in (let _41_1313 = (Support.List.fold_left (fun ( _41_1291 ) ( _41_1300 ) -> (match ((_41_1291, _41_1300)) with
| ((env, fnames), ((f, _41_1294, _41_1296), _41_1299)) -> begin
(let _41_1310 = (match (f) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(let _41_1305 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_41_1305) with
| (env, xx) -> begin
(env, Support.Microsoft.FStar.Util.Inl (xx))
end))
end
| Support.Microsoft.FStar.Util.Inr (l) -> begin
(let _68_19141 = (Microsoft_FStar_Parser_DesugarEnv.push_rec_binding env (Microsoft_FStar_Parser_DesugarEnv.Binding_let (l)))
in (_68_19141, Support.Microsoft.FStar.Util.Inr (l)))
end)
in (match (_41_1310) with
| (env, lbname) -> begin
(env, (lbname)::fnames)
end))
end)) (env, []) funs)
in (match (_41_1313) with
| (env', fnames) -> begin
(let fnames = (Support.List.rev fnames)
in (let desugar_one_def = (fun ( env ) ( lbname ) ( _41_1324 ) -> (match (_41_1324) with
| ((_41_1319, args, result_t), def) -> begin
(let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _68_19148 = (Support.Microsoft.FStar.Range.union_ranges t.Microsoft_FStar_Parser_AST.range def.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Ascribed ((def, t))) _68_19148 Microsoft_FStar_Parser_AST.Expr))
end)
in (let def = (match (args) with
| [] -> begin
def
end
| _41_1331 -> begin
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
in (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), body)))))))
end))))
end))
in (let ds_non_rec = (fun ( pat ) ( t1 ) ( t2 ) -> (let t1 = (desugar_exp env t1)
in (let _41_1344 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_41_1344) with
| (env, binder, pat) -> begin
(match (binder) with
| TBinder (_41_1346) -> begin
(failwith ("Unexpected type binder in let"))
end
| LetBinder ((l, t)) -> begin
(let body = (desugar_exp env t2)
in (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((false, ({Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = Microsoft_FStar_Absyn_Const.effect_ALL_lid; Microsoft_FStar_Absyn_Syntax.lbdef = t1})::[]), body))))
end
| VBinder ((x, t, _41_1356)) -> begin
(let body = (desugar_exp env t2)
in (let body = (match (pat) with
| (None) | (Some ({Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_wild (_); Microsoft_FStar_Absyn_Syntax.sort = _; Microsoft_FStar_Absyn_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _68_19160 = (let _68_19159 = (Microsoft_FStar_Absyn_Util.bvd_to_exp x t)
in (_68_19159, ((pat, None, body))::[]))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _68_19160 None body.Microsoft_FStar_Absyn_Syntax.pos))
end)
in (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((false, ((mk_lb (Support.Microsoft.FStar.Util.Inl (x), t, t1)))::[]), body)))))
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
(let _68_19173 = (let _68_19172 = (let _68_19171 = (desugar_exp env t1)
in (let _68_19170 = (let _68_19169 = (let _68_19165 = (desugar_exp env t2)
in ((Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (true))) None t2.Microsoft_FStar_Parser_AST.range), None, _68_19165))
in (let _68_19168 = (let _68_19167 = (let _68_19166 = (desugar_exp env t3)
in ((Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (false))) None t3.Microsoft_FStar_Parser_AST.range), None, _68_19166))
in (_68_19167)::[])
in (_68_19169)::_68_19168))
in (_68_19171, _68_19170)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _68_19172))
in (Support.Prims.pipe_left pos _68_19173))
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
(let desugar_branch = (fun ( _41_1395 ) -> (match (_41_1395) with
| (pat, wopt, b) -> begin
(let _41_1398 = (desugar_match_pat env pat)
in (match (_41_1398) with
| (env, pat) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _68_19176 = (desugar_exp env e)
in Some (_68_19176))
end)
in (let b = (desugar_exp env b)
in (pat, wopt, b)))
end))
end))
in (let _68_19182 = (let _68_19181 = (let _68_19180 = (desugar_exp env e)
in (let _68_19179 = (Support.List.map desugar_branch branches)
in (_68_19180, _68_19179)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _68_19181))
in (Support.Prims.pipe_left pos _68_19182)))
end
| Microsoft_FStar_Parser_AST.Ascribed ((e, t)) -> begin
(let _68_19188 = (let _68_19187 = (let _68_19186 = (desugar_exp env e)
in (let _68_19185 = (desugar_typ env t)
in (_68_19186, _68_19185, None)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed _68_19187))
in (Support.Prims.pipe_left pos _68_19188))
end
| Microsoft_FStar_Parser_AST.Record ((_41_1409, [])) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected empty record", top.Microsoft_FStar_Parser_AST.range))))
end
| Microsoft_FStar_Parser_AST.Record ((eopt, fields)) -> begin
(let _41_1420 = (Support.List.hd fields)
in (match (_41_1420) with
| (f, _41_1419) -> begin
(let qfn = (fun ( g ) -> (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append f.Microsoft_FStar_Absyn_Syntax.ns ((g)::[]))))
in (let _41_1426 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_41_1426) with
| (record, _41_1425) -> begin
(let get_field = (fun ( xopt ) ( f ) -> (let fn = f.Microsoft_FStar_Absyn_Syntax.ident
in (let found = (Support.Prims.pipe_right fields (Support.Microsoft.FStar.Util.find_opt (fun ( _41_1434 ) -> (match (_41_1434) with
| (g, _41_1433) -> begin
(let gn = g.Microsoft_FStar_Absyn_Syntax.ident
in (fn.Microsoft_FStar_Absyn_Syntax.idText = gn.Microsoft_FStar_Absyn_Syntax.idText))
end))))
in (match (found) with
| Some ((_41_1438, e)) -> begin
(let _68_19196 = (qfn fn)
in (_68_19196, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _68_19200 = (let _68_19199 = (let _68_19198 = (let _68_19197 = (Microsoft_FStar_Absyn_Syntax.text_of_lid f)
in (Support.Microsoft.FStar.Util.format1 "Field %s is missing" _68_19197))
in (_68_19198, top.Microsoft_FStar_Parser_AST.range))
in Microsoft_FStar_Absyn_Syntax.Error (_68_19199))
in (raise (_68_19200)))
end
| Some (x) -> begin
(let _68_19201 = (qfn fn)
in (_68_19201, (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Project ((x, f))) x.Microsoft_FStar_Parser_AST.range x.Microsoft_FStar_Parser_AST.level)))
end)
end))))
in (let recterm = (match (eopt) with
| None -> begin
(let _68_19206 = (let _68_19205 = (Support.Prims.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map (fun ( _41_1450 ) -> (match (_41_1450) with
| (f, _41_1449) -> begin
(let _68_19204 = (let _68_19203 = (get_field None f)
in (Support.Prims.pipe_left Support.Prims.snd _68_19203))
in (_68_19204, Microsoft_FStar_Parser_AST.Nothing))
end))))
in (record.Microsoft_FStar_Parser_DesugarEnv.constrname, _68_19205))
in Microsoft_FStar_Parser_AST.Construct (_68_19206))
end
| Some (e) -> begin
(let x = (Microsoft_FStar_Absyn_Util.genident (Some (e.Microsoft_FStar_Parser_AST.range)))
in (let xterm = (let _68_19208 = (let _68_19207 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((x)::[]))
in Microsoft_FStar_Parser_AST.Var (_68_19207))
in (Microsoft_FStar_Parser_AST.mk_term _68_19208 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr))
in (let record = (let _68_19211 = (let _68_19210 = (Support.Prims.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map (fun ( _41_1458 ) -> (match (_41_1458) with
| (f, _41_1457) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _68_19210))
in Microsoft_FStar_Parser_AST.Record (_68_19211))
in Microsoft_FStar_Parser_AST.Let ((false, (((Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatVar ((x, false))) x.Microsoft_FStar_Absyn_Syntax.idRange), e))::[], (Microsoft_FStar_Parser_AST.mk_term record top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))))))
end)
in (let recterm = (Microsoft_FStar_Parser_AST.mk_term recterm top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level)
in (let e = (desugar_exp env recterm)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _41_1481)); Microsoft_FStar_Absyn_Syntax.tk = _41_1478; Microsoft_FStar_Absyn_Syntax.pos = _41_1476; Microsoft_FStar_Absyn_Syntax.fvs = _41_1474; Microsoft_FStar_Absyn_Syntax.uvs = _41_1472}, args)); Microsoft_FStar_Absyn_Syntax.tk = _41_1470; Microsoft_FStar_Absyn_Syntax.pos = _41_1468; Microsoft_FStar_Absyn_Syntax.fvs = _41_1466; Microsoft_FStar_Absyn_Syntax.uvs = _41_1464}, Microsoft_FStar_Absyn_Syntax.Data_app))) -> begin
(let e = (let _68_19221 = (let _68_19220 = (let _68_19219 = (let _68_19218 = (let _68_19217 = (let _68_19216 = (let _68_19215 = (let _68_19214 = (Support.Prims.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map Support.Prims.fst))
in (record.Microsoft_FStar_Parser_DesugarEnv.typename, _68_19214))
in Microsoft_FStar_Absyn_Syntax.Record_ctor (_68_19215))
in Some (_68_19216))
in (fv, _68_19217))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _68_19218 None e.Microsoft_FStar_Absyn_Syntax.pos))
in (_68_19219, args))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _68_19220))
in (Support.Prims.pipe_left pos _68_19221))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Data_app)))))
end
| _41_1495 -> begin
e
end)))))
end)))
end))
end
| Microsoft_FStar_Parser_AST.Project ((e, f)) -> begin
(let _41_1503 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_41_1503) with
| (_41_1501, fieldname) -> begin
(let e = (desugar_exp env e)
in (let fn = (let _41_1508 = (Support.Microsoft.FStar.Util.prefix fieldname.Microsoft_FStar_Absyn_Syntax.ns)
in (match (_41_1508) with
| (ns, _41_1507) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append ns ((f.Microsoft_FStar_Absyn_Syntax.ident)::[])))
end))
in (let _68_19229 = (let _68_19228 = (let _68_19227 = (let _68_19224 = (Microsoft_FStar_Absyn_Syntax.range_of_lid f)
in (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Record_projector (fn))) fieldname _68_19224))
in (let _68_19226 = (let _68_19225 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_68_19225)::[])
in (_68_19227, _68_19226)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _68_19228))
in (Support.Prims.pipe_left pos _68_19229))))
end))
end
| Microsoft_FStar_Parser_AST.Paren (e) -> begin
(desugar_exp env e)
end
| _41_1513 -> begin
(Microsoft_FStar_Parser_AST.error "Unexpected term" top top.Microsoft_FStar_Parser_AST.range)
end))))
and desugar_typ = (fun ( env ) ( top ) -> (let wpos = (fun ( t ) -> (t None top.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( t ) -> (let _41_1520 = t
in {Microsoft_FStar_Absyn_Syntax.n = _41_1520.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _41_1520.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = top.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _41_1520.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _41_1520.Microsoft_FStar_Absyn_Syntax.uvs}))
in (let top = (unparen top)
in (let head_and_args = (fun ( t ) -> (let rec aux = (fun ( args ) ( t ) -> (match ((let _68_19252 = (unparen t)
in _68_19252.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((t, arg, imp)) -> begin
(aux (((arg, imp))::args) t)
end
| Microsoft_FStar_Parser_AST.Construct ((l, args')) -> begin
({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Name (l); Microsoft_FStar_Parser_AST.range = t.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Parser_AST.level = t.Microsoft_FStar_Parser_AST.level}, (Support.List.append args' args))
end
| _41_1538 -> begin
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
(let _68_19253 = (desugar_exp env t)
in (Support.Prims.pipe_right _68_19253 Microsoft_FStar_Absyn_Util.b2t))
end))
end
| Microsoft_FStar_Parser_AST.Ensures ((t, lopt)) -> begin
(let t = (label_conjuncts "post-condition" false lopt t)
in (match ((is_type env t)) with
| true -> begin
(desugar_typ env t)
end
| false -> begin
(let _68_19254 = (desugar_exp env t)
in (Support.Prims.pipe_right _68_19254 Microsoft_FStar_Absyn_Util.b2t))
end))
end
| Microsoft_FStar_Parser_AST.Op (("*", t1::_41_1552::[])) -> begin
(match ((is_type env t1)) with
| true -> begin
(let rec flatten = (fun ( t ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Op (("*", t1::t2::[])) -> begin
(let rest = (flatten t2)
in (t1)::rest)
end
| _41_1567 -> begin
(t)::[]
end))
in (let targs = (let _68_19259 = (flatten top)
in (Support.Prims.pipe_right _68_19259 (Support.List.map (fun ( t ) -> (let _68_19258 = (desugar_typ env t)
in (Microsoft_FStar_Absyn_Syntax.targ _68_19258))))))
in (let tup = (let _68_19260 = (Microsoft_FStar_Absyn_Util.mk_tuple_lid (Support.List.length targs) top.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) _68_19260))
in (Support.Prims.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))))
end
| false -> begin
(let _68_19266 = (let _68_19265 = (let _68_19264 = (let _68_19263 = (Microsoft_FStar_Parser_AST.term_to_string t1)
in (Support.Microsoft.FStar.Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _68_19263))
in (_68_19264, top.Microsoft_FStar_Parser_AST.range))
in Microsoft_FStar_Absyn_Syntax.Error (_68_19265))
in (raise (_68_19266)))
end)
end
| Microsoft_FStar_Parser_AST.Op (("=!=", args)) -> begin
(desugar_typ env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Op (("~", ((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Op (("==", args))) top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))::[]))) top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match ((op_as_tylid env (Support.List.length args) top.Microsoft_FStar_Parser_AST.range s)) with
| None -> begin
(let _68_19267 = (desugar_exp env top)
in (Support.Prims.pipe_right _68_19267 Microsoft_FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(let args = (Support.List.map (fun ( t ) -> (let _68_19269 = (desugar_typ_or_exp env t)
in (Support.Prims.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _68_19269))) args)
in (let _68_19270 = (Microsoft_FStar_Absyn_Util.ftv l Microsoft_FStar_Absyn_Syntax.kun)
in (Microsoft_FStar_Absyn_Util.mk_typ_app _68_19270 args)))
end)
end
| Microsoft_FStar_Parser_AST.Tvar (a) -> begin
(let _68_19271 = (Microsoft_FStar_Parser_DesugarEnv.fail_or2 (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (Support.Prims.pipe_left setpos _68_19271))
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) when ((Support.List.length l.Microsoft_FStar_Absyn_Syntax.ns) = 0) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env l.Microsoft_FStar_Absyn_Syntax.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _68_19272 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (Support.Prims.pipe_left setpos _68_19272))
end)
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) -> begin
(let l = (Microsoft_FStar_Absyn_Util.set_lid_range l top.Microsoft_FStar_Parser_AST.range)
in (let _68_19273 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (Support.Prims.pipe_left setpos _68_19273)))
end
| Microsoft_FStar_Parser_AST.Construct ((l, args)) -> begin
(let t = (let _68_19274 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (Support.Prims.pipe_left setpos _68_19274))
in (let args = (Support.List.map (fun ( _41_1603 ) -> (match (_41_1603) with
| (t, imp) -> begin
(let _68_19276 = (desugar_typ_or_exp env t)
in (Support.Prims.pipe_left (arg_withimp_t imp) _68_19276))
end)) args)
in (Microsoft_FStar_Absyn_Util.mk_typ_app t args)))
end
| Microsoft_FStar_Parser_AST.Abs ((binders, body)) -> begin
(let rec aux = (fun ( env ) ( bs ) ( _41_8 ) -> (match (_41_8) with
| [] -> begin
(let body = (desugar_typ env body)
in (Support.Prims.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam ((Support.List.rev bs), body))))
end
| hd::tl -> begin
(let _41_1621 = (desugar_binding_pat env hd)
in (match (_41_1621) with
| (env, bnd, pat) -> begin
(match (pat) with
| Some (q) -> begin
(let _68_19288 = (let _68_19287 = (let _68_19286 = (let _68_19285 = (Microsoft_FStar_Absyn_Print.pat_to_string q)
in (Support.Microsoft.FStar.Util.format1 "Pattern matching at the type level is not supported; got %s\n" _68_19285))
in (_68_19286, hd.Microsoft_FStar_Parser_AST.prange))
in Microsoft_FStar_Absyn_Syntax.Error (_68_19287))
in (raise (_68_19288)))
end
| None -> begin
(let b = (binder_of_bnd bnd)
in (aux env ((b)::bs) tl))
end)
end))
end))
in (aux env [] binders))
end
| Microsoft_FStar_Parser_AST.App (_41_1627) -> begin
(let rec aux = (fun ( args ) ( e ) -> (match ((let _68_19293 = (unparen e)
in _68_19293.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((e, arg, imp)) -> begin
(let arg = (let _68_19294 = (desugar_typ_or_exp env arg)
in (Support.Prims.pipe_left (arg_withimp_t imp) _68_19294))
in (aux ((arg)::args) e))
end
| _41_1639 -> begin
(let head = (desugar_typ env e)
in (Support.Prims.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (head, args))))
end))
in (aux [] top))
end
| Microsoft_FStar_Parser_AST.Product (([], t)) -> begin
(failwith ("Impossible: product with no binders"))
end
| Microsoft_FStar_Parser_AST.Product ((binders, t)) -> begin
(let _41_1651 = (uncurry binders t)
in (match (_41_1651) with
| (bs, t) -> begin
(let rec aux = (fun ( env ) ( bs ) ( _41_9 ) -> (match (_41_9) with
| [] -> begin
(let cod = (desugar_comp top.Microsoft_FStar_Parser_AST.range true env t)
in (Support.Prims.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun ((Support.List.rev bs), cod))))
end
| hd::tl -> begin
(let mlenv = (Microsoft_FStar_Parser_DesugarEnv.default_ml env)
in (let bb = (desugar_binder mlenv hd)
in (let _41_1665 = (as_binder env hd.Microsoft_FStar_Parser_AST.aqual bb)
in (match (_41_1665) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| Microsoft_FStar_Parser_AST.Refine ((b, f)) -> begin
(match ((desugar_exp_binder env b)) with
| (None, _41_1672) -> begin
(failwith ("Missing binder in refinement"))
end
| b -> begin
(let _41_1686 = (match ((as_binder env None (Support.Microsoft.FStar.Util.Inr (b)))) with
| ((Support.Microsoft.FStar.Util.Inr (x), _41_1678), env) -> begin
(x, env)
end
| _41_1683 -> begin
(failwith ("impossible"))
end)
in (match (_41_1686) with
| (b, env) -> begin
(let f = (match ((is_type env f)) with
| true -> begin
(desugar_formula env f)
end
| false -> begin
(let _68_19305 = (desugar_exp env f)
in (Support.Prims.pipe_right _68_19305 Microsoft_FStar_Absyn_Util.b2t))
end)
in (Support.Prims.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (b, f))))
end))
end)
end
| (Microsoft_FStar_Parser_AST.NamedTyp ((_, t))) | (Microsoft_FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| Microsoft_FStar_Parser_AST.Ascribed ((t, k)) -> begin
(let _68_19313 = (let _68_19312 = (let _68_19311 = (desugar_typ env t)
in (let _68_19310 = (desugar_kind env k)
in (_68_19311, _68_19310)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed' _68_19312))
in (Support.Prims.pipe_left wpos _68_19313))
end
| Microsoft_FStar_Parser_AST.Sum ((binders, t)) -> begin
(let _41_1720 = (Support.List.fold_left (fun ( _41_1705 ) ( b ) -> (match (_41_1705) with
| (env, tparams, typs) -> begin
(let _41_1709 = (desugar_exp_binder env b)
in (match (_41_1709) with
| (xopt, t) -> begin
(let _41_1715 = (match (xopt) with
| None -> begin
(let _68_19316 = (Microsoft_FStar_Absyn_Util.new_bvd (Some (top.Microsoft_FStar_Parser_AST.range)))
in (env, _68_19316))
end
| Some (x) -> begin
(Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_41_1715) with
| (env, x) -> begin
(let _68_19320 = (let _68_19319 = (let _68_19318 = (let _68_19317 = (Microsoft_FStar_Absyn_Util.close_with_lam tparams t)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _68_19317))
in (_68_19318)::[])
in (Support.List.append typs _68_19319))
in (env, (Support.List.append tparams (((Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)), None))::[])), _68_19320))
end))
end))
end)) (env, [], []) (Support.List.append binders (((Microsoft_FStar_Parser_AST.mk_binder (Microsoft_FStar_Parser_AST.NoName (t)) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Type None))::[])))
in (match (_41_1720) with
| (env, _41_1718, targs) -> begin
(let tup = (let _68_19321 = (Microsoft_FStar_Absyn_Util.mk_dtuple_lid (Support.List.length targs) top.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) _68_19321))
in (Support.Prims.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))
end))
end
| Microsoft_FStar_Parser_AST.Record (_41_1723) -> begin
(failwith ("Unexpected record type"))
end
| (Microsoft_FStar_Parser_AST.If (_)) | (Microsoft_FStar_Parser_AST.Labeled (_)) -> begin
(desugar_formula env top)
end
| _41_1732 when (top.Microsoft_FStar_Parser_AST.level = Microsoft_FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _41_1734 -> begin
(Microsoft_FStar_Parser_AST.error "Expected a type" top top.Microsoft_FStar_Parser_AST.range)
end))))))
and desugar_comp = (fun ( r ) ( default_ok ) ( env ) ( t ) -> (let fail = (fun ( msg ) -> (raise (Microsoft_FStar_Absyn_Syntax.Error ((msg, r)))))
in (let pre_process_comp_typ = (fun ( t ) -> (let _41_1745 = (head_and_args t)
in (match (_41_1745) with
| (head, args) -> begin
(match (head.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Name (lemma) when (lemma.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "Lemma") -> begin
(let unit = ((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.unit_lid)) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Type), Microsoft_FStar_Parser_AST.Nothing)
in (let nil_pat = ((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.nil_lid)) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Expr), Microsoft_FStar_Parser_AST.Nothing)
in (let _41_1771 = (Support.Prims.pipe_right args (Support.List.partition (fun ( _41_1753 ) -> (match (_41_1753) with
| (arg, _41_1752) -> begin
(match ((let _68_19333 = (unparen arg)
in _68_19333.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App (({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Var (d); Microsoft_FStar_Parser_AST.range = _41_1757; Microsoft_FStar_Parser_AST.level = _41_1755}, _41_1762, _41_1764)) -> begin
(d.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "decreases")
end
| _41_1768 -> begin
false
end)
end))))
in (match (_41_1771) with
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
| Microsoft_FStar_Parser_AST.Name (tot) when (((tot.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "Tot") && (not ((Microsoft_FStar_Parser_DesugarEnv.is_effect_name env Microsoft_FStar_Absyn_Const.effect_Tot_lid)))) && (let _68_19334 = (Microsoft_FStar_Parser_DesugarEnv.current_module env)
in (Microsoft_FStar_Absyn_Syntax.lid_equals _68_19334 Microsoft_FStar_Absyn_Const.prims_lid))) -> begin
(let args = (Support.List.map (fun ( _41_1786 ) -> (match (_41_1786) with
| (t, imp) -> begin
(let _68_19336 = (desugar_typ_or_exp env t)
in (Support.Prims.pipe_left (arg_withimp_t imp) _68_19336))
end)) args)
in (let _68_19337 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.effect_Tot_lid Microsoft_FStar_Absyn_Syntax.kun)
in (Microsoft_FStar_Absyn_Util.mk_typ_app _68_19337 args)))
end
| _41_1789 -> begin
(desugar_typ env t)
end)
end)))
in (let t = (pre_process_comp_typ t)
in (let _41_1793 = (Microsoft_FStar_Absyn_Util.head_and_args t)
in (match (_41_1793) with
| (head, args) -> begin
(match ((let _68_19339 = (let _68_19338 = (Microsoft_FStar_Absyn_Util.compress_typ head)
in _68_19338.Microsoft_FStar_Absyn_Syntax.n)
in (_68_19339, args))) with
| (Microsoft_FStar_Absyn_Syntax.Typ_const (eff), (Support.Microsoft.FStar.Util.Inl (result_typ), _41_1800)::rest) -> begin
(let _41_1840 = (Support.Prims.pipe_right rest (Support.List.partition (fun ( _41_10 ) -> (match (_41_10) with
| (Support.Microsoft.FStar.Util.Inr (_41_1806), _41_1809) -> begin
false
end
| (Support.Microsoft.FStar.Util.Inl (t), _41_1814) -> begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (fv); Microsoft_FStar_Absyn_Syntax.tk = _41_1823; Microsoft_FStar_Absyn_Syntax.pos = _41_1821; Microsoft_FStar_Absyn_Syntax.fvs = _41_1819; Microsoft_FStar_Absyn_Syntax.uvs = _41_1817}, (Support.Microsoft.FStar.Util.Inr (_41_1828), _41_1831)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.decreases_lid)
end
| _41_1837 -> begin
false
end)
end))))
in (match (_41_1840) with
| (dec, rest) -> begin
(let decreases_clause = (Support.Prims.pipe_right dec (Support.List.map (fun ( _41_11 ) -> (match (_41_11) with
| (Support.Microsoft.FStar.Util.Inl (t), _41_1845) -> begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((_41_1848, (Support.Microsoft.FStar.Util.Inr (arg), _41_1852)::[])) -> begin
Microsoft_FStar_Absyn_Syntax.DECREASES (arg)
end
| _41_1858 -> begin
(failwith ("impos"))
end)
end
| _41_1860 -> begin
(failwith ("impos"))
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
(let _68_19343 = (let _68_19342 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "%s is not an effect" _68_19342))
in (fail _68_19343))
end)
end))
end))
end
| _41_1864 -> begin
(match (default_ok) with
| true -> begin
(env.Microsoft_FStar_Parser_DesugarEnv.default_result_effect t r)
end
| false -> begin
(let _68_19345 = (let _68_19344 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "%s is not an effect" _68_19344))
in (fail _68_19345))
end)
end)
end))))))
and desugar_kind = (fun ( env ) ( k ) -> (let pos = (fun ( f ) -> (f k.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( kk ) -> (let _41_1871 = kk
in {Microsoft_FStar_Absyn_Syntax.n = _41_1871.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _41_1871.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = k.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _41_1871.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _41_1871.Microsoft_FStar_Absyn_Syntax.uvs}))
in (let k = (unparen k)
in (match (k.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Name ({Microsoft_FStar_Absyn_Syntax.ns = _41_1880; Microsoft_FStar_Absyn_Syntax.ident = _41_1878; Microsoft_FStar_Absyn_Syntax.nsstr = _41_1876; Microsoft_FStar_Absyn_Syntax.str = "Type"}) -> begin
(setpos Microsoft_FStar_Absyn_Syntax.mk_Kind_type)
end
| Microsoft_FStar_Parser_AST.Name ({Microsoft_FStar_Absyn_Syntax.ns = _41_1889; Microsoft_FStar_Absyn_Syntax.ident = _41_1887; Microsoft_FStar_Absyn_Syntax.nsstr = _41_1885; Microsoft_FStar_Absyn_Syntax.str = "Effect"}) -> begin
(setpos Microsoft_FStar_Absyn_Syntax.mk_Kind_effect)
end
| Microsoft_FStar_Parser_AST.Name (l) -> begin
(match ((let _68_19357 = (Microsoft_FStar_Parser_DesugarEnv.qualify_lid env l)
in (Microsoft_FStar_Parser_DesugarEnv.find_kind_abbrev env _68_19357))) with
| Some (l) -> begin
(Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev ((l, []), Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown)))
end
| _41_1897 -> begin
(Microsoft_FStar_Parser_AST.error "Unexpected term where kind was expected" k k.Microsoft_FStar_Parser_AST.range)
end)
end
| Microsoft_FStar_Parser_AST.Wild -> begin
(setpos Microsoft_FStar_Absyn_Syntax.kun)
end
| Microsoft_FStar_Parser_AST.Product ((bs, k)) -> begin
(let _41_1905 = (uncurry bs k)
in (match (_41_1905) with
| (bs, k) -> begin
(let rec aux = (fun ( env ) ( bs ) ( _41_12 ) -> (match (_41_12) with
| [] -> begin
(let _68_19368 = (let _68_19367 = (let _68_19366 = (desugar_kind env k)
in ((Support.List.rev bs), _68_19366))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_19367))
in (Support.Prims.pipe_left pos _68_19368))
end
| hd::tl -> begin
(let _41_1916 = (let _68_19370 = (let _68_19369 = (Microsoft_FStar_Parser_DesugarEnv.default_ml env)
in (desugar_binder _68_19369 hd))
in (Support.Prims.pipe_right _68_19370 (as_binder env hd.Microsoft_FStar_Parser_AST.aqual)))
in (match (_41_1916) with
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
(let args = (Support.List.map (fun ( _41_1926 ) -> (match (_41_1926) with
| (t, b) -> begin
(let qual = (match ((b = Microsoft_FStar_Parser_AST.Hash)) with
| true -> begin
Some (Microsoft_FStar_Absyn_Syntax.Implicit)
end
| false -> begin
None
end)
in (let _68_19372 = (desugar_typ_or_exp env t)
in (_68_19372, qual)))
end)) args)
in (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown))))
end)
end
| _41_1930 -> begin
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
| _41_1941 -> begin
None
end))
in (let pos = (fun ( t ) -> (t None f.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( t ) -> (let _41_1946 = t
in {Microsoft_FStar_Absyn_Syntax.n = _41_1946.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _41_1946.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = f.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _41_1946.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _41_1946.Microsoft_FStar_Absyn_Syntax.uvs}))
in (let desugar_quant = (fun ( q ) ( qt ) ( b ) ( pats ) ( body ) -> (let tk = (desugar_binder env (let _41_1954 = b
in {Microsoft_FStar_Parser_AST.b = _41_1954.Microsoft_FStar_Parser_AST.b; Microsoft_FStar_Parser_AST.brange = _41_1954.Microsoft_FStar_Parser_AST.brange; Microsoft_FStar_Parser_AST.blevel = Microsoft_FStar_Parser_AST.Formula; Microsoft_FStar_Parser_AST.aqual = _41_1954.Microsoft_FStar_Parser_AST.aqual}))
in (match (tk) with
| Support.Microsoft.FStar.Util.Inl ((Some (a), k)) -> begin
(let _41_1964 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_41_1964) with
| (env, a) -> begin
(let pats = (Support.List.map (fun ( e ) -> (let _68_19403 = (desugar_typ_or_exp env e)
in (Support.Prims.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _68_19403))) pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _41_1970 -> begin
(let _68_19404 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
in (Support.Prims.pipe_left setpos _68_19404))
end)
in (let body = (let _68_19410 = (let _68_19409 = (let _68_19408 = (let _68_19407 = (Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_68_19407)::[])
in (_68_19408, body))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_19409))
in (Support.Prims.pipe_left pos _68_19410))
in (let _68_19415 = (let _68_19414 = (let _68_19411 = (Microsoft_FStar_Absyn_Util.set_lid_range qt b.Microsoft_FStar_Parser_AST.brange)
in (Microsoft_FStar_Absyn_Util.ftv _68_19411 Microsoft_FStar_Absyn_Syntax.kun))
in (let _68_19413 = (let _68_19412 = (Microsoft_FStar_Absyn_Syntax.targ body)
in (_68_19412)::[])
in (Microsoft_FStar_Absyn_Util.mk_typ_app _68_19414 _68_19413)))
in (Support.Prims.pipe_left setpos _68_19415))))))
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _41_1980 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_41_1980) with
| (env, x) -> begin
(let pats = (Support.List.map (fun ( e ) -> (let _68_19417 = (desugar_typ_or_exp env e)
in (Support.Prims.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _68_19417))) pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _41_1986 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
end)
in (let body = (let _68_19423 = (let _68_19422 = (let _68_19421 = (let _68_19420 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_68_19420)::[])
in (_68_19421, body))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_19422))
in (Support.Prims.pipe_left pos _68_19423))
in (let _68_19428 = (let _68_19427 = (let _68_19424 = (Microsoft_FStar_Absyn_Util.set_lid_range q b.Microsoft_FStar_Parser_AST.brange)
in (Microsoft_FStar_Absyn_Util.ftv _68_19424 Microsoft_FStar_Absyn_Syntax.kun))
in (let _68_19426 = (let _68_19425 = (Microsoft_FStar_Absyn_Syntax.targ body)
in (_68_19425)::[])
in (Microsoft_FStar_Absyn_Util.mk_typ_app _68_19427 _68_19426)))
in (Support.Prims.pipe_left setpos _68_19428))))))
end))
end
| _41_1990 -> begin
(failwith ("impossible"))
end)))
in (let push_quant = (fun ( q ) ( binders ) ( pats ) ( body ) -> (match (binders) with
| b::b'::_rest -> begin
(let rest = (b')::_rest
in (let body = (let _68_19443 = (q (rest, pats, body))
in (let _68_19442 = (Support.Microsoft.FStar.Range.union_ranges b'.Microsoft_FStar_Parser_AST.brange body.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_AST.mk_term _68_19443 _68_19442 Microsoft_FStar_Parser_AST.Formula)))
in (let _68_19444 = (q ((b)::[], [], body))
in (Microsoft_FStar_Parser_AST.mk_term _68_19444 f.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Formula))))
end
| _41_2004 -> begin
(failwith ("impossible"))
end))
in (match ((let _68_19445 = (unparen f)
in _68_19445.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Labeled ((f, l, p)) -> begin
(let f = (desugar_formula env f)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((f, l, Microsoft_FStar_Absyn_Syntax.dummyRange, p)))))
end
| Microsoft_FStar_Parser_AST.Op (("==", hd::_args)) -> begin
(let args = (hd)::_args
in (let args = (Support.List.map (fun ( t ) -> (let _68_19447 = (desugar_typ_or_exp env t)
in (Support.Prims.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _68_19447))) args)
in (let eq = (match ((is_type env hd)) with
| true -> begin
(let _68_19448 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.eqT_lid f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _68_19448 Microsoft_FStar_Absyn_Syntax.kun))
end
| false -> begin
(let _68_19449 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.eq2_lid f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _68_19449 Microsoft_FStar_Absyn_Syntax.kun))
end)
in (Microsoft_FStar_Absyn_Util.mk_typ_app eq args))))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match (((connective s), args)) with
| (Some (conn), _41_2030::_41_2028::[]) -> begin
(let _68_19454 = (let _68_19450 = (Microsoft_FStar_Absyn_Util.set_lid_range conn f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _68_19450 Microsoft_FStar_Absyn_Syntax.kun))
in (let _68_19453 = (Support.List.map (fun ( x ) -> (let _68_19452 = (desugar_formula env x)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _68_19452))) args)
in (Microsoft_FStar_Absyn_Util.mk_typ_app _68_19454 _68_19453)))
end
| _41_2035 -> begin
(match ((is_type env f)) with
| true -> begin
(desugar_typ env f)
end
| false -> begin
(let _68_19455 = (desugar_exp env f)
in (Support.Prims.pipe_right _68_19455 Microsoft_FStar_Absyn_Util.b2t))
end)
end)
end
| Microsoft_FStar_Parser_AST.If ((f1, f2, f3)) -> begin
(let _68_19460 = (let _68_19456 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.ite_lid f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _68_19456 Microsoft_FStar_Absyn_Syntax.kun))
in (let _68_19459 = (Support.List.map (fun ( x ) -> (match ((desugar_typ_or_exp env x)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| Support.Microsoft.FStar.Util.Inr (v) -> begin
(let _68_19458 = (Microsoft_FStar_Absyn_Util.b2t v)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _68_19458))
end)) ((f1)::(f2)::(f3)::[]))
in (Microsoft_FStar_Absyn_Util.mk_typ_app _68_19460 _68_19459)))
end
| Microsoft_FStar_Parser_AST.QForall ((_1::_2::_3, pats, body)) -> begin
(let binders = (_1)::(_2)::_3
in (let _68_19462 = (push_quant (fun ( x ) -> Microsoft_FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _68_19462)))
end
| Microsoft_FStar_Parser_AST.QExists ((_1::_2::_3, pats, body)) -> begin
(let binders = (_1)::(_2)::_3
in (let _68_19464 = (push_quant (fun ( x ) -> Microsoft_FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _68_19464)))
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
| _41_2083 -> begin
(match ((is_type env f)) with
| true -> begin
(desugar_typ env f)
end
| false -> begin
(let _68_19465 = (desugar_exp env f)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Util.b2t _68_19465))
end)
end)))))))
and desugar_formula = (fun ( env ) ( t ) -> (desugar_formula' (let _41_2086 = env
in {Microsoft_FStar_Parser_DesugarEnv.curmodule = _41_2086.Microsoft_FStar_Parser_DesugarEnv.curmodule; Microsoft_FStar_Parser_DesugarEnv.modules = _41_2086.Microsoft_FStar_Parser_DesugarEnv.modules; Microsoft_FStar_Parser_DesugarEnv.open_namespaces = _41_2086.Microsoft_FStar_Parser_DesugarEnv.open_namespaces; Microsoft_FStar_Parser_DesugarEnv.sigaccum = _41_2086.Microsoft_FStar_Parser_DesugarEnv.sigaccum; Microsoft_FStar_Parser_DesugarEnv.localbindings = _41_2086.Microsoft_FStar_Parser_DesugarEnv.localbindings; Microsoft_FStar_Parser_DesugarEnv.recbindings = _41_2086.Microsoft_FStar_Parser_DesugarEnv.recbindings; Microsoft_FStar_Parser_DesugarEnv.phase = Microsoft_FStar_Parser_AST.Formula; Microsoft_FStar_Parser_DesugarEnv.sigmap = _41_2086.Microsoft_FStar_Parser_DesugarEnv.sigmap; Microsoft_FStar_Parser_DesugarEnv.default_result_effect = _41_2086.Microsoft_FStar_Parser_DesugarEnv.default_result_effect; Microsoft_FStar_Parser_DesugarEnv.iface = _41_2086.Microsoft_FStar_Parser_DesugarEnv.iface; Microsoft_FStar_Parser_DesugarEnv.admitted_iface = _41_2086.Microsoft_FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder = (fun ( env ) ( b ) -> (match ((is_type_binder env b)) with
| true -> begin
(let _68_19470 = (desugar_type_binder env b)
in Support.Microsoft.FStar.Util.Inl (_68_19470))
end
| false -> begin
(let _68_19471 = (desugar_exp_binder env b)
in Support.Microsoft.FStar.Util.Inr (_68_19471))
end))
and typars_of_binders = (fun ( env ) ( bs ) -> (let _41_2119 = (Support.List.fold_left (fun ( _41_2094 ) ( b ) -> (match (_41_2094) with
| (env, out) -> begin
(let tk = (desugar_binder env (let _41_2096 = b
in {Microsoft_FStar_Parser_AST.b = _41_2096.Microsoft_FStar_Parser_AST.b; Microsoft_FStar_Parser_AST.brange = _41_2096.Microsoft_FStar_Parser_AST.brange; Microsoft_FStar_Parser_AST.blevel = Microsoft_FStar_Parser_AST.Formula; Microsoft_FStar_Parser_AST.aqual = _41_2096.Microsoft_FStar_Parser_AST.aqual}))
in (match (tk) with
| Support.Microsoft.FStar.Util.Inl ((Some (a), k)) -> begin
(let _41_2106 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_41_2106) with
| (env, a) -> begin
(env, ((Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)), b.Microsoft_FStar_Parser_AST.aqual))::out)
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _41_2114 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_41_2114) with
| (env, x) -> begin
(env, ((Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)), b.Microsoft_FStar_Parser_AST.aqual))::out)
end))
end
| _41_2116 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected binder", b.Microsoft_FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_41_2119) with
| (env, tpars) -> begin
(env, (Support.List.rev tpars))
end)))
and desugar_exp_binder = (fun ( env ) ( b ) -> (match (b.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Annotated ((x, t)) -> begin
(let _68_19478 = (desugar_typ env t)
in (Some (x), _68_19478))
end
| Microsoft_FStar_Parser_AST.TVariable (t) -> begin
(let _68_19479 = (Microsoft_FStar_Parser_DesugarEnv.fail_or2 (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in (None, _68_19479))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(let _68_19480 = (desugar_typ env t)
in (None, _68_19480))
end
| Microsoft_FStar_Parser_AST.Variable (x) -> begin
(Some (x), Microsoft_FStar_Absyn_Syntax.tun)
end
| _41_2133 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a type)", b.Microsoft_FStar_Parser_AST.brange))))
end))
and desugar_type_binder = (fun ( env ) ( b ) -> (let fail = (fun ( _41_2137 ) -> (match (()) with
| () -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a kind)", b.Microsoft_FStar_Parser_AST.brange))))
end))
in (match (b.Microsoft_FStar_Parser_AST.b) with
| (Microsoft_FStar_Parser_AST.Annotated ((x, t))) | (Microsoft_FStar_Parser_AST.TAnnotated ((x, t))) -> begin
(let _68_19485 = (desugar_kind env t)
in (Some (x), _68_19485))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(let _68_19486 = (desugar_kind env t)
in (None, _68_19486))
end
| Microsoft_FStar_Parser_AST.TVariable (x) -> begin
(Some (x), (let _41_2148 = Microsoft_FStar_Absyn_Syntax.mk_Kind_type
in {Microsoft_FStar_Absyn_Syntax.n = _41_2148.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _41_2148.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = b.Microsoft_FStar_Parser_AST.brange; Microsoft_FStar_Absyn_Syntax.fvs = _41_2148.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _41_2148.Microsoft_FStar_Absyn_Syntax.uvs}))
end
| _41_2151 -> begin
(fail ())
end)))

let gather_tc_binders = (fun ( tps ) ( k ) -> (let rec aux = (fun ( bs ) ( k ) -> (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((binders, k)) -> begin
(aux (Support.List.append bs binders) k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_41_2162, k)) -> begin
(aux bs k)
end
| _41_2167 -> begin
bs
end))
in (let _68_19495 = (aux tps k)
in (Support.Prims.pipe_right _68_19495 Microsoft_FStar_Absyn_Util.name_binders))))

let mk_data_discriminators = (fun ( quals ) ( env ) ( t ) ( tps ) ( k ) ( datas ) -> (let quals = (fun ( q ) -> (match (((Support.Prims.pipe_left Support.Prims.op_Negation env.Microsoft_FStar_Parser_DesugarEnv.iface) || env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface)) with
| true -> begin
(Support.List.append ((Microsoft_FStar_Absyn_Syntax.Assumption)::q) quals)
end
| false -> begin
(Support.List.append q quals)
end))
in (let binders = (gather_tc_binders tps k)
in (let p = (Microsoft_FStar_Absyn_Syntax.range_of_lid t)
in (let imp_binders = (Support.Prims.pipe_right binders (Support.List.map (fun ( _41_2181 ) -> (match (_41_2181) with
| (x, _41_2180) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end))))
in (let binders = (let _68_19516 = (let _68_19515 = (let _68_19514 = (let _68_19513 = (let _68_19512 = (Microsoft_FStar_Absyn_Util.ftv t Microsoft_FStar_Absyn_Syntax.kun)
in (let _68_19511 = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (_68_19512, _68_19511)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' _68_19513 None p))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.null_v_binder _68_19514))
in (_68_19515)::[])
in (Support.List.append imp_binders _68_19516))
in (let disc_type = (let _68_19519 = (let _68_19518 = (let _68_19517 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.bool_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.total_comp _68_19517 p))
in (binders, _68_19518))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _68_19519 None p))
in (Support.Prims.pipe_right datas (Support.List.map (fun ( d ) -> (let disc_name = (Microsoft_FStar_Absyn_Util.mk_discriminator d)
in (let _68_19523 = (let _68_19522 = (quals ((Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Discriminator (d))::[]))
in (let _68_19521 = (Microsoft_FStar_Absyn_Syntax.range_of_lid disc_name)
in (disc_name, disc_type, _68_19522, _68_19521)))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_68_19523)))))))))))))

let mk_indexed_projectors = (fun ( refine_domain ) ( env ) ( _41_2192 ) ( lid ) ( formals ) ( t ) -> (match (_41_2192) with
| (tc, tps, k) -> begin
(let binders = (gather_tc_binders tps k)
in (let p = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (let arg_binder = (let arg_typ = (let _68_19532 = (let _68_19531 = (Microsoft_FStar_Absyn_Util.ftv tc Microsoft_FStar_Absyn_Syntax.kun)
in (let _68_19530 = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (_68_19531, _68_19530)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' _68_19532 None p))
in (let projectee = (let _68_19534 = (Microsoft_FStar_Absyn_Syntax.mk_ident ("projectee", p))
in (let _68_19533 = (Microsoft_FStar_Absyn_Util.genident (Some (p)))
in {Microsoft_FStar_Absyn_Syntax.ppname = _68_19534; Microsoft_FStar_Absyn_Syntax.realname = _68_19533}))
in (match ((not (refine_domain))) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end
| false -> begin
(let disc_name = (Microsoft_FStar_Absyn_Util.mk_discriminator lid)
in (let x = (Microsoft_FStar_Absyn_Util.gen_bvar arg_typ)
in (let _68_19544 = (let _68_19543 = (let _68_19542 = (let _68_19541 = (let _68_19540 = (let _68_19539 = (let _68_19538 = (Microsoft_FStar_Absyn_Util.fvar None disc_name p)
in (let _68_19537 = (let _68_19536 = (let _68_19535 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg _68_19535))
in (_68_19536)::[])
in (_68_19538, _68_19537)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _68_19539 None p))
in (Microsoft_FStar_Absyn_Util.b2t _68_19540))
in (x, _68_19541))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _68_19542 None p))
in (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s projectee) _68_19543))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.v_binder _68_19544))))
end)))
in (let imp_binders = (Support.Prims.pipe_right binders (Support.List.map (fun ( _41_2206 ) -> (match (_41_2206) with
| (x, _41_2205) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end))))
in (let binders = (Support.List.append imp_binders ((arg_binder)::[]))
in (let arg = (Microsoft_FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (let subst = (let _68_19554 = (Support.Prims.pipe_right formals (Support.List.mapi (fun ( i ) ( f ) -> (match ((Support.Prims.fst f)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(match ((Support.Prims.pipe_right binders (Support.Microsoft.FStar.Util.for_some (fun ( _41_13 ) -> (match (_41_13) with
| (Support.Microsoft.FStar.Util.Inl (b), _41_2218) -> begin
(Microsoft_FStar_Absyn_Util.bvd_eq a.Microsoft_FStar_Absyn_Syntax.v b.Microsoft_FStar_Absyn_Syntax.v)
end
| _41_2221 -> begin
false
end))))) with
| true -> begin
[]
end
| false -> begin
(let _41_2225 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_41_2225) with
| (field_name, _41_2224) -> begin
(let proj = (let _68_19550 = (let _68_19549 = (Microsoft_FStar_Absyn_Util.ftv field_name Microsoft_FStar_Absyn_Syntax.kun)
in (_68_19549, (arg)::[]))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_19550 None p))
in (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, proj)))::[])
end))
end)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(match ((Support.Prims.pipe_right binders (Support.Microsoft.FStar.Util.for_some (fun ( _41_14 ) -> (match (_41_14) with
| (Support.Microsoft.FStar.Util.Inr (y), _41_2233) -> begin
(Microsoft_FStar_Absyn_Util.bvd_eq x.Microsoft_FStar_Absyn_Syntax.v y.Microsoft_FStar_Absyn_Syntax.v)
end
| _41_2236 -> begin
false
end))))) with
| true -> begin
[]
end
| false -> begin
(let _41_2240 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_41_2240) with
| (field_name, _41_2239) -> begin
(let proj = (let _68_19553 = (let _68_19552 = (Microsoft_FStar_Absyn_Util.fvar None field_name p)
in (_68_19552, (arg)::[]))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _68_19553 None p))
in (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, proj)))::[])
end))
end)
end))))
in (Support.Prims.pipe_right _68_19554 Support.List.flatten))
in (Support.Prims.pipe_right formals (Support.List.mapi (fun ( i ) ( ax ) -> (match ((Support.Prims.fst ax)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _41_2250 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_41_2250) with
| (field_name, _41_2249) -> begin
(let kk = (let _68_19558 = (let _68_19557 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (binders, _68_19557))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_19558 p))
in (let _68_19560 = (let _68_19559 = (Microsoft_FStar_Absyn_Syntax.range_of_lid field_name)
in (field_name, [], kk, [], [], (Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Projector ((lid, Support.Microsoft.FStar.Util.Inl (a.Microsoft_FStar_Absyn_Syntax.v))))::[], _68_19559))
in Microsoft_FStar_Absyn_Syntax.Sig_tycon (_68_19560)))
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _41_2257 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_41_2257) with
| (field_name, _41_2256) -> begin
(let t = (let _68_19563 = (let _68_19562 = (let _68_19561 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Absyn_Util.total_comp _68_19561 p))
in (binders, _68_19562))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _68_19563 None p))
in (let quals = (fun ( q ) -> (match (((not (env.Microsoft_FStar_Parser_DesugarEnv.iface)) || env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.Assumption)::q
end
| false -> begin
q
end))
in (let _68_19567 = (let _68_19566 = (Microsoft_FStar_Absyn_Syntax.range_of_lid field_name)
in (field_name, t, (quals ((Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Projector ((lid, Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.v))))::[])), _68_19566))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_68_19567))))
end))
end)))))))))))
end))

let mk_data_projectors = (fun ( env ) ( _41_16 ) -> (match (_41_16) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, _41_2268, _41_2270)) when (not ((Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.lexcons_lid))) -> begin
(let refine_domain = (match ((Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _41_15 ) -> (match (_41_15) with
| Microsoft_FStar_Absyn_Syntax.RecordConstructor (_41_2275) -> begin
true
end
| _41_2278 -> begin
false
end))))) with
| true -> begin
false
end
| false -> begin
(let _41_2284 = tycon
in (match (_41_2284) with
| (l, _41_2281, _41_2283) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.find_all_datacons env l)) with
| Some (l) -> begin
((Support.List.length l) > 1)
end
| _41_2288 -> begin
true
end)
end))
end)
in (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((formals, cod)) -> begin
(let cod = (Microsoft_FStar_Absyn_Util.comp_result cod)
in (mk_indexed_projectors refine_domain env tycon lid formals cod))
end
| _41_2296 -> begin
[]
end))
end
| _41_2298 -> begin
[]
end))

let rec desugar_tycon = (fun ( env ) ( rng ) ( quals ) ( tcs ) -> (let tycon_id = (fun ( _41_17 ) -> (match (_41_17) with
| (Microsoft_FStar_Parser_AST.TyconAbstract ((id, _, _))) | (Microsoft_FStar_Parser_AST.TyconAbbrev ((id, _, _, _))) | (Microsoft_FStar_Parser_AST.TyconRecord ((id, _, _, _))) | (Microsoft_FStar_Parser_AST.TyconVariant ((id, _, _, _))) -> begin
id
end))
in (let binder_to_term = (fun ( b ) -> (match (b.Microsoft_FStar_Parser_AST.b) with
| (Microsoft_FStar_Parser_AST.Annotated ((x, _))) | (Microsoft_FStar_Parser_AST.Variable (x)) -> begin
(let _68_19586 = (let _68_19585 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((x)::[]))
in Microsoft_FStar_Parser_AST.Var (_68_19585))
in (Microsoft_FStar_Parser_AST.mk_term _68_19586 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr))
end
| (Microsoft_FStar_Parser_AST.TAnnotated ((a, _))) | (Microsoft_FStar_Parser_AST.TVariable (a)) -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Tvar (a)) a.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type)
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
t
end))
in (let tot = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.effect_Tot_lid)) rng Microsoft_FStar_Parser_AST.Expr)
in (let with_constructor_effect = (fun ( t ) -> (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.App ((tot, t, Microsoft_FStar_Parser_AST.Nothing))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level))
in (let apply_binders = (fun ( t ) ( binders ) -> (Support.List.fold_left (fun ( out ) ( b ) -> (let _68_19597 = (let _68_19596 = (let _68_19595 = (binder_to_term b)
in (out, _68_19595, Microsoft_FStar_Parser_AST.Nothing))
in Microsoft_FStar_Parser_AST.App (_68_19596))
in (Microsoft_FStar_Parser_AST.mk_term _68_19597 out.Microsoft_FStar_Parser_AST.range out.Microsoft_FStar_Parser_AST.level))) t binders))
in (let tycon_record_as_variant = (fun ( _41_18 ) -> (match (_41_18) with
| Microsoft_FStar_Parser_AST.TyconRecord ((id, parms, kopt, fields)) -> begin
(let constrName = (Microsoft_FStar_Absyn_Syntax.mk_ident ((Support.String.strcat "Mk" id.Microsoft_FStar_Absyn_Syntax.idText), id.Microsoft_FStar_Absyn_Syntax.idRange))
in (let mfields = (Support.List.map (fun ( _41_2370 ) -> (match (_41_2370) with
| (x, t) -> begin
(let _68_19603 = (let _68_19602 = (let _68_19601 = (Microsoft_FStar_Absyn_Util.mangle_field_name x)
in (_68_19601, t))
in Microsoft_FStar_Parser_AST.Annotated (_68_19602))
in (Microsoft_FStar_Parser_AST.mk_binder _68_19603 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr None))
end)) fields)
in (let result = (let _68_19606 = (let _68_19605 = (let _68_19604 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id)::[]))
in Microsoft_FStar_Parser_AST.Var (_68_19604))
in (Microsoft_FStar_Parser_AST.mk_term _68_19605 id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type))
in (apply_binders _68_19606 parms))
in (let constrTyp = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type)
in (let _68_19608 = (Support.Prims.pipe_right fields (Support.List.map (fun ( _41_2377 ) -> (match (_41_2377) with
| (x, _41_2376) -> begin
(Microsoft_FStar_Parser_DesugarEnv.qualify env x)
end))))
in (Microsoft_FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _68_19608))))))
end
| _41_2379 -> begin
(failwith ("impossible"))
end))
in (let desugar_abstract_tc = (fun ( quals ) ( _env ) ( mutuals ) ( _41_19 ) -> (match (_41_19) with
| Microsoft_FStar_Parser_AST.TyconAbstract ((id, binders, kopt)) -> begin
(let _41_2393 = (typars_of_binders _env binders)
in (match (_41_2393) with
| (_env', typars) -> begin
(let k = (match (kopt) with
| None -> begin
Microsoft_FStar_Absyn_Syntax.kun
end
| Some (k) -> begin
(desugar_kind _env' k)
end)
in (let tconstr = (let _68_19619 = (let _68_19618 = (let _68_19617 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id)::[]))
in Microsoft_FStar_Parser_AST.Var (_68_19617))
in (Microsoft_FStar_Parser_AST.mk_term _68_19618 id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type))
in (apply_binders _68_19619 binders))
in (let qlid = (Microsoft_FStar_Parser_DesugarEnv.qualify _env id)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_tycon ((qlid, typars, k, mutuals, [], quals, rng))
in (let _env = (Microsoft_FStar_Parser_DesugarEnv.push_rec_binding _env (Microsoft_FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (let _env2 = (Microsoft_FStar_Parser_DesugarEnv.push_rec_binding _env' (Microsoft_FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (_env, (_env2, typars), se, tconstr)))))))
end))
end
| _41_2404 -> begin
(failwith ("Unexpected tycon"))
end))
in (let push_tparam = (fun ( env ) ( _41_20 ) -> (match (_41_20) with
| (Support.Microsoft.FStar.Util.Inr (x), _41_2411) -> begin
(Microsoft_FStar_Parser_DesugarEnv.push_bvvdef env x.Microsoft_FStar_Absyn_Syntax.v)
end
| (Support.Microsoft.FStar.Util.Inl (a), _41_2416) -> begin
(Microsoft_FStar_Parser_DesugarEnv.push_btvdef env a.Microsoft_FStar_Absyn_Syntax.v)
end))
in (let push_tparams = (Support.List.fold_left push_tparam)
in (match (tcs) with
| Microsoft_FStar_Parser_AST.TyconAbstract (_41_2420)::[] -> begin
(let tc = (Support.List.hd tcs)
in (let _41_2431 = (desugar_abstract_tc quals env [] tc)
in (match (_41_2431) with
| (_41_2425, _41_2427, se, _41_2430) -> begin
(let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))
end)))
end
| Microsoft_FStar_Parser_AST.TyconAbbrev ((id, binders, kopt, t))::[] -> begin
(let _41_2442 = (typars_of_binders env binders)
in (match (_41_2442) with
| (env', typars) -> begin
(let k = (match (kopt) with
| None -> begin
(match ((Support.Microsoft.FStar.Util.for_some (fun ( _41_21 ) -> (match (_41_21) with
| Microsoft_FStar_Absyn_Syntax.Effect -> begin
true
end
| _41_2447 -> begin
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
in (let quals = (match ((Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _41_22 ) -> (match (_41_22) with
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
true
end
| _41_2455 -> begin
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
in (let se = (match ((Support.Prims.pipe_right quals (Support.List.contains Microsoft_FStar_Absyn_Syntax.Effect))) with
| true -> begin
(let c = (desugar_comp t.Microsoft_FStar_Parser_AST.range false env' t)
in (let _68_19631 = (let _68_19630 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (let _68_19629 = (Support.Prims.pipe_right quals (Support.List.filter (fun ( _41_23 ) -> (match (_41_23) with
| Microsoft_FStar_Absyn_Syntax.Effect -> begin
false
end
| _41_2461 -> begin
true
end))))
in (_68_19630, typars, c, _68_19629, rng)))
in Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_68_19631)))
end
| false -> begin
(let t = (desugar_typ env' t)
in (let _68_19633 = (let _68_19632 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (_68_19632, typars, k, t, quals, rng))
in Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_68_19633)))
end)
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| Microsoft_FStar_Parser_AST.TyconRecord (_41_2466)::[] -> begin
(let trec = (Support.List.hd tcs)
in (let _41_2472 = (tycon_record_as_variant trec)
in (match (_41_2472) with
| (t, fs) -> begin
(desugar_tycon env rng ((Microsoft_FStar_Absyn_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _41_2476::_41_2474 -> begin
(let env0 = env
in (let mutuals = (Support.List.map (fun ( x ) -> (Support.Prims.pipe_left (Microsoft_FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (let rec collect_tcs = (fun ( quals ) ( et ) ( tc ) -> (let _41_2487 = et
in (match (_41_2487) with
| (env, tcs) -> begin
(match (tc) with
| Microsoft_FStar_Parser_AST.TyconRecord (_41_2489) -> begin
(let trec = tc
in (let _41_2494 = (tycon_record_as_variant trec)
in (match (_41_2494) with
| (t, fs) -> begin
(collect_tcs ((Microsoft_FStar_Absyn_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| Microsoft_FStar_Parser_AST.TyconVariant ((id, binders, kopt, constructors)) -> begin
(let _41_2508 = (desugar_abstract_tc quals env mutuals (Microsoft_FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_41_2508) with
| (env, (_41_2503, tps), se, tconstr) -> begin
(env, (Support.Microsoft.FStar.Util.Inl ((se, tps, constructors, tconstr, quals)))::tcs)
end))
end
| Microsoft_FStar_Parser_AST.TyconAbbrev ((id, binders, kopt, t)) -> begin
(let _41_2522 = (desugar_abstract_tc quals env mutuals (Microsoft_FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_41_2522) with
| (env, (_41_2517, tps), se, tconstr) -> begin
(env, (Support.Microsoft.FStar.Util.Inr ((se, tps, t, quals)))::tcs)
end))
end
| _41_2524 -> begin
(failwith ("Unrecognized mutual type definition"))
end)
end)))
in (let _41_2527 = (Support.List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_41_2527) with
| (env, tcs) -> begin
(let tcs = (Support.List.rev tcs)
in (let sigelts = (Support.Prims.pipe_right tcs (Support.List.collect (fun ( _41_25 ) -> (match (_41_25) with
| Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Syntax.Sig_tycon ((id, tpars, k, _41_2534, _41_2536, _41_2538, _41_2540)), tps, t, quals)) -> begin
(let env_tps = (push_tparams env tps)
in (let t = (desugar_typ env_tps t)
in (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((id, tpars, k, t, [], rng)))::[]))
end
| Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, _41_2555, tags, _41_2558)), tps, constrs, tconstr, quals)) -> begin
(let tycon = (tname, tpars, k)
in (let env_tps = (push_tparams env tps)
in (let _41_2594 = (let _68_19652 = (Support.Prims.pipe_right constrs (Support.List.map (fun ( _41_2572 ) -> (match (_41_2572) with
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
(failwith ("Impossible"))
end
| Some (t) -> begin
t
end)
end)
in (let t = (let _68_19644 = (Microsoft_FStar_Parser_DesugarEnv.default_total env_tps)
in (let _68_19643 = (close env_tps t)
in (desugar_typ _68_19644 _68_19643)))
in (let name = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (let quals = (Support.Prims.pipe_right tags (Support.List.collect (fun ( _41_24 ) -> (match (_41_24) with
| Microsoft_FStar_Absyn_Syntax.RecordType (fns) -> begin
(Microsoft_FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _41_2586 -> begin
[]
end))))
in (let _68_19651 = (let _68_19650 = (let _68_19649 = (let _68_19648 = (let _68_19647 = (Support.List.map (fun ( _41_2591 ) -> (match (_41_2591) with
| (x, _41_2590) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end)) tps)
in (Microsoft_FStar_Absyn_Util.close_typ _68_19647 t))
in (Support.Prims.pipe_right _68_19648 Microsoft_FStar_Absyn_Util.name_function_binders))
in (name, _68_19649, tycon, quals, mutuals, rng))
in Microsoft_FStar_Absyn_Syntax.Sig_datacon (_68_19650))
in (name, _68_19651))))))
end))))
in (Support.Prims.pipe_left Support.List.split _68_19652))
in (match (_41_2594) with
| (constrNames, constrs) -> begin
(Microsoft_FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, constrNames, tags, rng)))::constrs
end))))
end
| _41_2596 -> begin
(failwith ("impossible"))
end))))
in (let bundle = (let _68_19654 = (let _68_19653 = (Support.List.collect Microsoft_FStar_Absyn_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _68_19653, rng))
in Microsoft_FStar_Absyn_Syntax.Sig_bundle (_68_19654))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (let data_ops = (Support.Prims.pipe_right sigelts (Support.List.collect (mk_data_projectors env)))
in (let discs = (Support.Prims.pipe_right sigelts (Support.List.collect (fun ( _41_26 ) -> (match (_41_26) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((tname, tps, k, _41_2606, constrs, quals, _41_2610)) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _41_2614 -> begin
[]
end))))
in (let ops = (Support.List.append discs data_ops)
in (let env = (Support.List.fold_left Microsoft_FStar_Parser_DesugarEnv.push_sigelt env ops)
in (env, (Support.List.append ((bundle)::[]) ops))))))))))
end)))))
end
| [] -> begin
(failwith ("impossible"))
end)))))))))))

let desugar_binders = (fun ( env ) ( binders ) -> (let _41_2645 = (Support.List.fold_left (fun ( _41_2623 ) ( b ) -> (match (_41_2623) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| Support.Microsoft.FStar.Util.Inl ((Some (a), k)) -> begin
(let _41_2632 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_41_2632) with
| (env, a) -> begin
(let _68_19663 = (let _68_19662 = (Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_68_19662)::binders)
in (env, _68_19663))
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _41_2640 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_41_2640) with
| (env, x) -> begin
(let _68_19665 = (let _68_19664 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_68_19664)::binders)
in (env, _68_19665))
end))
end
| _41_2642 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Missing name in binder", b.Microsoft_FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_41_2645) with
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
(match ((let _68_19671 = (let _68_19670 = (desugar_exp_maybe_top true env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Let ((isrec, lets, (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Const (Microsoft_FStar_Absyn_Syntax.Const_unit)) d.Microsoft_FStar_Parser_AST.drange Microsoft_FStar_Parser_AST.Expr)))) d.Microsoft_FStar_Parser_AST.drange Microsoft_FStar_Parser_AST.Expr))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Util.compress_exp _68_19670))
in _68_19671.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, _41_2664)) -> begin
(let lids = (Support.Prims.pipe_right (Support.Prims.snd lbs) (Support.List.map (fun ( lb ) -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inr (l) -> begin
l
end
| _41_2671 -> begin
(failwith ("impossible"))
end))))
in (let quals = (Support.Prims.pipe_right (Support.Prims.snd lbs) (Support.List.collect (fun ( _41_27 ) -> (match (_41_27) with
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (_41_2681); Microsoft_FStar_Absyn_Syntax.lbtyp = _41_2679; Microsoft_FStar_Absyn_Syntax.lbeff = _41_2677; Microsoft_FStar_Absyn_Syntax.lbdef = _41_2675} -> begin
[]
end
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = _41_2689; Microsoft_FStar_Absyn_Syntax.lbeff = _41_2687; Microsoft_FStar_Absyn_Syntax.lbdef = _41_2685} -> begin
(Microsoft_FStar_Parser_DesugarEnv.lookup_letbinding_quals env l)
end))))
in (let s = Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, d.Microsoft_FStar_Parser_AST.drange, lids, quals))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env s)
in (env, (s)::[])))))
end
| _41_2697 -> begin
(failwith ("Desugaring a let did not produce a let"))
end)
end
| Microsoft_FStar_Parser_AST.Main (t) -> begin
(let e = (desugar_exp env t)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_main ((e, d.Microsoft_FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| Microsoft_FStar_Parser_AST.Assume ((atag, id, t)) -> begin
(let f = (desugar_formula env t)
in (let _68_19677 = (let _68_19676 = (let _68_19675 = (let _68_19674 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (_68_19674, f, (Microsoft_FStar_Absyn_Syntax.Assumption)::[], d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Sig_assume (_68_19675))
in (_68_19676)::[])
in (env, _68_19677)))
end
| Microsoft_FStar_Parser_AST.Val ((quals, id, t)) -> begin
(let t = (let _68_19678 = (close_fun env t)
in (desugar_typ env _68_19678))
in (let quals = (match ((env.Microsoft_FStar_Parser_DesugarEnv.iface && env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.Assumption)::quals
end
| false -> begin
quals
end)
in (let se = (let _68_19680 = (let _68_19679 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (_68_19679, t, quals, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_68_19680))
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
in (let t = (let _68_19685 = (let _68_19684 = (let _68_19681 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_68_19681)::[])
in (let _68_19683 = (let _68_19682 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) Microsoft_FStar_Absyn_Const.exn_lid)
in (Microsoft_FStar_Absyn_Syntax.mk_Total _68_19682))
in (_68_19684, _68_19683)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _68_19685 None d.Microsoft_FStar_Parser_AST.drange))
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
(let _41_2750 = (desugar_binders env binders)
in (match (_41_2750) with
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
in (let _41_2766 = (desugar_binders env eff_binders)
in (match (_41_2766) with
| (env, binders) -> begin
(let defn = (desugar_typ env defn)
in (let _41_2770 = (Microsoft_FStar_Absyn_Util.head_and_args defn)
in (match (_41_2770) with
| (head, args) -> begin
(match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (eff) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_effect_defn env eff.Microsoft_FStar_Absyn_Syntax.v)) with
| None -> begin
(let _68_19690 = (let _68_19689 = (let _68_19688 = (let _68_19687 = (let _68_19686 = (Microsoft_FStar_Absyn_Print.sli eff.Microsoft_FStar_Absyn_Syntax.v)
in (Support.String.strcat "Effect " _68_19686))
in (Support.String.strcat _68_19687 " not found"))
in (_68_19688, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Error (_68_19689))
in (raise (_68_19690)))
end
| Some (ed) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.subst_of_list ed.Microsoft_FStar_Absyn_Syntax.binders args)
in (let sub = (Microsoft_FStar_Absyn_Util.subst_typ subst)
in (let ed = (let _68_19707 = (Microsoft_FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _68_19706 = (Microsoft_FStar_Absyn_Util.subst_kind subst ed.Microsoft_FStar_Absyn_Syntax.signature)
in (let _68_19705 = (sub ed.Microsoft_FStar_Absyn_Syntax.ret)
in (let _68_19704 = (sub ed.Microsoft_FStar_Absyn_Syntax.bind_wp)
in (let _68_19703 = (sub ed.Microsoft_FStar_Absyn_Syntax.bind_wlp)
in (let _68_19702 = (sub ed.Microsoft_FStar_Absyn_Syntax.if_then_else)
in (let _68_19701 = (sub ed.Microsoft_FStar_Absyn_Syntax.ite_wp)
in (let _68_19700 = (sub ed.Microsoft_FStar_Absyn_Syntax.ite_wlp)
in (let _68_19699 = (sub ed.Microsoft_FStar_Absyn_Syntax.wp_binop)
in (let _68_19698 = (sub ed.Microsoft_FStar_Absyn_Syntax.wp_as_type)
in (let _68_19697 = (sub ed.Microsoft_FStar_Absyn_Syntax.close_wp)
in (let _68_19696 = (sub ed.Microsoft_FStar_Absyn_Syntax.close_wp_t)
in (let _68_19695 = (sub ed.Microsoft_FStar_Absyn_Syntax.assert_p)
in (let _68_19694 = (sub ed.Microsoft_FStar_Absyn_Syntax.assume_p)
in (let _68_19693 = (sub ed.Microsoft_FStar_Absyn_Syntax.null_wp)
in (let _68_19692 = (sub ed.Microsoft_FStar_Absyn_Syntax.trivial)
in {Microsoft_FStar_Absyn_Syntax.mname = _68_19707; Microsoft_FStar_Absyn_Syntax.binders = binders; Microsoft_FStar_Absyn_Syntax.qualifiers = quals; Microsoft_FStar_Absyn_Syntax.signature = _68_19706; Microsoft_FStar_Absyn_Syntax.ret = _68_19705; Microsoft_FStar_Absyn_Syntax.bind_wp = _68_19704; Microsoft_FStar_Absyn_Syntax.bind_wlp = _68_19703; Microsoft_FStar_Absyn_Syntax.if_then_else = _68_19702; Microsoft_FStar_Absyn_Syntax.ite_wp = _68_19701; Microsoft_FStar_Absyn_Syntax.ite_wlp = _68_19700; Microsoft_FStar_Absyn_Syntax.wp_binop = _68_19699; Microsoft_FStar_Absyn_Syntax.wp_as_type = _68_19698; Microsoft_FStar_Absyn_Syntax.close_wp = _68_19697; Microsoft_FStar_Absyn_Syntax.close_wp_t = _68_19696; Microsoft_FStar_Absyn_Syntax.assert_p = _68_19695; Microsoft_FStar_Absyn_Syntax.assume_p = _68_19694; Microsoft_FStar_Absyn_Syntax.null_wp = _68_19693; Microsoft_FStar_Absyn_Syntax.trivial = _68_19692}))))))))))))))))
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ed, d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)
end
| _41_2782 -> begin
(let _68_19711 = (let _68_19710 = (let _68_19709 = (let _68_19708 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (Support.String.strcat _68_19708 " is not an effect"))
in (_68_19709, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Error (_68_19710))
in (raise (_68_19711)))
end)
end)))
end)))
end
| Microsoft_FStar_Parser_AST.NewEffect ((quals, Microsoft_FStar_Parser_AST.DefineEffect ((eff_name, eff_binders, eff_kind, eff_decls)))) -> begin
(let env0 = env
in (let env = (Microsoft_FStar_Parser_DesugarEnv.enter_monad_scope env eff_name)
in (let _41_2796 = (desugar_binders env eff_binders)
in (match (_41_2796) with
| (env, binders) -> begin
(let eff_k = (desugar_kind env eff_kind)
in (let _41_2807 = (Support.Prims.pipe_right eff_decls (Support.List.fold_left (fun ( _41_2800 ) ( decl ) -> (match (_41_2800) with
| (env, out) -> begin
(let _41_2804 = (desugar_decl env decl)
in (match (_41_2804) with
| (env, ses) -> begin
(let _68_19715 = (let _68_19714 = (Support.List.hd ses)
in (_68_19714)::out)
in (env, _68_19715))
end))
end)) (env, [])))
in (match (_41_2807) with
| (env, decls) -> begin
(let decls = (Support.List.rev decls)
in (let lookup = (fun ( s ) -> (match ((let _68_19719 = (let _68_19718 = (Microsoft_FStar_Absyn_Syntax.mk_ident (s, d.Microsoft_FStar_Parser_AST.drange))
in (Microsoft_FStar_Parser_DesugarEnv.qualify env _68_19718))
in (Microsoft_FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _68_19719))) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat (Support.String.strcat (Support.String.strcat "Monad " eff_name.Microsoft_FStar_Absyn_Syntax.idText) " expects definition of ") s), d.Microsoft_FStar_Parser_AST.drange))))
end
| Some (t) -> begin
t
end))
in (let ed = (let _68_19734 = (Microsoft_FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _68_19733 = (lookup "return")
in (let _68_19732 = (lookup "bind_wp")
in (let _68_19731 = (lookup "bind_wlp")
in (let _68_19730 = (lookup "if_then_else")
in (let _68_19729 = (lookup "ite_wp")
in (let _68_19728 = (lookup "ite_wlp")
in (let _68_19727 = (lookup "wp_binop")
in (let _68_19726 = (lookup "wp_as_type")
in (let _68_19725 = (lookup "close_wp")
in (let _68_19724 = (lookup "close_wp_t")
in (let _68_19723 = (lookup "assert_p")
in (let _68_19722 = (lookup "assume_p")
in (let _68_19721 = (lookup "null_wp")
in (let _68_19720 = (lookup "trivial")
in {Microsoft_FStar_Absyn_Syntax.mname = _68_19734; Microsoft_FStar_Absyn_Syntax.binders = binders; Microsoft_FStar_Absyn_Syntax.qualifiers = quals; Microsoft_FStar_Absyn_Syntax.signature = eff_k; Microsoft_FStar_Absyn_Syntax.ret = _68_19733; Microsoft_FStar_Absyn_Syntax.bind_wp = _68_19732; Microsoft_FStar_Absyn_Syntax.bind_wlp = _68_19731; Microsoft_FStar_Absyn_Syntax.if_then_else = _68_19730; Microsoft_FStar_Absyn_Syntax.ite_wp = _68_19729; Microsoft_FStar_Absyn_Syntax.ite_wlp = _68_19728; Microsoft_FStar_Absyn_Syntax.wp_binop = _68_19727; Microsoft_FStar_Absyn_Syntax.wp_as_type = _68_19726; Microsoft_FStar_Absyn_Syntax.close_wp = _68_19725; Microsoft_FStar_Absyn_Syntax.close_wp_t = _68_19724; Microsoft_FStar_Absyn_Syntax.assert_p = _68_19723; Microsoft_FStar_Absyn_Syntax.assume_p = _68_19722; Microsoft_FStar_Absyn_Syntax.null_wp = _68_19721; Microsoft_FStar_Absyn_Syntax.trivial = _68_19720})))))))))))))))
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ed, d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)))
end))))
end
| Microsoft_FStar_Parser_AST.SubEffect (l) -> begin
(let lookup = (fun ( l ) -> (match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_effect_name env l)) with
| None -> begin
(let _68_19741 = (let _68_19740 = (let _68_19739 = (let _68_19738 = (let _68_19737 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.String.strcat "Effect name " _68_19737))
in (Support.String.strcat _68_19738 " not found"))
in (_68_19739, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Error (_68_19740))
in (raise (_68_19741)))
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

let desugar_decls = (fun ( env ) ( decls ) -> (Support.List.fold_left (fun ( _41_2832 ) ( d ) -> (match (_41_2832) with
| (env, sigelts) -> begin
(let _41_2836 = (desugar_decl env d)
in (match (_41_2836) with
| (env, se) -> begin
(env, (Support.List.append sigelts se))
end))
end)) (env, []) decls))

let desugar_modul_common = (fun ( curmod ) ( env ) ( m ) -> (let open_ns = (fun ( mname ) ( d ) -> (match (((Support.List.length mname.Microsoft_FStar_Absyn_Syntax.ns) <> 0)) with
| true -> begin
(let _68_19758 = (let _68_19757 = (let _68_19755 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids mname.Microsoft_FStar_Absyn_Syntax.ns)
in Microsoft_FStar_Parser_AST.Open (_68_19755))
in (let _68_19756 = (Microsoft_FStar_Absyn_Syntax.range_of_lid mname)
in (Microsoft_FStar_Parser_AST.mk_decl _68_19757 _68_19756)))
in (_68_19758)::d)
end
| false -> begin
d
end))
in (let env = (match (curmod) with
| None -> begin
env
end
| Some ((prev_mod, _41_2846)) -> begin
(Microsoft_FStar_Parser_DesugarEnv.finish_module_or_interface env prev_mod)
end)
in (let _41_2863 = (match (m) with
| Microsoft_FStar_Parser_AST.Interface ((mname, decls, admitted)) -> begin
(let _68_19760 = (Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _68_19759 = (open_ns mname decls)
in (_68_19760, mname, _68_19759, true)))
end
| Microsoft_FStar_Parser_AST.Module ((mname, decls)) -> begin
(let _68_19762 = (Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _68_19761 = (open_ns mname decls)
in (_68_19762, mname, _68_19761, false)))
end)
in (match (_41_2863) with
| (env, mname, decls, intf) -> begin
(let _41_2866 = (desugar_decls env decls)
in (match (_41_2866) with
| (env, sigelts) -> begin
(let modul = {Microsoft_FStar_Absyn_Syntax.name = mname; Microsoft_FStar_Absyn_Syntax.declarations = sigelts; Microsoft_FStar_Absyn_Syntax.exports = []; Microsoft_FStar_Absyn_Syntax.is_interface = intf; Microsoft_FStar_Absyn_Syntax.is_deserialized = false}
in (env, modul))
end))
end)))))

let desugar_partial_modul = (fun ( curmod ) ( env ) ( m ) -> (let m = (match ((Support.ST.read Microsoft_FStar_Options.interactive_fsi)) with
| true -> begin
(match (m) with
| Microsoft_FStar_Parser_AST.Module ((mname, decls)) -> begin
(let _68_19769 = (let _68_19768 = (let _68_19767 = (Support.ST.read Microsoft_FStar_Options.admit_fsi)
in (Support.Microsoft.FStar.Util.for_some (fun ( m ) -> (m = mname.Microsoft_FStar_Absyn_Syntax.str)) _68_19767))
in (mname, decls, _68_19768))
in Microsoft_FStar_Parser_AST.Interface (_68_19769))
end
| Microsoft_FStar_Parser_AST.Interface ((mname, _41_2878, _41_2880)) -> begin
(failwith ((Support.String.strcat "Impossible: " mname.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)))
end)
end
| false -> begin
m
end)
in (desugar_modul_common curmod env m)))

let desugar_modul = (fun ( env ) ( m ) -> (let _41_2888 = (desugar_modul_common None env m)
in (match (_41_2888) with
| (env, modul) -> begin
(let env = (Microsoft_FStar_Parser_DesugarEnv.finish_module_or_interface env modul)
in (let _41_2890 = (match ((Microsoft_FStar_Options.should_dump modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(let _68_19774 = (Microsoft_FStar_Absyn_Print.modul_to_string modul)
in (Support.Microsoft.FStar.Util.fprint1 "%s\n" _68_19774))
end
| false -> begin
()
end)
in (env, modul)))
end)))

let desugar_file = (fun ( env ) ( f ) -> (let _41_2903 = (Support.List.fold_left (fun ( _41_2896 ) ( m ) -> (match (_41_2896) with
| (env, mods) -> begin
(let _41_2900 = (desugar_modul env m)
in (match (_41_2900) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_41_2903) with
| (env, mods) -> begin
(env, (Support.List.rev mods))
end)))

let add_modul_to_env = (fun ( m ) ( en ) -> (let en = (Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface false false en m.Microsoft_FStar_Absyn_Syntax.name)
in (let en = (Support.List.fold_left Microsoft_FStar_Parser_DesugarEnv.push_sigelt (let _41_2907 = en
in {Microsoft_FStar_Parser_DesugarEnv.curmodule = Some (m.Microsoft_FStar_Absyn_Syntax.name); Microsoft_FStar_Parser_DesugarEnv.modules = _41_2907.Microsoft_FStar_Parser_DesugarEnv.modules; Microsoft_FStar_Parser_DesugarEnv.open_namespaces = _41_2907.Microsoft_FStar_Parser_DesugarEnv.open_namespaces; Microsoft_FStar_Parser_DesugarEnv.sigaccum = _41_2907.Microsoft_FStar_Parser_DesugarEnv.sigaccum; Microsoft_FStar_Parser_DesugarEnv.localbindings = _41_2907.Microsoft_FStar_Parser_DesugarEnv.localbindings; Microsoft_FStar_Parser_DesugarEnv.recbindings = _41_2907.Microsoft_FStar_Parser_DesugarEnv.recbindings; Microsoft_FStar_Parser_DesugarEnv.phase = _41_2907.Microsoft_FStar_Parser_DesugarEnv.phase; Microsoft_FStar_Parser_DesugarEnv.sigmap = _41_2907.Microsoft_FStar_Parser_DesugarEnv.sigmap; Microsoft_FStar_Parser_DesugarEnv.default_result_effect = _41_2907.Microsoft_FStar_Parser_DesugarEnv.default_result_effect; Microsoft_FStar_Parser_DesugarEnv.iface = _41_2907.Microsoft_FStar_Parser_DesugarEnv.iface; Microsoft_FStar_Parser_DesugarEnv.admitted_iface = _41_2907.Microsoft_FStar_Parser_DesugarEnv.admitted_iface}) m.Microsoft_FStar_Absyn_Syntax.exports)
in (Microsoft_FStar_Parser_DesugarEnv.finish_module_or_interface en m))))




