
let as_imp = (fun ( _41_1 ) -> (match (_41_1) with
| (Microsoft_FStar_Parser_AST.Hash) | (Microsoft_FStar_Parser_AST.FsTypApp) -> begin
Some (Microsoft_FStar_Absyn_Syntax.Implicit)
end
| _ -> begin
None
end))

let arg_withimp_e = (fun ( imp ) ( t ) -> (t, (as_imp imp)))

let arg_withimp_t = (fun ( imp ) ( t ) -> (match (imp) with
| Microsoft_FStar_Parser_AST.Hash -> begin
(t, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end
| _ -> begin
(t, None)
end))

let contains_binder = (fun ( binders ) -> (Support.Prims.pipe_right binders (Support.Microsoft.FStar.Util.for_some (fun ( b ) -> (match (b.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Annotated (_) -> begin
true
end
| _ -> begin
false
end)))))

let rec unparen = (fun ( t ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _ -> begin
t
end))

let rec unlabel = (fun ( t ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (t) -> begin
(unlabel t)
end
| Microsoft_FStar_Parser_AST.Labeled ((t, _, _)) -> begin
(unlabel t)
end
| _ -> begin
t
end))

let kind_star = (fun ( r ) -> (let _65_18666 = (let _65_18665 = (Microsoft_FStar_Absyn_Syntax.lid_of_path (("Type")::[]) r)
in Microsoft_FStar_Parser_AST.Name (_65_18665))
in (Microsoft_FStar_Parser_AST.mk_term _65_18666 r Microsoft_FStar_Parser_AST.Kind)))

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
| _ -> begin
"UNKNOWN"
end))
in (let rec aux = (fun ( i ) -> (match ((i = (Support.String.length s))) with
| true -> begin
[]
end
| false -> begin
(let _65_18677 = (let _65_18675 = (Support.Microsoft.FStar.Util.char_at s i)
in (name_of_char _65_18675))
in (let _65_18676 = (aux (i + 1))
in (_65_18677)::_65_18676))
end))
in (let _65_18679 = (let _65_18678 = (aux 0)
in (Support.String.concat "_" _65_18678))
in (Support.String.strcat "op_" _65_18679)))))

let compile_op_lid = (fun ( n ) ( s ) ( r ) -> (let _65_18689 = (let _65_18688 = (let _65_18687 = (let _65_18686 = (compile_op n s)
in (_65_18686, r))
in (Microsoft_FStar_Absyn_Syntax.mk_ident _65_18687))
in (_65_18688)::[])
in (Support.Prims.pipe_right _65_18689 Microsoft_FStar_Absyn_Syntax.lid_of_ids)))

let op_as_vlid = (fun ( env ) ( arity ) ( rng ) ( s ) -> (let r = (fun ( l ) -> (let _65_18700 = (Microsoft_FStar_Absyn_Util.set_lid_range l rng)
in Some (_65_18700)))
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
| _ -> begin
None
end)
end))
in (match ((let _65_18703 = (compile_op_lid arity s rng)
in (Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env _65_18703))) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}) -> begin
Some (fv.Microsoft_FStar_Absyn_Syntax.v)
end
| _ -> begin
(fallback ())
end))))

let op_as_tylid = (fun ( env ) ( arity ) ( rng ) ( s ) -> (let r = (fun ( l ) -> (let _65_18714 = (Microsoft_FStar_Absyn_Util.set_lid_range l rng)
in Some (_65_18714)))
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
(match ((let _65_18715 = (compile_op_lid arity s rng)
in (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env _65_18715))) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (ftv); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}) -> begin
Some (ftv.Microsoft_FStar_Absyn_Syntax.v)
end
| _ -> begin
None
end)
end)))

let rec is_type = (fun ( env ) ( t ) -> (match ((t.Microsoft_FStar_Parser_AST.level = Microsoft_FStar_Parser_AST.Type)) with
| true -> begin
true
end
| false -> begin
(match ((let _65_18722 = (unparen t)
in _65_18722.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Wild -> begin
true
end
| Microsoft_FStar_Parser_AST.Labeled (_) -> begin
true
end
| Microsoft_FStar_Parser_AST.Op (("*", hd::_)) -> begin
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
| _ -> begin
true
end)
end
| (Microsoft_FStar_Parser_AST.QForall (_)) | (Microsoft_FStar_Parser_AST.QExists (_)) | (Microsoft_FStar_Parser_AST.Sum (_)) | (Microsoft_FStar_Parser_AST.Refine (_)) | (Microsoft_FStar_Parser_AST.Tvar (_)) | (Microsoft_FStar_Parser_AST.NamedTyp (_)) -> begin
true
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) when ((Support.List.length l.Microsoft_FStar_Absyn_Syntax.ns) = 0) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env l.Microsoft_FStar_Absyn_Syntax.ident)) with
| Some (_) -> begin
true
end
| _ -> begin
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
| Microsoft_FStar_Parser_AST.Product ((_, t)) -> begin
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
| Microsoft_FStar_Parser_AST.PatTvar ((id, _)) -> begin
(let _41_327 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_41_327) with
| (env, _) -> begin
(aux env pats)
end))
end
| Microsoft_FStar_Parser_AST.PatAscribed ((p, tm)) -> begin
(let env = (match ((is_kind env tm)) with
| true -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| (Microsoft_FStar_Parser_AST.PatVar ((id, _))) | (Microsoft_FStar_Parser_AST.PatTvar ((id, _))) -> begin
(let _65_18727 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (Support.Prims.pipe_right _65_18727 Support.Prims.fst))
end
| _ -> begin
env
end)
end
| false -> begin
env
end)
in (aux env pats))
end
| _ -> begin
false
end)
end))
in (aux env pats))
end
| _ -> begin
false
end)
end))
and is_kind = (fun ( env ) ( t ) -> (match ((t.Microsoft_FStar_Parser_AST.level = Microsoft_FStar_Parser_AST.Kind)) with
| true -> begin
true
end
| false -> begin
(match ((let _65_18730 = (unparen t)
in _65_18730.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Name ({Microsoft_FStar_Absyn_Syntax.ns = _; Microsoft_FStar_Absyn_Syntax.ident = _; Microsoft_FStar_Absyn_Syntax.nsstr = _; Microsoft_FStar_Absyn_Syntax.str = "Type"}) -> begin
true
end
| Microsoft_FStar_Parser_AST.Product ((_, t)) -> begin
(is_kind env t)
end
| Microsoft_FStar_Parser_AST.Paren (t) -> begin
(is_kind env t)
end
| (Microsoft_FStar_Parser_AST.Construct ((l, _))) | (Microsoft_FStar_Parser_AST.Name (l)) -> begin
(Microsoft_FStar_Parser_DesugarEnv.is_kind_abbrev env l)
end
| _ -> begin
false
end)
end))

let rec is_type_binder = (fun ( env ) ( b ) -> (match ((b.Microsoft_FStar_Parser_AST.blevel = Microsoft_FStar_Parser_AST.Formula)) with
| true -> begin
(match (b.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Variable (_) -> begin
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
| Microsoft_FStar_Parser_AST.Variable (_) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected binder without annotation", b.Microsoft_FStar_Parser_AST.brange))))
end
| Microsoft_FStar_Parser_AST.TVariable (_) -> begin
false
end
| Microsoft_FStar_Parser_AST.TAnnotated (_) -> begin
true
end
| (Microsoft_FStar_Parser_AST.Annotated ((_, t))) | (Microsoft_FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end))

let sort_ftv = (fun ( ftv ) -> (let _65_18741 = (Support.Microsoft.FStar.Util.remove_dups (fun ( x ) ( y ) -> (x.Microsoft_FStar_Absyn_Syntax.idText = y.Microsoft_FStar_Absyn_Syntax.idText)) ftv)
in (Support.Prims.pipe_left (Support.Microsoft.FStar.Util.sort_with (fun ( x ) ( y ) -> (Support.String.compare x.Microsoft_FStar_Absyn_Syntax.idText y.Microsoft_FStar_Absyn_Syntax.idText))) _65_18741)))

let rec free_type_vars_b = (fun ( env ) ( binder ) -> (match (binder.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Variable (_) -> begin
(env, [])
end
| Microsoft_FStar_Parser_AST.TVariable (x) -> begin
(let _41_421 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env x)
in (match (_41_421) with
| (env, _) -> begin
(env, (x)::[])
end))
end
| Microsoft_FStar_Parser_AST.Annotated ((_, term)) -> begin
(let _65_18748 = (free_type_vars env term)
in (env, _65_18748))
end
| Microsoft_FStar_Parser_AST.TAnnotated ((id, _)) -> begin
(let _41_435 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_41_435) with
| (env, _) -> begin
(env, [])
end))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(let _65_18749 = (free_type_vars env t)
in (env, _65_18749))
end))
and free_type_vars = (fun ( env ) ( t ) -> (match ((let _65_18752 = (unparen t)
in _65_18752.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Tvar (a) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env a)) with
| None -> begin
(a)::[]
end
| _ -> begin
[]
end)
end
| (Microsoft_FStar_Parser_AST.Wild) | (Microsoft_FStar_Parser_AST.Const (_)) | (Microsoft_FStar_Parser_AST.Var (_)) | (Microsoft_FStar_Parser_AST.Name (_)) -> begin
[]
end
| (Microsoft_FStar_Parser_AST.Requires ((t, _))) | (Microsoft_FStar_Parser_AST.Ensures ((t, _))) | (Microsoft_FStar_Parser_AST.Labeled ((t, _, _))) | (Microsoft_FStar_Parser_AST.NamedTyp ((_, t))) | (Microsoft_FStar_Parser_AST.Paren (t)) | (Microsoft_FStar_Parser_AST.Ascribed ((t, _))) -> begin
(free_type_vars env t)
end
| Microsoft_FStar_Parser_AST.Construct ((_, ts)) -> begin
(Support.List.collect (fun ( _41_487 ) -> (match (_41_487) with
| (t, _) -> begin
(free_type_vars env t)
end)) ts)
end
| Microsoft_FStar_Parser_AST.Op ((_, ts)) -> begin
(Support.List.collect (free_type_vars env) ts)
end
| Microsoft_FStar_Parser_AST.App ((t1, t2, _)) -> begin
(let _65_18755 = (free_type_vars env t1)
in (let _65_18754 = (free_type_vars env t2)
in (Support.List.append _65_18755 _65_18754)))
end
| Microsoft_FStar_Parser_AST.Refine ((b, t)) -> begin
(let _41_505 = (free_type_vars_b env b)
in (match (_41_505) with
| (env, f) -> begin
(let _65_18756 = (free_type_vars env t)
in (Support.List.append f _65_18756))
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
(let _65_18759 = (free_type_vars env body)
in (Support.List.append free _65_18759))
end))
end
| Microsoft_FStar_Parser_AST.Project ((t, _)) -> begin
(free_type_vars env t)
end
| (Microsoft_FStar_Parser_AST.Abs (_)) | (Microsoft_FStar_Parser_AST.If (_)) | (Microsoft_FStar_Parser_AST.QForall (_)) | (Microsoft_FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (Microsoft_FStar_Parser_AST.Let (_)) | (Microsoft_FStar_Parser_AST.Record (_)) | (Microsoft_FStar_Parser_AST.Match (_)) | (Microsoft_FStar_Parser_AST.TryWith (_)) | (Microsoft_FStar_Parser_AST.Seq (_)) -> begin
(Microsoft_FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.Microsoft_FStar_Parser_AST.range)
end))

let head_and_args = (fun ( t ) -> (let rec aux = (fun ( args ) ( t ) -> (match ((let _65_18766 = (unparen t)
in _65_18766.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((t, arg, imp)) -> begin
(aux (((arg, imp))::args) t)
end
| Microsoft_FStar_Parser_AST.Construct ((l, args')) -> begin
({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Name (l); Microsoft_FStar_Parser_AST.range = t.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Parser_AST.level = t.Microsoft_FStar_Parser_AST.level}, (Support.List.append args' args))
end
| _ -> begin
(t, args)
end))
in (aux [] t)))

let close = (fun ( env ) ( t ) -> (let ftv = (let _65_18771 = (free_type_vars env t)
in (Support.Prims.pipe_left sort_ftv _65_18771))
in (match (((Support.List.length ftv) = 0)) with
| true -> begin
t
end
| false -> begin
(let binders = (Support.Prims.pipe_right ftv (Support.List.map (fun ( x ) -> (let _65_18775 = (let _65_18774 = (let _65_18773 = (kind_star x.Microsoft_FStar_Absyn_Syntax.idRange)
in (x, _65_18773))
in Microsoft_FStar_Parser_AST.TAnnotated (_65_18774))
in (Microsoft_FStar_Parser_AST.mk_binder _65_18775 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type (Some (Microsoft_FStar_Absyn_Syntax.Implicit)))))))
in (let result = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((binders, t))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
in result))
end)))

let close_fun = (fun ( env ) ( t ) -> (let ftv = (let _65_18780 = (free_type_vars env t)
in (Support.Prims.pipe_left sort_ftv _65_18780))
in (match (((Support.List.length ftv) = 0)) with
| true -> begin
t
end
| false -> begin
(let binders = (Support.Prims.pipe_right ftv (Support.List.map (fun ( x ) -> (let _65_18784 = (let _65_18783 = (let _65_18782 = (kind_star x.Microsoft_FStar_Absyn_Syntax.idRange)
in (x, _65_18782))
in Microsoft_FStar_Parser_AST.TAnnotated (_65_18783))
in (Microsoft_FStar_Parser_AST.mk_binder _65_18784 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type (Some (Microsoft_FStar_Absyn_Syntax.Implicit)))))))
in (let t = (match ((let _65_18785 = (unlabel t)
in _65_18785.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Product (_) -> begin
t
end
| _ -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.App (((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.effect_Tot_lid)) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level), t, Microsoft_FStar_Parser_AST.Nothing))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
end)
in (let result = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((binders, t))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
in result)))
end)))

let rec uncurry = (fun ( bs ) ( t ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Product ((binders, t)) -> begin
(uncurry (Support.List.append bs binders) t)
end
| _ -> begin
(bs, t)
end))

let rec is_app_pattern = (fun ( p ) -> (match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed ((p, _)) -> begin
(is_app_pattern p)
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar (_); Microsoft_FStar_Parser_AST.prange = _}, _)) -> begin
true
end
| _ -> begin
false
end))

let rec destruct_app_pattern = (fun ( env ) ( is_top_level ) ( p ) -> (match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed ((p, t)) -> begin
(let _41_624 = (destruct_app_pattern env is_top_level p)
in (match (_41_624) with
| (name, args, _) -> begin
(name, args, Some (t))
end))
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((id, _)); Microsoft_FStar_Parser_AST.prange = _}, args)) when is_top_level -> begin
(let _65_18799 = (let _65_18798 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in Support.Microsoft.FStar.Util.Inr (_65_18798))
in (_65_18799, args, None))
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((id, _)); Microsoft_FStar_Parser_AST.prange = _}, args)) -> begin
(Support.Microsoft.FStar.Util.Inl (id), args, None)
end
| _ -> begin
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
| _ -> begin
(failwith ("Impossible"))
end))

let as_binder = (fun ( env ) ( imp ) ( _41_4 ) -> (match (_41_4) with
| Support.Microsoft.FStar.Util.Inl ((None, k)) -> begin
(let _65_18829 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (_65_18829, env))
end
| Support.Microsoft.FStar.Util.Inr ((None, t)) -> begin
(let _65_18830 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_65_18830, env))
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
| _ -> begin
(let _65_18841 = (Support.Microsoft.FStar.Range.string_of_range f.Microsoft_FStar_Parser_AST.range)
in (Support.Microsoft.FStar.Util.format2 "%s at %s" tag _65_18841))
end)
in (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Labeled ((f, msg, polarity))) f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level)))
in (let rec aux = (fun ( f ) -> (match (f.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (g) -> begin
(let _65_18845 = (let _65_18844 = (aux g)
in Microsoft_FStar_Parser_AST.Paren (_65_18844))
in (Microsoft_FStar_Parser_AST.mk_term _65_18845 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Op (("/\\", f1::f2::[])) -> begin
(let _65_18851 = (let _65_18850 = (let _65_18849 = (let _65_18848 = (aux f1)
in (let _65_18847 = (let _65_18846 = (aux f2)
in (_65_18846)::[])
in (_65_18848)::_65_18847))
in ("/\\", _65_18849))
in Microsoft_FStar_Parser_AST.Op (_65_18850))
in (Microsoft_FStar_Parser_AST.mk_term _65_18851 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.If ((f1, f2, f3)) -> begin
(let _65_18855 = (let _65_18854 = (let _65_18853 = (aux f2)
in (let _65_18852 = (aux f3)
in (f1, _65_18853, _65_18852)))
in Microsoft_FStar_Parser_AST.If (_65_18854))
in (Microsoft_FStar_Parser_AST.mk_term _65_18855 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Abs ((binders, g)) -> begin
(let _65_18858 = (let _65_18857 = (let _65_18856 = (aux g)
in (binders, _65_18856))
in Microsoft_FStar_Parser_AST.Abs (_65_18857))
in (Microsoft_FStar_Parser_AST.mk_term _65_18858 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| _ -> begin
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
| _ -> begin
false
end))))) with
| Some (Support.Microsoft.FStar.Util.Inr (y)) -> begin
(l, e, y)
end
| _ -> begin
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
| _ -> begin
false
end))))) with
| Some (Support.Microsoft.FStar.Util.Inl (b)) -> begin
(l, e, b)
end
| _ -> begin
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
| (loc, env, _, p) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_41_801) with
| (loc, env, ps) -> begin
(let pat = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_disj ((p)::(Support.List.rev ps))))
in (let _41_803 = (let _65_18930 = (Microsoft_FStar_Absyn_Syntax.pat_vars pat)
in (Support.Prims.ignore _65_18930))
in (loc, env, var, pat)))
end))
end))
end
| Microsoft_FStar_Parser_AST.PatAscribed ((p, t)) -> begin
(let p = (match ((is_kind env t)) with
| true -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatTvar (_) -> begin
p
end
| Microsoft_FStar_Parser_AST.PatVar ((x, imp)) -> begin
(let _41_816 = p
in {Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatTvar ((x, imp)); Microsoft_FStar_Parser_AST.prange = _41_816.Microsoft_FStar_Parser_AST.prange})
end
| _ -> begin
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
| LetBinder (_) -> begin
(failwith ("impossible"))
end
| TBinder ((x, _, aq)) -> begin
(let _65_18932 = (let _65_18931 = (desugar_kind env t)
in (x, _65_18931, aq))
in TBinder (_65_18932))
end
| VBinder ((x, _, aq)) -> begin
(let t = (close_fun env t)
in (let _65_18934 = (let _65_18933 = (desugar_typ env t)
in (x, _65_18933, aq))
in VBinder (_65_18934)))
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
in (let _65_18935 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_twild ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a Microsoft_FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((a, Microsoft_FStar_Absyn_Syntax.kun, aq)), _65_18935)))
end
| false -> begin
(let _41_852 = (resolvea loc env a)
in (match (_41_852) with
| (loc, env, abvd) -> begin
(let _65_18936 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_tvar ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s abvd Microsoft_FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((abvd, Microsoft_FStar_Absyn_Syntax.kun, aq)), _65_18936))
end))
end))
end
| Microsoft_FStar_Parser_AST.PatWild -> begin
(let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let y = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _65_18937 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_wild ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s y Microsoft_FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _65_18937))))
end
| Microsoft_FStar_Parser_AST.PatConst (c) -> begin
(let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _65_18938 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_constant (c)))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _65_18938)))
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
(let _65_18939 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_var (((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s xbvd Microsoft_FStar_Absyn_Syntax.tun), imp))))
in (loc, env, VBinder ((xbvd, Microsoft_FStar_Absyn_Syntax.tun, aq)), _65_18939))
end)))
end
| Microsoft_FStar_Parser_AST.PatName (l) -> begin
(let l = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _65_18940 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), []))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _65_18940))))
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatName (l); Microsoft_FStar_Parser_AST.prange = _}, args)) -> begin
(let _41_894 = (Support.List.fold_right (fun ( arg ) ( _41_884 ) -> (match (_41_884) with
| (loc, env, args) -> begin
(let _41_890 = (aux loc env arg)
in (match (_41_890) with
| (loc, env, _, arg) -> begin
(loc, env, (arg)::args)
end))
end)) args (loc, env, []))
in (match (_41_894) with
| (loc, env, args) -> begin
(let l = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _65_18943 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _65_18943))))
end))
end
| Microsoft_FStar_Parser_AST.PatApp (_) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern", p.Microsoft_FStar_Parser_AST.prange))))
end
| Microsoft_FStar_Parser_AST.PatList (pats) -> begin
(let _41_916 = (Support.List.fold_right (fun ( pat ) ( _41_906 ) -> (match (_41_906) with
| (loc, env, pats) -> begin
(let _41_912 = (aux loc env pat)
in (match (_41_912) with
| (loc, env, _, pat) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_41_916) with
| (loc, env, pats) -> begin
(let pat = (let _65_18956 = (let _65_18955 = (let _65_18951 = (Support.Microsoft.FStar.Range.end_range p.Microsoft_FStar_Parser_AST.prange)
in (pos_r _65_18951))
in (let _65_18954 = (let _65_18953 = (let _65_18952 = (Microsoft_FStar_Absyn_Util.fv Microsoft_FStar_Absyn_Const.nil_lid)
in (_65_18952, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), []))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_65_18953))
in (Support.Prims.pipe_left _65_18955 _65_18954)))
in (Support.List.fold_right (fun ( hd ) ( tl ) -> (let r = (Support.Microsoft.FStar.Range.union_ranges hd.Microsoft_FStar_Absyn_Syntax.p tl.Microsoft_FStar_Absyn_Syntax.p)
in (let _65_18950 = (let _65_18949 = (let _65_18948 = (Microsoft_FStar_Absyn_Util.fv Microsoft_FStar_Absyn_Const.cons_lid)
in (_65_18948, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), (hd)::(tl)::[]))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_65_18949))
in (Support.Prims.pipe_left (pos_r r) _65_18950)))) pats _65_18956))
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), pat)))
end))
end
| Microsoft_FStar_Parser_AST.PatTuple ((args, dep)) -> begin
(let _41_940 = (Support.List.fold_left (fun ( _41_929 ) ( p ) -> (match (_41_929) with
| (loc, env, pats) -> begin
(let _41_936 = (aux loc env p)
in (match (_41_936) with
| (loc, env, _, pat) -> begin
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
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, _)) -> begin
v
end
| _ -> begin
(failwith ("impossible"))
end)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _65_18959 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _65_18959)))))))
end))
end
| Microsoft_FStar_Parser_AST.PatRecord ([]) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern", p.Microsoft_FStar_Parser_AST.prange))))
end
| Microsoft_FStar_Parser_AST.PatRecord (fields) -> begin
(let _41_960 = (Support.List.hd fields)
in (match (_41_960) with
| (f, _) -> begin
(let _41_964 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_41_964) with
| (record, _) -> begin
(let fields = (Support.Prims.pipe_right fields (Support.List.map (fun ( _41_967 ) -> (match (_41_967) with
| (f, p) -> begin
(let _65_18961 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in (_65_18961, p))
end))))
in (let args = (Support.Prims.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map (fun ( _41_972 ) -> (match (_41_972) with
| (f, _) -> begin
(match ((Support.Prims.pipe_right fields (Support.List.tryFind (fun ( _41_976 ) -> (match (_41_976) with
| (g, _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals f g)
end))))) with
| None -> begin
(Microsoft_FStar_Parser_AST.mk_pattern Microsoft_FStar_Parser_AST.PatWild p.Microsoft_FStar_Parser_AST.prange)
end
| Some ((_, p)) -> begin
p
end)
end))))
in (let app = (Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatApp (((Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatName (record.Microsoft_FStar_Parser_DesugarEnv.constrname)) p.Microsoft_FStar_Parser_AST.prange), args))) p.Microsoft_FStar_Parser_AST.prange)
in (let _41_989 = (aux loc env app)
in (match (_41_989) with
| (env, e, b, p) -> begin
(let p = (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, _, args)) -> begin
(let _65_18969 = (let _65_18968 = (let _65_18967 = (let _65_18966 = (let _65_18965 = (let _65_18964 = (Support.Prims.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map Support.Prims.fst))
in (record.Microsoft_FStar_Parser_DesugarEnv.typename, _65_18964))
in Microsoft_FStar_Absyn_Syntax.Record_ctor (_65_18965))
in Some (_65_18966))
in (fv, _65_18967, args))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_65_18968))
in (Support.Prims.pipe_left pos _65_18969))
end
| _ -> begin
p
end)
in (env, e, b, p))
end)))))
end))
end))
end))))
in (let _41_1004 = (aux [] env p)
in (match (_41_1004) with
| (_, env, b, p) -> begin
(env, b, p)
end))))))
and desugar_binding_pat_maybe_top = (fun ( top ) ( env ) ( p ) -> (match (top) with
| true -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatVar ((x, _)) -> begin
(let _65_18975 = (let _65_18974 = (let _65_18973 = (Microsoft_FStar_Parser_DesugarEnv.qualify env x)
in (_65_18973, Microsoft_FStar_Absyn_Syntax.tun))
in LetBinder (_65_18974))
in (env, _65_18975, None))
end
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((x, _)); Microsoft_FStar_Parser_AST.prange = _}, t)) -> begin
(let _65_18979 = (let _65_18978 = (let _65_18977 = (Microsoft_FStar_Parser_DesugarEnv.qualify env x)
in (let _65_18976 = (desugar_typ env t)
in (_65_18977, _65_18976)))
in LetBinder (_65_18978))
in (env, _65_18979, None))
end
| _ -> begin
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
| _ -> begin
Some (p)
end)
in (env, binder, p))
end))
end))
and desugar_binding_pat = (fun ( env ) ( p ) -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top = (fun ( _41_1044 ) ( env ) ( pat ) -> (let _41_1052 = (desugar_data_pat env pat)
in (match (_41_1052) with
| (env, _, pat) -> begin
(env, pat)
end)))
and desugar_match_pat = (fun ( env ) ( p ) -> (desugar_match_pat_maybe_top false env p))
and desugar_typ_or_exp = (fun ( env ) ( t ) -> (match ((is_type env t)) with
| true -> begin
(let _65_18989 = (desugar_typ env t)
in Support.Microsoft.FStar.Util.Inl (_65_18989))
end
| false -> begin
(let _65_18990 = (desugar_exp env t)
in Support.Microsoft.FStar.Util.Inr (_65_18990))
end))
and desugar_exp = (fun ( env ) ( e ) -> (desugar_exp_maybe_top false env e))
and desugar_exp_maybe_top = (fun ( top_level ) ( env ) ( top ) -> (let pos = (fun ( e ) -> (e None top.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( e ) -> (let _41_1066 = e
in {Microsoft_FStar_Absyn_Syntax.n = _41_1066.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _41_1066.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = top.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _41_1066.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _41_1066.Microsoft_FStar_Absyn_Syntax.uvs}))
in (match ((let _65_19010 = (unparen top)
in _65_19010.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Const (c) -> begin
(Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match ((op_as_vlid env (Support.List.length args) top.Microsoft_FStar_Parser_AST.range s)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat "Unexpected operator: " s), top.Microsoft_FStar_Parser_AST.range))))
end
| Some (l) -> begin
(let op = (let _65_19013 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (Microsoft_FStar_Absyn_Util.fvar None l _65_19013))
in (let args = (Support.Prims.pipe_right args (Support.List.map (fun ( t ) -> (let _65_19015 = (desugar_typ_or_exp env t)
in (_65_19015, None)))))
in (let _65_19016 = (Microsoft_FStar_Absyn_Util.mk_exp_app op args)
in (Support.Prims.pipe_left setpos _65_19016))))
end)
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) -> begin
(match ((l.Microsoft_FStar_Absyn_Syntax.str = "ref")) with
| true -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env Microsoft_FStar_Absyn_Const.alloc_lid)) with
| None -> begin
(let _65_19019 = (let _65_19018 = (let _65_19017 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in ("Identifier \'ref\' not found; include lib/st.fst in your path", _65_19017))
in Microsoft_FStar_Absyn_Syntax.Error (_65_19018))
in (raise (_65_19019)))
end
| Some (e) -> begin
(setpos e)
end)
end
| false -> begin
(let _65_19020 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (Support.Prims.pipe_left setpos _65_19020))
end)
end
| Microsoft_FStar_Parser_AST.Construct ((l, args)) -> begin
(let dt = (let _65_19025 = (let _65_19024 = (let _65_19023 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (_65_19023, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _65_19024))
in (Support.Prims.pipe_left pos _65_19025))
in (match (args) with
| [] -> begin
dt
end
| _ -> begin
(let args = (Support.List.map (fun ( _41_1096 ) -> (match (_41_1096) with
| (t, imp) -> begin
(let te = (desugar_typ_or_exp env t)
in (arg_withimp_e imp te))
end)) args)
in (let _65_19030 = (let _65_19029 = (let _65_19028 = (let _65_19027 = (Microsoft_FStar_Absyn_Util.mk_exp_app dt args)
in (_65_19027, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_65_19028))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _65_19029))
in (Support.Prims.pipe_left setpos _65_19030)))
end))
end
| Microsoft_FStar_Parser_AST.Abs ((binders, body)) -> begin
(let _41_1133 = (Support.List.fold_left (fun ( _41_1105 ) ( pat ) -> (match (_41_1105) with
| (env, ftvs) -> begin
(match (pat.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatTvar ((a, imp)); Microsoft_FStar_Parser_AST.prange = _}, t)) -> begin
(let ftvs = (let _65_19033 = (free_type_vars env t)
in (Support.List.append _65_19033 ftvs))
in (let _65_19035 = (let _65_19034 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (Support.Prims.pipe_left Support.Prims.fst _65_19034))
in (_65_19035, ftvs)))
end
| Microsoft_FStar_Parser_AST.PatTvar ((a, _)) -> begin
(let _65_19037 = (let _65_19036 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (Support.Prims.pipe_left Support.Prims.fst _65_19036))
in (_65_19037, ftvs))
end
| Microsoft_FStar_Parser_AST.PatAscribed ((_, t)) -> begin
(let _65_19039 = (let _65_19038 = (free_type_vars env t)
in (Support.List.append _65_19038 ftvs))
in (env, _65_19039))
end
| _ -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_41_1133) with
| (_, ftv) -> begin
(let ftv = (sort_ftv ftv)
in (let binders = (let _65_19041 = (Support.Prims.pipe_right ftv (Support.List.map (fun ( a ) -> (Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatTvar ((a, true))) top.Microsoft_FStar_Parser_AST.range))))
in (Support.List.append _65_19041 binders))
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
| LetBinder (_) -> begin
(failwith ("Impossible"))
end
| TBinder ((a, k, aq)) -> begin
(let _65_19050 = (binder_of_bnd b)
in (_65_19050, sc_pat_opt))
end
| VBinder ((x, t, aq)) -> begin
(let b = (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)
in (let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _65_19052 = (let _65_19051 = (Microsoft_FStar_Absyn_Util.bvar_to_exp b)
in (_65_19051, p))
in Some (_65_19052))
end
| (Some (p), Some ((sc, p'))) -> begin
(match ((sc.Microsoft_FStar_Absyn_Syntax.n, p'.Microsoft_FStar_Absyn_Syntax.v)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_), _) -> begin
(let tup = (Microsoft_FStar_Absyn_Util.mk_tuple_data_lid 2 top.Microsoft_FStar_Parser_AST.range)
in (let sc = (let _65_19059 = (let _65_19058 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) tup top.Microsoft_FStar_Parser_AST.range)
in (let _65_19057 = (let _65_19056 = (Microsoft_FStar_Absyn_Syntax.varg sc)
in (let _65_19055 = (let _65_19054 = (let _65_19053 = (Microsoft_FStar_Absyn_Util.bvar_to_exp b)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg _65_19053))
in (_65_19054)::[])
in (_65_19056)::_65_19055))
in (_65_19058, _65_19057)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _65_19059 None top.Microsoft_FStar_Parser_AST.range))
in (let p = (let _65_19063 = (let _65_19061 = (let _65_19060 = (Microsoft_FStar_Absyn_Util.fv tup)
in (_65_19060, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), (p')::(p)::[]))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_65_19061))
in (let _65_19062 = (Support.Microsoft.FStar.Range.union_ranges p'.Microsoft_FStar_Absyn_Syntax.p p.Microsoft_FStar_Absyn_Syntax.p)
in (Microsoft_FStar_Absyn_Util.withinfo _65_19063 None _65_19062)))
in Some ((sc, p)))))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app ((_, args)), Microsoft_FStar_Absyn_Syntax.Pat_cons ((_, _, pats))) -> begin
(let tup = (Microsoft_FStar_Absyn_Util.mk_tuple_data_lid (1 + (Support.List.length args)) top.Microsoft_FStar_Parser_AST.range)
in (let sc = (let _65_19069 = (let _65_19068 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) tup top.Microsoft_FStar_Parser_AST.range)
in (let _65_19067 = (let _65_19066 = (let _65_19065 = (let _65_19064 = (Microsoft_FStar_Absyn_Util.bvar_to_exp b)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg _65_19064))
in (_65_19065)::[])
in (Support.List.append args _65_19066))
in (_65_19068, _65_19067)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _65_19069 None top.Microsoft_FStar_Parser_AST.range))
in (let p = (let _65_19073 = (let _65_19071 = (let _65_19070 = (Microsoft_FStar_Absyn_Util.fv tup)
in (_65_19070, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), (Support.List.append pats ((p)::[]))))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_65_19071))
in (let _65_19072 = (Support.Microsoft.FStar.Range.union_ranges p'.Microsoft_FStar_Absyn_Syntax.p p.Microsoft_FStar_Absyn_Syntax.p)
in (Microsoft_FStar_Absyn_Util.withinfo _65_19073 None _65_19072)))
in Some ((sc, p)))))
end
| _ -> begin
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
| Microsoft_FStar_Parser_AST.App (({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Var (a); Microsoft_FStar_Parser_AST.range = _; Microsoft_FStar_Parser_AST.level = _}, arg, _)) when ((Microsoft_FStar_Absyn_Syntax.lid_equals a Microsoft_FStar_Absyn_Const.assert_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals a Microsoft_FStar_Absyn_Const.assume_lid)) -> begin
(let phi = (desugar_formula env arg)
in (let _65_19084 = (let _65_19083 = (let _65_19082 = (let _65_19076 = (Microsoft_FStar_Absyn_Syntax.range_of_lid a)
in (Microsoft_FStar_Absyn_Util.fvar None a _65_19076))
in (let _65_19081 = (let _65_19080 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ phi)
in (let _65_19079 = (let _65_19078 = (let _65_19077 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant Microsoft_FStar_Absyn_Syntax.Const_unit None top.Microsoft_FStar_Parser_AST.range)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg _65_19077))
in (_65_19078)::[])
in (_65_19080)::_65_19079))
in (_65_19082, _65_19081)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _65_19083))
in (Support.Prims.pipe_left pos _65_19084)))
end
| Microsoft_FStar_Parser_AST.App (_) -> begin
(let rec aux = (fun ( args ) ( e ) -> (match ((let _65_19089 = (unparen e)
in _65_19089.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((e, t, imp)) -> begin
(let arg = (let _65_19090 = (desugar_typ_or_exp env t)
in (Support.Prims.pipe_left (arg_withimp_e imp) _65_19090))
in (aux ((arg)::args) e))
end
| _ -> begin
(let head = (desugar_exp env e)
in (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (head, args))))
end))
in (aux [] top))
end
| Microsoft_FStar_Parser_AST.Seq ((t1, t2)) -> begin
(let _65_19096 = (let _65_19095 = (let _65_19094 = (let _65_19093 = (desugar_exp env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Let ((false, (((Microsoft_FStar_Parser_AST.mk_pattern Microsoft_FStar_Parser_AST.PatWild t1.Microsoft_FStar_Parser_AST.range), t1))::[], t2))) top.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Expr))
in (_65_19093, Microsoft_FStar_Absyn_Syntax.Sequence))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_65_19094))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _65_19095))
in (Support.Prims.pipe_left setpos _65_19096))
end
| Microsoft_FStar_Parser_AST.Let ((is_rec, (pat, _snd)::_tl, body)) -> begin
(let ds_let_rec = (fun ( _41_1259 ) -> (match (()) with
| () -> begin
(let bindings = ((pat, _snd))::_tl
in (let funs = (Support.Prims.pipe_right bindings (Support.List.map (fun ( _41_1263 ) -> (match (_41_1263) with
| (p, def) -> begin
(match ((is_app_pattern p)) with
| true -> begin
(let _65_19100 = (destruct_app_pattern env top_level p)
in (_65_19100, def))
end
| false -> begin
(match ((Microsoft_FStar_Parser_AST.un_function p def)) with
| Some ((p, def)) -> begin
(let _65_19101 = (destruct_app_pattern env top_level p)
in (_65_19101, def))
end
| _ -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((id, _)); Microsoft_FStar_Parser_AST.prange = _}, t)) -> begin
(match (top_level) with
| true -> begin
(let _65_19104 = (let _65_19103 = (let _65_19102 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in Support.Microsoft.FStar.Util.Inr (_65_19102))
in (_65_19103, [], Some (t)))
in (_65_19104, def))
end
| false -> begin
((Support.Microsoft.FStar.Util.Inl (id), [], Some (t)), def)
end)
end
| Microsoft_FStar_Parser_AST.PatVar ((id, _)) -> begin
(match (top_level) with
| true -> begin
(let _65_19107 = (let _65_19106 = (let _65_19105 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in Support.Microsoft.FStar.Util.Inr (_65_19105))
in (_65_19106, [], None))
in (_65_19107, def))
end
| false -> begin
((Support.Microsoft.FStar.Util.Inl (id), [], None), def)
end)
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected let binding", p.Microsoft_FStar_Parser_AST.prange))))
end)
end)
end)
end))))
in (let _41_1313 = (Support.List.fold_left (fun ( _41_1291 ) ( _41_1300 ) -> (match ((_41_1291, _41_1300)) with
| ((env, fnames), ((f, _, _), _)) -> begin
(let _41_1310 = (match (f) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(let _41_1305 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_41_1305) with
| (env, xx) -> begin
(env, Support.Microsoft.FStar.Util.Inl (xx))
end))
end
| Support.Microsoft.FStar.Util.Inr (l) -> begin
(let _65_19110 = (Microsoft_FStar_Parser_DesugarEnv.push_rec_binding env (Microsoft_FStar_Parser_DesugarEnv.Binding_let (l)))
in (_65_19110, Support.Microsoft.FStar.Util.Inr (l)))
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
| ((_, args, result_t), def) -> begin
(let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _65_19117 = (Support.Microsoft.FStar.Range.union_ranges t.Microsoft_FStar_Parser_AST.range def.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Ascribed ((def, t))) _65_19117 Microsoft_FStar_Parser_AST.Expr))
end)
in (let def = (match (args) with
| [] -> begin
def
end
| _ -> begin
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
| TBinder (_) -> begin
(failwith ("Unexpected type binder in let"))
end
| LetBinder ((l, t)) -> begin
(let body = (desugar_exp env t2)
in (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((false, ({Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = Microsoft_FStar_Absyn_Const.effect_ALL_lid; Microsoft_FStar_Absyn_Syntax.lbdef = t1})::[]), body))))
end
| VBinder ((x, t, _)) -> begin
(let body = (desugar_exp env t2)
in (let body = (match (pat) with
| (None) | (Some ({Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_wild (_); Microsoft_FStar_Absyn_Syntax.sort = _; Microsoft_FStar_Absyn_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _65_19129 = (let _65_19128 = (Microsoft_FStar_Absyn_Util.bvd_to_exp x t)
in (_65_19128, ((pat, None, body))::[]))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _65_19129 None body.Microsoft_FStar_Absyn_Syntax.pos))
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
(let _65_19142 = (let _65_19141 = (let _65_19140 = (desugar_exp env t1)
in (let _65_19139 = (let _65_19138 = (let _65_19134 = (desugar_exp env t2)
in ((Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (true))) None t2.Microsoft_FStar_Parser_AST.range), None, _65_19134))
in (let _65_19137 = (let _65_19136 = (let _65_19135 = (desugar_exp env t3)
in ((Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (false))) None t3.Microsoft_FStar_Parser_AST.range), None, _65_19135))
in (_65_19136)::[])
in (_65_19138)::_65_19137))
in (_65_19140, _65_19139)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _65_19141))
in (Support.Prims.pipe_left pos _65_19142))
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
(let _65_19145 = (desugar_exp env e)
in Some (_65_19145))
end)
in (let b = (desugar_exp env b)
in (pat, wopt, b)))
end))
end))
in (let _65_19151 = (let _65_19150 = (let _65_19149 = (desugar_exp env e)
in (let _65_19148 = (Support.List.map desugar_branch branches)
in (_65_19149, _65_19148)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _65_19150))
in (Support.Prims.pipe_left pos _65_19151)))
end
| Microsoft_FStar_Parser_AST.Ascribed ((e, t)) -> begin
(let _65_19157 = (let _65_19156 = (let _65_19155 = (desugar_exp env e)
in (let _65_19154 = (desugar_typ env t)
in (_65_19155, _65_19154, None)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed _65_19156))
in (Support.Prims.pipe_left pos _65_19157))
end
| Microsoft_FStar_Parser_AST.Record ((_, [])) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected empty record", top.Microsoft_FStar_Parser_AST.range))))
end
| Microsoft_FStar_Parser_AST.Record ((eopt, fields)) -> begin
(let _41_1420 = (Support.List.hd fields)
in (match (_41_1420) with
| (f, _) -> begin
(let qfn = (fun ( g ) -> (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append f.Microsoft_FStar_Absyn_Syntax.ns ((g)::[]))))
in (let _41_1426 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_41_1426) with
| (record, _) -> begin
(let get_field = (fun ( xopt ) ( f ) -> (let fn = f.Microsoft_FStar_Absyn_Syntax.ident
in (let found = (Support.Prims.pipe_right fields (Support.Microsoft.FStar.Util.find_opt (fun ( _41_1434 ) -> (match (_41_1434) with
| (g, _) -> begin
(let gn = g.Microsoft_FStar_Absyn_Syntax.ident
in (fn.Microsoft_FStar_Absyn_Syntax.idText = gn.Microsoft_FStar_Absyn_Syntax.idText))
end))))
in (match (found) with
| Some ((_, e)) -> begin
(let _65_19165 = (qfn fn)
in (_65_19165, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _65_19169 = (let _65_19168 = (let _65_19167 = (let _65_19166 = (Microsoft_FStar_Absyn_Syntax.text_of_lid f)
in (Support.Microsoft.FStar.Util.format1 "Field %s is missing" _65_19166))
in (_65_19167, top.Microsoft_FStar_Parser_AST.range))
in Microsoft_FStar_Absyn_Syntax.Error (_65_19168))
in (raise (_65_19169)))
end
| Some (x) -> begin
(let _65_19170 = (qfn fn)
in (_65_19170, (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Project ((x, f))) x.Microsoft_FStar_Parser_AST.range x.Microsoft_FStar_Parser_AST.level)))
end)
end))))
in (let recterm = (match (eopt) with
| None -> begin
(let _65_19175 = (let _65_19174 = (Support.Prims.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map (fun ( _41_1450 ) -> (match (_41_1450) with
| (f, _) -> begin
(let _65_19173 = (let _65_19172 = (get_field None f)
in (Support.Prims.pipe_left Support.Prims.snd _65_19172))
in (_65_19173, Microsoft_FStar_Parser_AST.Nothing))
end))))
in (record.Microsoft_FStar_Parser_DesugarEnv.constrname, _65_19174))
in Microsoft_FStar_Parser_AST.Construct (_65_19175))
end
| Some (e) -> begin
(let x = (Microsoft_FStar_Absyn_Util.genident (Some (e.Microsoft_FStar_Parser_AST.range)))
in (let xterm = (let _65_19177 = (let _65_19176 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((x)::[]))
in Microsoft_FStar_Parser_AST.Var (_65_19176))
in (Microsoft_FStar_Parser_AST.mk_term _65_19177 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr))
in (let record = (let _65_19180 = (let _65_19179 = (Support.Prims.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map (fun ( _41_1458 ) -> (match (_41_1458) with
| (f, _) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _65_19179))
in Microsoft_FStar_Parser_AST.Record (_65_19180))
in Microsoft_FStar_Parser_AST.Let ((false, (((Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatVar ((x, false))) x.Microsoft_FStar_Absyn_Syntax.idRange), e))::[], (Microsoft_FStar_Parser_AST.mk_term record top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))))))
end)
in (let recterm = (Microsoft_FStar_Parser_AST.mk_term recterm top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level)
in (let e = (desugar_exp env recterm)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, Microsoft_FStar_Absyn_Syntax.Data_app))) -> begin
(let e = (let _65_19190 = (let _65_19189 = (let _65_19188 = (let _65_19187 = (let _65_19186 = (let _65_19185 = (let _65_19184 = (let _65_19183 = (Support.Prims.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map Support.Prims.fst))
in (record.Microsoft_FStar_Parser_DesugarEnv.typename, _65_19183))
in Microsoft_FStar_Absyn_Syntax.Record_ctor (_65_19184))
in Some (_65_19185))
in (fv, _65_19186))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _65_19187 None e.Microsoft_FStar_Absyn_Syntax.pos))
in (_65_19188, args))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _65_19189))
in (Support.Prims.pipe_left pos _65_19190))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Data_app)))))
end
| _ -> begin
e
end)))))
end)))
end))
end
| Microsoft_FStar_Parser_AST.Project ((e, f)) -> begin
(let _41_1503 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_41_1503) with
| (_, fieldname) -> begin
(let e = (desugar_exp env e)
in (let fn = (let _41_1508 = (Support.Microsoft.FStar.Util.prefix fieldname.Microsoft_FStar_Absyn_Syntax.ns)
in (match (_41_1508) with
| (ns, _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append ns ((f.Microsoft_FStar_Absyn_Syntax.ident)::[])))
end))
in (let _65_19198 = (let _65_19197 = (let _65_19196 = (let _65_19193 = (Microsoft_FStar_Absyn_Syntax.range_of_lid f)
in (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Record_projector (fn))) fieldname _65_19193))
in (let _65_19195 = (let _65_19194 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_65_19194)::[])
in (_65_19196, _65_19195)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _65_19197))
in (Support.Prims.pipe_left pos _65_19198))))
end))
end
| Microsoft_FStar_Parser_AST.Paren (e) -> begin
(desugar_exp env e)
end
| _ -> begin
(Microsoft_FStar_Parser_AST.error "Unexpected term" top top.Microsoft_FStar_Parser_AST.range)
end))))
and desugar_typ = (fun ( env ) ( top ) -> (let wpos = (fun ( t ) -> (t None top.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( t ) -> (let _41_1520 = t
in {Microsoft_FStar_Absyn_Syntax.n = _41_1520.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _41_1520.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = top.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _41_1520.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _41_1520.Microsoft_FStar_Absyn_Syntax.uvs}))
in (let top = (unparen top)
in (let head_and_args = (fun ( t ) -> (let rec aux = (fun ( args ) ( t ) -> (match ((let _65_19221 = (unparen t)
in _65_19221.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((t, arg, imp)) -> begin
(aux (((arg, imp))::args) t)
end
| Microsoft_FStar_Parser_AST.Construct ((l, args')) -> begin
({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Name (l); Microsoft_FStar_Parser_AST.range = t.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Parser_AST.level = t.Microsoft_FStar_Parser_AST.level}, (Support.List.append args' args))
end
| _ -> begin
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
(let _65_19222 = (desugar_exp env t)
in (Support.Prims.pipe_right _65_19222 Microsoft_FStar_Absyn_Util.b2t))
end))
end
| Microsoft_FStar_Parser_AST.Ensures ((t, lopt)) -> begin
(let t = (label_conjuncts "post-condition" false lopt t)
in (match ((is_type env t)) with
| true -> begin
(desugar_typ env t)
end
| false -> begin
(let _65_19223 = (desugar_exp env t)
in (Support.Prims.pipe_right _65_19223 Microsoft_FStar_Absyn_Util.b2t))
end))
end
| Microsoft_FStar_Parser_AST.Op (("*", t1::_::[])) -> begin
(match ((is_type env t1)) with
| true -> begin
(let rec flatten = (fun ( t ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Op (("*", t1::t2::[])) -> begin
(let rest = (flatten t2)
in (t1)::rest)
end
| _ -> begin
(t)::[]
end))
in (let targs = (let _65_19228 = (flatten top)
in (Support.Prims.pipe_right _65_19228 (Support.List.map (fun ( t ) -> (let _65_19227 = (desugar_typ env t)
in (Microsoft_FStar_Absyn_Syntax.targ _65_19227))))))
in (let tup = (let _65_19229 = (Microsoft_FStar_Absyn_Util.mk_tuple_lid (Support.List.length targs) top.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) _65_19229))
in (Support.Prims.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))))
end
| false -> begin
(let _65_19235 = (let _65_19234 = (let _65_19233 = (let _65_19232 = (Microsoft_FStar_Parser_AST.term_to_string t1)
in (Support.Microsoft.FStar.Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _65_19232))
in (_65_19233, top.Microsoft_FStar_Parser_AST.range))
in Microsoft_FStar_Absyn_Syntax.Error (_65_19234))
in (raise (_65_19235)))
end)
end
| Microsoft_FStar_Parser_AST.Op (("=!=", args)) -> begin
(desugar_typ env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Op (("~", ((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Op (("==", args))) top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))::[]))) top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match ((op_as_tylid env (Support.List.length args) top.Microsoft_FStar_Parser_AST.range s)) with
| None -> begin
(let _65_19236 = (desugar_exp env top)
in (Support.Prims.pipe_right _65_19236 Microsoft_FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(let args = (Support.List.map (fun ( t ) -> (let _65_19238 = (desugar_typ_or_exp env t)
in (Support.Prims.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _65_19238))) args)
in (let _65_19239 = (Microsoft_FStar_Absyn_Util.ftv l Microsoft_FStar_Absyn_Syntax.kun)
in (Microsoft_FStar_Absyn_Util.mk_typ_app _65_19239 args)))
end)
end
| Microsoft_FStar_Parser_AST.Tvar (a) -> begin
(let _65_19240 = (Microsoft_FStar_Parser_DesugarEnv.fail_or2 (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (Support.Prims.pipe_left setpos _65_19240))
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) when ((Support.List.length l.Microsoft_FStar_Absyn_Syntax.ns) = 0) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env l.Microsoft_FStar_Absyn_Syntax.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _65_19241 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (Support.Prims.pipe_left setpos _65_19241))
end)
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) -> begin
(let l = (Microsoft_FStar_Absyn_Util.set_lid_range l top.Microsoft_FStar_Parser_AST.range)
in (let _65_19242 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (Support.Prims.pipe_left setpos _65_19242)))
end
| Microsoft_FStar_Parser_AST.Construct ((l, args)) -> begin
(let t = (let _65_19243 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (Support.Prims.pipe_left setpos _65_19243))
in (let args = (Support.List.map (fun ( _41_1603 ) -> (match (_41_1603) with
| (t, imp) -> begin
(let _65_19245 = (desugar_typ_or_exp env t)
in (Support.Prims.pipe_left (arg_withimp_t imp) _65_19245))
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
(let _65_19257 = (let _65_19256 = (let _65_19255 = (let _65_19254 = (Microsoft_FStar_Absyn_Print.pat_to_string q)
in (Support.Microsoft.FStar.Util.format1 "Pattern matching at the type level is not supported; got %s\n" _65_19254))
in (_65_19255, hd.Microsoft_FStar_Parser_AST.prange))
in Microsoft_FStar_Absyn_Syntax.Error (_65_19256))
in (raise (_65_19257)))
end
| None -> begin
(let b = (binder_of_bnd bnd)
in (aux env ((b)::bs) tl))
end)
end))
end))
in (aux env [] binders))
end
| Microsoft_FStar_Parser_AST.App (_) -> begin
(let rec aux = (fun ( args ) ( e ) -> (match ((let _65_19262 = (unparen e)
in _65_19262.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((e, arg, imp)) -> begin
(let arg = (let _65_19263 = (desugar_typ_or_exp env arg)
in (Support.Prims.pipe_left (arg_withimp_t imp) _65_19263))
in (aux ((arg)::args) e))
end
| _ -> begin
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
| (None, _) -> begin
(failwith ("Missing binder in refinement"))
end
| b -> begin
(let _41_1686 = (match ((as_binder env None (Support.Microsoft.FStar.Util.Inr (b)))) with
| ((Support.Microsoft.FStar.Util.Inr (x), _), env) -> begin
(x, env)
end
| _ -> begin
(failwith ("impossible"))
end)
in (match (_41_1686) with
| (b, env) -> begin
(let f = (match ((is_type env f)) with
| true -> begin
(desugar_formula env f)
end
| false -> begin
(let _65_19274 = (desugar_exp env f)
in (Support.Prims.pipe_right _65_19274 Microsoft_FStar_Absyn_Util.b2t))
end)
in (Support.Prims.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (b, f))))
end))
end)
end
| (Microsoft_FStar_Parser_AST.NamedTyp ((_, t))) | (Microsoft_FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| Microsoft_FStar_Parser_AST.Ascribed ((t, k)) -> begin
(let _65_19282 = (let _65_19281 = (let _65_19280 = (desugar_typ env t)
in (let _65_19279 = (desugar_kind env k)
in (_65_19280, _65_19279)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed' _65_19281))
in (Support.Prims.pipe_left wpos _65_19282))
end
| Microsoft_FStar_Parser_AST.Sum ((binders, t)) -> begin
(let _41_1720 = (Support.List.fold_left (fun ( _41_1705 ) ( b ) -> (match (_41_1705) with
| (env, tparams, typs) -> begin
(let _41_1709 = (desugar_exp_binder env b)
in (match (_41_1709) with
| (xopt, t) -> begin
(let _41_1715 = (match (xopt) with
| None -> begin
(let _65_19285 = (Microsoft_FStar_Absyn_Util.new_bvd (Some (top.Microsoft_FStar_Parser_AST.range)))
in (env, _65_19285))
end
| Some (x) -> begin
(Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_41_1715) with
| (env, x) -> begin
(let _65_19289 = (let _65_19288 = (let _65_19287 = (let _65_19286 = (Microsoft_FStar_Absyn_Util.close_with_lam tparams t)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _65_19286))
in (_65_19287)::[])
in (Support.List.append typs _65_19288))
in (env, (Support.List.append tparams (((Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)), None))::[])), _65_19289))
end))
end))
end)) (env, [], []) (Support.List.append binders (((Microsoft_FStar_Parser_AST.mk_binder (Microsoft_FStar_Parser_AST.NoName (t)) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Type None))::[])))
in (match (_41_1720) with
| (env, _, targs) -> begin
(let tup = (let _65_19290 = (Microsoft_FStar_Absyn_Util.mk_dtuple_lid (Support.List.length targs) top.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) _65_19290))
in (Support.Prims.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))
end))
end
| Microsoft_FStar_Parser_AST.Record (_) -> begin
(failwith ("Unexpected record type"))
end
| (Microsoft_FStar_Parser_AST.If (_)) | (Microsoft_FStar_Parser_AST.Labeled (_)) -> begin
(desugar_formula env top)
end
| _ when (top.Microsoft_FStar_Parser_AST.level = Microsoft_FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _ -> begin
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
| (arg, _) -> begin
(match ((let _65_19302 = (unparen arg)
in _65_19302.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App (({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Var (d); Microsoft_FStar_Parser_AST.range = _; Microsoft_FStar_Parser_AST.level = _}, _, _)) -> begin
(d.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "decreases")
end
| _ -> begin
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
| Microsoft_FStar_Parser_AST.Name (tot) when (((tot.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "Tot") && (not ((Microsoft_FStar_Parser_DesugarEnv.is_effect_name env Microsoft_FStar_Absyn_Const.effect_Tot_lid)))) && (let _65_19303 = (Microsoft_FStar_Parser_DesugarEnv.current_module env)
in (Microsoft_FStar_Absyn_Syntax.lid_equals _65_19303 Microsoft_FStar_Absyn_Const.prims_lid))) -> begin
(let args = (Support.List.map (fun ( _41_1786 ) -> (match (_41_1786) with
| (t, imp) -> begin
(let _65_19305 = (desugar_typ_or_exp env t)
in (Support.Prims.pipe_left (arg_withimp_t imp) _65_19305))
end)) args)
in (let _65_19306 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.effect_Tot_lid Microsoft_FStar_Absyn_Syntax.kun)
in (Microsoft_FStar_Absyn_Util.mk_typ_app _65_19306 args)))
end
| _ -> begin
(desugar_typ env t)
end)
end)))
in (let t = (pre_process_comp_typ t)
in (let _41_1793 = (Microsoft_FStar_Absyn_Util.head_and_args t)
in (match (_41_1793) with
| (head, args) -> begin
(match ((let _65_19308 = (let _65_19307 = (Microsoft_FStar_Absyn_Util.compress_typ head)
in _65_19307.Microsoft_FStar_Absyn_Syntax.n)
in (_65_19308, args))) with
| (Microsoft_FStar_Absyn_Syntax.Typ_const (eff), (Support.Microsoft.FStar.Util.Inl (result_typ), _)::rest) -> begin
(let _41_1840 = (Support.Prims.pipe_right rest (Support.List.partition (fun ( _41_10 ) -> (match (_41_10) with
| (Support.Microsoft.FStar.Util.Inr (_), _) -> begin
false
end
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (fv); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, (Support.Microsoft.FStar.Util.Inr (_), _)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.decreases_lid)
end
| _ -> begin
false
end)
end))))
in (match (_41_1840) with
| (dec, rest) -> begin
(let decreases_clause = (Support.Prims.pipe_right dec (Support.List.map (fun ( _41_11 ) -> (match (_41_11) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((_, (Support.Microsoft.FStar.Util.Inr (arg), _)::[])) -> begin
Microsoft_FStar_Absyn_Syntax.DECREASES (arg)
end
| _ -> begin
(failwith ("impos"))
end)
end
| _ -> begin
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
(let _65_19312 = (let _65_19311 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "%s is not an effect" _65_19311))
in (fail _65_19312))
end)
end))
end))
end
| _ -> begin
(match (default_ok) with
| true -> begin
(env.Microsoft_FStar_Parser_DesugarEnv.default_result_effect t r)
end
| false -> begin
(let _65_19314 = (let _65_19313 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "%s is not an effect" _65_19313))
in (fail _65_19314))
end)
end)
end))))))
and desugar_kind = (fun ( env ) ( k ) -> (let pos = (fun ( f ) -> (f k.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( kk ) -> (let _41_1871 = kk
in {Microsoft_FStar_Absyn_Syntax.n = _41_1871.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _41_1871.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = k.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _41_1871.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _41_1871.Microsoft_FStar_Absyn_Syntax.uvs}))
in (let k = (unparen k)
in (match (k.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Name ({Microsoft_FStar_Absyn_Syntax.ns = _; Microsoft_FStar_Absyn_Syntax.ident = _; Microsoft_FStar_Absyn_Syntax.nsstr = _; Microsoft_FStar_Absyn_Syntax.str = "Type"}) -> begin
(setpos Microsoft_FStar_Absyn_Syntax.mk_Kind_type)
end
| Microsoft_FStar_Parser_AST.Name ({Microsoft_FStar_Absyn_Syntax.ns = _; Microsoft_FStar_Absyn_Syntax.ident = _; Microsoft_FStar_Absyn_Syntax.nsstr = _; Microsoft_FStar_Absyn_Syntax.str = "Effect"}) -> begin
(setpos Microsoft_FStar_Absyn_Syntax.mk_Kind_effect)
end
| Microsoft_FStar_Parser_AST.Name (l) -> begin
(match ((let _65_19326 = (Microsoft_FStar_Parser_DesugarEnv.qualify_lid env l)
in (Microsoft_FStar_Parser_DesugarEnv.find_kind_abbrev env _65_19326))) with
| Some (l) -> begin
(Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev ((l, []), Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown)))
end
| _ -> begin
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
(let _65_19337 = (let _65_19336 = (let _65_19335 = (desugar_kind env k)
in ((Support.List.rev bs), _65_19335))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _65_19336))
in (Support.Prims.pipe_left pos _65_19337))
end
| hd::tl -> begin
(let _41_1916 = (let _65_19339 = (let _65_19338 = (Microsoft_FStar_Parser_DesugarEnv.default_ml env)
in (desugar_binder _65_19338 hd))
in (Support.Prims.pipe_right _65_19339 (as_binder env hd.Microsoft_FStar_Parser_AST.aqual)))
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
in (let _65_19341 = (desugar_typ_or_exp env t)
in (_65_19341, qual)))
end)) args)
in (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown))))
end)
end
| _ -> begin
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
| _ -> begin
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
(let pats = (Support.List.map (fun ( e ) -> (let _65_19372 = (desugar_typ_or_exp env e)
in (Support.Prims.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _65_19372))) pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _ -> begin
(let _65_19373 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
in (Support.Prims.pipe_left setpos _65_19373))
end)
in (let body = (let _65_19379 = (let _65_19378 = (let _65_19377 = (let _65_19376 = (Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_65_19376)::[])
in (_65_19377, body))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _65_19378))
in (Support.Prims.pipe_left pos _65_19379))
in (let _65_19384 = (let _65_19383 = (let _65_19380 = (Microsoft_FStar_Absyn_Util.set_lid_range qt b.Microsoft_FStar_Parser_AST.brange)
in (Microsoft_FStar_Absyn_Util.ftv _65_19380 Microsoft_FStar_Absyn_Syntax.kun))
in (let _65_19382 = (let _65_19381 = (Microsoft_FStar_Absyn_Syntax.targ body)
in (_65_19381)::[])
in (Microsoft_FStar_Absyn_Util.mk_typ_app _65_19383 _65_19382)))
in (Support.Prims.pipe_left setpos _65_19384))))))
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _41_1980 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_41_1980) with
| (env, x) -> begin
(let pats = (Support.List.map (fun ( e ) -> (let _65_19386 = (desugar_typ_or_exp env e)
in (Support.Prims.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _65_19386))) pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
end)
in (let body = (let _65_19392 = (let _65_19391 = (let _65_19390 = (let _65_19389 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_65_19389)::[])
in (_65_19390, body))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _65_19391))
in (Support.Prims.pipe_left pos _65_19392))
in (let _65_19397 = (let _65_19396 = (let _65_19393 = (Microsoft_FStar_Absyn_Util.set_lid_range q b.Microsoft_FStar_Parser_AST.brange)
in (Microsoft_FStar_Absyn_Util.ftv _65_19393 Microsoft_FStar_Absyn_Syntax.kun))
in (let _65_19395 = (let _65_19394 = (Microsoft_FStar_Absyn_Syntax.targ body)
in (_65_19394)::[])
in (Microsoft_FStar_Absyn_Util.mk_typ_app _65_19396 _65_19395)))
in (Support.Prims.pipe_left setpos _65_19397))))))
end))
end
| _ -> begin
(failwith ("impossible"))
end)))
in (let push_quant = (fun ( q ) ( binders ) ( pats ) ( body ) -> (match (binders) with
| b::b'::_rest -> begin
(let rest = (b')::_rest
in (let body = (let _65_19412 = (q (rest, pats, body))
in (let _65_19411 = (Support.Microsoft.FStar.Range.union_ranges b'.Microsoft_FStar_Parser_AST.brange body.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_AST.mk_term _65_19412 _65_19411 Microsoft_FStar_Parser_AST.Formula)))
in (let _65_19413 = (q ((b)::[], [], body))
in (Microsoft_FStar_Parser_AST.mk_term _65_19413 f.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Formula))))
end
| _ -> begin
(failwith ("impossible"))
end))
in (match ((let _65_19414 = (unparen f)
in _65_19414.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Labeled ((f, l, p)) -> begin
(let f = (desugar_formula env f)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((f, l, Microsoft_FStar_Absyn_Syntax.dummyRange, p)))))
end
| Microsoft_FStar_Parser_AST.Op (("==", hd::_args)) -> begin
(let args = (hd)::_args
in (let args = (Support.List.map (fun ( t ) -> (let _65_19416 = (desugar_typ_or_exp env t)
in (Support.Prims.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _65_19416))) args)
in (let eq = (match ((is_type env hd)) with
| true -> begin
(let _65_19417 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.eqT_lid f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _65_19417 Microsoft_FStar_Absyn_Syntax.kun))
end
| false -> begin
(let _65_19418 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.eq2_lid f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _65_19418 Microsoft_FStar_Absyn_Syntax.kun))
end)
in (Microsoft_FStar_Absyn_Util.mk_typ_app eq args))))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match (((connective s), args)) with
| (Some (conn), _::_::[]) -> begin
(let _65_19423 = (let _65_19419 = (Microsoft_FStar_Absyn_Util.set_lid_range conn f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _65_19419 Microsoft_FStar_Absyn_Syntax.kun))
in (let _65_19422 = (Support.List.map (fun ( x ) -> (let _65_19421 = (desugar_formula env x)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _65_19421))) args)
in (Microsoft_FStar_Absyn_Util.mk_typ_app _65_19423 _65_19422)))
end
| _ -> begin
(match ((is_type env f)) with
| true -> begin
(desugar_typ env f)
end
| false -> begin
(let _65_19424 = (desugar_exp env f)
in (Support.Prims.pipe_right _65_19424 Microsoft_FStar_Absyn_Util.b2t))
end)
end)
end
| Microsoft_FStar_Parser_AST.If ((f1, f2, f3)) -> begin
(let _65_19429 = (let _65_19425 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.ite_lid f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _65_19425 Microsoft_FStar_Absyn_Syntax.kun))
in (let _65_19428 = (Support.List.map (fun ( x ) -> (match ((desugar_typ_or_exp env x)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| Support.Microsoft.FStar.Util.Inr (v) -> begin
(let _65_19427 = (Microsoft_FStar_Absyn_Util.b2t v)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _65_19427))
end)) ((f1)::(f2)::(f3)::[]))
in (Microsoft_FStar_Absyn_Util.mk_typ_app _65_19429 _65_19428)))
end
| Microsoft_FStar_Parser_AST.QForall ((_1::_2::_3, pats, body)) -> begin
(let binders = (_1)::(_2)::_3
in (let _65_19431 = (push_quant (fun ( x ) -> Microsoft_FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _65_19431)))
end
| Microsoft_FStar_Parser_AST.QExists ((_1::_2::_3, pats, body)) -> begin
(let binders = (_1)::(_2)::_3
in (let _65_19433 = (push_quant (fun ( x ) -> Microsoft_FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _65_19433)))
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
| _ -> begin
(match ((is_type env f)) with
| true -> begin
(desugar_typ env f)
end
| false -> begin
(let _65_19434 = (desugar_exp env f)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Util.b2t _65_19434))
end)
end)))))))
and desugar_formula = (fun ( env ) ( t ) -> (desugar_formula' (let _41_2086 = env
in {Microsoft_FStar_Parser_DesugarEnv.curmodule = _41_2086.Microsoft_FStar_Parser_DesugarEnv.curmodule; Microsoft_FStar_Parser_DesugarEnv.modules = _41_2086.Microsoft_FStar_Parser_DesugarEnv.modules; Microsoft_FStar_Parser_DesugarEnv.open_namespaces = _41_2086.Microsoft_FStar_Parser_DesugarEnv.open_namespaces; Microsoft_FStar_Parser_DesugarEnv.sigaccum = _41_2086.Microsoft_FStar_Parser_DesugarEnv.sigaccum; Microsoft_FStar_Parser_DesugarEnv.localbindings = _41_2086.Microsoft_FStar_Parser_DesugarEnv.localbindings; Microsoft_FStar_Parser_DesugarEnv.recbindings = _41_2086.Microsoft_FStar_Parser_DesugarEnv.recbindings; Microsoft_FStar_Parser_DesugarEnv.phase = Microsoft_FStar_Parser_AST.Formula; Microsoft_FStar_Parser_DesugarEnv.sigmap = _41_2086.Microsoft_FStar_Parser_DesugarEnv.sigmap; Microsoft_FStar_Parser_DesugarEnv.default_result_effect = _41_2086.Microsoft_FStar_Parser_DesugarEnv.default_result_effect; Microsoft_FStar_Parser_DesugarEnv.iface = _41_2086.Microsoft_FStar_Parser_DesugarEnv.iface; Microsoft_FStar_Parser_DesugarEnv.admitted_iface = _41_2086.Microsoft_FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder = (fun ( env ) ( b ) -> (match ((is_type_binder env b)) with
| true -> begin
(let _65_19439 = (desugar_type_binder env b)
in Support.Microsoft.FStar.Util.Inl (_65_19439))
end
| false -> begin
(let _65_19440 = (desugar_exp_binder env b)
in Support.Microsoft.FStar.Util.Inr (_65_19440))
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
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected binder", b.Microsoft_FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_41_2119) with
| (env, tpars) -> begin
(env, (Support.List.rev tpars))
end)))
and desugar_exp_binder = (fun ( env ) ( b ) -> (match (b.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Annotated ((x, t)) -> begin
(let _65_19447 = (desugar_typ env t)
in (Some (x), _65_19447))
end
| Microsoft_FStar_Parser_AST.TVariable (t) -> begin
(let _65_19448 = (Microsoft_FStar_Parser_DesugarEnv.fail_or2 (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in (None, _65_19448))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(let _65_19449 = (desugar_typ env t)
in (None, _65_19449))
end
| Microsoft_FStar_Parser_AST.Variable (x) -> begin
(Some (x), Microsoft_FStar_Absyn_Syntax.tun)
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a type)", b.Microsoft_FStar_Parser_AST.brange))))
end))
and desugar_type_binder = (fun ( env ) ( b ) -> (let fail = (fun ( _41_2137 ) -> (match (()) with
| () -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a kind)", b.Microsoft_FStar_Parser_AST.brange))))
end))
in (match (b.Microsoft_FStar_Parser_AST.b) with
| (Microsoft_FStar_Parser_AST.Annotated ((x, t))) | (Microsoft_FStar_Parser_AST.TAnnotated ((x, t))) -> begin
(let _65_19454 = (desugar_kind env t)
in (Some (x), _65_19454))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(let _65_19455 = (desugar_kind env t)
in (None, _65_19455))
end
| Microsoft_FStar_Parser_AST.TVariable (x) -> begin
(Some (x), (let _41_2148 = Microsoft_FStar_Absyn_Syntax.mk_Kind_type
in {Microsoft_FStar_Absyn_Syntax.n = _41_2148.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _41_2148.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = b.Microsoft_FStar_Parser_AST.brange; Microsoft_FStar_Absyn_Syntax.fvs = _41_2148.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _41_2148.Microsoft_FStar_Absyn_Syntax.uvs}))
end
| _ -> begin
(fail ())
end)))

let gather_tc_binders = (fun ( tps ) ( k ) -> (let rec aux = (fun ( bs ) ( k ) -> (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((binders, k)) -> begin
(aux (Support.List.append bs binders) k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(aux bs k)
end
| _ -> begin
bs
end))
in (let _65_19464 = (aux tps k)
in (Support.Prims.pipe_right _65_19464 Microsoft_FStar_Absyn_Util.name_binders))))

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
| (x, _) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end))))
in (let binders = (let _65_19485 = (let _65_19484 = (let _65_19483 = (let _65_19482 = (let _65_19481 = (Microsoft_FStar_Absyn_Util.ftv t Microsoft_FStar_Absyn_Syntax.kun)
in (let _65_19480 = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (_65_19481, _65_19480)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' _65_19482 None p))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.null_v_binder _65_19483))
in (_65_19484)::[])
in (Support.List.append imp_binders _65_19485))
in (let disc_type = (let _65_19488 = (let _65_19487 = (let _65_19486 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.bool_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.total_comp _65_19486 p))
in (binders, _65_19487))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _65_19488 None p))
in (Support.Prims.pipe_right datas (Support.List.map (fun ( d ) -> (let disc_name = (Microsoft_FStar_Absyn_Util.mk_discriminator d)
in (let _65_19492 = (let _65_19491 = (quals ((Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Discriminator (d))::[]))
in (let _65_19490 = (Microsoft_FStar_Absyn_Syntax.range_of_lid disc_name)
in (disc_name, disc_type, _65_19491, _65_19490)))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_65_19492)))))))))))))

let mk_indexed_projectors = (fun ( refine_domain ) ( env ) ( _41_2192 ) ( lid ) ( formals ) ( t ) -> (match (_41_2192) with
| (tc, tps, k) -> begin
(let binders = (gather_tc_binders tps k)
in (let p = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (let arg_binder = (let arg_typ = (let _65_19501 = (let _65_19500 = (Microsoft_FStar_Absyn_Util.ftv tc Microsoft_FStar_Absyn_Syntax.kun)
in (let _65_19499 = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (_65_19500, _65_19499)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' _65_19501 None p))
in (let projectee = (let _65_19503 = (Microsoft_FStar_Absyn_Syntax.mk_ident ("projectee", p))
in (let _65_19502 = (Microsoft_FStar_Absyn_Util.genident (Some (p)))
in {Microsoft_FStar_Absyn_Syntax.ppname = _65_19503; Microsoft_FStar_Absyn_Syntax.realname = _65_19502}))
in (match ((not (refine_domain))) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end
| false -> begin
(let disc_name = (Microsoft_FStar_Absyn_Util.mk_discriminator lid)
in (let x = (Microsoft_FStar_Absyn_Util.gen_bvar arg_typ)
in (let _65_19513 = (let _65_19512 = (let _65_19511 = (let _65_19510 = (let _65_19509 = (let _65_19508 = (let _65_19507 = (Microsoft_FStar_Absyn_Util.fvar None disc_name p)
in (let _65_19506 = (let _65_19505 = (let _65_19504 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg _65_19504))
in (_65_19505)::[])
in (_65_19507, _65_19506)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _65_19508 None p))
in (Microsoft_FStar_Absyn_Util.b2t _65_19509))
in (x, _65_19510))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _65_19511 None p))
in (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s projectee) _65_19512))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.v_binder _65_19513))))
end)))
in (let imp_binders = (Support.Prims.pipe_right binders (Support.List.map (fun ( _41_2206 ) -> (match (_41_2206) with
| (x, _) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end))))
in (let binders = (Support.List.append imp_binders ((arg_binder)::[]))
in (let arg = (Microsoft_FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (let subst = (let _65_19523 = (Support.Prims.pipe_right formals (Support.List.mapi (fun ( i ) ( f ) -> (match ((Support.Prims.fst f)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(match ((Support.Prims.pipe_right binders (Support.Microsoft.FStar.Util.for_some (fun ( _41_13 ) -> (match (_41_13) with
| (Support.Microsoft.FStar.Util.Inl (b), _) -> begin
(Microsoft_FStar_Absyn_Util.bvd_eq a.Microsoft_FStar_Absyn_Syntax.v b.Microsoft_FStar_Absyn_Syntax.v)
end
| _ -> begin
false
end))))) with
| true -> begin
[]
end
| false -> begin
(let _41_2225 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_41_2225) with
| (field_name, _) -> begin
(let proj = (let _65_19519 = (let _65_19518 = (Microsoft_FStar_Absyn_Util.ftv field_name Microsoft_FStar_Absyn_Syntax.kun)
in (_65_19518, (arg)::[]))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _65_19519 None p))
in (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, proj)))::[])
end))
end)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(match ((Support.Prims.pipe_right binders (Support.Microsoft.FStar.Util.for_some (fun ( _41_14 ) -> (match (_41_14) with
| (Support.Microsoft.FStar.Util.Inr (y), _) -> begin
(Microsoft_FStar_Absyn_Util.bvd_eq x.Microsoft_FStar_Absyn_Syntax.v y.Microsoft_FStar_Absyn_Syntax.v)
end
| _ -> begin
false
end))))) with
| true -> begin
[]
end
| false -> begin
(let _41_2240 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_41_2240) with
| (field_name, _) -> begin
(let proj = (let _65_19522 = (let _65_19521 = (Microsoft_FStar_Absyn_Util.fvar None field_name p)
in (_65_19521, (arg)::[]))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _65_19522 None p))
in (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, proj)))::[])
end))
end)
end))))
in (Support.Prims.pipe_right _65_19523 Support.List.flatten))
in (Support.Prims.pipe_right formals (Support.List.mapi (fun ( i ) ( ax ) -> (match ((Support.Prims.fst ax)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _41_2250 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_41_2250) with
| (field_name, _) -> begin
(let kk = (let _65_19527 = (let _65_19526 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (binders, _65_19526))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _65_19527 p))
in (let _65_19529 = (let _65_19528 = (Microsoft_FStar_Absyn_Syntax.range_of_lid field_name)
in (field_name, [], kk, [], [], (Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Projector ((lid, Support.Microsoft.FStar.Util.Inl (a.Microsoft_FStar_Absyn_Syntax.v))))::[], _65_19528))
in Microsoft_FStar_Absyn_Syntax.Sig_tycon (_65_19529)))
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _41_2257 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_41_2257) with
| (field_name, _) -> begin
(let t = (let _65_19532 = (let _65_19531 = (let _65_19530 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Absyn_Util.total_comp _65_19530 p))
in (binders, _65_19531))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _65_19532 None p))
in (let quals = (fun ( q ) -> (match (((not (env.Microsoft_FStar_Parser_DesugarEnv.iface)) || env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.Assumption)::q
end
| false -> begin
q
end))
in (let _65_19536 = (let _65_19535 = (Microsoft_FStar_Absyn_Syntax.range_of_lid field_name)
in (field_name, t, (quals ((Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Projector ((lid, Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.v))))::[])), _65_19535))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_65_19536))))
end))
end)))))))))))
end))

let mk_data_projectors = (fun ( env ) ( _41_16 ) -> (match (_41_16) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, _, _)) when (not ((Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.lexcons_lid))) -> begin
(let refine_domain = (match ((Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _41_15 ) -> (match (_41_15) with
| Microsoft_FStar_Absyn_Syntax.RecordConstructor (_) -> begin
true
end
| _ -> begin
false
end))))) with
| true -> begin
false
end
| false -> begin
(let _41_2284 = tycon
in (match (_41_2284) with
| (l, _, _) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.find_all_datacons env l)) with
| Some (l) -> begin
((Support.List.length l) > 1)
end
| _ -> begin
true
end)
end))
end)
in (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((formals, cod)) -> begin
(let cod = (Microsoft_FStar_Absyn_Util.comp_result cod)
in (mk_indexed_projectors refine_domain env tycon lid formals cod))
end
| _ -> begin
[]
end))
end
| _ -> begin
[]
end))

let rec desugar_tycon = (fun ( env ) ( rng ) ( quals ) ( tcs ) -> (let tycon_id = (fun ( _41_17 ) -> (match (_41_17) with
| (Microsoft_FStar_Parser_AST.TyconAbstract ((id, _, _))) | (Microsoft_FStar_Parser_AST.TyconAbbrev ((id, _, _, _))) | (Microsoft_FStar_Parser_AST.TyconRecord ((id, _, _, _))) | (Microsoft_FStar_Parser_AST.TyconVariant ((id, _, _, _))) -> begin
id
end))
in (let binder_to_term = (fun ( b ) -> (match (b.Microsoft_FStar_Parser_AST.b) with
| (Microsoft_FStar_Parser_AST.Annotated ((x, _))) | (Microsoft_FStar_Parser_AST.Variable (x)) -> begin
(let _65_19555 = (let _65_19554 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((x)::[]))
in Microsoft_FStar_Parser_AST.Var (_65_19554))
in (Microsoft_FStar_Parser_AST.mk_term _65_19555 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr))
end
| (Microsoft_FStar_Parser_AST.TAnnotated ((a, _))) | (Microsoft_FStar_Parser_AST.TVariable (a)) -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Tvar (a)) a.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type)
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
t
end))
in (let tot = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.effect_Tot_lid)) rng Microsoft_FStar_Parser_AST.Expr)
in (let with_constructor_effect = (fun ( t ) -> (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.App ((tot, t, Microsoft_FStar_Parser_AST.Nothing))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level))
in (let apply_binders = (fun ( t ) ( binders ) -> (Support.List.fold_left (fun ( out ) ( b ) -> (let _65_19566 = (let _65_19565 = (let _65_19564 = (binder_to_term b)
in (out, _65_19564, Microsoft_FStar_Parser_AST.Nothing))
in Microsoft_FStar_Parser_AST.App (_65_19565))
in (Microsoft_FStar_Parser_AST.mk_term _65_19566 out.Microsoft_FStar_Parser_AST.range out.Microsoft_FStar_Parser_AST.level))) t binders))
in (let tycon_record_as_variant = (fun ( _41_18 ) -> (match (_41_18) with
| Microsoft_FStar_Parser_AST.TyconRecord ((id, parms, kopt, fields)) -> begin
(let constrName = (Microsoft_FStar_Absyn_Syntax.mk_ident ((Support.String.strcat "Mk" id.Microsoft_FStar_Absyn_Syntax.idText), id.Microsoft_FStar_Absyn_Syntax.idRange))
in (let mfields = (Support.List.map (fun ( _41_2370 ) -> (match (_41_2370) with
| (x, t) -> begin
(let _65_19572 = (let _65_19571 = (let _65_19570 = (Microsoft_FStar_Absyn_Util.mangle_field_name x)
in (_65_19570, t))
in Microsoft_FStar_Parser_AST.Annotated (_65_19571))
in (Microsoft_FStar_Parser_AST.mk_binder _65_19572 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr None))
end)) fields)
in (let result = (let _65_19575 = (let _65_19574 = (let _65_19573 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id)::[]))
in Microsoft_FStar_Parser_AST.Var (_65_19573))
in (Microsoft_FStar_Parser_AST.mk_term _65_19574 id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type))
in (apply_binders _65_19575 parms))
in (let constrTyp = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type)
in (let _65_19577 = (Support.Prims.pipe_right fields (Support.List.map (fun ( _41_2377 ) -> (match (_41_2377) with
| (x, _) -> begin
(Microsoft_FStar_Parser_DesugarEnv.qualify env x)
end))))
in (Microsoft_FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _65_19577))))))
end
| _ -> begin
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
in (let tconstr = (let _65_19588 = (let _65_19587 = (let _65_19586 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id)::[]))
in Microsoft_FStar_Parser_AST.Var (_65_19586))
in (Microsoft_FStar_Parser_AST.mk_term _65_19587 id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type))
in (apply_binders _65_19588 binders))
in (let qlid = (Microsoft_FStar_Parser_DesugarEnv.qualify _env id)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_tycon ((qlid, typars, k, mutuals, [], quals, rng))
in (let _env = (Microsoft_FStar_Parser_DesugarEnv.push_rec_binding _env (Microsoft_FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (let _env2 = (Microsoft_FStar_Parser_DesugarEnv.push_rec_binding _env' (Microsoft_FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (_env, (_env2, typars), se, tconstr)))))))
end))
end
| _ -> begin
(failwith ("Unexpected tycon"))
end))
in (let push_tparam = (fun ( env ) ( _41_20 ) -> (match (_41_20) with
| (Support.Microsoft.FStar.Util.Inr (x), _) -> begin
(Microsoft_FStar_Parser_DesugarEnv.push_bvvdef env x.Microsoft_FStar_Absyn_Syntax.v)
end
| (Support.Microsoft.FStar.Util.Inl (a), _) -> begin
(Microsoft_FStar_Parser_DesugarEnv.push_btvdef env a.Microsoft_FStar_Absyn_Syntax.v)
end))
in (let push_tparams = (Support.List.fold_left push_tparam)
in (match (tcs) with
| Microsoft_FStar_Parser_AST.TyconAbstract (_)::[] -> begin
(let tc = (Support.List.hd tcs)
in (let _41_2431 = (desugar_abstract_tc quals env [] tc)
in (match (_41_2431) with
| (_, _, se, _) -> begin
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
| _ -> begin
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
| _ -> begin
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
in (let _65_19600 = (let _65_19599 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (let _65_19598 = (Support.Prims.pipe_right quals (Support.List.filter (fun ( _41_23 ) -> (match (_41_23) with
| Microsoft_FStar_Absyn_Syntax.Effect -> begin
false
end
| _ -> begin
true
end))))
in (_65_19599, typars, c, _65_19598, rng)))
in Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_65_19600)))
end
| false -> begin
(let t = (desugar_typ env' t)
in (let _65_19602 = (let _65_19601 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (_65_19601, typars, k, t, quals, rng))
in Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_65_19602)))
end)
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| Microsoft_FStar_Parser_AST.TyconRecord (_)::[] -> begin
(let trec = (Support.List.hd tcs)
in (let _41_2472 = (tycon_record_as_variant trec)
in (match (_41_2472) with
| (t, fs) -> begin
(desugar_tycon env rng ((Microsoft_FStar_Absyn_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _::_ -> begin
(let env0 = env
in (let mutuals = (Support.List.map (fun ( x ) -> (Support.Prims.pipe_left (Microsoft_FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (let rec collect_tcs = (fun ( quals ) ( et ) ( tc ) -> (let _41_2487 = et
in (match (_41_2487) with
| (env, tcs) -> begin
(match (tc) with
| Microsoft_FStar_Parser_AST.TyconRecord (_) -> begin
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
| (env, (_, tps), se, tconstr) -> begin
(env, (Support.Microsoft.FStar.Util.Inl ((se, tps, constructors, tconstr, quals)))::tcs)
end))
end
| Microsoft_FStar_Parser_AST.TyconAbbrev ((id, binders, kopt, t)) -> begin
(let _41_2522 = (desugar_abstract_tc quals env mutuals (Microsoft_FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_41_2522) with
| (env, (_, tps), se, tconstr) -> begin
(env, (Support.Microsoft.FStar.Util.Inr ((se, tps, t, quals)))::tcs)
end))
end
| _ -> begin
(failwith ("Unrecognized mutual type definition"))
end)
end)))
in (let _41_2527 = (Support.List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_41_2527) with
| (env, tcs) -> begin
(let tcs = (Support.List.rev tcs)
in (let sigelts = (Support.Prims.pipe_right tcs (Support.List.collect (fun ( _41_25 ) -> (match (_41_25) with
| Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Syntax.Sig_tycon ((id, tpars, k, _, _, _, _)), tps, t, quals)) -> begin
(let env_tps = (push_tparams env tps)
in (let t = (desugar_typ env_tps t)
in (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((id, tpars, k, t, [], rng)))::[]))
end
| Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, _, tags, _)), tps, constrs, tconstr, quals)) -> begin
(let tycon = (tname, tpars, k)
in (let env_tps = (push_tparams env tps)
in (let _41_2594 = (let _65_19621 = (Support.Prims.pipe_right constrs (Support.List.map (fun ( _41_2572 ) -> (match (_41_2572) with
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
in (let t = (let _65_19613 = (Microsoft_FStar_Parser_DesugarEnv.default_total env_tps)
in (let _65_19612 = (close env_tps t)
in (desugar_typ _65_19613 _65_19612)))
in (let name = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (let quals = (Support.Prims.pipe_right tags (Support.List.collect (fun ( _41_24 ) -> (match (_41_24) with
| Microsoft_FStar_Absyn_Syntax.RecordType (fns) -> begin
(Microsoft_FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _ -> begin
[]
end))))
in (let _65_19620 = (let _65_19619 = (let _65_19618 = (let _65_19617 = (let _65_19616 = (Support.List.map (fun ( _41_2591 ) -> (match (_41_2591) with
| (x, _) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end)) tps)
in (Microsoft_FStar_Absyn_Util.close_typ _65_19616 t))
in (Support.Prims.pipe_right _65_19617 Microsoft_FStar_Absyn_Util.name_function_binders))
in (name, _65_19618, tycon, quals, mutuals, rng))
in Microsoft_FStar_Absyn_Syntax.Sig_datacon (_65_19619))
in (name, _65_19620))))))
end))))
in (Support.Prims.pipe_left Support.List.split _65_19621))
in (match (_41_2594) with
| (constrNames, constrs) -> begin
(Microsoft_FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, constrNames, tags, rng)))::constrs
end))))
end
| _ -> begin
(failwith ("impossible"))
end))))
in (let bundle = (let _65_19623 = (let _65_19622 = (Support.List.collect Microsoft_FStar_Absyn_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _65_19622, rng))
in Microsoft_FStar_Absyn_Syntax.Sig_bundle (_65_19623))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (let data_ops = (Support.Prims.pipe_right sigelts (Support.List.collect (mk_data_projectors env)))
in (let discs = (Support.Prims.pipe_right sigelts (Support.List.collect (fun ( _41_26 ) -> (match (_41_26) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((tname, tps, k, _, constrs, quals, _)) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _ -> begin
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
(let _65_19632 = (let _65_19631 = (Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_65_19631)::binders)
in (env, _65_19632))
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _41_2640 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_41_2640) with
| (env, x) -> begin
(let _65_19634 = (let _65_19633 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_65_19633)::binders)
in (env, _65_19634))
end))
end
| _ -> begin
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
(match ((let _65_19640 = (let _65_19639 = (desugar_exp_maybe_top true env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Let ((isrec, lets, (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Const (Microsoft_FStar_Absyn_Syntax.Const_unit)) d.Microsoft_FStar_Parser_AST.drange Microsoft_FStar_Parser_AST.Expr)))) d.Microsoft_FStar_Parser_AST.drange Microsoft_FStar_Parser_AST.Expr))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Util.compress_exp _65_19639))
in _65_19640.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, _)) -> begin
(let lids = (Support.Prims.pipe_right (Support.Prims.snd lbs) (Support.List.map (fun ( lb ) -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inr (l) -> begin
l
end
| _ -> begin
(failwith ("impossible"))
end))))
in (let quals = (Support.Prims.pipe_right (Support.Prims.snd lbs) (Support.List.collect (fun ( _41_27 ) -> (match (_41_27) with
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (_); Microsoft_FStar_Absyn_Syntax.lbtyp = _; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = _} -> begin
[]
end
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = _; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = _} -> begin
(Microsoft_FStar_Parser_DesugarEnv.lookup_letbinding_quals env l)
end))))
in (let s = Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, d.Microsoft_FStar_Parser_AST.drange, lids, quals))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env s)
in (env, (s)::[])))))
end
| _ -> begin
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
in (let _65_19646 = (let _65_19645 = (let _65_19644 = (let _65_19643 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (_65_19643, f, (Microsoft_FStar_Absyn_Syntax.Assumption)::[], d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Sig_assume (_65_19644))
in (_65_19645)::[])
in (env, _65_19646)))
end
| Microsoft_FStar_Parser_AST.Val ((quals, id, t)) -> begin
(let t = (let _65_19647 = (close_fun env t)
in (desugar_typ env _65_19647))
in (let quals = (match ((env.Microsoft_FStar_Parser_DesugarEnv.iface && env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.Assumption)::quals
end
| false -> begin
quals
end)
in (let se = (let _65_19649 = (let _65_19648 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (_65_19648, t, quals, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_65_19649))
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
in (let t = (let _65_19654 = (let _65_19653 = (let _65_19650 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_65_19650)::[])
in (let _65_19652 = (let _65_19651 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) Microsoft_FStar_Absyn_Const.exn_lid)
in (Microsoft_FStar_Absyn_Syntax.mk_Total _65_19651))
in (_65_19653, _65_19652)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _65_19654 None d.Microsoft_FStar_Parser_AST.drange))
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
(let _65_19659 = (let _65_19658 = (let _65_19657 = (let _65_19656 = (let _65_19655 = (Microsoft_FStar_Absyn_Print.sli eff.Microsoft_FStar_Absyn_Syntax.v)
in (Support.String.strcat "Effect " _65_19655))
in (Support.String.strcat _65_19656 " not found"))
in (_65_19657, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Error (_65_19658))
in (raise (_65_19659)))
end
| Some (ed) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.subst_of_list ed.Microsoft_FStar_Absyn_Syntax.binders args)
in (let sub = (Microsoft_FStar_Absyn_Util.subst_typ subst)
in (let ed = (let _65_19676 = (Microsoft_FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _65_19675 = (Microsoft_FStar_Absyn_Util.subst_kind subst ed.Microsoft_FStar_Absyn_Syntax.signature)
in (let _65_19674 = (sub ed.Microsoft_FStar_Absyn_Syntax.ret)
in (let _65_19673 = (sub ed.Microsoft_FStar_Absyn_Syntax.bind_wp)
in (let _65_19672 = (sub ed.Microsoft_FStar_Absyn_Syntax.bind_wlp)
in (let _65_19671 = (sub ed.Microsoft_FStar_Absyn_Syntax.if_then_else)
in (let _65_19670 = (sub ed.Microsoft_FStar_Absyn_Syntax.ite_wp)
in (let _65_19669 = (sub ed.Microsoft_FStar_Absyn_Syntax.ite_wlp)
in (let _65_19668 = (sub ed.Microsoft_FStar_Absyn_Syntax.wp_binop)
in (let _65_19667 = (sub ed.Microsoft_FStar_Absyn_Syntax.wp_as_type)
in (let _65_19666 = (sub ed.Microsoft_FStar_Absyn_Syntax.close_wp)
in (let _65_19665 = (sub ed.Microsoft_FStar_Absyn_Syntax.close_wp_t)
in (let _65_19664 = (sub ed.Microsoft_FStar_Absyn_Syntax.assert_p)
in (let _65_19663 = (sub ed.Microsoft_FStar_Absyn_Syntax.assume_p)
in (let _65_19662 = (sub ed.Microsoft_FStar_Absyn_Syntax.null_wp)
in (let _65_19661 = (sub ed.Microsoft_FStar_Absyn_Syntax.trivial)
in {Microsoft_FStar_Absyn_Syntax.mname = _65_19676; Microsoft_FStar_Absyn_Syntax.binders = binders; Microsoft_FStar_Absyn_Syntax.qualifiers = quals; Microsoft_FStar_Absyn_Syntax.signature = _65_19675; Microsoft_FStar_Absyn_Syntax.ret = _65_19674; Microsoft_FStar_Absyn_Syntax.bind_wp = _65_19673; Microsoft_FStar_Absyn_Syntax.bind_wlp = _65_19672; Microsoft_FStar_Absyn_Syntax.if_then_else = _65_19671; Microsoft_FStar_Absyn_Syntax.ite_wp = _65_19670; Microsoft_FStar_Absyn_Syntax.ite_wlp = _65_19669; Microsoft_FStar_Absyn_Syntax.wp_binop = _65_19668; Microsoft_FStar_Absyn_Syntax.wp_as_type = _65_19667; Microsoft_FStar_Absyn_Syntax.close_wp = _65_19666; Microsoft_FStar_Absyn_Syntax.close_wp_t = _65_19665; Microsoft_FStar_Absyn_Syntax.assert_p = _65_19664; Microsoft_FStar_Absyn_Syntax.assume_p = _65_19663; Microsoft_FStar_Absyn_Syntax.null_wp = _65_19662; Microsoft_FStar_Absyn_Syntax.trivial = _65_19661}))))))))))))))))
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ed, d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)
end
| _ -> begin
(let _65_19680 = (let _65_19679 = (let _65_19678 = (let _65_19677 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (Support.String.strcat _65_19677 " is not an effect"))
in (_65_19678, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Error (_65_19679))
in (raise (_65_19680)))
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
(let _65_19684 = (let _65_19683 = (Support.List.hd ses)
in (_65_19683)::out)
in (env, _65_19684))
end))
end)) (env, [])))
in (match (_41_2807) with
| (env, decls) -> begin
(let decls = (Support.List.rev decls)
in (let lookup = (fun ( s ) -> (match ((let _65_19688 = (let _65_19687 = (Microsoft_FStar_Absyn_Syntax.mk_ident (s, d.Microsoft_FStar_Parser_AST.drange))
in (Microsoft_FStar_Parser_DesugarEnv.qualify env _65_19687))
in (Microsoft_FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _65_19688))) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat (Support.String.strcat (Support.String.strcat "Monad " eff_name.Microsoft_FStar_Absyn_Syntax.idText) " expects definition of ") s), d.Microsoft_FStar_Parser_AST.drange))))
end
| Some (t) -> begin
t
end))
in (let ed = (let _65_19703 = (Microsoft_FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _65_19702 = (lookup "return")
in (let _65_19701 = (lookup "bind_wp")
in (let _65_19700 = (lookup "bind_wlp")
in (let _65_19699 = (lookup "if_then_else")
in (let _65_19698 = (lookup "ite_wp")
in (let _65_19697 = (lookup "ite_wlp")
in (let _65_19696 = (lookup "wp_binop")
in (let _65_19695 = (lookup "wp_as_type")
in (let _65_19694 = (lookup "close_wp")
in (let _65_19693 = (lookup "close_wp_t")
in (let _65_19692 = (lookup "assert_p")
in (let _65_19691 = (lookup "assume_p")
in (let _65_19690 = (lookup "null_wp")
in (let _65_19689 = (lookup "trivial")
in {Microsoft_FStar_Absyn_Syntax.mname = _65_19703; Microsoft_FStar_Absyn_Syntax.binders = binders; Microsoft_FStar_Absyn_Syntax.qualifiers = quals; Microsoft_FStar_Absyn_Syntax.signature = eff_k; Microsoft_FStar_Absyn_Syntax.ret = _65_19702; Microsoft_FStar_Absyn_Syntax.bind_wp = _65_19701; Microsoft_FStar_Absyn_Syntax.bind_wlp = _65_19700; Microsoft_FStar_Absyn_Syntax.if_then_else = _65_19699; Microsoft_FStar_Absyn_Syntax.ite_wp = _65_19698; Microsoft_FStar_Absyn_Syntax.ite_wlp = _65_19697; Microsoft_FStar_Absyn_Syntax.wp_binop = _65_19696; Microsoft_FStar_Absyn_Syntax.wp_as_type = _65_19695; Microsoft_FStar_Absyn_Syntax.close_wp = _65_19694; Microsoft_FStar_Absyn_Syntax.close_wp_t = _65_19693; Microsoft_FStar_Absyn_Syntax.assert_p = _65_19692; Microsoft_FStar_Absyn_Syntax.assume_p = _65_19691; Microsoft_FStar_Absyn_Syntax.null_wp = _65_19690; Microsoft_FStar_Absyn_Syntax.trivial = _65_19689})))))))))))))))
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ed, d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)))
end))))
end
| Microsoft_FStar_Parser_AST.SubEffect (l) -> begin
(let lookup = (fun ( l ) -> (match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_effect_name env l)) with
| None -> begin
(let _65_19710 = (let _65_19709 = (let _65_19708 = (let _65_19707 = (let _65_19706 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.String.strcat "Effect name " _65_19706))
in (Support.String.strcat _65_19707 " not found"))
in (_65_19708, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Error (_65_19709))
in (raise (_65_19710)))
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
(let _65_19727 = (let _65_19726 = (let _65_19724 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids mname.Microsoft_FStar_Absyn_Syntax.ns)
in Microsoft_FStar_Parser_AST.Open (_65_19724))
in (let _65_19725 = (Microsoft_FStar_Absyn_Syntax.range_of_lid mname)
in (Microsoft_FStar_Parser_AST.mk_decl _65_19726 _65_19725)))
in (_65_19727)::d)
end
| false -> begin
d
end))
in (let env = (match (curmod) with
| None -> begin
env
end
| Some ((prev_mod, _)) -> begin
(Microsoft_FStar_Parser_DesugarEnv.finish_module_or_interface env prev_mod)
end)
in (let _41_2863 = (match (m) with
| Microsoft_FStar_Parser_AST.Interface ((mname, decls, admitted)) -> begin
(let _65_19729 = (Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _65_19728 = (open_ns mname decls)
in (_65_19729, mname, _65_19728, true)))
end
| Microsoft_FStar_Parser_AST.Module ((mname, decls)) -> begin
(let _65_19731 = (Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _65_19730 = (open_ns mname decls)
in (_65_19731, mname, _65_19730, false)))
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
(let _65_19738 = (let _65_19737 = (let _65_19736 = (Support.ST.read Microsoft_FStar_Options.admit_fsi)
in (Support.Microsoft.FStar.Util.for_some (fun ( m ) -> (m = mname.Microsoft_FStar_Absyn_Syntax.str)) _65_19736))
in (mname, decls, _65_19737))
in Microsoft_FStar_Parser_AST.Interface (_65_19738))
end
| Microsoft_FStar_Parser_AST.Interface ((mname, _, _)) -> begin
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
(let _65_19743 = (Microsoft_FStar_Absyn_Print.modul_to_string modul)
in (Support.Microsoft.FStar.Util.fprint1 "%s\n" _65_19743))
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




