
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

let kind_star = (fun ( r ) -> (let _70_20918 = (let _70_20917 = (Microsoft_FStar_Absyn_Syntax.lid_of_path (("Type")::[]) r)
in Microsoft_FStar_Parser_AST.Name (_70_20917))
in (Microsoft_FStar_Parser_AST.mk_term _70_20918 r Microsoft_FStar_Parser_AST.Kind)))

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
(let _70_20929 = (let _70_20927 = (Support.Microsoft.FStar.Util.char_at s i)
in (name_of_char _70_20927))
in (let _70_20928 = (aux (i + 1))
in (_70_20929)::_70_20928))
end))
in (let _70_20931 = (let _70_20930 = (aux 0)
in (Support.String.concat "_" _70_20930))
in (Support.String.strcat "op_" _70_20931)))))

let compile_op_lid = (fun ( n ) ( s ) ( r ) -> (let _70_20941 = (let _70_20940 = (let _70_20939 = (let _70_20938 = (compile_op n s)
in (_70_20938, r))
in (Microsoft_FStar_Absyn_Syntax.mk_ident _70_20939))
in (_70_20940)::[])
in (Support.All.pipe_right _70_20941 Microsoft_FStar_Absyn_Syntax.lid_of_ids)))

let op_as_vlid = (fun ( env ) ( arity ) ( rng ) ( s ) -> (let r = (fun ( l ) -> (let _70_20952 = (Microsoft_FStar_Absyn_Util.set_lid_range l rng)
in Some (_70_20952)))
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
in (match ((let _70_20955 = (compile_op_lid arity s rng)
in (Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env _70_20955))) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _43_135)); Microsoft_FStar_Absyn_Syntax.tk = _43_132; Microsoft_FStar_Absyn_Syntax.pos = _43_130; Microsoft_FStar_Absyn_Syntax.fvs = _43_128; Microsoft_FStar_Absyn_Syntax.uvs = _43_126}) -> begin
Some (fv.Microsoft_FStar_Absyn_Syntax.v)
end
| _43_141 -> begin
(fallback ())
end))))

let op_as_tylid = (fun ( env ) ( arity ) ( rng ) ( s ) -> (let r = (fun ( l ) -> (let _70_20966 = (Microsoft_FStar_Absyn_Util.set_lid_range l rng)
in Some (_70_20966)))
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
(match ((let _70_20967 = (compile_op_lid arity s rng)
in (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env _70_20967))) with
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
(match ((let _70_20974 = (unparen t)
in _70_20974.Microsoft_FStar_Parser_AST.tm)) with
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
(let _70_20979 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (Support.All.pipe_right _70_20979 Support.Prims.fst))
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
(match ((let _70_20982 = (unparen t)
in _70_20982.Microsoft_FStar_Parser_AST.tm)) with
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

let sort_ftv = (fun ( ftv ) -> (let _70_20993 = (Support.Microsoft.FStar.Util.remove_dups (fun ( x ) ( y ) -> (x.Microsoft_FStar_Absyn_Syntax.idText = y.Microsoft_FStar_Absyn_Syntax.idText)) ftv)
in (Support.All.pipe_left (Support.Microsoft.FStar.Util.sort_with (fun ( x ) ( y ) -> (Support.String.compare x.Microsoft_FStar_Absyn_Syntax.idText y.Microsoft_FStar_Absyn_Syntax.idText))) _70_20993)))

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
(let _70_21000 = (free_type_vars env term)
in (env, _70_21000))
end
| Microsoft_FStar_Parser_AST.TAnnotated ((id, _43_431)) -> begin
(let _43_437 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_43_437) with
| (env, _43_436) -> begin
(env, [])
end))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(let _70_21001 = (free_type_vars env t)
in (env, _70_21001))
end))
and free_type_vars = (fun ( env ) ( t ) -> (match ((let _70_21004 = (unparen t)
in _70_21004.Microsoft_FStar_Parser_AST.tm)) with
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
(let _70_21007 = (free_type_vars env t1)
in (let _70_21006 = (free_type_vars env t2)
in (Support.List.append _70_21007 _70_21006)))
end
| Microsoft_FStar_Parser_AST.Refine ((b, t)) -> begin
(let _43_507 = (free_type_vars_b env b)
in (match (_43_507) with
| (env, f) -> begin
(let _70_21008 = (free_type_vars env t)
in (Support.List.append f _70_21008))
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
(let _70_21011 = (free_type_vars env body)
in (Support.List.append free _70_21011))
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

let head_and_args = (fun ( t ) -> (let rec aux = (fun ( args ) ( t ) -> (match ((let _70_21018 = (unparen t)
in _70_21018.Microsoft_FStar_Parser_AST.tm)) with
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

let close = (fun ( env ) ( t ) -> (let ftv = (let _70_21023 = (free_type_vars env t)
in (Support.All.pipe_left sort_ftv _70_21023))
in (match (((Support.List.length ftv) = 0)) with
| true -> begin
t
end
| false -> begin
(let binders = (Support.All.pipe_right ftv (Support.List.map (fun ( x ) -> (let _70_21027 = (let _70_21026 = (let _70_21025 = (kind_star x.Microsoft_FStar_Absyn_Syntax.idRange)
in (x, _70_21025))
in Microsoft_FStar_Parser_AST.TAnnotated (_70_21026))
in (Microsoft_FStar_Parser_AST.mk_binder _70_21027 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type (Some (Microsoft_FStar_Absyn_Syntax.Implicit)))))))
in (let result = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((binders, t))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
in result))
end)))

let close_fun = (fun ( env ) ( t ) -> (let ftv = (let _70_21032 = (free_type_vars env t)
in (Support.All.pipe_left sort_ftv _70_21032))
in (match (((Support.List.length ftv) = 0)) with
| true -> begin
t
end
| false -> begin
(let binders = (Support.All.pipe_right ftv (Support.List.map (fun ( x ) -> (let _70_21036 = (let _70_21035 = (let _70_21034 = (kind_star x.Microsoft_FStar_Absyn_Syntax.idRange)
in (x, _70_21034))
in Microsoft_FStar_Parser_AST.TAnnotated (_70_21035))
in (Microsoft_FStar_Parser_AST.mk_binder _70_21036 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type (Some (Microsoft_FStar_Absyn_Syntax.Implicit)))))))
in (let t = (match ((let _70_21037 = (unlabel t)
in _70_21037.Microsoft_FStar_Parser_AST.tm)) with
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
(let _70_21051 = (let _70_21050 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in Support.Microsoft.FStar.Util.Inr (_70_21050))
in (_70_21051, args, None))
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
(let _70_21102 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (_70_21102, env))
end
| Support.Microsoft.FStar.Util.Inr ((None, t)) -> begin
(let _70_21103 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_70_21103, env))
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
(let _70_21114 = (Support.Microsoft.FStar.Range.string_of_range f.Microsoft_FStar_Parser_AST.range)
in (Support.Microsoft.FStar.Util.format2 "%s at %s" tag _70_21114))
end)
in (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Labeled ((f, msg, polarity))) f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level)))
in (let rec aux = (fun ( f ) -> (match (f.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (g) -> begin
(let _70_21118 = (let _70_21117 = (aux g)
in Microsoft_FStar_Parser_AST.Paren (_70_21117))
in (Microsoft_FStar_Parser_AST.mk_term _70_21118 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Op (("/\\", f1::f2::[])) -> begin
(let _70_21124 = (let _70_21123 = (let _70_21122 = (let _70_21121 = (aux f1)
in (let _70_21120 = (let _70_21119 = (aux f2)
in (_70_21119)::[])
in (_70_21121)::_70_21120))
in ("/\\", _70_21122))
in Microsoft_FStar_Parser_AST.Op (_70_21123))
in (Microsoft_FStar_Parser_AST.mk_term _70_21124 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.If ((f1, f2, f3)) -> begin
(let _70_21128 = (let _70_21127 = (let _70_21126 = (aux f2)
in (let _70_21125 = (aux f3)
in (f1, _70_21126, _70_21125)))
in Microsoft_FStar_Parser_AST.If (_70_21127))
in (Microsoft_FStar_Parser_AST.mk_term _70_21128 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Abs ((binders, g)) -> begin
(let _70_21131 = (let _70_21130 = (let _70_21129 = (aux g)
in (binders, _70_21129))
in Microsoft_FStar_Parser_AST.Abs (_70_21130))
in (Microsoft_FStar_Parser_AST.mk_term _70_21131 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
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
in (let _43_812 = (let _70_21203 = (Microsoft_FStar_Absyn_Syntax.pat_vars pat)
in (Support.Prims.ignore _70_21203))
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
(let _70_21205 = (let _70_21204 = (desugar_kind env t)
in (x, _70_21204, aq))
in TBinder (_70_21205))
end
| VBinder ((x, _43_847, aq)) -> begin
(let t = (close_fun env t)
in (let _70_21207 = (let _70_21206 = (desugar_typ env t)
in (x, _70_21206, aq))
in VBinder (_70_21207)))
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
in (let _70_21208 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_twild ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a Microsoft_FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((a, Microsoft_FStar_Absyn_Syntax.kun, aq)), _70_21208, imp)))
end
| false -> begin
(let _43_862 = (resolvea loc env a)
in (match (_43_862) with
| (loc, env, abvd) -> begin
(let _70_21209 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_tvar ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s abvd Microsoft_FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((abvd, Microsoft_FStar_Absyn_Syntax.kun, aq)), _70_21209, imp))
end))
end))
end
| Microsoft_FStar_Parser_AST.PatWild -> begin
(let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let y = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _70_21210 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_wild ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s y Microsoft_FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _70_21210, false))))
end
| Microsoft_FStar_Parser_AST.PatConst (c) -> begin
(let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _70_21211 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_constant (c)))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _70_21211, false)))
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
(let _70_21212 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_var ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s xbvd Microsoft_FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((xbvd, Microsoft_FStar_Absyn_Syntax.tun, aq)), _70_21212, imp))
end)))
end
| Microsoft_FStar_Parser_AST.PatName (l) -> begin
(let l = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _70_21213 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), []))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _70_21213, false))))
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
in (let _70_21216 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _70_21216, false))))
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
(let pat = (let _70_21229 = (let _70_21228 = (let _70_21224 = (Support.Microsoft.FStar.Range.end_range p.Microsoft_FStar_Parser_AST.prange)
in (pos_r _70_21224))
in (let _70_21227 = (let _70_21226 = (let _70_21225 = (Microsoft_FStar_Absyn_Util.fv Microsoft_FStar_Absyn_Const.nil_lid)
in (_70_21225, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), []))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_70_21226))
in (Support.All.pipe_left _70_21228 _70_21227)))
in (Support.List.fold_right (fun ( hd ) ( tl ) -> (let r = (Support.Microsoft.FStar.Range.union_ranges hd.Microsoft_FStar_Absyn_Syntax.p tl.Microsoft_FStar_Absyn_Syntax.p)
in (let _70_21223 = (let _70_21222 = (let _70_21221 = (Microsoft_FStar_Absyn_Util.fv Microsoft_FStar_Absyn_Const.cons_lid)
in (_70_21221, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), ((hd, false))::((tl, false))::[]))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_70_21222))
in (Support.All.pipe_left (pos_r r) _70_21223)))) pats _70_21229))
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
in (let _70_21232 = (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _70_21232, false)))))))
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
(let _70_21234 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in (_70_21234, p))
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
(let _70_21242 = (let _70_21241 = (let _70_21240 = (let _70_21239 = (let _70_21238 = (let _70_21237 = (Support.All.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map Support.Prims.fst))
in (record.Microsoft_FStar_Parser_DesugarEnv.typename, _70_21237))
in Microsoft_FStar_Absyn_Syntax.Record_ctor (_70_21238))
in Some (_70_21239))
in (fv, _70_21240, args))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_70_21241))
in (Support.All.pipe_left pos _70_21242))
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
(let _70_21248 = (let _70_21247 = (let _70_21246 = (Microsoft_FStar_Parser_DesugarEnv.qualify env x)
in (_70_21246, Microsoft_FStar_Absyn_Syntax.tun))
in LetBinder (_70_21247))
in (env, _70_21248, None))
end
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((x, _43_1036)); Microsoft_FStar_Parser_AST.prange = _43_1033}, t)) -> begin
(let _70_21252 = (let _70_21251 = (let _70_21250 = (Microsoft_FStar_Parser_DesugarEnv.qualify env x)
in (let _70_21249 = (desugar_typ env t)
in (_70_21250, _70_21249)))
in LetBinder (_70_21251))
in (env, _70_21252, None))
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
(let _70_21262 = (desugar_typ env t)
in Support.Microsoft.FStar.Util.Inl (_70_21262))
end
| false -> begin
(let _70_21263 = (desugar_exp env t)
in Support.Microsoft.FStar.Util.Inr (_70_21263))
end))
and desugar_exp = (fun ( env ) ( e ) -> (desugar_exp_maybe_top false env e))
and desugar_exp_maybe_top = (fun ( top_level ) ( env ) ( top ) -> (let pos = (fun ( e ) -> (e None top.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( e ) -> (let _43_1085 = e
in {Microsoft_FStar_Absyn_Syntax.n = _43_1085.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _43_1085.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = top.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _43_1085.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _43_1085.Microsoft_FStar_Absyn_Syntax.uvs}))
in (match ((let _70_21283 = (unparen top)
in _70_21283.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Const (c) -> begin
(Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match ((op_as_vlid env (Support.List.length args) top.Microsoft_FStar_Parser_AST.range s)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat "Unexpected operator: " s), top.Microsoft_FStar_Parser_AST.range))))
end
| Some (l) -> begin
(let op = (let _70_21286 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (Microsoft_FStar_Absyn_Util.fvar None l _70_21286))
in (let args = (Support.All.pipe_right args (Support.List.map (fun ( t ) -> (let _70_21288 = (desugar_typ_or_exp env t)
in (_70_21288, None)))))
in (let _70_21289 = (Microsoft_FStar_Absyn_Util.mk_exp_app op args)
in (Support.All.pipe_left setpos _70_21289))))
end)
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) -> begin
(match ((l.Microsoft_FStar_Absyn_Syntax.str = "ref")) with
| true -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env Microsoft_FStar_Absyn_Const.alloc_lid)) with
| None -> begin
(let _70_21292 = (let _70_21291 = (let _70_21290 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in ("Identifier \'ref\' not found; include lib/st.fst in your path", _70_21290))
in Microsoft_FStar_Absyn_Syntax.Error (_70_21291))
in (raise (_70_21292)))
end
| Some (e) -> begin
(setpos e)
end)
end
| false -> begin
(let _70_21293 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (Support.All.pipe_left setpos _70_21293))
end)
end
| Microsoft_FStar_Parser_AST.Construct ((l, args)) -> begin
(let dt = (let _70_21298 = (let _70_21297 = (let _70_21296 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (_70_21296, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _70_21297))
in (Support.All.pipe_left pos _70_21298))
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
in (let _70_21303 = (let _70_21302 = (let _70_21301 = (let _70_21300 = (Microsoft_FStar_Absyn_Util.mk_exp_app dt args)
in (_70_21300, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_70_21301))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _70_21302))
in (Support.All.pipe_left setpos _70_21303)))
end))
end
| Microsoft_FStar_Parser_AST.Abs ((binders, body)) -> begin
(let _43_1152 = (Support.List.fold_left (fun ( _43_1124 ) ( pat ) -> (match (_43_1124) with
| (env, ftvs) -> begin
(match (pat.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatTvar ((a, imp)); Microsoft_FStar_Parser_AST.prange = _43_1127}, t)) -> begin
(let ftvs = (let _70_21306 = (free_type_vars env t)
in (Support.List.append _70_21306 ftvs))
in (let _70_21308 = (let _70_21307 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (Support.All.pipe_left Support.Prims.fst _70_21307))
in (_70_21308, ftvs)))
end
| Microsoft_FStar_Parser_AST.PatTvar ((a, _43_1139)) -> begin
(let _70_21310 = (let _70_21309 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (Support.All.pipe_left Support.Prims.fst _70_21309))
in (_70_21310, ftvs))
end
| Microsoft_FStar_Parser_AST.PatAscribed ((_43_1143, t)) -> begin
(let _70_21312 = (let _70_21311 = (free_type_vars env t)
in (Support.List.append _70_21311 ftvs))
in (env, _70_21312))
end
| _43_1148 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_43_1152) with
| (_43_1150, ftv) -> begin
(let ftv = (sort_ftv ftv)
in (let binders = (let _70_21314 = (Support.All.pipe_right ftv (Support.List.map (fun ( a ) -> (Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatTvar ((a, true))) top.Microsoft_FStar_Parser_AST.range))))
in (Support.List.append _70_21314 binders))
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
(let _70_21323 = (binder_of_bnd b)
in (_70_21323, sc_pat_opt))
end
| VBinder ((x, t, aq)) -> begin
(let b = (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)
in (let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _43_1192) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _70_21325 = (let _70_21324 = (Microsoft_FStar_Absyn_Util.bvar_to_exp b)
in (_70_21324, p))
in Some (_70_21325))
end
| (Some (p), Some ((sc, p'))) -> begin
(match ((sc.Microsoft_FStar_Absyn_Syntax.n, p'.Microsoft_FStar_Absyn_Syntax.v)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_43_1206), _43_1209) -> begin
(let tup = (Microsoft_FStar_Absyn_Util.mk_tuple_data_lid 2 top.Microsoft_FStar_Parser_AST.range)
in (let sc = (let _70_21332 = (let _70_21331 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) tup top.Microsoft_FStar_Parser_AST.range)
in (let _70_21330 = (let _70_21329 = (Microsoft_FStar_Absyn_Syntax.varg sc)
in (let _70_21328 = (let _70_21327 = (let _70_21326 = (Microsoft_FStar_Absyn_Util.bvar_to_exp b)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.varg _70_21326))
in (_70_21327)::[])
in (_70_21329)::_70_21328))
in (_70_21331, _70_21330)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _70_21332 None top.Microsoft_FStar_Parser_AST.range))
in (let p = (let _70_21336 = (let _70_21334 = (let _70_21333 = (Microsoft_FStar_Absyn_Util.fv tup)
in (_70_21333, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), ((p', false))::((p, false))::[]))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_70_21334))
in (let _70_21335 = (Support.Microsoft.FStar.Range.union_ranges p'.Microsoft_FStar_Absyn_Syntax.p p.Microsoft_FStar_Absyn_Syntax.p)
in (Microsoft_FStar_Absyn_Util.withinfo _70_21336 None _70_21335)))
in Some ((sc, p)))))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app ((_43_1215, args)), Microsoft_FStar_Absyn_Syntax.Pat_cons ((_43_1220, _43_1222, pats))) -> begin
(let tup = (Microsoft_FStar_Absyn_Util.mk_tuple_data_lid (1 + (Support.List.length args)) top.Microsoft_FStar_Parser_AST.range)
in (let sc = (let _70_21342 = (let _70_21341 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) tup top.Microsoft_FStar_Parser_AST.range)
in (let _70_21340 = (let _70_21339 = (let _70_21338 = (let _70_21337 = (Microsoft_FStar_Absyn_Util.bvar_to_exp b)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.varg _70_21337))
in (_70_21338)::[])
in (Support.List.append args _70_21339))
in (_70_21341, _70_21340)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _70_21342 None top.Microsoft_FStar_Parser_AST.range))
in (let p = (let _70_21346 = (let _70_21344 = (let _70_21343 = (Microsoft_FStar_Absyn_Util.fv tup)
in (_70_21343, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), (Support.List.append pats (((p, false))::[]))))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_70_21344))
in (let _70_21345 = (Support.Microsoft.FStar.Range.union_ranges p'.Microsoft_FStar_Absyn_Syntax.p p.Microsoft_FStar_Absyn_Syntax.p)
in (Microsoft_FStar_Absyn_Util.withinfo _70_21346 None _70_21345)))
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
in (let _70_21357 = (let _70_21356 = (let _70_21355 = (let _70_21349 = (Microsoft_FStar_Absyn_Syntax.range_of_lid a)
in (Microsoft_FStar_Absyn_Util.fvar None a _70_21349))
in (let _70_21354 = (let _70_21353 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ phi)
in (let _70_21352 = (let _70_21351 = (let _70_21350 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant Microsoft_FStar_Absyn_Syntax.Const_unit None top.Microsoft_FStar_Parser_AST.range)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.varg _70_21350))
in (_70_21351)::[])
in (_70_21353)::_70_21352))
in (_70_21355, _70_21354)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _70_21356))
in (Support.All.pipe_left pos _70_21357)))
end
| Microsoft_FStar_Parser_AST.App (_43_1250) -> begin
(let rec aux = (fun ( args ) ( e ) -> (match ((let _70_21362 = (unparen e)
in _70_21362.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((e, t, imp)) -> begin
(let arg = (let _70_21363 = (desugar_typ_or_exp env t)
in (Support.All.pipe_left (arg_withimp_e imp) _70_21363))
in (aux ((arg)::args) e))
end
| _43_1262 -> begin
(let head = (desugar_exp env e)
in (Support.All.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (head, args))))
end))
in (aux [] top))
end
| Microsoft_FStar_Parser_AST.Seq ((t1, t2)) -> begin
(let _70_21369 = (let _70_21368 = (let _70_21367 = (let _70_21366 = (desugar_exp env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Let ((false, (((Microsoft_FStar_Parser_AST.mk_pattern Microsoft_FStar_Parser_AST.PatWild t1.Microsoft_FStar_Parser_AST.range), t1))::[], t2))) top.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Expr))
in (_70_21366, Microsoft_FStar_Absyn_Syntax.Sequence))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_70_21367))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _70_21368))
in (Support.All.pipe_left setpos _70_21369))
end
| Microsoft_FStar_Parser_AST.Let ((is_rec, (pat, _snd)::_tl, body)) -> begin
(let ds_let_rec = (fun ( _43_1278 ) -> (match (()) with
| () -> begin
(let bindings = ((pat, _snd))::_tl
in (let funs = (Support.All.pipe_right bindings (Support.List.map (fun ( _43_1282 ) -> (match (_43_1282) with
| (p, def) -> begin
(match ((is_app_pattern p)) with
| true -> begin
(let _70_21373 = (destruct_app_pattern env top_level p)
in (_70_21373, def))
end
| false -> begin
(match ((Microsoft_FStar_Parser_AST.un_function p def)) with
| Some ((p, def)) -> begin
(let _70_21374 = (destruct_app_pattern env top_level p)
in (_70_21374, def))
end
| _43_1288 -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((id, _43_1293)); Microsoft_FStar_Parser_AST.prange = _43_1290}, t)) -> begin
(match (top_level) with
| true -> begin
(let _70_21377 = (let _70_21376 = (let _70_21375 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in Support.Microsoft.FStar.Util.Inr (_70_21375))
in (_70_21376, [], Some (t)))
in (_70_21377, def))
end
| false -> begin
((Support.Microsoft.FStar.Util.Inl (id), [], Some (t)), def)
end)
end
| Microsoft_FStar_Parser_AST.PatVar ((id, _43_1302)) -> begin
(match (top_level) with
| true -> begin
(let _70_21380 = (let _70_21379 = (let _70_21378 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in Support.Microsoft.FStar.Util.Inr (_70_21378))
in (_70_21379, [], None))
in (_70_21380, def))
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
(let _70_21383 = (Microsoft_FStar_Parser_DesugarEnv.push_rec_binding env (Microsoft_FStar_Parser_DesugarEnv.Binding_let (l)))
in (_70_21383, Support.Microsoft.FStar.Util.Inr (l)))
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
(let _70_21390 = (Support.Microsoft.FStar.Range.union_ranges t.Microsoft_FStar_Parser_AST.range def.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Ascribed ((def, t))) _70_21390 Microsoft_FStar_Parser_AST.Expr))
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
(let _70_21402 = (let _70_21401 = (Microsoft_FStar_Absyn_Util.bvd_to_exp x t)
in (_70_21401, ((pat, None, body))::[]))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _70_21402 None body.Microsoft_FStar_Absyn_Syntax.pos))
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
(let _70_21415 = (let _70_21414 = (let _70_21413 = (desugar_exp env t1)
in (let _70_21412 = (let _70_21411 = (let _70_21407 = (desugar_exp env t2)
in ((Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (true))) None t2.Microsoft_FStar_Parser_AST.range), None, _70_21407))
in (let _70_21410 = (let _70_21409 = (let _70_21408 = (desugar_exp env t3)
in ((Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (false))) None t3.Microsoft_FStar_Parser_AST.range), None, _70_21408))
in (_70_21409)::[])
in (_70_21411)::_70_21410))
in (_70_21413, _70_21412)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _70_21414))
in (Support.All.pipe_left pos _70_21415))
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
(let _70_21418 = (desugar_exp env e)
in Some (_70_21418))
end)
in (let b = (desugar_exp env b)
in (pat, wopt, b)))
end))
end))
in (let _70_21424 = (let _70_21423 = (let _70_21422 = (desugar_exp env e)
in (let _70_21421 = (Support.List.map desugar_branch branches)
in (_70_21422, _70_21421)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _70_21423))
in (Support.All.pipe_left pos _70_21424)))
end
| Microsoft_FStar_Parser_AST.Ascribed ((e, t)) -> begin
(let _70_21430 = (let _70_21429 = (let _70_21428 = (desugar_exp env e)
in (let _70_21427 = (desugar_typ env t)
in (_70_21428, _70_21427, None)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed _70_21429))
in (Support.All.pipe_left pos _70_21430))
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
(let _70_21438 = (qfn fn)
in (_70_21438, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _70_21442 = (let _70_21441 = (let _70_21440 = (let _70_21439 = (Microsoft_FStar_Absyn_Syntax.text_of_lid f)
in (Support.Microsoft.FStar.Util.format1 "Field %s is missing" _70_21439))
in (_70_21440, top.Microsoft_FStar_Parser_AST.range))
in Microsoft_FStar_Absyn_Syntax.Error (_70_21441))
in (raise (_70_21442)))
end
| Some (x) -> begin
(let _70_21443 = (qfn fn)
in (_70_21443, (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Project ((x, f))) x.Microsoft_FStar_Parser_AST.range x.Microsoft_FStar_Parser_AST.level)))
end)
end))))
in (let recterm = (match (eopt) with
| None -> begin
(let _70_21448 = (let _70_21447 = (Support.All.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map (fun ( _43_1469 ) -> (match (_43_1469) with
| (f, _43_1468) -> begin
(let _70_21446 = (let _70_21445 = (get_field None f)
in (Support.All.pipe_left Support.Prims.snd _70_21445))
in (_70_21446, Microsoft_FStar_Parser_AST.Nothing))
end))))
in (record.Microsoft_FStar_Parser_DesugarEnv.constrname, _70_21447))
in Microsoft_FStar_Parser_AST.Construct (_70_21448))
end
| Some (e) -> begin
(let x = (Microsoft_FStar_Absyn_Util.genident (Some (e.Microsoft_FStar_Parser_AST.range)))
in (let xterm = (let _70_21450 = (let _70_21449 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((x)::[]))
in Microsoft_FStar_Parser_AST.Var (_70_21449))
in (Microsoft_FStar_Parser_AST.mk_term _70_21450 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr))
in (let record = (let _70_21453 = (let _70_21452 = (Support.All.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map (fun ( _43_1477 ) -> (match (_43_1477) with
| (f, _43_1476) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _70_21452))
in Microsoft_FStar_Parser_AST.Record (_70_21453))
in Microsoft_FStar_Parser_AST.Let ((false, (((Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatVar ((x, false))) x.Microsoft_FStar_Absyn_Syntax.idRange), e))::[], (Microsoft_FStar_Parser_AST.mk_term record top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))))))
end)
in (let recterm = (Microsoft_FStar_Parser_AST.mk_term recterm top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level)
in (let e = (desugar_exp env recterm)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _43_1500)); Microsoft_FStar_Absyn_Syntax.tk = _43_1497; Microsoft_FStar_Absyn_Syntax.pos = _43_1495; Microsoft_FStar_Absyn_Syntax.fvs = _43_1493; Microsoft_FStar_Absyn_Syntax.uvs = _43_1491}, args)); Microsoft_FStar_Absyn_Syntax.tk = _43_1489; Microsoft_FStar_Absyn_Syntax.pos = _43_1487; Microsoft_FStar_Absyn_Syntax.fvs = _43_1485; Microsoft_FStar_Absyn_Syntax.uvs = _43_1483}, Microsoft_FStar_Absyn_Syntax.Data_app))) -> begin
(let e = (let _70_21463 = (let _70_21462 = (let _70_21461 = (let _70_21460 = (let _70_21459 = (let _70_21458 = (let _70_21457 = (let _70_21456 = (Support.All.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map Support.Prims.fst))
in (record.Microsoft_FStar_Parser_DesugarEnv.typename, _70_21456))
in Microsoft_FStar_Absyn_Syntax.Record_ctor (_70_21457))
in Some (_70_21458))
in (fv, _70_21459))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _70_21460 None e.Microsoft_FStar_Absyn_Syntax.pos))
in (_70_21461, args))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _70_21462))
in (Support.All.pipe_left pos _70_21463))
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
in (let _70_21471 = (let _70_21470 = (let _70_21469 = (let _70_21466 = (Microsoft_FStar_Absyn_Syntax.range_of_lid f)
in (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Record_projector (fn))) fieldname _70_21466))
in (let _70_21468 = (let _70_21467 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_70_21467)::[])
in (_70_21469, _70_21468)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _70_21470))
in (Support.All.pipe_left pos _70_21471))))
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
in (let head_and_args = (fun ( t ) -> (let rec aux = (fun ( args ) ( t ) -> (match ((let _70_21494 = (unparen t)
in _70_21494.Microsoft_FStar_Parser_AST.tm)) with
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
(let _70_21495 = (desugar_exp env t)
in (Support.All.pipe_right _70_21495 Microsoft_FStar_Absyn_Util.b2t))
end))
end
| Microsoft_FStar_Parser_AST.Ensures ((t, lopt)) -> begin
(let t = (label_conjuncts "post-condition" false lopt t)
in (match ((is_type env t)) with
| true -> begin
(desugar_typ env t)
end
| false -> begin
(let _70_21496 = (desugar_exp env t)
in (Support.All.pipe_right _70_21496 Microsoft_FStar_Absyn_Util.b2t))
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
in (let targs = (let _70_21501 = (flatten top)
in (Support.All.pipe_right _70_21501 (Support.List.map (fun ( t ) -> (let _70_21500 = (desugar_typ env t)
in (Microsoft_FStar_Absyn_Syntax.targ _70_21500))))))
in (let tup = (let _70_21502 = (Microsoft_FStar_Absyn_Util.mk_tuple_lid (Support.List.length targs) top.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) _70_21502))
in (Support.All.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))))
end
| false -> begin
(let _70_21508 = (let _70_21507 = (let _70_21506 = (let _70_21505 = (Microsoft_FStar_Parser_AST.term_to_string t1)
in (Support.Microsoft.FStar.Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _70_21505))
in (_70_21506, top.Microsoft_FStar_Parser_AST.range))
in Microsoft_FStar_Absyn_Syntax.Error (_70_21507))
in (raise (_70_21508)))
end)
end
| Microsoft_FStar_Parser_AST.Op (("=!=", args)) -> begin
(desugar_typ env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Op (("~", ((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Op (("==", args))) top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))::[]))) top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match ((op_as_tylid env (Support.List.length args) top.Microsoft_FStar_Parser_AST.range s)) with
| None -> begin
(let _70_21509 = (desugar_exp env top)
in (Support.All.pipe_right _70_21509 Microsoft_FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(let args = (Support.List.map (fun ( t ) -> (let _70_21511 = (desugar_typ_or_exp env t)
in (Support.All.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _70_21511))) args)
in (let _70_21512 = (Microsoft_FStar_Absyn_Util.ftv l Microsoft_FStar_Absyn_Syntax.kun)
in (Microsoft_FStar_Absyn_Util.mk_typ_app _70_21512 args)))
end)
end
| Microsoft_FStar_Parser_AST.Tvar (a) -> begin
(let _70_21513 = (Microsoft_FStar_Parser_DesugarEnv.fail_or2 (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (Support.All.pipe_left setpos _70_21513))
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) when ((Support.List.length l.Microsoft_FStar_Absyn_Syntax.ns) = 0) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env l.Microsoft_FStar_Absyn_Syntax.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _70_21514 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (Support.All.pipe_left setpos _70_21514))
end)
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) -> begin
(let l = (Microsoft_FStar_Absyn_Util.set_lid_range l top.Microsoft_FStar_Parser_AST.range)
in (let _70_21515 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (Support.All.pipe_left setpos _70_21515)))
end
| Microsoft_FStar_Parser_AST.Construct ((l, args)) -> begin
(let t = (let _70_21516 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (Support.All.pipe_left setpos _70_21516))
in (let args = (Support.List.map (fun ( _43_1622 ) -> (match (_43_1622) with
| (t, imp) -> begin
(let _70_21518 = (desugar_typ_or_exp env t)
in (Support.All.pipe_left (arg_withimp_t imp) _70_21518))
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
(let _70_21530 = (let _70_21529 = (let _70_21528 = (let _70_21527 = (Microsoft_FStar_Absyn_Print.pat_to_string q)
in (Support.Microsoft.FStar.Util.format1 "Pattern matching at the type level is not supported; got %s\n" _70_21527))
in (_70_21528, hd.Microsoft_FStar_Parser_AST.prange))
in Microsoft_FStar_Absyn_Syntax.Error (_70_21529))
in (raise (_70_21530)))
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
(let rec aux = (fun ( args ) ( e ) -> (match ((let _70_21535 = (unparen e)
in _70_21535.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((e, arg, imp)) -> begin
(let arg = (let _70_21536 = (desugar_typ_or_exp env arg)
in (Support.All.pipe_left (arg_withimp_t imp) _70_21536))
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
(let _70_21547 = (desugar_exp env f)
in (Support.All.pipe_right _70_21547 Microsoft_FStar_Absyn_Util.b2t))
end)
in (Support.All.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (b, f))))
end))
end)
end
| (Microsoft_FStar_Parser_AST.NamedTyp ((_, t))) | (Microsoft_FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| Microsoft_FStar_Parser_AST.Ascribed ((t, k)) -> begin
(let _70_21555 = (let _70_21554 = (let _70_21553 = (desugar_typ env t)
in (let _70_21552 = (desugar_kind env k)
in (_70_21553, _70_21552)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed' _70_21554))
in (Support.All.pipe_left wpos _70_21555))
end
| Microsoft_FStar_Parser_AST.Sum ((binders, t)) -> begin
(let _43_1739 = (Support.List.fold_left (fun ( _43_1724 ) ( b ) -> (match (_43_1724) with
| (env, tparams, typs) -> begin
(let _43_1728 = (desugar_exp_binder env b)
in (match (_43_1728) with
| (xopt, t) -> begin
(let _43_1734 = (match (xopt) with
| None -> begin
(let _70_21558 = (Microsoft_FStar_Absyn_Util.new_bvd (Some (top.Microsoft_FStar_Parser_AST.range)))
in (env, _70_21558))
end
| Some (x) -> begin
(Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_43_1734) with
| (env, x) -> begin
(let _70_21562 = (let _70_21561 = (let _70_21560 = (let _70_21559 = (Microsoft_FStar_Absyn_Util.close_with_lam tparams t)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _70_21559))
in (_70_21560)::[])
in (Support.List.append typs _70_21561))
in (env, (Support.List.append tparams (((Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)), None))::[])), _70_21562))
end))
end))
end)) (env, [], []) (Support.List.append binders (((Microsoft_FStar_Parser_AST.mk_binder (Microsoft_FStar_Parser_AST.NoName (t)) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Type None))::[])))
in (match (_43_1739) with
| (env, _43_1737, targs) -> begin
(let tup = (let _70_21563 = (Microsoft_FStar_Absyn_Util.mk_dtuple_lid (Support.List.length targs) top.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) _70_21563))
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
(match ((let _70_21575 = (unparen arg)
in _70_21575.Microsoft_FStar_Parser_AST.tm)) with
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
| Microsoft_FStar_Parser_AST.Name (tot) when (((tot.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "Tot") && (not ((Microsoft_FStar_Parser_DesugarEnv.is_effect_name env Microsoft_FStar_Absyn_Const.effect_Tot_lid)))) && (let _70_21576 = (Microsoft_FStar_Parser_DesugarEnv.current_module env)
in (Microsoft_FStar_Absyn_Syntax.lid_equals _70_21576 Microsoft_FStar_Absyn_Const.prims_lid))) -> begin
(let args = (Support.List.map (fun ( _43_1805 ) -> (match (_43_1805) with
| (t, imp) -> begin
(let _70_21578 = (desugar_typ_or_exp env t)
in (Support.All.pipe_left (arg_withimp_t imp) _70_21578))
end)) args)
in (let _70_21579 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.effect_Tot_lid Microsoft_FStar_Absyn_Syntax.kun)
in (Microsoft_FStar_Absyn_Util.mk_typ_app _70_21579 args)))
end
| _43_1808 -> begin
(desugar_typ env t)
end)
end)))
in (let t = (pre_process_comp_typ t)
in (let _43_1812 = (Microsoft_FStar_Absyn_Util.head_and_args t)
in (match (_43_1812) with
| (head, args) -> begin
(match ((let _70_21581 = (let _70_21580 = (Microsoft_FStar_Absyn_Util.compress_typ head)
in _70_21580.Microsoft_FStar_Absyn_Syntax.n)
in (_70_21581, args))) with
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
(let _70_21585 = (let _70_21584 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "%s is not an effect" _70_21584))
in (fail _70_21585))
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
(let _70_21587 = (let _70_21586 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "%s is not an effect" _70_21586))
in (fail _70_21587))
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
(match ((let _70_21599 = (Microsoft_FStar_Parser_DesugarEnv.qualify_lid env l)
in (Microsoft_FStar_Parser_DesugarEnv.find_kind_abbrev env _70_21599))) with
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
(let _70_21610 = (let _70_21609 = (let _70_21608 = (desugar_kind env k)
in ((Support.List.rev bs), _70_21608))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _70_21609))
in (Support.All.pipe_left pos _70_21610))
end
| hd::tl -> begin
(let _43_1935 = (let _70_21612 = (let _70_21611 = (Microsoft_FStar_Parser_DesugarEnv.default_ml env)
in (desugar_binder _70_21611 hd))
in (Support.All.pipe_right _70_21612 (as_binder env hd.Microsoft_FStar_Parser_AST.aqual)))
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
in (let _70_21614 = (desugar_typ_or_exp env t)
in (_70_21614, qual)))
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
(let pats = (Support.List.map (fun ( e ) -> (let _70_21645 = (desugar_typ_or_exp env e)
in (Support.All.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _70_21645))) pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _43_1989 -> begin
(let _70_21646 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
in (Support.All.pipe_left setpos _70_21646))
end)
in (let body = (let _70_21652 = (let _70_21651 = (let _70_21650 = (let _70_21649 = (Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_70_21649)::[])
in (_70_21650, body))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_21651))
in (Support.All.pipe_left pos _70_21652))
in (let _70_21657 = (let _70_21656 = (let _70_21653 = (Microsoft_FStar_Absyn_Util.set_lid_range qt b.Microsoft_FStar_Parser_AST.brange)
in (Microsoft_FStar_Absyn_Util.ftv _70_21653 Microsoft_FStar_Absyn_Syntax.kun))
in (let _70_21655 = (let _70_21654 = (Microsoft_FStar_Absyn_Syntax.targ body)
in (_70_21654)::[])
in (Microsoft_FStar_Absyn_Util.mk_typ_app _70_21656 _70_21655)))
in (Support.All.pipe_left setpos _70_21657))))))
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _43_1999 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_43_1999) with
| (env, x) -> begin
(let pats = (Support.List.map (fun ( e ) -> (let _70_21659 = (desugar_typ_or_exp env e)
in (Support.All.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _70_21659))) pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _43_2005 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
end)
in (let body = (let _70_21665 = (let _70_21664 = (let _70_21663 = (let _70_21662 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_70_21662)::[])
in (_70_21663, body))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_21664))
in (Support.All.pipe_left pos _70_21665))
in (let _70_21670 = (let _70_21669 = (let _70_21666 = (Microsoft_FStar_Absyn_Util.set_lid_range q b.Microsoft_FStar_Parser_AST.brange)
in (Microsoft_FStar_Absyn_Util.ftv _70_21666 Microsoft_FStar_Absyn_Syntax.kun))
in (let _70_21668 = (let _70_21667 = (Microsoft_FStar_Absyn_Syntax.targ body)
in (_70_21667)::[])
in (Microsoft_FStar_Absyn_Util.mk_typ_app _70_21669 _70_21668)))
in (Support.All.pipe_left setpos _70_21670))))))
end))
end
| _43_2009 -> begin
(Support.All.failwith "impossible")
end)))
in (let push_quant = (fun ( q ) ( binders ) ( pats ) ( body ) -> (match (binders) with
| b::b'::_rest -> begin
(let rest = (b')::_rest
in (let body = (let _70_21685 = (q (rest, pats, body))
in (let _70_21684 = (Support.Microsoft.FStar.Range.union_ranges b'.Microsoft_FStar_Parser_AST.brange body.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_AST.mk_term _70_21685 _70_21684 Microsoft_FStar_Parser_AST.Formula)))
in (let _70_21686 = (q ((b)::[], [], body))
in (Microsoft_FStar_Parser_AST.mk_term _70_21686 f.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Formula))))
end
| _43_2023 -> begin
(Support.All.failwith "impossible")
end))
in (match ((let _70_21687 = (unparen f)
in _70_21687.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Labeled ((f, l, p)) -> begin
(let f = (desugar_formula env f)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((f, l, Microsoft_FStar_Absyn_Syntax.dummyRange, p)))))
end
| Microsoft_FStar_Parser_AST.Op (("==", hd::_args)) -> begin
(let args = (hd)::_args
in (let args = (Support.List.map (fun ( t ) -> (let _70_21689 = (desugar_typ_or_exp env t)
in (Support.All.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _70_21689))) args)
in (let eq = (match ((is_type env hd)) with
| true -> begin
(let _70_21690 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.eqT_lid f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _70_21690 Microsoft_FStar_Absyn_Syntax.kun))
end
| false -> begin
(let _70_21691 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.eq2_lid f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _70_21691 Microsoft_FStar_Absyn_Syntax.kun))
end)
in (Microsoft_FStar_Absyn_Util.mk_typ_app eq args))))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match (((connective s), args)) with
| (Some (conn), _43_2049::_43_2047::[]) -> begin
(let _70_21696 = (let _70_21692 = (Microsoft_FStar_Absyn_Util.set_lid_range conn f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _70_21692 Microsoft_FStar_Absyn_Syntax.kun))
in (let _70_21695 = (Support.List.map (fun ( x ) -> (let _70_21694 = (desugar_formula env x)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _70_21694))) args)
in (Microsoft_FStar_Absyn_Util.mk_typ_app _70_21696 _70_21695)))
end
| _43_2054 -> begin
(match ((is_type env f)) with
| true -> begin
(desugar_typ env f)
end
| false -> begin
(let _70_21697 = (desugar_exp env f)
in (Support.All.pipe_right _70_21697 Microsoft_FStar_Absyn_Util.b2t))
end)
end)
end
| Microsoft_FStar_Parser_AST.If ((f1, f2, f3)) -> begin
(let _70_21702 = (let _70_21698 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.ite_lid f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _70_21698 Microsoft_FStar_Absyn_Syntax.kun))
in (let _70_21701 = (Support.List.map (fun ( x ) -> (match ((desugar_typ_or_exp env x)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| Support.Microsoft.FStar.Util.Inr (v) -> begin
(let _70_21700 = (Microsoft_FStar_Absyn_Util.b2t v)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _70_21700))
end)) ((f1)::(f2)::(f3)::[]))
in (Microsoft_FStar_Absyn_Util.mk_typ_app _70_21702 _70_21701)))
end
| Microsoft_FStar_Parser_AST.QForall ((_1::_2::_3, pats, body)) -> begin
(let binders = (_1)::(_2)::_3
in (let _70_21704 = (push_quant (fun ( x ) -> Microsoft_FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _70_21704)))
end
| Microsoft_FStar_Parser_AST.QExists ((_1::_2::_3, pats, body)) -> begin
(let binders = (_1)::(_2)::_3
in (let _70_21706 = (push_quant (fun ( x ) -> Microsoft_FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _70_21706)))
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
(let _70_21707 = (desugar_exp env f)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Util.b2t _70_21707))
end)
end)))))))
and desugar_formula = (fun ( env ) ( t ) -> (desugar_formula' (let _43_2105 = env
in {Microsoft_FStar_Parser_DesugarEnv.curmodule = _43_2105.Microsoft_FStar_Parser_DesugarEnv.curmodule; Microsoft_FStar_Parser_DesugarEnv.modules = _43_2105.Microsoft_FStar_Parser_DesugarEnv.modules; Microsoft_FStar_Parser_DesugarEnv.open_namespaces = _43_2105.Microsoft_FStar_Parser_DesugarEnv.open_namespaces; Microsoft_FStar_Parser_DesugarEnv.sigaccum = _43_2105.Microsoft_FStar_Parser_DesugarEnv.sigaccum; Microsoft_FStar_Parser_DesugarEnv.localbindings = _43_2105.Microsoft_FStar_Parser_DesugarEnv.localbindings; Microsoft_FStar_Parser_DesugarEnv.recbindings = _43_2105.Microsoft_FStar_Parser_DesugarEnv.recbindings; Microsoft_FStar_Parser_DesugarEnv.phase = Microsoft_FStar_Parser_AST.Formula; Microsoft_FStar_Parser_DesugarEnv.sigmap = _43_2105.Microsoft_FStar_Parser_DesugarEnv.sigmap; Microsoft_FStar_Parser_DesugarEnv.default_result_effect = _43_2105.Microsoft_FStar_Parser_DesugarEnv.default_result_effect; Microsoft_FStar_Parser_DesugarEnv.iface = _43_2105.Microsoft_FStar_Parser_DesugarEnv.iface; Microsoft_FStar_Parser_DesugarEnv.admitted_iface = _43_2105.Microsoft_FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder = (fun ( env ) ( b ) -> (match ((is_type_binder env b)) with
| true -> begin
(let _70_21712 = (desugar_type_binder env b)
in Support.Microsoft.FStar.Util.Inl (_70_21712))
end
| false -> begin
(let _70_21713 = (desugar_exp_binder env b)
in Support.Microsoft.FStar.Util.Inr (_70_21713))
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
(let _70_21720 = (desugar_typ env t)
in (Some (x), _70_21720))
end
| Microsoft_FStar_Parser_AST.TVariable (t) -> begin
(let _70_21721 = (Microsoft_FStar_Parser_DesugarEnv.fail_or2 (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in (None, _70_21721))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(let _70_21722 = (desugar_typ env t)
in (None, _70_21722))
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
(let _70_21727 = (desugar_kind env t)
in (Some (x), _70_21727))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(let _70_21728 = (desugar_kind env t)
in (None, _70_21728))
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
in (let _70_21737 = (aux tps k)
in (Support.All.pipe_right _70_21737 Microsoft_FStar_Absyn_Util.name_binders))))

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
in (let binders = (let _70_21758 = (let _70_21757 = (let _70_21756 = (let _70_21755 = (let _70_21754 = (Microsoft_FStar_Absyn_Util.ftv t Microsoft_FStar_Absyn_Syntax.kun)
in (let _70_21753 = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (_70_21754, _70_21753)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' _70_21755 None p))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.null_v_binder _70_21756))
in (_70_21757)::[])
in (Support.List.append imp_binders _70_21758))
in (let disc_type = (let _70_21761 = (let _70_21760 = (let _70_21759 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.bool_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.total_comp _70_21759 p))
in (binders, _70_21760))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _70_21761 None p))
in (Support.All.pipe_right datas (Support.List.map (fun ( d ) -> (let disc_name = (Microsoft_FStar_Absyn_Util.mk_discriminator d)
in (let _70_21765 = (let _70_21764 = (quals ((Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Discriminator (d))::[]))
in (let _70_21763 = (Microsoft_FStar_Absyn_Syntax.range_of_lid disc_name)
in (disc_name, disc_type, _70_21764, _70_21763)))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_70_21765)))))))))))))

let mk_indexed_projectors = (fun ( fvq ) ( refine_domain ) ( env ) ( _43_2212 ) ( lid ) ( formals ) ( t ) -> (match (_43_2212) with
| (tc, tps, k) -> begin
(let binders = (gather_tc_binders tps k)
in (let p = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (let pos = (fun ( q ) -> (Microsoft_FStar_Absyn_Syntax.withinfo q None p))
in (let projectee = (let _70_21776 = (Microsoft_FStar_Absyn_Syntax.mk_ident ("projectee", p))
in (let _70_21775 = (Microsoft_FStar_Absyn_Util.genident (Some (p)))
in {Microsoft_FStar_Absyn_Syntax.ppname = _70_21776; Microsoft_FStar_Absyn_Syntax.realname = _70_21775}))
in (let arg_exp = (Microsoft_FStar_Absyn_Util.bvd_to_exp projectee Microsoft_FStar_Absyn_Syntax.tun)
in (let arg_binder = (let arg_typ = (let _70_21779 = (let _70_21778 = (Microsoft_FStar_Absyn_Util.ftv tc Microsoft_FStar_Absyn_Syntax.kun)
in (let _70_21777 = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (_70_21778, _70_21777)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' _70_21779 None p))
in (match ((not (refine_domain))) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end
| false -> begin
(let disc_name = (Microsoft_FStar_Absyn_Util.mk_discriminator lid)
in (let x = (Microsoft_FStar_Absyn_Util.gen_bvar arg_typ)
in (let _70_21789 = (let _70_21788 = (let _70_21787 = (let _70_21786 = (let _70_21785 = (let _70_21784 = (let _70_21783 = (Microsoft_FStar_Absyn_Util.fvar None disc_name p)
in (let _70_21782 = (let _70_21781 = (let _70_21780 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.varg _70_21780))
in (_70_21781)::[])
in (_70_21783, _70_21782)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _70_21784 None p))
in (Microsoft_FStar_Absyn_Util.b2t _70_21785))
in (x, _70_21786))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _70_21787 None p))
in (Support.All.pipe_left (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s projectee) _70_21788))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.v_binder _70_21789))))
end))
in (let imp_binders = (Support.All.pipe_right binders (Support.List.map (fun ( _43_2229 ) -> (match (_43_2229) with
| (x, _43_2228) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end))))
in (let binders = (Support.List.append imp_binders ((arg_binder)::[]))
in (let arg = (Microsoft_FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (let subst = (let _70_21799 = (Support.All.pipe_right formals (Support.List.mapi (fun ( i ) ( f ) -> (match ((Support.Prims.fst f)) with
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
(let proj = (let _70_21795 = (let _70_21794 = (Microsoft_FStar_Absyn_Util.ftv field_name Microsoft_FStar_Absyn_Syntax.kun)
in (_70_21794, (arg)::[]))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_21795 None p))
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
(let proj = (let _70_21798 = (let _70_21797 = (Microsoft_FStar_Absyn_Util.fvar None field_name p)
in (_70_21797, (arg)::[]))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _70_21798 None p))
in (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, proj)))::[])
end))
end)
end))))
in (Support.All.pipe_right _70_21799 Support.List.flatten))
in (let ntps = (Support.List.length tps)
in (let _70_21837 = (Support.All.pipe_right formals (Support.List.mapi (fun ( i ) ( ax ) -> (match ((Support.Prims.fst ax)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _43_2274 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_43_2274) with
| (field_name, _43_2273) -> begin
(let kk = (let _70_21803 = (let _70_21802 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (binders, _70_21802))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _70_21803 p))
in (let _70_21806 = (let _70_21805 = (let _70_21804 = (Microsoft_FStar_Absyn_Syntax.range_of_lid field_name)
in (field_name, [], kk, [], [], (Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Projector ((lid, Support.Microsoft.FStar.Util.Inl (a.Microsoft_FStar_Absyn_Syntax.v))))::[], _70_21804))
in Microsoft_FStar_Absyn_Syntax.Sig_tycon (_70_21805))
in (_70_21806)::[]))
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _43_2281 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_43_2281) with
| (field_name, _43_2280) -> begin
(let t = (let _70_21809 = (let _70_21808 = (let _70_21807 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Absyn_Util.total_comp _70_21807 p))
in (binders, _70_21808))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _70_21809 None p))
in (let quals = (fun ( q ) -> (match (((not (env.Microsoft_FStar_Parser_DesugarEnv.iface)) || env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.Assumption)::q
end
| false -> begin
q
end))
in (let quals = (quals ((Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Projector ((lid, Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.v))))::[]))
in (let impl = (match ((((let _70_21812 = (Microsoft_FStar_Parser_DesugarEnv.current_module env)
in (Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.prims_lid _70_21812)) || (fvq <> Microsoft_FStar_Absyn_Syntax.Data_ctor)) || (Support.ST.read Microsoft_FStar_Options.__temp_no_proj))) with
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
in (let arg_pats = (let _70_21827 = (Support.All.pipe_right formals (Support.List.mapi (fun ( j ) ( by ) -> (match (by) with
| (Support.Microsoft.FStar.Util.Inl (_43_2296), imp) -> begin
(match ((j < ntps)) with
| true -> begin
[]
end
| false -> begin
(let _70_21820 = (let _70_21819 = (let _70_21818 = (let _70_21817 = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.kun)
in Microsoft_FStar_Absyn_Syntax.Pat_tvar (_70_21817))
in (pos _70_21818))
in (_70_21819, (as_imp imp)))
in (_70_21820)::[])
end)
end
| (Support.Microsoft.FStar.Util.Inr (_43_2301), imp) -> begin
(match ((i = j)) with
| true -> begin
(let _70_21822 = (let _70_21821 = (pos (Microsoft_FStar_Absyn_Syntax.Pat_var (projection)))
in (_70_21821, (as_imp imp)))
in (_70_21822)::[])
end
| false -> begin
(let _70_21826 = (let _70_21825 = (let _70_21824 = (let _70_21823 = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in Microsoft_FStar_Absyn_Syntax.Pat_wild (_70_21823))
in (pos _70_21824))
in (_70_21825, (as_imp imp)))
in (_70_21826)::[])
end)
end))))
in (Support.All.pipe_right _70_21827 Support.List.flatten))
in (let pat = (let _70_21832 = (let _70_21830 = (let _70_21829 = (let _70_21828 = (Microsoft_FStar_Absyn_Util.fv lid)
in (_70_21828, Some (fvq), arg_pats))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_70_21829))
in (Support.All.pipe_right _70_21830 pos))
in (let _70_21831 = (Microsoft_FStar_Absyn_Util.bvar_to_exp projection)
in (_70_21832, None, _70_21831)))
in (let body = (Microsoft_FStar_Absyn_Syntax.mk_Exp_match (arg_exp, (pat)::[]) None p)
in (let imp = (let _70_21833 = (Microsoft_FStar_Absyn_Syntax.range_of_lid field_name)
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (binders, body) None _70_21833))
in (let lb = {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (field_name); Microsoft_FStar_Absyn_Syntax.lbtyp = Microsoft_FStar_Absyn_Syntax.tun; Microsoft_FStar_Absyn_Syntax.lbeff = Microsoft_FStar_Absyn_Const.effect_Tot_lid; Microsoft_FStar_Absyn_Syntax.lbdef = imp}
in (Microsoft_FStar_Absyn_Syntax.Sig_let (((false, (lb)::[]), p, [], quals)))::[])))))))
end)
in (let _70_21836 = (let _70_21835 = (let _70_21834 = (Microsoft_FStar_Absyn_Syntax.range_of_lid field_name)
in (field_name, t, quals, _70_21834))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_70_21835))
in (_70_21836)::impl)))))
end))
end))))
in (Support.All.pipe_right _70_21837 Support.List.flatten)))))))))))))
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
(let _70_21857 = (let _70_21856 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((x)::[]))
in Microsoft_FStar_Parser_AST.Var (_70_21856))
in (Microsoft_FStar_Parser_AST.mk_term _70_21857 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr))
end
| (Microsoft_FStar_Parser_AST.TAnnotated ((a, _))) | (Microsoft_FStar_Parser_AST.TVariable (a)) -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Tvar (a)) a.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type)
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
t
end))
in (let tot = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.effect_Tot_lid)) rng Microsoft_FStar_Parser_AST.Expr)
in (let with_constructor_effect = (fun ( t ) -> (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.App ((tot, t, Microsoft_FStar_Parser_AST.Nothing))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level))
in (let apply_binders = (fun ( t ) ( binders ) -> (Support.List.fold_left (fun ( out ) ( b ) -> (let _70_21868 = (let _70_21867 = (let _70_21866 = (binder_to_term b)
in (out, _70_21866, Microsoft_FStar_Parser_AST.Nothing))
in Microsoft_FStar_Parser_AST.App (_70_21867))
in (Microsoft_FStar_Parser_AST.mk_term _70_21868 out.Microsoft_FStar_Parser_AST.range out.Microsoft_FStar_Parser_AST.level))) t binders))
in (let tycon_record_as_variant = (fun ( _43_20 ) -> (match (_43_20) with
| Microsoft_FStar_Parser_AST.TyconRecord ((id, parms, kopt, fields)) -> begin
(let constrName = (Microsoft_FStar_Absyn_Syntax.mk_ident ((Support.String.strcat "Mk" id.Microsoft_FStar_Absyn_Syntax.idText), id.Microsoft_FStar_Absyn_Syntax.idRange))
in (let mfields = (Support.List.map (fun ( _43_2429 ) -> (match (_43_2429) with
| (x, t) -> begin
(let _70_21874 = (let _70_21873 = (let _70_21872 = (Microsoft_FStar_Absyn_Util.mangle_field_name x)
in (_70_21872, t))
in Microsoft_FStar_Parser_AST.Annotated (_70_21873))
in (Microsoft_FStar_Parser_AST.mk_binder _70_21874 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr None))
end)) fields)
in (let result = (let _70_21877 = (let _70_21876 = (let _70_21875 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id)::[]))
in Microsoft_FStar_Parser_AST.Var (_70_21875))
in (Microsoft_FStar_Parser_AST.mk_term _70_21876 id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type))
in (apply_binders _70_21877 parms))
in (let constrTyp = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type)
in (let _70_21879 = (Support.All.pipe_right fields (Support.List.map (fun ( _43_2436 ) -> (match (_43_2436) with
| (x, _43_2435) -> begin
(Microsoft_FStar_Parser_DesugarEnv.qualify env x)
end))))
in (Microsoft_FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _70_21879))))))
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
in (let tconstr = (let _70_21890 = (let _70_21889 = (let _70_21888 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id)::[]))
in Microsoft_FStar_Parser_AST.Var (_70_21888))
in (Microsoft_FStar_Parser_AST.mk_term _70_21889 id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type))
in (apply_binders _70_21890 binders))
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
in (let _70_21902 = (let _70_21901 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (let _70_21900 = (Support.All.pipe_right quals (Support.List.filter (fun ( _43_25 ) -> (match (_43_25) with
| Microsoft_FStar_Absyn_Syntax.Effect -> begin
false
end
| _43_2520 -> begin
true
end))))
in (_70_21901, typars, c, _70_21900, rng)))
in Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_70_21902)))
end
| false -> begin
(let t = (desugar_typ env' t)
in (let _70_21904 = (let _70_21903 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (_70_21903, typars, k, t, quals, rng))
in Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_70_21904)))
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
in (let _43_2653 = (let _70_21923 = (Support.All.pipe_right constrs (Support.List.map (fun ( _43_2631 ) -> (match (_43_2631) with
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
in (let t = (let _70_21915 = (Microsoft_FStar_Parser_DesugarEnv.default_total env_tps)
in (let _70_21914 = (close env_tps t)
in (desugar_typ _70_21915 _70_21914)))
in (let name = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (let quals = (Support.All.pipe_right tags (Support.List.collect (fun ( _43_26 ) -> (match (_43_26) with
| Microsoft_FStar_Absyn_Syntax.RecordType (fns) -> begin
(Microsoft_FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _43_2645 -> begin
[]
end))))
in (let _70_21922 = (let _70_21921 = (let _70_21920 = (let _70_21919 = (let _70_21918 = (Support.List.map (fun ( _43_2650 ) -> (match (_43_2650) with
| (x, _43_2649) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end)) tps)
in (Microsoft_FStar_Absyn_Util.close_typ _70_21918 t))
in (Support.All.pipe_right _70_21919 Microsoft_FStar_Absyn_Util.name_function_binders))
in (name, _70_21920, tycon, quals, mutuals, rng))
in Microsoft_FStar_Absyn_Syntax.Sig_datacon (_70_21921))
in (name, _70_21922))))))
end))))
in (Support.All.pipe_left Support.List.split _70_21923))
in (match (_43_2653) with
| (constrNames, constrs) -> begin
(Microsoft_FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, constrNames, tags, rng)))::constrs
end))))
end
| _43_2655 -> begin
(Support.All.failwith "impossible")
end))))
in (let bundle = (let _70_21925 = (let _70_21924 = (Support.List.collect Microsoft_FStar_Absyn_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _70_21924, rng))
in Microsoft_FStar_Absyn_Syntax.Sig_bundle (_70_21925))
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
(let _70_21934 = (let _70_21933 = (Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_70_21933)::binders)
in (env, _70_21934))
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _43_2699 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_43_2699) with
| (env, x) -> begin
(let _70_21936 = (let _70_21935 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_70_21935)::binders)
in (env, _70_21936))
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
(match ((let _70_21942 = (let _70_21941 = (desugar_exp_maybe_top true env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Let ((isrec, lets, (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Const (Microsoft_FStar_Absyn_Syntax.Const_unit)) d.Microsoft_FStar_Parser_AST.drange Microsoft_FStar_Parser_AST.Expr)))) d.Microsoft_FStar_Parser_AST.drange Microsoft_FStar_Parser_AST.Expr))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Util.compress_exp _70_21941))
in _70_21942.Microsoft_FStar_Absyn_Syntax.n)) with
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
in (let _70_21948 = (let _70_21947 = (let _70_21946 = (let _70_21945 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (_70_21945, f, (Microsoft_FStar_Absyn_Syntax.Assumption)::[], d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Sig_assume (_70_21946))
in (_70_21947)::[])
in (env, _70_21948)))
end
| Microsoft_FStar_Parser_AST.Val ((quals, id, t)) -> begin
(let t = (let _70_21949 = (close_fun env t)
in (desugar_typ env _70_21949))
in (let quals = (match ((env.Microsoft_FStar_Parser_DesugarEnv.iface && env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.Assumption)::quals
end
| false -> begin
quals
end)
in (let se = (let _70_21951 = (let _70_21950 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (_70_21950, t, quals, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_70_21951))
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
in (let t = (let _70_21956 = (let _70_21955 = (let _70_21952 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_70_21952)::[])
in (let _70_21954 = (let _70_21953 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) Microsoft_FStar_Absyn_Const.exn_lid)
in (Microsoft_FStar_Absyn_Syntax.mk_Total _70_21953))
in (_70_21955, _70_21954)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _70_21956 None d.Microsoft_FStar_Parser_AST.drange))
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
(let _70_21961 = (let _70_21960 = (let _70_21959 = (let _70_21958 = (let _70_21957 = (Microsoft_FStar_Absyn_Print.sli eff.Microsoft_FStar_Absyn_Syntax.v)
in (Support.String.strcat "Effect " _70_21957))
in (Support.String.strcat _70_21958 " not found"))
in (_70_21959, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Error (_70_21960))
in (raise (_70_21961)))
end
| Some (ed) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.subst_of_list ed.Microsoft_FStar_Absyn_Syntax.binders args)
in (let sub = (Microsoft_FStar_Absyn_Util.subst_typ subst)
in (let ed = (let _70_21978 = (Microsoft_FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _70_21977 = (Microsoft_FStar_Absyn_Util.subst_kind subst ed.Microsoft_FStar_Absyn_Syntax.signature)
in (let _70_21976 = (sub ed.Microsoft_FStar_Absyn_Syntax.ret)
in (let _70_21975 = (sub ed.Microsoft_FStar_Absyn_Syntax.bind_wp)
in (let _70_21974 = (sub ed.Microsoft_FStar_Absyn_Syntax.bind_wlp)
in (let _70_21973 = (sub ed.Microsoft_FStar_Absyn_Syntax.if_then_else)
in (let _70_21972 = (sub ed.Microsoft_FStar_Absyn_Syntax.ite_wp)
in (let _70_21971 = (sub ed.Microsoft_FStar_Absyn_Syntax.ite_wlp)
in (let _70_21970 = (sub ed.Microsoft_FStar_Absyn_Syntax.wp_binop)
in (let _70_21969 = (sub ed.Microsoft_FStar_Absyn_Syntax.wp_as_type)
in (let _70_21968 = (sub ed.Microsoft_FStar_Absyn_Syntax.close_wp)
in (let _70_21967 = (sub ed.Microsoft_FStar_Absyn_Syntax.close_wp_t)
in (let _70_21966 = (sub ed.Microsoft_FStar_Absyn_Syntax.assert_p)
in (let _70_21965 = (sub ed.Microsoft_FStar_Absyn_Syntax.assume_p)
in (let _70_21964 = (sub ed.Microsoft_FStar_Absyn_Syntax.null_wp)
in (let _70_21963 = (sub ed.Microsoft_FStar_Absyn_Syntax.trivial)
in {Microsoft_FStar_Absyn_Syntax.mname = _70_21978; Microsoft_FStar_Absyn_Syntax.binders = binders; Microsoft_FStar_Absyn_Syntax.qualifiers = quals; Microsoft_FStar_Absyn_Syntax.signature = _70_21977; Microsoft_FStar_Absyn_Syntax.ret = _70_21976; Microsoft_FStar_Absyn_Syntax.bind_wp = _70_21975; Microsoft_FStar_Absyn_Syntax.bind_wlp = _70_21974; Microsoft_FStar_Absyn_Syntax.if_then_else = _70_21973; Microsoft_FStar_Absyn_Syntax.ite_wp = _70_21972; Microsoft_FStar_Absyn_Syntax.ite_wlp = _70_21971; Microsoft_FStar_Absyn_Syntax.wp_binop = _70_21970; Microsoft_FStar_Absyn_Syntax.wp_as_type = _70_21969; Microsoft_FStar_Absyn_Syntax.close_wp = _70_21968; Microsoft_FStar_Absyn_Syntax.close_wp_t = _70_21967; Microsoft_FStar_Absyn_Syntax.assert_p = _70_21966; Microsoft_FStar_Absyn_Syntax.assume_p = _70_21965; Microsoft_FStar_Absyn_Syntax.null_wp = _70_21964; Microsoft_FStar_Absyn_Syntax.trivial = _70_21963}))))))))))))))))
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ed, d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)
end
| _43_2841 -> begin
(let _70_21982 = (let _70_21981 = (let _70_21980 = (let _70_21979 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (Support.String.strcat _70_21979 " is not an effect"))
in (_70_21980, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Error (_70_21981))
in (raise (_70_21982)))
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
(let _70_21986 = (let _70_21985 = (Support.List.hd ses)
in (_70_21985)::out)
in (env, _70_21986))
end))
end)) (env, [])))
in (match (_43_2866) with
| (env, decls) -> begin
(let decls = (Support.List.rev decls)
in (let lookup = (fun ( s ) -> (match ((let _70_21990 = (let _70_21989 = (Microsoft_FStar_Absyn_Syntax.mk_ident (s, d.Microsoft_FStar_Parser_AST.drange))
in (Microsoft_FStar_Parser_DesugarEnv.qualify env _70_21989))
in (Microsoft_FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _70_21990))) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat (Support.String.strcat (Support.String.strcat "Monad " eff_name.Microsoft_FStar_Absyn_Syntax.idText) " expects definition of ") s), d.Microsoft_FStar_Parser_AST.drange))))
end
| Some (t) -> begin
t
end))
in (let ed = (let _70_22005 = (Microsoft_FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _70_22004 = (lookup "return")
in (let _70_22003 = (lookup "bind_wp")
in (let _70_22002 = (lookup "bind_wlp")
in (let _70_22001 = (lookup "if_then_else")
in (let _70_22000 = (lookup "ite_wp")
in (let _70_21999 = (lookup "ite_wlp")
in (let _70_21998 = (lookup "wp_binop")
in (let _70_21997 = (lookup "wp_as_type")
in (let _70_21996 = (lookup "close_wp")
in (let _70_21995 = (lookup "close_wp_t")
in (let _70_21994 = (lookup "assert_p")
in (let _70_21993 = (lookup "assume_p")
in (let _70_21992 = (lookup "null_wp")
in (let _70_21991 = (lookup "trivial")
in {Microsoft_FStar_Absyn_Syntax.mname = _70_22005; Microsoft_FStar_Absyn_Syntax.binders = binders; Microsoft_FStar_Absyn_Syntax.qualifiers = quals; Microsoft_FStar_Absyn_Syntax.signature = eff_k; Microsoft_FStar_Absyn_Syntax.ret = _70_22004; Microsoft_FStar_Absyn_Syntax.bind_wp = _70_22003; Microsoft_FStar_Absyn_Syntax.bind_wlp = _70_22002; Microsoft_FStar_Absyn_Syntax.if_then_else = _70_22001; Microsoft_FStar_Absyn_Syntax.ite_wp = _70_22000; Microsoft_FStar_Absyn_Syntax.ite_wlp = _70_21999; Microsoft_FStar_Absyn_Syntax.wp_binop = _70_21998; Microsoft_FStar_Absyn_Syntax.wp_as_type = _70_21997; Microsoft_FStar_Absyn_Syntax.close_wp = _70_21996; Microsoft_FStar_Absyn_Syntax.close_wp_t = _70_21995; Microsoft_FStar_Absyn_Syntax.assert_p = _70_21994; Microsoft_FStar_Absyn_Syntax.assume_p = _70_21993; Microsoft_FStar_Absyn_Syntax.null_wp = _70_21992; Microsoft_FStar_Absyn_Syntax.trivial = _70_21991})))))))))))))))
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ed, d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)))
end))))
end
| Microsoft_FStar_Parser_AST.SubEffect (l) -> begin
(let lookup = (fun ( l ) -> (match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_effect_name env l)) with
| None -> begin
(let _70_22012 = (let _70_22011 = (let _70_22010 = (let _70_22009 = (let _70_22008 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.String.strcat "Effect name " _70_22008))
in (Support.String.strcat _70_22009 " not found"))
in (_70_22010, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Error (_70_22011))
in (raise (_70_22012)))
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
(let _70_22029 = (let _70_22028 = (let _70_22026 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids mname.Microsoft_FStar_Absyn_Syntax.ns)
in Microsoft_FStar_Parser_AST.Open (_70_22026))
in (let _70_22027 = (Microsoft_FStar_Absyn_Syntax.range_of_lid mname)
in (Microsoft_FStar_Parser_AST.mk_decl _70_22028 _70_22027)))
in (_70_22029)::d)
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
(let _70_22031 = (Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _70_22030 = (open_ns mname decls)
in (_70_22031, mname, _70_22030, true)))
end
| Microsoft_FStar_Parser_AST.Module ((mname, decls)) -> begin
(let _70_22033 = (Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _70_22032 = (open_ns mname decls)
in (_70_22033, mname, _70_22032, false)))
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
(let _70_22040 = (let _70_22039 = (let _70_22038 = (Support.ST.read Microsoft_FStar_Options.admit_fsi)
in (Support.Microsoft.FStar.Util.for_some (fun ( m ) -> (m = mname.Microsoft_FStar_Absyn_Syntax.str)) _70_22038))
in (mname, decls, _70_22039))
in Microsoft_FStar_Parser_AST.Interface (_70_22040))
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
(let _70_22045 = (Microsoft_FStar_Absyn_Print.modul_to_string modul)
in (Support.Microsoft.FStar.Util.fprint1 "%s\n" _70_22045))
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




