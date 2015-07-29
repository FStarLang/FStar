
let as_imp = (fun ( _41_1  :  Microsoft_FStar_Parser_AST.imp ) -> (match (_41_1) with
| (Microsoft_FStar_Parser_AST.Hash) | (Microsoft_FStar_Parser_AST.FsTypApp) -> begin
Some (Microsoft_FStar_Absyn_Syntax.Implicit)
end
| _ -> begin
None
end))

let arg_withimp_e = (fun ( imp  :  Microsoft_FStar_Parser_AST.imp ) ( t  :  'u41u2928 ) -> (t, (as_imp imp)))

let arg_withimp_t = (fun ( imp  :  Microsoft_FStar_Parser_AST.imp ) ( t  :  'u41u2979 ) -> (match (imp) with
| Microsoft_FStar_Parser_AST.Hash -> begin
(t, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end
| _ -> begin
(t, None)
end))

let contains_binder = (fun ( binders  :  Microsoft_FStar_Parser_AST.binder list ) -> (Support.Prims.pipe_right binders (Support.Microsoft.FStar.Util.for_some (fun ( b  :  Microsoft_FStar_Parser_AST.binder ) -> (match (b.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Annotated (_) -> begin
true
end
| _ -> begin
false
end)))))

let rec unparen = (fun ( t  :  Microsoft_FStar_Parser_AST.term ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _ -> begin
t
end))

let rec unlabel = (fun ( t  :  Microsoft_FStar_Parser_AST.term ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (t) -> begin
(unlabel t)
end
| Microsoft_FStar_Parser_AST.Labeled ((t, _, _)) -> begin
(unlabel t)
end
| _ -> begin
t
end))

let kind_star = (fun ( r  :  Support.Microsoft.FStar.Range.range ) -> (let _52_15358 = (let _52_15357 = (Microsoft_FStar_Absyn_Syntax.lid_of_path (("Type")::[]) r)
in Microsoft_FStar_Parser_AST.Name (_52_15357))
in (Microsoft_FStar_Parser_AST.mk_term _52_15358 r Microsoft_FStar_Parser_AST.Kind)))

let compile_op = (fun ( arity  :  int ) ( s  :  string ) -> (let name_of_char = (fun ( _41_2  :  char ) -> (match (_41_2) with
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
in (let rec aux = (fun ( i  :  int ) -> (match ((i = (Support.String.length s))) with
| true -> begin
[]
end
| false -> begin
(let _52_15369 = (let _52_15367 = (Support.Microsoft.FStar.Util.char_at s i)
in (name_of_char _52_15367))
in (let _52_15368 = (aux (i + 1))
in (_52_15369)::_52_15368))
end))
in (let _52_15371 = (let _52_15370 = (aux 0)
in (Support.String.concat "_" _52_15370))
in (Support.String.strcat "op_" _52_15371)))))

let compile_op_lid = (fun ( n  :  int ) ( s  :  string ) ( r  :  Support.Microsoft.FStar.Range.range ) -> (let _52_15381 = (let _52_15380 = (let _52_15379 = (let _52_15378 = (compile_op n s)
in (_52_15378, r))
in (Microsoft_FStar_Absyn_Syntax.mk_ident _52_15379))
in (_52_15380)::[])
in (Support.Prims.pipe_right _52_15381 Microsoft_FStar_Absyn_Syntax.lid_of_ids)))

let op_as_vlid = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( arity  :  int ) ( rng  :  Support.Microsoft.FStar.Range.range ) ( s  :  string ) -> (let r = (fun ( l  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) -> (let _52_15392 = (Microsoft_FStar_Absyn_Util.set_lid_range l rng)
in Some (_52_15392)))
in (let fallback = (fun ( _41_100  :  unit ) -> (match (()) with
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
in (match ((let _52_15395 = (compile_op_lid arity s rng)
in (Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env _52_15395))) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}) -> begin
Some (fv.Microsoft_FStar_Absyn_Syntax.v)
end
| _ -> begin
(fallback ())
end))))

let op_as_tylid = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( arity  :  int ) ( rng  :  Support.Microsoft.FStar.Range.range ) ( s  :  string ) -> (let r = (fun ( l  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) -> (let _52_15406 = (Microsoft_FStar_Absyn_Util.set_lid_range l rng)
in Some (_52_15406)))
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
(match ((let _52_15407 = (compile_op_lid arity s rng)
in (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env _52_15407))) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (ftv); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}) -> begin
Some (ftv.Microsoft_FStar_Absyn_Syntax.v)
end
| _ -> begin
None
end)
end)))

let rec is_type = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( t  :  Microsoft_FStar_Parser_AST.term ) -> (match ((t.Microsoft_FStar_Parser_AST.level = Microsoft_FStar_Parser_AST.Type)) with
| true -> begin
true
end
| false -> begin
(match ((let _52_15414 = (unparen t)
in _52_15414.Microsoft_FStar_Parser_AST.tm)) with
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
(let _52_15415 = (is_kind env t)
in (not (_52_15415)))
end
| Microsoft_FStar_Parser_AST.If ((t, t1, t2)) -> begin
(let _52_15419 = (let _52_15417 = (is_type env t)
in (let _52_15416 = (is_type env t1)
in (_52_15417 || _52_15416)))
in (let _52_15418 = (is_type env t2)
in (_52_15419 || _52_15418)))
end
| Microsoft_FStar_Parser_AST.Abs ((pats, t)) -> begin
(let rec aux = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( pats  :  Microsoft_FStar_Parser_AST.pattern list ) -> (match (pats) with
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
(let _52_15424 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (Support.Prims.pipe_right _52_15424 Support.Prims.fst))
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
and is_kind = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( t  :  Microsoft_FStar_Parser_AST.term ) -> (match ((t.Microsoft_FStar_Parser_AST.level = Microsoft_FStar_Parser_AST.Kind)) with
| true -> begin
true
end
| false -> begin
(match ((let _52_15427 = (unparen t)
in _52_15427.Microsoft_FStar_Parser_AST.tm)) with
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

let rec is_type_binder = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( b  :  Microsoft_FStar_Parser_AST.binder ) -> (match ((b.Microsoft_FStar_Parser_AST.blevel = Microsoft_FStar_Parser_AST.Formula)) with
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

let sort_ftv = (fun ( ftv  :  Microsoft_FStar_Absyn_Syntax.ident list ) -> (let _52_15438 = (Support.Microsoft.FStar.Util.remove_dups (fun ( x  :  Microsoft_FStar_Absyn_Syntax.ident ) ( y  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (x.Microsoft_FStar_Absyn_Syntax.idText = y.Microsoft_FStar_Absyn_Syntax.idText)) ftv)
in (Support.Prims.pipe_left (Support.Microsoft.FStar.Util.sort_with (fun ( x  :  Microsoft_FStar_Absyn_Syntax.ident ) ( y  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (Support.String.compare x.Microsoft_FStar_Absyn_Syntax.idText y.Microsoft_FStar_Absyn_Syntax.idText))) _52_15438)))

let rec free_type_vars_b = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( binder  :  Microsoft_FStar_Parser_AST.binder ) -> (match (binder.Microsoft_FStar_Parser_AST.b) with
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
(let _52_15445 = (free_type_vars env term)
in (env, _52_15445))
end
| Microsoft_FStar_Parser_AST.TAnnotated ((id, _)) -> begin
(let _41_435 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_41_435) with
| (env, _) -> begin
(env, [])
end))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(let _52_15446 = (free_type_vars env t)
in (env, _52_15446))
end))
and free_type_vars = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( t  :  Microsoft_FStar_Parser_AST.term ) -> (match ((let _52_15449 = (unparen t)
in _52_15449.Microsoft_FStar_Parser_AST.tm)) with
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
(Support.List.collect (fun ( _41_487  :  (Microsoft_FStar_Parser_AST.term * Microsoft_FStar_Parser_AST.imp) ) -> (match (_41_487) with
| (t, _) -> begin
(free_type_vars env t)
end)) ts)
end
| Microsoft_FStar_Parser_AST.Op ((_, ts)) -> begin
(Support.List.collect (free_type_vars env) ts)
end
| Microsoft_FStar_Parser_AST.App ((t1, t2, _)) -> begin
(let _52_15452 = (free_type_vars env t1)
in (let _52_15451 = (free_type_vars env t2)
in (Support.List.append _52_15452 _52_15451)))
end
| Microsoft_FStar_Parser_AST.Refine ((b, t)) -> begin
(let _41_505 = (free_type_vars_b env b)
in (match (_41_505) with
| (env, f) -> begin
(let _52_15453 = (free_type_vars env t)
in (Support.List.append f _52_15453))
end))
end
| (Microsoft_FStar_Parser_AST.Product ((binders, body))) | (Microsoft_FStar_Parser_AST.Sum ((binders, body))) -> begin
(let _41_521 = (Support.List.fold_left (fun ( _41_514  :  (Microsoft_FStar_Parser_DesugarEnv.env * Microsoft_FStar_Absyn_Syntax.ident list) ) ( binder  :  Microsoft_FStar_Parser_AST.binder ) -> (match (_41_514) with
| (env, free) -> begin
(let _41_518 = (free_type_vars_b env binder)
in (match (_41_518) with
| (env, f) -> begin
(env, (Support.List.append f free))
end))
end)) (env, []) binders)
in (match (_41_521) with
| (env, free) -> begin
(let _52_15456 = (free_type_vars env body)
in (Support.List.append free _52_15456))
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

let head_and_args = (fun ( t  :  Microsoft_FStar_Parser_AST.term ) -> (let rec aux = (fun ( args  :  (Microsoft_FStar_Parser_AST.term * Microsoft_FStar_Parser_AST.imp) list ) ( t  :  Microsoft_FStar_Parser_AST.term ) -> (match ((let _52_15463 = (unparen t)
in _52_15463.Microsoft_FStar_Parser_AST.tm)) with
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

let close = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( t  :  Microsoft_FStar_Parser_AST.term ) -> (let ftv = (let _52_15468 = (free_type_vars env t)
in (Support.Prims.pipe_left sort_ftv _52_15468))
in (match (((Support.List.length ftv) = 0)) with
| true -> begin
t
end
| false -> begin
(let binders = (Support.Prims.pipe_right ftv (Support.List.map (fun ( x  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (let _52_15472 = (let _52_15471 = (let _52_15470 = (kind_star x.Microsoft_FStar_Absyn_Syntax.idRange)
in (x, _52_15470))
in Microsoft_FStar_Parser_AST.TAnnotated (_52_15471))
in (Microsoft_FStar_Parser_AST.mk_binder _52_15472 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type (Some (Microsoft_FStar_Absyn_Syntax.Implicit)))))))
in (let result = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((binders, t))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
in result))
end)))

let close_fun = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( t  :  Microsoft_FStar_Parser_AST.term ) -> (let ftv = (let _52_15477 = (free_type_vars env t)
in (Support.Prims.pipe_left sort_ftv _52_15477))
in (match (((Support.List.length ftv) = 0)) with
| true -> begin
t
end
| false -> begin
(let binders = (Support.Prims.pipe_right ftv (Support.List.map (fun ( x  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (let _52_15481 = (let _52_15480 = (let _52_15479 = (kind_star x.Microsoft_FStar_Absyn_Syntax.idRange)
in (x, _52_15479))
in Microsoft_FStar_Parser_AST.TAnnotated (_52_15480))
in (Microsoft_FStar_Parser_AST.mk_binder _52_15481 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type (Some (Microsoft_FStar_Absyn_Syntax.Implicit)))))))
in (let t = (match ((let _52_15482 = (unlabel t)
in _52_15482.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Product (_) -> begin
t
end
| _ -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.App (((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.effect_Tot_lid)) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level), t, Microsoft_FStar_Parser_AST.Nothing))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
end)
in (let result = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((binders, t))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
in result)))
end)))

let rec uncurry = (fun ( bs  :  Microsoft_FStar_Parser_AST.binder list ) ( t  :  Microsoft_FStar_Parser_AST.term ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Product ((binders, t)) -> begin
(uncurry (Support.List.append bs binders) t)
end
| _ -> begin
(bs, t)
end))

let rec is_app_pattern = (fun ( p  :  Microsoft_FStar_Parser_AST.pattern ) -> (match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed ((p, _)) -> begin
(is_app_pattern p)
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar (_); Microsoft_FStar_Parser_AST.prange = _}, _)) -> begin
true
end
| _ -> begin
false
end))

let rec destruct_app_pattern = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( is_top_level  :  bool ) ( p  :  Microsoft_FStar_Parser_AST.pattern ) -> (match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed ((p, t)) -> begin
(let _41_624 = (destruct_app_pattern env is_top_level p)
in (match (_41_624) with
| (name, args, _) -> begin
(name, args, Some (t))
end))
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((id, _)); Microsoft_FStar_Parser_AST.prange = _}, args)) when is_top_level -> begin
(let _52_15496 = (let _52_15495 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in Support.Microsoft.FStar.Util.Inr (_52_15495))
in (_52_15496, args, None))
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

let binder_of_bnd = (fun ( _41_3  :  bnd ) -> (match (_41_3) with
| TBinder ((a, k, aq)) -> begin
(Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)), aq)
end
| VBinder ((x, t, aq)) -> begin
(Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)), aq)
end
| _ -> begin
(failwith ("Impossible"))
end))

let as_binder = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( imp  :  Microsoft_FStar_Absyn_Syntax.arg_qualifier option ) ( _41_4  :  ((Microsoft_FStar_Absyn_Syntax.ident option * Microsoft_FStar_Absyn_Syntax.knd), (Microsoft_FStar_Absyn_Syntax.ident option * Microsoft_FStar_Absyn_Syntax.typ)) Support.Microsoft.FStar.Util.either ) -> (match (_41_4) with
| Support.Microsoft.FStar.Util.Inl ((None, k)) -> begin
(let _52_15526 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (_52_15526, env))
end
| Support.Microsoft.FStar.Util.Inr ((None, t)) -> begin
(let _52_15527 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_52_15527, env))
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

let label_conjuncts = (fun ( tag  :  string ) ( polarity  :  bool ) ( label_opt  :  string option ) ( f  :  Microsoft_FStar_Parser_AST.term ) -> (let label = (fun ( f  :  Microsoft_FStar_Parser_AST.term ) -> (let msg = (match (label_opt) with
| Some (l) -> begin
l
end
| _ -> begin
(let _52_15538 = (Support.Microsoft.FStar.Range.string_of_range f.Microsoft_FStar_Parser_AST.range)
in (Support.Microsoft.FStar.Util.format2 "%s at %s" tag _52_15538))
end)
in (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Labeled ((f, msg, polarity))) f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level)))
in (let rec aux = (fun ( f  :  Microsoft_FStar_Parser_AST.term ) -> (match (f.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (g) -> begin
(let _52_15542 = (let _52_15541 = (aux g)
in Microsoft_FStar_Parser_AST.Paren (_52_15541))
in (Microsoft_FStar_Parser_AST.mk_term _52_15542 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Op (("/\\", f1::f2::[])) -> begin
(let _52_15548 = (let _52_15547 = (let _52_15546 = (let _52_15545 = (aux f1)
in (let _52_15544 = (let _52_15543 = (aux f2)
in (_52_15543)::[])
in (_52_15545)::_52_15544))
in ("/\\", _52_15546))
in Microsoft_FStar_Parser_AST.Op (_52_15547))
in (Microsoft_FStar_Parser_AST.mk_term _52_15548 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.If ((f1, f2, f3)) -> begin
(let _52_15552 = (let _52_15551 = (let _52_15550 = (aux f2)
in (let _52_15549 = (aux f3)
in (f1, _52_15550, _52_15549)))
in Microsoft_FStar_Parser_AST.If (_52_15551))
in (Microsoft_FStar_Parser_AST.mk_term _52_15552 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Abs ((binders, g)) -> begin
(let _52_15555 = (let _52_15554 = (let _52_15553 = (aux g)
in (binders, _52_15553))
in Microsoft_FStar_Parser_AST.Abs (_52_15554))
in (Microsoft_FStar_Parser_AST.mk_term _52_15555 f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level))
end
| _ -> begin
(label f)
end))
in (aux f))))

let mk_lb = (fun ( _41_730  :  (Microsoft_FStar_Absyn_Syntax.lbname * Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.exp) ) -> (match (_41_730) with
| (n, t, e) -> begin
{Microsoft_FStar_Absyn_Syntax.lbname = n; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = Microsoft_FStar_Absyn_Const.effect_ALL_lid; Microsoft_FStar_Absyn_Syntax.lbdef = e}
end))

let rec desugar_data_pat = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( p  :  Microsoft_FStar_Parser_AST.pattern ) -> (let resolvex = (fun ( l  :  lenv_t ) ( e  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( x  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (match ((Support.Prims.pipe_right l (Support.Microsoft.FStar.Util.find_opt (fun ( _41_5  :  ((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef) Support.Microsoft.FStar.Util.either ) -> (match (_41_5) with
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
in (let resolvea = (fun ( l  :  lenv_t ) ( e  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( a  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (match ((Support.Prims.pipe_right l (Support.Microsoft.FStar.Util.find_opt (fun ( _41_6  :  ((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef) Support.Microsoft.FStar.Util.either ) -> (match (_41_6) with
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
in (let rec aux = (fun ( loc  :  lenv_t ) ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( p  :  Microsoft_FStar_Parser_AST.pattern ) -> (let pos = (fun ( q  :  Microsoft_FStar_Absyn_Syntax.pat' ) -> (Microsoft_FStar_Absyn_Syntax.withinfo q None p.Microsoft_FStar_Parser_AST.prange))
in (let pos_r = (fun ( r  :  Support.Microsoft.FStar.Range.range ) ( q  :  Microsoft_FStar_Absyn_Syntax.pat' ) -> (Microsoft_FStar_Absyn_Syntax.withinfo q None r))
in (match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatOr ([]) -> begin
(failwith ("impossible"))
end
| Microsoft_FStar_Parser_AST.PatOr (p::ps) -> begin
(let _41_786 = (aux loc env p)
in (match (_41_786) with
| (loc, env, var, p) -> begin
(let _41_801 = (Support.List.fold_left (fun ( _41_790  :  (lenv_t * Microsoft_FStar_Parser_DesugarEnv.env * Microsoft_FStar_Absyn_Syntax.pat list) ) ( p  :  Microsoft_FStar_Parser_AST.pattern ) -> (match (_41_790) with
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
in (let _41_803 = (let _52_15627 = (Microsoft_FStar_Absyn_Syntax.pat_vars pat)
in (Support.Prims.ignore _52_15627))
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
(let _52_15629 = (let _52_15628 = (desugar_kind env t)
in (x, _52_15628, aq))
in TBinder (_52_15629))
end
| VBinder ((x, _, aq)) -> begin
(let t = (close_fun env t)
in (let _52_15631 = (let _52_15630 = (desugar_typ env t)
in (x, _52_15630, aq))
in VBinder (_52_15631)))
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
in (let _52_15632 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_twild ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a Microsoft_FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((a, Microsoft_FStar_Absyn_Syntax.kun, aq)), _52_15632)))
end
| false -> begin
(let _41_852 = (resolvea loc env a)
in (match (_41_852) with
| (loc, env, abvd) -> begin
(let _52_15633 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_tvar ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s abvd Microsoft_FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((abvd, Microsoft_FStar_Absyn_Syntax.kun, aq)), _52_15633))
end))
end))
end
| Microsoft_FStar_Parser_AST.PatWild -> begin
(let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let y = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _52_15634 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_wild ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s y Microsoft_FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _52_15634))))
end
| Microsoft_FStar_Parser_AST.PatConst (c) -> begin
(let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _52_15635 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_constant (c)))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _52_15635)))
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
(let _52_15636 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_var (((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s xbvd Microsoft_FStar_Absyn_Syntax.tun), imp))))
in (loc, env, VBinder ((xbvd, Microsoft_FStar_Absyn_Syntax.tun, aq)), _52_15636))
end)))
end
| Microsoft_FStar_Parser_AST.PatName (l) -> begin
(let l = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let _52_15637 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), []))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _52_15637))))
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatName (l); Microsoft_FStar_Parser_AST.prange = _}, args)) -> begin
(let _41_894 = (Support.List.fold_right (fun ( arg  :  Microsoft_FStar_Parser_AST.pattern ) ( _41_884  :  (lenv_t * Microsoft_FStar_Parser_DesugarEnv.env * Microsoft_FStar_Absyn_Syntax.pat list) ) -> (match (_41_884) with
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
in (let _52_15640 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _52_15640))))
end))
end
| Microsoft_FStar_Parser_AST.PatApp (_) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern", p.Microsoft_FStar_Parser_AST.prange))))
end
| Microsoft_FStar_Parser_AST.PatList (pats) -> begin
(let _41_916 = (Support.List.fold_right (fun ( pat  :  Microsoft_FStar_Parser_AST.pattern ) ( _41_906  :  (lenv_t * Microsoft_FStar_Parser_DesugarEnv.env * Microsoft_FStar_Absyn_Syntax.pat list) ) -> (match (_41_906) with
| (loc, env, pats) -> begin
(let _41_912 = (aux loc env pat)
in (match (_41_912) with
| (loc, env, _, pat) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_41_916) with
| (loc, env, pats) -> begin
(let pat = (let _52_15653 = (let _52_15652 = (let _52_15648 = (Support.Microsoft.FStar.Range.end_range p.Microsoft_FStar_Parser_AST.prange)
in (pos_r _52_15648))
in (let _52_15651 = (let _52_15650 = (let _52_15649 = (Microsoft_FStar_Absyn_Util.fv Microsoft_FStar_Absyn_Const.nil_lid)
in (_52_15649, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), []))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_52_15650))
in (Support.Prims.pipe_left _52_15652 _52_15651)))
in (Support.List.fold_right (fun ( hd  :  (Microsoft_FStar_Absyn_Syntax.pat', ((Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either option) Microsoft_FStar_Absyn_Syntax.withinfo_t ) ( tl  :  (Microsoft_FStar_Absyn_Syntax.pat', ((Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either option) Microsoft_FStar_Absyn_Syntax.withinfo_t ) -> (let r = (Support.Microsoft.FStar.Range.union_ranges hd.Microsoft_FStar_Absyn_Syntax.p tl.Microsoft_FStar_Absyn_Syntax.p)
in (let _52_15647 = (let _52_15646 = (let _52_15645 = (Microsoft_FStar_Absyn_Util.fv Microsoft_FStar_Absyn_Const.cons_lid)
in (_52_15645, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), (hd)::(tl)::[]))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_52_15646))
in (Support.Prims.pipe_left (pos_r r) _52_15647)))) pats _52_15653))
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), pat)))
end))
end
| Microsoft_FStar_Parser_AST.PatTuple ((args, dep)) -> begin
(let _41_940 = (Support.List.fold_left (fun ( _41_929  :  (lenv_t * Microsoft_FStar_Parser_DesugarEnv.env * Microsoft_FStar_Absyn_Syntax.pat list) ) ( p  :  Microsoft_FStar_Parser_AST.pattern ) -> (match (_41_929) with
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
in (let _52_15656 = (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), _52_15656)))))))
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
(let fields = (Support.Prims.pipe_right fields (Support.List.map (fun ( _41_967  :  (Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Parser_AST.pattern) ) -> (match (_41_967) with
| (f, p) -> begin
(let _52_15658 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in (_52_15658, p))
end))))
in (let args = (Support.Prims.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map (fun ( _41_972  :  (Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Absyn_Syntax.typ) ) -> (match (_41_972) with
| (f, _) -> begin
(match ((Support.Prims.pipe_right fields (Support.List.tryFind (fun ( _41_976  :  (Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Parser_AST.pattern) ) -> (match (_41_976) with
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
(let _52_15666 = (let _52_15665 = (let _52_15664 = (let _52_15663 = (let _52_15662 = (let _52_15661 = (Support.Prims.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map Support.Prims.fst))
in (record.Microsoft_FStar_Parser_DesugarEnv.typename, _52_15661))
in Microsoft_FStar_Absyn_Syntax.Record_ctor (_52_15662))
in Some (_52_15663))
in (fv, _52_15664, args))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_52_15665))
in (Support.Prims.pipe_left pos _52_15666))
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
and desugar_binding_pat_maybe_top = (fun ( top  :  bool ) ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( p  :  Microsoft_FStar_Parser_AST.pattern ) -> (match (top) with
| true -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatVar ((x, _)) -> begin
(let _52_15672 = (let _52_15671 = (let _52_15670 = (Microsoft_FStar_Parser_DesugarEnv.qualify env x)
in (_52_15670, Microsoft_FStar_Absyn_Syntax.tun))
in LetBinder (_52_15671))
in (env, _52_15672, None))
end
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((x, _)); Microsoft_FStar_Parser_AST.prange = _}, t)) -> begin
(let _52_15676 = (let _52_15675 = (let _52_15674 = (Microsoft_FStar_Parser_DesugarEnv.qualify env x)
in (let _52_15673 = (desugar_typ env t)
in (_52_15674, _52_15673)))
in LetBinder (_52_15675))
in (env, _52_15676, None))
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
and desugar_binding_pat = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( p  :  Microsoft_FStar_Parser_AST.pattern ) -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top = (fun ( _41_1044  :  bool ) ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( pat  :  Microsoft_FStar_Parser_AST.pattern ) -> (let _41_1052 = (desugar_data_pat env pat)
in (match (_41_1052) with
| (env, _, pat) -> begin
(env, pat)
end)))
and desugar_match_pat = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( p  :  Microsoft_FStar_Parser_AST.pattern ) -> (desugar_match_pat_maybe_top false env p))
and desugar_typ_or_exp = (fun ( env  :  env_t ) ( t  :  Microsoft_FStar_Parser_AST.term ) -> (match ((is_type env t)) with
| true -> begin
(let _52_15686 = (desugar_typ env t)
in Support.Microsoft.FStar.Util.Inl (_52_15686))
end
| false -> begin
(let _52_15687 = (desugar_exp env t)
in Support.Microsoft.FStar.Util.Inr (_52_15687))
end))
and desugar_exp = (fun ( env  :  env_t ) ( e  :  Microsoft_FStar_Parser_AST.term ) -> (desugar_exp_maybe_top false env e))
and desugar_exp_maybe_top = (fun ( top_level  :  bool ) ( env  :  env_t ) ( top  :  Microsoft_FStar_Parser_AST.term ) -> (let pos = (fun ( e  :  Microsoft_FStar_Absyn_Syntax.typ option  ->  Support.Microsoft.FStar.Range.range  ->  Microsoft_FStar_Absyn_Syntax.exp ) -> (e None top.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( e  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _41_1066 = e
in {Microsoft_FStar_Absyn_Syntax.n = _41_1066.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _41_1066.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = top.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _41_1066.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _41_1066.Microsoft_FStar_Absyn_Syntax.uvs}))
in (match ((let _52_15707 = (unparen top)
in _52_15707.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Const (c) -> begin
(Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match ((op_as_vlid env (Support.List.length args) top.Microsoft_FStar_Parser_AST.range s)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat "Unexpected operator: " s), top.Microsoft_FStar_Parser_AST.range))))
end
| Some (l) -> begin
(let op = (let _52_15710 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (Microsoft_FStar_Absyn_Util.fvar None l _52_15710))
in (let args = (Support.Prims.pipe_right args (Support.List.map (fun ( t  :  Microsoft_FStar_Parser_AST.term ) -> (let _52_15712 = (desugar_typ_or_exp env t)
in (_52_15712, None)))))
in (let _52_15713 = (Microsoft_FStar_Absyn_Util.mk_exp_app op args)
in (Support.Prims.pipe_left setpos _52_15713))))
end)
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) -> begin
(match ((l.Microsoft_FStar_Absyn_Syntax.str = "ref")) with
| true -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env Microsoft_FStar_Absyn_Const.alloc_lid)) with
| None -> begin
(let _52_15716 = (let _52_15715 = (let _52_15714 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in ("Identifier \'ref\' not found; include lib/st.fst in your path", _52_15714))
in Microsoft_FStar_Absyn_Syntax.Error (_52_15715))
in (raise (_52_15716)))
end
| Some (e) -> begin
(setpos e)
end)
end
| false -> begin
(let _52_15717 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (Support.Prims.pipe_left setpos _52_15717))
end)
end
| Microsoft_FStar_Parser_AST.Construct ((l, args)) -> begin
(let dt = (let _52_15722 = (let _52_15721 = (let _52_15720 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (_52_15720, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _52_15721))
in (Support.Prims.pipe_left pos _52_15722))
in (match (args) with
| [] -> begin
dt
end
| _ -> begin
(let args = (Support.List.map (fun ( _41_1096  :  (Microsoft_FStar_Parser_AST.term * Microsoft_FStar_Parser_AST.imp) ) -> (match (_41_1096) with
| (t, imp) -> begin
(let te = (desugar_typ_or_exp env t)
in (arg_withimp_e imp te))
end)) args)
in (let _52_15727 = (let _52_15726 = (let _52_15725 = (let _52_15724 = (Microsoft_FStar_Absyn_Util.mk_exp_app dt args)
in (_52_15724, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_52_15725))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _52_15726))
in (Support.Prims.pipe_left setpos _52_15727)))
end))
end
| Microsoft_FStar_Parser_AST.Abs ((binders, body)) -> begin
(let _41_1133 = (Support.List.fold_left (fun ( _41_1105  :  (Microsoft_FStar_Parser_DesugarEnv.env * Microsoft_FStar_Absyn_Syntax.ident list) ) ( pat  :  Microsoft_FStar_Parser_AST.pattern ) -> (match (_41_1105) with
| (env, ftvs) -> begin
(match (pat.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatTvar ((a, imp)); Microsoft_FStar_Parser_AST.prange = _}, t)) -> begin
(let ftvs = (let _52_15730 = (free_type_vars env t)
in (Support.List.append _52_15730 ftvs))
in (let _52_15732 = (let _52_15731 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (Support.Prims.pipe_left Support.Prims.fst _52_15731))
in (_52_15732, ftvs)))
end
| Microsoft_FStar_Parser_AST.PatTvar ((a, _)) -> begin
(let _52_15734 = (let _52_15733 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (Support.Prims.pipe_left Support.Prims.fst _52_15733))
in (_52_15734, ftvs))
end
| Microsoft_FStar_Parser_AST.PatAscribed ((_, t)) -> begin
(let _52_15736 = (let _52_15735 = (free_type_vars env t)
in (Support.List.append _52_15735 ftvs))
in (env, _52_15736))
end
| _ -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_41_1133) with
| (_, ftv) -> begin
(let ftv = (sort_ftv ftv)
in (let binders = (let _52_15738 = (Support.Prims.pipe_right ftv (Support.List.map (fun ( a  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatTvar ((a, true))) top.Microsoft_FStar_Parser_AST.range))))
in (Support.List.append _52_15738 binders))
in (let rec aux = (fun ( env  :  env_t ) ( bs  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) ( sc_pat_opt  :  (Microsoft_FStar_Absyn_Syntax.exp * Microsoft_FStar_Absyn_Syntax.pat) option ) ( _41_7  :  Microsoft_FStar_Parser_AST.pattern list ) -> (match (_41_7) with
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
(let _52_15747 = (binder_of_bnd b)
in (_52_15747, sc_pat_opt))
end
| VBinder ((x, t, aq)) -> begin
(let b = (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)
in (let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _52_15749 = (let _52_15748 = (Microsoft_FStar_Absyn_Util.bvar_to_exp b)
in (_52_15748, p))
in Some (_52_15749))
end
| (Some (p), Some ((sc, p'))) -> begin
(match ((sc.Microsoft_FStar_Absyn_Syntax.n, p'.Microsoft_FStar_Absyn_Syntax.v)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_), _) -> begin
(let tup = (Microsoft_FStar_Absyn_Util.mk_tuple_data_lid 2 top.Microsoft_FStar_Parser_AST.range)
in (let sc = (let _52_15756 = (let _52_15755 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) tup top.Microsoft_FStar_Parser_AST.range)
in (let _52_15754 = (let _52_15753 = (Microsoft_FStar_Absyn_Syntax.varg sc)
in (let _52_15752 = (let _52_15751 = (let _52_15750 = (Microsoft_FStar_Absyn_Util.bvar_to_exp b)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg _52_15750))
in (_52_15751)::[])
in (_52_15753)::_52_15752))
in (_52_15755, _52_15754)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _52_15756 None top.Microsoft_FStar_Parser_AST.range))
in (let p = (let _52_15760 = (let _52_15758 = (let _52_15757 = (Microsoft_FStar_Absyn_Util.fv tup)
in (_52_15757, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), (p')::(p)::[]))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_52_15758))
in (let _52_15759 = (Support.Microsoft.FStar.Range.union_ranges p'.Microsoft_FStar_Absyn_Syntax.p p.Microsoft_FStar_Absyn_Syntax.p)
in (Microsoft_FStar_Absyn_Util.withinfo _52_15760 None _52_15759)))
in Some ((sc, p)))))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app ((_, args)), Microsoft_FStar_Absyn_Syntax.Pat_cons ((_, _, pats))) -> begin
(let tup = (Microsoft_FStar_Absyn_Util.mk_tuple_data_lid (1 + (Support.List.length args)) top.Microsoft_FStar_Parser_AST.range)
in (let sc = (let _52_15766 = (let _52_15765 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) tup top.Microsoft_FStar_Parser_AST.range)
in (let _52_15764 = (let _52_15763 = (let _52_15762 = (let _52_15761 = (Microsoft_FStar_Absyn_Util.bvar_to_exp b)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg _52_15761))
in (_52_15762)::[])
in (Support.List.append args _52_15763))
in (_52_15765, _52_15764)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _52_15766 None top.Microsoft_FStar_Parser_AST.range))
in (let p = (let _52_15770 = (let _52_15768 = (let _52_15767 = (Microsoft_FStar_Absyn_Util.fv tup)
in (_52_15767, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor), (Support.List.append pats ((p)::[]))))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_52_15768))
in (let _52_15769 = (Support.Microsoft.FStar.Range.union_ranges p'.Microsoft_FStar_Absyn_Syntax.p p.Microsoft_FStar_Absyn_Syntax.p)
in (Microsoft_FStar_Absyn_Util.withinfo _52_15770 None _52_15769)))
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
in (let _52_15781 = (let _52_15780 = (let _52_15779 = (let _52_15773 = (Microsoft_FStar_Absyn_Syntax.range_of_lid a)
in (Microsoft_FStar_Absyn_Util.fvar None a _52_15773))
in (let _52_15778 = (let _52_15777 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ phi)
in (let _52_15776 = (let _52_15775 = (let _52_15774 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant Microsoft_FStar_Absyn_Syntax.Const_unit None top.Microsoft_FStar_Parser_AST.range)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg _52_15774))
in (_52_15775)::[])
in (_52_15777)::_52_15776))
in (_52_15779, _52_15778)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _52_15780))
in (Support.Prims.pipe_left pos _52_15781)))
end
| Microsoft_FStar_Parser_AST.App (_) -> begin
(let rec aux = (fun ( args  :  ((Microsoft_FStar_Absyn_Syntax.typ, Microsoft_FStar_Absyn_Syntax.exp) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) ( e  :  Microsoft_FStar_Parser_AST.term ) -> (match ((let _52_15786 = (unparen e)
in _52_15786.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((e, t, imp)) -> begin
(let arg = (let _52_15787 = (desugar_typ_or_exp env t)
in (Support.Prims.pipe_left (arg_withimp_e imp) _52_15787))
in (aux ((arg)::args) e))
end
| _ -> begin
(let head = (desugar_exp env e)
in (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (head, args))))
end))
in (aux [] top))
end
| Microsoft_FStar_Parser_AST.Seq ((t1, t2)) -> begin
(let _52_15793 = (let _52_15792 = (let _52_15791 = (let _52_15790 = (desugar_exp env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Let ((false, (((Microsoft_FStar_Parser_AST.mk_pattern Microsoft_FStar_Parser_AST.PatWild t1.Microsoft_FStar_Parser_AST.range), t1))::[], t2))) top.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Expr))
in (_52_15790, Microsoft_FStar_Absyn_Syntax.Sequence))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_52_15791))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _52_15792))
in (Support.Prims.pipe_left setpos _52_15793))
end
| Microsoft_FStar_Parser_AST.Let ((is_rec, (pat, _snd)::_tl, body)) -> begin
(let ds_let_rec = (fun ( _41_1259  :  unit ) -> (match (()) with
| () -> begin
(let bindings = ((pat, _snd))::_tl
in (let funs = (Support.Prims.pipe_right bindings (Support.List.map (fun ( _41_1263  :  (Microsoft_FStar_Parser_AST.pattern * Microsoft_FStar_Parser_AST.term) ) -> (match (_41_1263) with
| (p, def) -> begin
(match ((is_app_pattern p)) with
| true -> begin
(let _52_15797 = (destruct_app_pattern env top_level p)
in (_52_15797, def))
end
| false -> begin
(match ((Microsoft_FStar_Parser_AST.un_function p def)) with
| Some ((p, def)) -> begin
(let _52_15798 = (destruct_app_pattern env top_level p)
in (_52_15798, def))
end
| _ -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((id, _)); Microsoft_FStar_Parser_AST.prange = _}, t)) -> begin
(match (top_level) with
| true -> begin
(let _52_15801 = (let _52_15800 = (let _52_15799 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in Support.Microsoft.FStar.Util.Inr (_52_15799))
in (_52_15800, [], Some (t)))
in (_52_15801, def))
end
| false -> begin
((Support.Microsoft.FStar.Util.Inl (id), [], Some (t)), def)
end)
end
| Microsoft_FStar_Parser_AST.PatVar ((id, _)) -> begin
(match (top_level) with
| true -> begin
(let _52_15804 = (let _52_15803 = (let _52_15802 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in Support.Microsoft.FStar.Util.Inr (_52_15802))
in (_52_15803, [], None))
in (_52_15804, def))
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
in (let _41_1313 = (Support.List.fold_left (fun ( _41_1291  :  (Microsoft_FStar_Parser_DesugarEnv.env * (Microsoft_FStar_Absyn_Syntax.bvvdef, Microsoft_FStar_Absyn_Syntax.lident) Support.Microsoft.FStar.Util.either list) ) ( _41_1300  :  (((Microsoft_FStar_Absyn_Syntax.ident, Microsoft_FStar_Absyn_Syntax.lident) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Parser_AST.pattern list * Microsoft_FStar_Parser_AST.term option) * Microsoft_FStar_Parser_AST.term) ) -> (match ((_41_1291, _41_1300)) with
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
(let _52_15807 = (Microsoft_FStar_Parser_DesugarEnv.push_rec_binding env (Microsoft_FStar_Parser_DesugarEnv.Binding_let (l)))
in (_52_15807, Support.Microsoft.FStar.Util.Inr (l)))
end)
in (match (_41_1310) with
| (env, lbname) -> begin
(env, (lbname)::fnames)
end))
end)) (env, []) funs)
in (match (_41_1313) with
| (env', fnames) -> begin
(let fnames = (Support.List.rev fnames)
in (let desugar_one_def = (fun ( env  :  env_t ) ( lbname  :  Microsoft_FStar_Absyn_Syntax.lbname ) ( _41_1324  :  (((Microsoft_FStar_Absyn_Syntax.ident, Microsoft_FStar_Absyn_Syntax.lident) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Parser_AST.pattern list * Microsoft_FStar_Parser_AST.term option) * Microsoft_FStar_Parser_AST.term) ) -> (match (_41_1324) with
| ((_, args, result_t), def) -> begin
(let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _52_15814 = (Support.Microsoft.FStar.Range.union_ranges t.Microsoft_FStar_Parser_AST.range def.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Ascribed ((def, t))) _52_15814 Microsoft_FStar_Parser_AST.Expr))
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
in (let ds_non_rec = (fun ( pat  :  Microsoft_FStar_Parser_AST.pattern ) ( t1  :  Microsoft_FStar_Parser_AST.term ) ( t2  :  Microsoft_FStar_Parser_AST.term ) -> (let t1 = (desugar_exp env t1)
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
(let _52_15826 = (let _52_15825 = (Microsoft_FStar_Absyn_Util.bvd_to_exp x t)
in (_52_15825, ((pat, None, body))::[]))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _52_15826 None body.Microsoft_FStar_Absyn_Syntax.pos))
end)
in (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((false, ((mk_lb (Support.Microsoft.FStar.Util.Inl (x), t, t1)))::[]), body)))))
end)
end))))
in (match ((let _52_15829 = (is_app_pattern pat)
in (is_rec || _52_15829))) with
| true -> begin
(ds_let_rec ())
end
| false -> begin
(ds_non_rec pat _snd body)
end)))
end
| Microsoft_FStar_Parser_AST.If ((t1, t2, t3)) -> begin
(let _52_15840 = (let _52_15839 = (let _52_15838 = (desugar_exp env t1)
in (let _52_15837 = (let _52_15836 = (let _52_15832 = (desugar_exp env t2)
in ((Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (true))) None t2.Microsoft_FStar_Parser_AST.range), None, _52_15832))
in (let _52_15835 = (let _52_15834 = (let _52_15833 = (desugar_exp env t3)
in ((Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (false))) None t3.Microsoft_FStar_Parser_AST.range), None, _52_15833))
in (_52_15834)::[])
in (_52_15836)::_52_15835))
in (_52_15838, _52_15837)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _52_15839))
in (Support.Prims.pipe_left pos _52_15840))
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
(let desugar_branch = (fun ( _41_1395  :  (Microsoft_FStar_Parser_AST.pattern * Microsoft_FStar_Parser_AST.term option * Microsoft_FStar_Parser_AST.term) ) -> (match (_41_1395) with
| (pat, wopt, b) -> begin
(let _41_1398 = (desugar_match_pat env pat)
in (match (_41_1398) with
| (env, pat) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _52_15843 = (desugar_exp env e)
in Some (_52_15843))
end)
in (let b = (desugar_exp env b)
in (pat, wopt, b)))
end))
end))
in (let _52_15849 = (let _52_15848 = (let _52_15847 = (desugar_exp env e)
in (let _52_15846 = (Support.List.map desugar_branch branches)
in (_52_15847, _52_15846)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _52_15848))
in (Support.Prims.pipe_left pos _52_15849)))
end
| Microsoft_FStar_Parser_AST.Ascribed ((e, t)) -> begin
(let _52_15855 = (let _52_15854 = (let _52_15853 = (desugar_exp env e)
in (let _52_15852 = (desugar_typ env t)
in (_52_15853, _52_15852, None)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed _52_15854))
in (Support.Prims.pipe_left pos _52_15855))
end
| Microsoft_FStar_Parser_AST.Record ((_, [])) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected empty record", top.Microsoft_FStar_Parser_AST.range))))
end
| Microsoft_FStar_Parser_AST.Record ((eopt, fields)) -> begin
(let _41_1420 = (Support.List.hd fields)
in (match (_41_1420) with
| (f, _) -> begin
(let qfn = (fun ( g  :  Microsoft_FStar_Absyn_Syntax.ident ) -> (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append f.Microsoft_FStar_Absyn_Syntax.ns ((g)::[]))))
in (let _41_1426 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_41_1426) with
| (record, _) -> begin
(let get_field = (fun ( xopt  :  Microsoft_FStar_Parser_AST.term option ) ( f  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) -> (let fn = f.Microsoft_FStar_Absyn_Syntax.ident
in (let found = (Support.Prims.pipe_right fields (Support.Microsoft.FStar.Util.find_opt (fun ( _41_1434  :  (Microsoft_FStar_Absyn_Syntax.l__LongIdent * Microsoft_FStar_Parser_AST.term) ) -> (match (_41_1434) with
| (g, _) -> begin
(let gn = g.Microsoft_FStar_Absyn_Syntax.ident
in (fn.Microsoft_FStar_Absyn_Syntax.idText = gn.Microsoft_FStar_Absyn_Syntax.idText))
end))))
in (match (found) with
| Some ((_, e)) -> begin
(let _52_15863 = (qfn fn)
in (_52_15863, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _52_15867 = (let _52_15866 = (let _52_15865 = (let _52_15864 = (Microsoft_FStar_Absyn_Syntax.text_of_lid f)
in (Support.Microsoft.FStar.Util.format1 "Field %s is missing" _52_15864))
in (_52_15865, top.Microsoft_FStar_Parser_AST.range))
in Microsoft_FStar_Absyn_Syntax.Error (_52_15866))
in (raise (_52_15867)))
end
| Some (x) -> begin
(let _52_15868 = (qfn fn)
in (_52_15868, (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Project ((x, f))) x.Microsoft_FStar_Parser_AST.range x.Microsoft_FStar_Parser_AST.level)))
end)
end))))
in (let recterm = (match (eopt) with
| None -> begin
(let _52_15873 = (let _52_15872 = (Support.Prims.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map (fun ( _41_1450  :  (Microsoft_FStar_Absyn_Syntax.l__LongIdent * Microsoft_FStar_Absyn_Syntax.typ) ) -> (match (_41_1450) with
| (f, _) -> begin
(let _52_15871 = (let _52_15870 = (get_field None f)
in (Support.Prims.pipe_left Support.Prims.snd _52_15870))
in (_52_15871, Microsoft_FStar_Parser_AST.Nothing))
end))))
in (record.Microsoft_FStar_Parser_DesugarEnv.constrname, _52_15872))
in Microsoft_FStar_Parser_AST.Construct (_52_15873))
end
| Some (e) -> begin
(let x = (Microsoft_FStar_Absyn_Util.genident (Some (e.Microsoft_FStar_Parser_AST.range)))
in (let xterm = (let _52_15875 = (let _52_15874 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((x)::[]))
in Microsoft_FStar_Parser_AST.Var (_52_15874))
in (Microsoft_FStar_Parser_AST.mk_term _52_15875 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr))
in (let record = (let _52_15878 = (let _52_15877 = (Support.Prims.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map (fun ( _41_1458  :  (Microsoft_FStar_Absyn_Syntax.l__LongIdent * Microsoft_FStar_Absyn_Syntax.typ) ) -> (match (_41_1458) with
| (f, _) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _52_15877))
in Microsoft_FStar_Parser_AST.Record (_52_15878))
in Microsoft_FStar_Parser_AST.Let ((false, (((Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatVar ((x, false))) x.Microsoft_FStar_Absyn_Syntax.idRange), e))::[], (Microsoft_FStar_Parser_AST.mk_term record top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))))))
end)
in (let recterm = (Microsoft_FStar_Parser_AST.mk_term recterm top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level)
in (let e = (desugar_exp env recterm)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, Microsoft_FStar_Absyn_Syntax.Data_app))) -> begin
(let e = (let _52_15888 = (let _52_15887 = (let _52_15886 = (let _52_15885 = (let _52_15884 = (let _52_15883 = (let _52_15882 = (let _52_15881 = (Support.Prims.pipe_right record.Microsoft_FStar_Parser_DesugarEnv.fields (Support.List.map Support.Prims.fst))
in (record.Microsoft_FStar_Parser_DesugarEnv.typename, _52_15881))
in Microsoft_FStar_Absyn_Syntax.Record_ctor (_52_15882))
in Some (_52_15883))
in (fv, _52_15884))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _52_15885 None e.Microsoft_FStar_Absyn_Syntax.pos))
in (_52_15886, args))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _52_15887))
in (Support.Prims.pipe_left pos _52_15888))
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
in (let _52_15896 = (let _52_15895 = (let _52_15894 = (let _52_15891 = (Microsoft_FStar_Absyn_Syntax.range_of_lid f)
in (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Record_projector (fn))) fieldname _52_15891))
in (let _52_15893 = (let _52_15892 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_52_15892)::[])
in (_52_15894, _52_15893)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _52_15895))
in (Support.Prims.pipe_left pos _52_15896))))
end))
end
| Microsoft_FStar_Parser_AST.Paren (e) -> begin
(desugar_exp env e)
end
| _ -> begin
(Microsoft_FStar_Parser_AST.error "Unexpected term" top top.Microsoft_FStar_Parser_AST.range)
end))))
and desugar_typ = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( top  :  Microsoft_FStar_Parser_AST.term ) -> (let wpos = (fun ( t  :  Microsoft_FStar_Absyn_Syntax.knd option  ->  Support.Microsoft.FStar.Range.range  ->  Microsoft_FStar_Absyn_Syntax.typ ) -> (t None top.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( t  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _41_1520 = t
in {Microsoft_FStar_Absyn_Syntax.n = _41_1520.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _41_1520.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = top.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _41_1520.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _41_1520.Microsoft_FStar_Absyn_Syntax.uvs}))
in (let top = (unparen top)
in (let head_and_args = (fun ( t  :  Microsoft_FStar_Parser_AST.term ) -> (let rec aux = (fun ( args  :  (Microsoft_FStar_Parser_AST.term * Microsoft_FStar_Parser_AST.imp) list ) ( t  :  Microsoft_FStar_Parser_AST.term ) -> (match ((let _52_15919 = (unparen t)
in _52_15919.Microsoft_FStar_Parser_AST.tm)) with
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
(let _52_15920 = (desugar_exp env t)
in (Support.Prims.pipe_right _52_15920 Microsoft_FStar_Absyn_Util.b2t))
end))
end
| Microsoft_FStar_Parser_AST.Ensures ((t, lopt)) -> begin
(let t = (label_conjuncts "post-condition" false lopt t)
in (match ((is_type env t)) with
| true -> begin
(desugar_typ env t)
end
| false -> begin
(let _52_15921 = (desugar_exp env t)
in (Support.Prims.pipe_right _52_15921 Microsoft_FStar_Absyn_Util.b2t))
end))
end
| Microsoft_FStar_Parser_AST.Op (("*", t1::_::[])) -> begin
(match ((is_type env t1)) with
| true -> begin
(let rec flatten = (fun ( t  :  Microsoft_FStar_Parser_AST.term ) -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Op (("*", t1::t2::[])) -> begin
(let rest = (flatten t2)
in (t1)::rest)
end
| _ -> begin
(t)::[]
end))
in (let targs = (let _52_15926 = (flatten top)
in (Support.Prims.pipe_right _52_15926 (Support.List.map (fun ( t  :  Microsoft_FStar_Parser_AST.term ) -> (let _52_15925 = (desugar_typ env t)
in (Microsoft_FStar_Absyn_Syntax.targ _52_15925))))))
in (let tup = (let _52_15927 = (Microsoft_FStar_Absyn_Util.mk_tuple_lid (Support.List.length targs) top.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) _52_15927))
in (Support.Prims.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))))
end
| false -> begin
(let _52_15933 = (let _52_15932 = (let _52_15931 = (let _52_15930 = (Microsoft_FStar_Parser_AST.term_to_string t1)
in (Support.Microsoft.FStar.Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _52_15930))
in (_52_15931, top.Microsoft_FStar_Parser_AST.range))
in Microsoft_FStar_Absyn_Syntax.Error (_52_15932))
in (raise (_52_15933)))
end)
end
| Microsoft_FStar_Parser_AST.Op (("=!=", args)) -> begin
(desugar_typ env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Op (("~", ((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Op (("==", args))) top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))::[]))) top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match ((op_as_tylid env (Support.List.length args) top.Microsoft_FStar_Parser_AST.range s)) with
| None -> begin
(let _52_15934 = (desugar_exp env top)
in (Support.Prims.pipe_right _52_15934 Microsoft_FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(let args = (Support.List.map (fun ( t  :  Microsoft_FStar_Parser_AST.term ) -> (let _52_15936 = (desugar_typ_or_exp env t)
in (Support.Prims.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _52_15936))) args)
in (let _52_15937 = (Microsoft_FStar_Absyn_Util.ftv l Microsoft_FStar_Absyn_Syntax.kun)
in (Microsoft_FStar_Absyn_Util.mk_typ_app _52_15937 args)))
end)
end
| Microsoft_FStar_Parser_AST.Tvar (a) -> begin
(let _52_15938 = (Microsoft_FStar_Parser_DesugarEnv.fail_or2 (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (Support.Prims.pipe_left setpos _52_15938))
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) when ((Support.List.length l.Microsoft_FStar_Absyn_Syntax.ns) = 0) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env l.Microsoft_FStar_Absyn_Syntax.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _52_15939 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (Support.Prims.pipe_left setpos _52_15939))
end)
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) -> begin
(let l = (Microsoft_FStar_Absyn_Util.set_lid_range l top.Microsoft_FStar_Parser_AST.range)
in (let _52_15940 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (Support.Prims.pipe_left setpos _52_15940)))
end
| Microsoft_FStar_Parser_AST.Construct ((l, args)) -> begin
(let t = (let _52_15941 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (Support.Prims.pipe_left setpos _52_15941))
in (let args = (Support.List.map (fun ( _41_1603  :  (Microsoft_FStar_Parser_AST.term * Microsoft_FStar_Parser_AST.imp) ) -> (match (_41_1603) with
| (t, imp) -> begin
(let _52_15943 = (desugar_typ_or_exp env t)
in (Support.Prims.pipe_left (arg_withimp_t imp) _52_15943))
end)) args)
in (Microsoft_FStar_Absyn_Util.mk_typ_app t args)))
end
| Microsoft_FStar_Parser_AST.Abs ((binders, body)) -> begin
(let rec aux = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( bs  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) ( _41_8  :  Microsoft_FStar_Parser_AST.pattern list ) -> (match (_41_8) with
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
(let _52_15955 = (let _52_15954 = (let _52_15953 = (let _52_15952 = (Microsoft_FStar_Absyn_Print.pat_to_string q)
in (Support.Microsoft.FStar.Util.format1 "Pattern matching at the type level is not supported; got %s\n" _52_15952))
in (_52_15953, hd.Microsoft_FStar_Parser_AST.prange))
in Microsoft_FStar_Absyn_Syntax.Error (_52_15954))
in (raise (_52_15955)))
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
(let rec aux = (fun ( args  :  ((Microsoft_FStar_Absyn_Syntax.typ, Microsoft_FStar_Absyn_Syntax.exp) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) ( e  :  Microsoft_FStar_Parser_AST.term ) -> (match ((let _52_15960 = (unparen e)
in _52_15960.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.App ((e, arg, imp)) -> begin
(let arg = (let _52_15961 = (desugar_typ_or_exp env arg)
in (Support.Prims.pipe_left (arg_withimp_t imp) _52_15961))
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
(let rec aux = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( bs  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) ( _41_9  :  Microsoft_FStar_Parser_AST.binder list ) -> (match (_41_9) with
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
(let _52_15972 = (desugar_exp env f)
in (Support.Prims.pipe_right _52_15972 Microsoft_FStar_Absyn_Util.b2t))
end)
in (Support.Prims.pipe_left wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (b, f))))
end))
end)
end
| (Microsoft_FStar_Parser_AST.NamedTyp ((_, t))) | (Microsoft_FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| Microsoft_FStar_Parser_AST.Ascribed ((t, k)) -> begin
(let _52_15980 = (let _52_15979 = (let _52_15978 = (desugar_typ env t)
in (let _52_15977 = (desugar_kind env k)
in (_52_15978, _52_15977)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed' _52_15979))
in (Support.Prims.pipe_left wpos _52_15980))
end
| Microsoft_FStar_Parser_AST.Sum ((binders, t)) -> begin
(let _41_1720 = (Support.List.fold_left (fun ( _41_1705  :  (Microsoft_FStar_Parser_DesugarEnv.env * ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, Microsoft_FStar_Absyn_Syntax.typ) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list * Microsoft_FStar_Absyn_Syntax.arg list) ) ( b  :  Microsoft_FStar_Parser_AST.binder ) -> (match (_41_1705) with
| (env, tparams, typs) -> begin
(let _41_1709 = (desugar_exp_binder env b)
in (match (_41_1709) with
| (xopt, t) -> begin
(let _41_1715 = (match (xopt) with
| None -> begin
(let _52_15983 = (Microsoft_FStar_Absyn_Util.new_bvd (Some (top.Microsoft_FStar_Parser_AST.range)))
in (env, _52_15983))
end
| Some (x) -> begin
(Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_41_1715) with
| (env, x) -> begin
(let _52_15987 = (let _52_15986 = (let _52_15985 = (let _52_15984 = (Microsoft_FStar_Absyn_Util.close_with_lam tparams t)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _52_15984))
in (_52_15985)::[])
in (Support.List.append typs _52_15986))
in (env, (Support.List.append tparams (((Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)), None))::[])), _52_15987))
end))
end))
end)) (env, [], []) (Support.List.append binders (((Microsoft_FStar_Parser_AST.mk_binder (Microsoft_FStar_Parser_AST.NoName (t)) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Type None))::[])))
in (match (_41_1720) with
| (env, _, targs) -> begin
(let tup = (let _52_15988 = (Microsoft_FStar_Absyn_Util.mk_dtuple_lid (Support.List.length targs) top.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) _52_15988))
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
and desugar_comp = (fun ( r  :  Support.Microsoft.FStar.Range.range ) ( default_ok  :  bool ) ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( t  :  Microsoft_FStar_Parser_AST.term ) -> (let fail = (fun ( msg  :  string ) -> (raise (Microsoft_FStar_Absyn_Syntax.Error ((msg, r)))))
in (let pre_process_comp_typ = (fun ( t  :  Microsoft_FStar_Parser_AST.term ) -> (let _41_1745 = (head_and_args t)
in (match (_41_1745) with
| (head, args) -> begin
(match (head.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Name (lemma) when (lemma.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "Lemma") -> begin
(let unit = ((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.unit_lid)) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Type), Microsoft_FStar_Parser_AST.Nothing)
in (let nil_pat = ((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.nil_lid)) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Expr), Microsoft_FStar_Parser_AST.Nothing)
in (let _41_1771 = (Support.Prims.pipe_right args (Support.List.partition (fun ( _41_1753  :  (Microsoft_FStar_Parser_AST.term * Microsoft_FStar_Parser_AST.imp) ) -> (match (_41_1753) with
| (arg, _) -> begin
(match ((let _52_16000 = (unparen arg)
in _52_16000.Microsoft_FStar_Parser_AST.tm)) with
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
| Microsoft_FStar_Parser_AST.Name (tot) when (let _52_16005 = (let _52_16002 = (let _52_16001 = (Microsoft_FStar_Parser_DesugarEnv.is_effect_name env Microsoft_FStar_Absyn_Const.effect_Tot_lid)
in (not (_52_16001)))
in ((tot.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "Tot") && _52_16002))
in (let _52_16004 = (let _52_16003 = (Microsoft_FStar_Parser_DesugarEnv.current_module env)
in (Microsoft_FStar_Absyn_Syntax.lid_equals _52_16003 Microsoft_FStar_Absyn_Const.prims_lid))
in (_52_16005 && _52_16004))) -> begin
(let args = (Support.List.map (fun ( _41_1786  :  (Microsoft_FStar_Parser_AST.term * Microsoft_FStar_Parser_AST.imp) ) -> (match (_41_1786) with
| (t, imp) -> begin
(let _52_16007 = (desugar_typ_or_exp env t)
in (Support.Prims.pipe_left (arg_withimp_t imp) _52_16007))
end)) args)
in (let _52_16008 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.effect_Tot_lid Microsoft_FStar_Absyn_Syntax.kun)
in (Microsoft_FStar_Absyn_Util.mk_typ_app _52_16008 args)))
end
| _ -> begin
(desugar_typ env t)
end)
end)))
in (let t = (pre_process_comp_typ t)
in (let _41_1793 = (Microsoft_FStar_Absyn_Util.head_and_args t)
in (match (_41_1793) with
| (head, args) -> begin
(match ((let _52_16010 = (let _52_16009 = (Microsoft_FStar_Absyn_Util.compress_typ head)
in _52_16009.Microsoft_FStar_Absyn_Syntax.n)
in (_52_16010, args))) with
| (Microsoft_FStar_Absyn_Syntax.Typ_const (eff), (Support.Microsoft.FStar.Util.Inl (result_typ), _)::rest) -> begin
(let _41_1840 = (Support.Prims.pipe_right rest (Support.List.partition (fun ( _41_10  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_41_10) with
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
(let decreases_clause = (Support.Prims.pipe_right dec (Support.List.map (fun ( _41_11  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_41_11) with
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
in (match ((let _52_16013 = (Microsoft_FStar_Parser_DesugarEnv.is_effect_name env eff.Microsoft_FStar_Absyn_Syntax.v)
in (_52_16013 || (Microsoft_FStar_Absyn_Syntax.lid_equals eff.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.effect_Tot_lid)))) with
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
(Microsoft_FStar_Parser_DesugarEnv_Mkenv.default_result_effect env t r)
end
| false -> begin
(let _52_16015 = (let _52_16014 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "%s is not an effect" _52_16014))
in (fail _52_16015))
end)
end))
end))
end
| _ -> begin
(match (default_ok) with
| true -> begin
(Microsoft_FStar_Parser_DesugarEnv_Mkenv.default_result_effect env t r)
end
| false -> begin
(let _52_16017 = (let _52_16016 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "%s is not an effect" _52_16016))
in (fail _52_16017))
end)
end)
end))))))
and desugar_kind = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( k  :  Microsoft_FStar_Parser_AST.term ) -> (let pos = (fun ( f  :  Support.Microsoft.FStar.Range.range  ->  Microsoft_FStar_Absyn_Syntax.knd ) -> (f k.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( kk  :  (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _41_1871 = kk
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
(match ((let _52_16029 = (Microsoft_FStar_Parser_DesugarEnv.qualify_lid env l)
in (Microsoft_FStar_Parser_DesugarEnv.find_kind_abbrev env _52_16029))) with
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
(let rec aux = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( bs  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) ( _41_12  :  Microsoft_FStar_Parser_AST.binder list ) -> (match (_41_12) with
| [] -> begin
(let _52_16040 = (let _52_16039 = (let _52_16038 = (desugar_kind env k)
in ((Support.List.rev bs), _52_16038))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_16039))
in (Support.Prims.pipe_left pos _52_16040))
end
| hd::tl -> begin
(let _41_1916 = (let _52_16042 = (let _52_16041 = (Microsoft_FStar_Parser_DesugarEnv.default_ml env)
in (desugar_binder _52_16041 hd))
in (Support.Prims.pipe_right _52_16042 (as_binder env hd.Microsoft_FStar_Parser_AST.aqual)))
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
(let args = (Support.List.map (fun ( _41_1926  :  (Microsoft_FStar_Parser_AST.term * Microsoft_FStar_Parser_AST.imp) ) -> (match (_41_1926) with
| (t, b) -> begin
(let qual = (match ((b = Microsoft_FStar_Parser_AST.Hash)) with
| true -> begin
Some (Microsoft_FStar_Absyn_Syntax.Implicit)
end
| false -> begin
None
end)
in (let _52_16044 = (desugar_typ_or_exp env t)
in (_52_16044, qual)))
end)) args)
in (Support.Prims.pipe_left pos (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown))))
end)
end
| _ -> begin
(Microsoft_FStar_Parser_AST.error "Unexpected term where kind was expected" k k.Microsoft_FStar_Parser_AST.range)
end)))))
and desugar_formula' = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( f  :  Microsoft_FStar_Parser_AST.term ) -> (let connective = (fun ( s  :  string ) -> (match (s) with
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
in (let pos = (fun ( t  :  Microsoft_FStar_Absyn_Syntax.knd option  ->  Support.Microsoft.FStar.Range.range  ->  Microsoft_FStar_Absyn_Syntax.typ ) -> (t None f.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun ( t  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _41_1946 = t
in {Microsoft_FStar_Absyn_Syntax.n = _41_1946.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _41_1946.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = f.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _41_1946.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _41_1946.Microsoft_FStar_Absyn_Syntax.uvs}))
in (let desugar_quant = (fun ( q  :  Microsoft_FStar_Absyn_Syntax.lident ) ( qt  :  Microsoft_FStar_Absyn_Syntax.lident ) ( b  :  Microsoft_FStar_Parser_AST.binder ) ( pats  :  Microsoft_FStar_Parser_AST.term list ) ( body  :  Microsoft_FStar_Parser_AST.term ) -> (let tk = (desugar_binder env (let _41_1954 = b
in {Microsoft_FStar_Parser_AST.b = _41_1954.Microsoft_FStar_Parser_AST.b; Microsoft_FStar_Parser_AST.brange = _41_1954.Microsoft_FStar_Parser_AST.brange; Microsoft_FStar_Parser_AST.blevel = Microsoft_FStar_Parser_AST.Formula; Microsoft_FStar_Parser_AST.aqual = _41_1954.Microsoft_FStar_Parser_AST.aqual}))
in (match (tk) with
| Support.Microsoft.FStar.Util.Inl ((Some (a), k)) -> begin
(let _41_1964 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_41_1964) with
| (env, a) -> begin
(let pats = (Support.List.map (fun ( e  :  Microsoft_FStar_Parser_AST.term ) -> (let _52_16075 = (desugar_typ_or_exp env e)
in (Support.Prims.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _52_16075))) pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _ -> begin
(let _52_16076 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
in (Support.Prims.pipe_left setpos _52_16076))
end)
in (let body = (let _52_16082 = (let _52_16081 = (let _52_16080 = (let _52_16079 = (Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_52_16079)::[])
in (_52_16080, body))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _52_16081))
in (Support.Prims.pipe_left pos _52_16082))
in (let _52_16087 = (let _52_16086 = (let _52_16083 = (Microsoft_FStar_Absyn_Util.set_lid_range qt b.Microsoft_FStar_Parser_AST.brange)
in (Microsoft_FStar_Absyn_Util.ftv _52_16083 Microsoft_FStar_Absyn_Syntax.kun))
in (let _52_16085 = (let _52_16084 = (Microsoft_FStar_Absyn_Syntax.targ body)
in (_52_16084)::[])
in (Microsoft_FStar_Absyn_Util.mk_typ_app _52_16086 _52_16085)))
in (Support.Prims.pipe_left setpos _52_16087))))))
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _41_1980 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_41_1980) with
| (env, x) -> begin
(let pats = (Support.List.map (fun ( e  :  Microsoft_FStar_Parser_AST.term ) -> (let _52_16089 = (desugar_typ_or_exp env e)
in (Support.Prims.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _52_16089))) pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
end)
in (let body = (let _52_16095 = (let _52_16094 = (let _52_16093 = (let _52_16092 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_52_16092)::[])
in (_52_16093, body))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _52_16094))
in (Support.Prims.pipe_left pos _52_16095))
in (let _52_16100 = (let _52_16099 = (let _52_16096 = (Microsoft_FStar_Absyn_Util.set_lid_range q b.Microsoft_FStar_Parser_AST.brange)
in (Microsoft_FStar_Absyn_Util.ftv _52_16096 Microsoft_FStar_Absyn_Syntax.kun))
in (let _52_16098 = (let _52_16097 = (Microsoft_FStar_Absyn_Syntax.targ body)
in (_52_16097)::[])
in (Microsoft_FStar_Absyn_Util.mk_typ_app _52_16099 _52_16098)))
in (Support.Prims.pipe_left setpos _52_16100))))))
end))
end
| _ -> begin
(failwith ("impossible"))
end)))
in (let push_quant = (fun ( q  :  (Microsoft_FStar_Parser_AST.binder list * Microsoft_FStar_Parser_AST.term list * Microsoft_FStar_Parser_AST.term)  ->  Microsoft_FStar_Parser_AST.term' ) ( binders  :  Microsoft_FStar_Parser_AST.binder list ) ( pats  :  Microsoft_FStar_Parser_AST.term list ) ( body  :  Microsoft_FStar_Parser_AST.term ) -> (match (binders) with
| b::b'::_rest -> begin
(let rest = (b')::_rest
in (let body = (let _52_16115 = (q (rest, pats, body))
in (let _52_16114 = (Support.Microsoft.FStar.Range.union_ranges b'.Microsoft_FStar_Parser_AST.brange body.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Parser_AST.mk_term _52_16115 _52_16114 Microsoft_FStar_Parser_AST.Formula)))
in (let _52_16116 = (q ((b)::[], [], body))
in (Microsoft_FStar_Parser_AST.mk_term _52_16116 f.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Formula))))
end
| _ -> begin
(failwith ("impossible"))
end))
in (match ((let _52_16117 = (unparen f)
in _52_16117.Microsoft_FStar_Parser_AST.tm)) with
| Microsoft_FStar_Parser_AST.Labeled ((f, l, p)) -> begin
(let f = (desugar_formula env f)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((f, l, Microsoft_FStar_Absyn_Syntax.dummyRange, p)))))
end
| Microsoft_FStar_Parser_AST.Op (("==", hd::_args)) -> begin
(let args = (hd)::_args
in (let args = (Support.List.map (fun ( t  :  Microsoft_FStar_Parser_AST.term ) -> (let _52_16119 = (desugar_typ_or_exp env t)
in (Support.Prims.pipe_left (arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) _52_16119))) args)
in (let eq = (match ((is_type env hd)) with
| true -> begin
(let _52_16120 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.eqT_lid f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _52_16120 Microsoft_FStar_Absyn_Syntax.kun))
end
| false -> begin
(let _52_16121 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.eq2_lid f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _52_16121 Microsoft_FStar_Absyn_Syntax.kun))
end)
in (Microsoft_FStar_Absyn_Util.mk_typ_app eq args))))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match (((connective s), args)) with
| (Some (conn), _::_::[]) -> begin
(let _52_16126 = (let _52_16122 = (Microsoft_FStar_Absyn_Util.set_lid_range conn f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _52_16122 Microsoft_FStar_Absyn_Syntax.kun))
in (let _52_16125 = (Support.List.map (fun ( x  :  Microsoft_FStar_Parser_AST.term ) -> (let _52_16124 = (desugar_formula env x)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _52_16124))) args)
in (Microsoft_FStar_Absyn_Util.mk_typ_app _52_16126 _52_16125)))
end
| _ -> begin
(match ((is_type env f)) with
| true -> begin
(desugar_typ env f)
end
| false -> begin
(let _52_16127 = (desugar_exp env f)
in (Support.Prims.pipe_right _52_16127 Microsoft_FStar_Absyn_Util.b2t))
end)
end)
end
| Microsoft_FStar_Parser_AST.If ((f1, f2, f3)) -> begin
(let _52_16132 = (let _52_16128 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.ite_lid f.Microsoft_FStar_Parser_AST.range)
in (Microsoft_FStar_Absyn_Util.ftv _52_16128 Microsoft_FStar_Absyn_Syntax.kun))
in (let _52_16131 = (Support.List.map (fun ( x  :  Microsoft_FStar_Parser_AST.term ) -> (match ((desugar_typ_or_exp env x)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| Support.Microsoft.FStar.Util.Inr (v) -> begin
(let _52_16130 = (Microsoft_FStar_Absyn_Util.b2t v)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _52_16130))
end)) ((f1)::(f2)::(f3)::[]))
in (Microsoft_FStar_Absyn_Util.mk_typ_app _52_16132 _52_16131)))
end
| Microsoft_FStar_Parser_AST.QForall ((_1::_2::_3, pats, body)) -> begin
(let binders = (_1)::(_2)::_3
in (let _52_16134 = (push_quant (fun ( x  :  (Microsoft_FStar_Parser_AST.binder list * Microsoft_FStar_Parser_AST.term list * Microsoft_FStar_Parser_AST.term) ) -> Microsoft_FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _52_16134)))
end
| Microsoft_FStar_Parser_AST.QExists ((_1::_2::_3, pats, body)) -> begin
(let binders = (_1)::(_2)::_3
in (let _52_16136 = (push_quant (fun ( x  :  (Microsoft_FStar_Parser_AST.binder list * Microsoft_FStar_Parser_AST.term list * Microsoft_FStar_Parser_AST.term) ) -> Microsoft_FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _52_16136)))
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
(let _52_16137 = (desugar_exp env f)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Util.b2t _52_16137))
end)
end)))))))
and desugar_formula = (fun ( env  :  env_t ) ( t  :  Microsoft_FStar_Parser_AST.term ) -> (desugar_formula' (let _41_2086 = env
in {Microsoft_FStar_Parser_DesugarEnv.curmodule = _41_2086.Microsoft_FStar_Parser_DesugarEnv.curmodule; Microsoft_FStar_Parser_DesugarEnv.modules = _41_2086.Microsoft_FStar_Parser_DesugarEnv.modules; Microsoft_FStar_Parser_DesugarEnv.open_namespaces = _41_2086.Microsoft_FStar_Parser_DesugarEnv.open_namespaces; Microsoft_FStar_Parser_DesugarEnv.sigaccum = _41_2086.Microsoft_FStar_Parser_DesugarEnv.sigaccum; Microsoft_FStar_Parser_DesugarEnv.localbindings = _41_2086.Microsoft_FStar_Parser_DesugarEnv.localbindings; Microsoft_FStar_Parser_DesugarEnv.recbindings = _41_2086.Microsoft_FStar_Parser_DesugarEnv.recbindings; Microsoft_FStar_Parser_DesugarEnv.phase = Microsoft_FStar_Parser_AST.Formula; Microsoft_FStar_Parser_DesugarEnv.sigmap = _41_2086.Microsoft_FStar_Parser_DesugarEnv.sigmap; Microsoft_FStar_Parser_DesugarEnv.default_result_effect = _41_2086.Microsoft_FStar_Parser_DesugarEnv.default_result_effect; Microsoft_FStar_Parser_DesugarEnv.iface = _41_2086.Microsoft_FStar_Parser_DesugarEnv.iface; Microsoft_FStar_Parser_DesugarEnv.admitted_iface = _41_2086.Microsoft_FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( b  :  Microsoft_FStar_Parser_AST.binder ) -> (match ((is_type_binder env b)) with
| true -> begin
(let _52_16142 = (desugar_type_binder env b)
in Support.Microsoft.FStar.Util.Inl (_52_16142))
end
| false -> begin
(let _52_16143 = (desugar_exp_binder env b)
in Support.Microsoft.FStar.Util.Inr (_52_16143))
end))
and typars_of_binders = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( bs  :  Microsoft_FStar_Parser_AST.binder list ) -> (let _41_2119 = (Support.List.fold_left (fun ( _41_2094  :  (Microsoft_FStar_Parser_DesugarEnv.env * ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, Microsoft_FStar_Absyn_Syntax.knd) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, Microsoft_FStar_Absyn_Syntax.typ) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.aqual) list) ) ( b  :  Microsoft_FStar_Parser_AST.binder ) -> (match (_41_2094) with
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
and desugar_exp_binder = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( b  :  Microsoft_FStar_Parser_AST.binder ) -> (match (b.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Annotated ((x, t)) -> begin
(let _52_16150 = (desugar_typ env t)
in (Some (x), _52_16150))
end
| Microsoft_FStar_Parser_AST.TVariable (t) -> begin
(let _52_16151 = (Microsoft_FStar_Parser_DesugarEnv.fail_or2 (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in (None, _52_16151))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(let _52_16152 = (desugar_typ env t)
in (None, _52_16152))
end
| Microsoft_FStar_Parser_AST.Variable (x) -> begin
(Some (x), Microsoft_FStar_Absyn_Syntax.tun)
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a type)", b.Microsoft_FStar_Parser_AST.brange))))
end))
and desugar_type_binder = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( b  :  Microsoft_FStar_Parser_AST.binder ) -> (let fail = (fun ( _41_2137  :  unit ) -> (match (()) with
| () -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a kind)", b.Microsoft_FStar_Parser_AST.brange))))
end))
in (match (b.Microsoft_FStar_Parser_AST.b) with
| (Microsoft_FStar_Parser_AST.Annotated ((x, t))) | (Microsoft_FStar_Parser_AST.TAnnotated ((x, t))) -> begin
(let _52_16157 = (desugar_kind env t)
in (Some (x), _52_16157))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(let _52_16158 = (desugar_kind env t)
in (None, _52_16158))
end
| Microsoft_FStar_Parser_AST.TVariable (x) -> begin
(Some (x), (let _41_2148 = Microsoft_FStar_Absyn_Syntax.mk_Kind_type
in {Microsoft_FStar_Absyn_Syntax.n = _41_2148.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _41_2148.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = b.Microsoft_FStar_Parser_AST.brange; Microsoft_FStar_Absyn_Syntax.fvs = _41_2148.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _41_2148.Microsoft_FStar_Absyn_Syntax.uvs}))
end
| _ -> begin
(fail ())
end)))

let gather_tc_binders = (fun ( tps  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) ( k  :  (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let rec aux = (fun ( bs  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) ( k  :  (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((binders, k)) -> begin
(aux (Support.List.append bs binders) k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(aux bs k)
end
| _ -> begin
bs
end))
in (let _52_16167 = (aux tps k)
in (Support.Prims.pipe_right _52_16167 Microsoft_FStar_Absyn_Util.name_binders))))

let mk_data_discriminators = (fun ( quals  :  Microsoft_FStar_Absyn_Syntax.qualifier list ) ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( t  :  Microsoft_FStar_Absyn_Syntax.lident ) ( tps  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) ( k  :  (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax ) ( datas  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent list ) -> (let quals = (fun ( q  :  Microsoft_FStar_Absyn_Syntax.qualifier list ) -> (match ((let _52_16182 = (Support.Prims.pipe_left Support.Prims.op_Negation env.Microsoft_FStar_Parser_DesugarEnv.iface)
in (_52_16182 || env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface))) with
| true -> begin
(Support.List.append ((Microsoft_FStar_Absyn_Syntax.Assumption)::q) quals)
end
| false -> begin
(Support.List.append q quals)
end))
in (let binders = (gather_tc_binders tps k)
in (let p = (Microsoft_FStar_Absyn_Syntax.range_of_lid t)
in (let imp_binders = (Support.Prims.pipe_right binders (Support.List.map (fun ( _41_2181  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_41_2181) with
| (x, _) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end))))
in (let binders = (let _52_16189 = (let _52_16188 = (let _52_16187 = (let _52_16186 = (let _52_16185 = (Microsoft_FStar_Absyn_Util.ftv t Microsoft_FStar_Absyn_Syntax.kun)
in (let _52_16184 = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (_52_16185, _52_16184)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' _52_16186 None p))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.null_v_binder _52_16187))
in (_52_16188)::[])
in (Support.List.append imp_binders _52_16189))
in (let disc_type = (let _52_16192 = (let _52_16191 = (let _52_16190 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.bool_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.total_comp _52_16190 p))
in (binders, _52_16191))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _52_16192 None p))
in (Support.Prims.pipe_right datas (Support.List.map (fun ( d  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) -> (let disc_name = (Microsoft_FStar_Absyn_Util.mk_discriminator d)
in (let _52_16196 = (let _52_16195 = (quals ((Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Discriminator (d))::[]))
in (let _52_16194 = (Microsoft_FStar_Absyn_Syntax.range_of_lid disc_name)
in (disc_name, disc_type, _52_16195, _52_16194)))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_52_16196)))))))))))))

let mk_indexed_projectors = (fun ( refine_domain  :  bool ) ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( _41_2192  :  (Microsoft_FStar_Absyn_Syntax.lident * ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list * (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) ) ( lid  :  Microsoft_FStar_Absyn_Syntax.lident ) ( formals  :  Microsoft_FStar_Absyn_Syntax.binder list ) ( t  :  'u41u40556 ) -> (match (_41_2192) with
| (tc, tps, k) -> begin
(let binders = (gather_tc_binders tps k)
in (let p = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (let arg_binder = (let arg_typ = (let _52_16205 = (let _52_16204 = (Microsoft_FStar_Absyn_Util.ftv tc Microsoft_FStar_Absyn_Syntax.kun)
in (let _52_16203 = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (_52_16204, _52_16203)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' _52_16205 None p))
in (let projectee = (let _52_16207 = (Microsoft_FStar_Absyn_Syntax.mk_ident ("projectee", p))
in (let _52_16206 = (Microsoft_FStar_Absyn_Util.genident (Some (p)))
in {Microsoft_FStar_Absyn_Syntax.ppname = _52_16207; Microsoft_FStar_Absyn_Syntax.realname = _52_16206}))
in (match ((not (refine_domain))) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end
| false -> begin
(let disc_name = (Microsoft_FStar_Absyn_Util.mk_discriminator lid)
in (let x = (Microsoft_FStar_Absyn_Util.gen_bvar arg_typ)
in (let _52_16217 = (let _52_16216 = (let _52_16215 = (let _52_16214 = (let _52_16213 = (let _52_16212 = (let _52_16211 = (Microsoft_FStar_Absyn_Util.fvar None disc_name p)
in (let _52_16210 = (let _52_16209 = (let _52_16208 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg _52_16208))
in (_52_16209)::[])
in (_52_16211, _52_16210)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _52_16212 None p))
in (Microsoft_FStar_Absyn_Util.b2t _52_16213))
in (x, _52_16214))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _52_16215 None p))
in (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s projectee) _52_16216))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.v_binder _52_16217))))
end)))
in (let imp_binders = (Support.Prims.pipe_right binders (Support.List.map (fun ( _41_2206  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_41_2206) with
| (x, _) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end))))
in (let binders = (Support.List.append imp_binders ((arg_binder)::[]))
in (let arg = (Microsoft_FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (let subst = (let _52_16227 = (Support.Prims.pipe_right formals (Support.List.mapi (fun ( i  :  int ) ( f  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match ((Support.Prims.fst f)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(match ((Support.Prims.pipe_right binders (Support.Microsoft.FStar.Util.for_some (fun ( _41_13  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_41_13) with
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
(let proj = (let _52_16223 = (let _52_16222 = (Microsoft_FStar_Absyn_Util.ftv field_name Microsoft_FStar_Absyn_Syntax.kun)
in (_52_16222, (arg)::[]))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_16223 None p))
in (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, proj)))::[])
end))
end)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(match ((Support.Prims.pipe_right binders (Support.Microsoft.FStar.Util.for_some (fun ( _41_14  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_41_14) with
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
(let proj = (let _52_16226 = (let _52_16225 = (Microsoft_FStar_Absyn_Util.fvar None field_name p)
in (_52_16225, (arg)::[]))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _52_16226 None p))
in (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, proj)))::[])
end))
end)
end))))
in (Support.Prims.pipe_right _52_16227 Support.List.flatten))
in (Support.Prims.pipe_right formals (Support.List.mapi (fun ( i  :  int ) ( ax  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, Microsoft_FStar_Absyn_Syntax.knd) Microsoft_FStar_Absyn_Syntax.bvar, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.bvar) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match ((Support.Prims.fst ax)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _41_2250 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_41_2250) with
| (field_name, _) -> begin
(let kk = (let _52_16231 = (let _52_16230 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (binders, _52_16230))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_16231 p))
in (let _52_16233 = (let _52_16232 = (Microsoft_FStar_Absyn_Syntax.range_of_lid field_name)
in (field_name, [], kk, [], [], (Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Projector ((lid, Support.Microsoft.FStar.Util.Inl (a.Microsoft_FStar_Absyn_Syntax.v))))::[], _52_16232))
in Microsoft_FStar_Absyn_Syntax.Sig_tycon (_52_16233)))
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _41_2257 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_41_2257) with
| (field_name, _) -> begin
(let t = (let _52_16236 = (let _52_16235 = (let _52_16234 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Absyn_Util.total_comp _52_16234 p))
in (binders, _52_16235))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _52_16236 None p))
in (let quals = (fun ( q  :  Microsoft_FStar_Absyn_Syntax.qualifier list ) -> (match (((not (env.Microsoft_FStar_Parser_DesugarEnv.iface)) || env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.Assumption)::q
end
| false -> begin
q
end))
in (let _52_16240 = (let _52_16239 = (Microsoft_FStar_Absyn_Syntax.range_of_lid field_name)
in (field_name, t, (quals ((Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Projector ((lid, Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.v))))::[])), _52_16239))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_52_16240))))
end))
end)))))))))))
end))

let mk_data_projectors = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( _41_16  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (match (_41_16) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, _, _)) when (not ((Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.lexcons_lid))) -> begin
(let refine_domain = (match ((Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _41_15  :  Microsoft_FStar_Absyn_Syntax.qualifier ) -> (match (_41_15) with
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

let rec desugar_tycon = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( rng  :  Support.Microsoft.FStar.Range.range ) ( quals  :  Microsoft_FStar_Absyn_Syntax.qualifier list ) ( tcs  :  Microsoft_FStar_Parser_AST.tycon list ) -> (let tycon_id = (fun ( _41_17  :  Microsoft_FStar_Parser_AST.tycon ) -> (match (_41_17) with
| (Microsoft_FStar_Parser_AST.TyconAbstract ((id, _, _))) | (Microsoft_FStar_Parser_AST.TyconAbbrev ((id, _, _, _))) | (Microsoft_FStar_Parser_AST.TyconRecord ((id, _, _, _))) | (Microsoft_FStar_Parser_AST.TyconVariant ((id, _, _, _))) -> begin
id
end))
in (let binder_to_term = (fun ( b  :  Microsoft_FStar_Parser_AST.binder ) -> (match (b.Microsoft_FStar_Parser_AST.b) with
| (Microsoft_FStar_Parser_AST.Annotated ((x, _))) | (Microsoft_FStar_Parser_AST.Variable (x)) -> begin
(let _52_16259 = (let _52_16258 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((x)::[]))
in Microsoft_FStar_Parser_AST.Var (_52_16258))
in (Microsoft_FStar_Parser_AST.mk_term _52_16259 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr))
end
| (Microsoft_FStar_Parser_AST.TAnnotated ((a, _))) | (Microsoft_FStar_Parser_AST.TVariable (a)) -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Tvar (a)) a.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type)
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
t
end))
in (let tot = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.effect_Tot_lid)) rng Microsoft_FStar_Parser_AST.Expr)
in (let with_constructor_effect = (fun ( t  :  Microsoft_FStar_Parser_AST.term ) -> (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.App ((tot, t, Microsoft_FStar_Parser_AST.Nothing))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level))
in (let apply_binders = (fun ( t  :  Microsoft_FStar_Parser_AST.term ) ( binders  :  Microsoft_FStar_Parser_AST.binder list ) -> (Support.List.fold_left (fun ( out  :  Microsoft_FStar_Parser_AST.term ) ( b  :  Microsoft_FStar_Parser_AST.binder ) -> (let _52_16270 = (let _52_16269 = (let _52_16268 = (binder_to_term b)
in (out, _52_16268, Microsoft_FStar_Parser_AST.Nothing))
in Microsoft_FStar_Parser_AST.App (_52_16269))
in (Microsoft_FStar_Parser_AST.mk_term _52_16270 out.Microsoft_FStar_Parser_AST.range out.Microsoft_FStar_Parser_AST.level))) t binders))
in (let tycon_record_as_variant = (fun ( _41_18  :  Microsoft_FStar_Parser_AST.tycon ) -> (match (_41_18) with
| Microsoft_FStar_Parser_AST.TyconRecord ((id, parms, kopt, fields)) -> begin
(let constrName = (Microsoft_FStar_Absyn_Syntax.mk_ident ((Support.String.strcat "Mk" id.Microsoft_FStar_Absyn_Syntax.idText), id.Microsoft_FStar_Absyn_Syntax.idRange))
in (let mfields = (Support.List.map (fun ( _41_2370  :  (Microsoft_FStar_Absyn_Syntax.ident * Microsoft_FStar_Parser_AST.term) ) -> (match (_41_2370) with
| (x, t) -> begin
(let _52_16276 = (let _52_16275 = (let _52_16274 = (Microsoft_FStar_Absyn_Util.mangle_field_name x)
in (_52_16274, t))
in Microsoft_FStar_Parser_AST.Annotated (_52_16275))
in (Microsoft_FStar_Parser_AST.mk_binder _52_16276 x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr None))
end)) fields)
in (let result = (let _52_16279 = (let _52_16278 = (let _52_16277 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id)::[]))
in Microsoft_FStar_Parser_AST.Var (_52_16277))
in (Microsoft_FStar_Parser_AST.mk_term _52_16278 id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type))
in (apply_binders _52_16279 parms))
in (let constrTyp = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type)
in (let _52_16281 = (Support.Prims.pipe_right fields (Support.List.map (fun ( _41_2377  :  (Microsoft_FStar_Absyn_Syntax.ident * Microsoft_FStar_Parser_AST.term) ) -> (match (_41_2377) with
| (x, _) -> begin
(Microsoft_FStar_Parser_DesugarEnv.qualify env x)
end))))
in (Microsoft_FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _52_16281))))))
end
| _ -> begin
(failwith ("impossible"))
end))
in (let desugar_abstract_tc = (fun ( quals  :  Microsoft_FStar_Absyn_Syntax.qualifier list ) ( _env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( mutuals  :  Microsoft_FStar_Absyn_Syntax.lident list ) ( _41_19  :  Microsoft_FStar_Parser_AST.tycon ) -> (match (_41_19) with
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
in (let tconstr = (let _52_16292 = (let _52_16291 = (let _52_16290 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id)::[]))
in Microsoft_FStar_Parser_AST.Var (_52_16290))
in (Microsoft_FStar_Parser_AST.mk_term _52_16291 id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type))
in (apply_binders _52_16292 binders))
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
in (let push_tparam = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( _41_20  :  (((Microsoft_FStar_Absyn_Syntax.btvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, (Microsoft_FStar_Absyn_Syntax.bvvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.aqual) ) -> (match (_41_20) with
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
(match ((Support.Microsoft.FStar.Util.for_some (fun ( _41_21  :  Microsoft_FStar_Absyn_Syntax.qualifier ) -> (match (_41_21) with
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
in (let quals = (match ((Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _41_22  :  Microsoft_FStar_Absyn_Syntax.qualifier ) -> (match (_41_22) with
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
in (let _52_16304 = (let _52_16303 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (let _52_16302 = (Support.Prims.pipe_right quals (Support.List.filter (fun ( _41_23  :  Microsoft_FStar_Absyn_Syntax.qualifier ) -> (match (_41_23) with
| Microsoft_FStar_Absyn_Syntax.Effect -> begin
false
end
| _ -> begin
true
end))))
in (_52_16303, typars, c, _52_16302, rng)))
in Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_52_16304)))
end
| false -> begin
(let t = (desugar_typ env' t)
in (let _52_16306 = (let _52_16305 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (_52_16305, typars, k, t, quals, rng))
in Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_52_16306)))
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
in (let mutuals = (Support.List.map (fun ( x  :  Microsoft_FStar_Parser_AST.tycon ) -> (Support.Prims.pipe_left (Microsoft_FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (let rec collect_tcs = (fun ( quals  :  Microsoft_FStar_Absyn_Syntax.qualifier list ) ( et  :  (Microsoft_FStar_Parser_DesugarEnv.env * ((Microsoft_FStar_Absyn_Syntax.sigelt * ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, Microsoft_FStar_Absyn_Syntax.knd) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, Microsoft_FStar_Absyn_Syntax.typ) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.aqual) list * (Microsoft_FStar_Absyn_Syntax.ident * Microsoft_FStar_Parser_AST.term option * bool) list * Microsoft_FStar_Parser_AST.term * Microsoft_FStar_Absyn_Syntax.qualifier list), (Microsoft_FStar_Absyn_Syntax.sigelt * ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, Microsoft_FStar_Absyn_Syntax.knd) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, Microsoft_FStar_Absyn_Syntax.typ) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.aqual) list * Microsoft_FStar_Parser_AST.term * Microsoft_FStar_Absyn_Syntax.qualifier list)) Support.Microsoft.FStar.Util.either list) ) ( tc  :  Microsoft_FStar_Parser_AST.tycon ) -> (let _41_2487 = et
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
in (let sigelts = (Support.Prims.pipe_right tcs (Support.List.collect (fun ( _41_25  :  ((Microsoft_FStar_Absyn_Syntax.sigelt * (((Microsoft_FStar_Absyn_Syntax.btvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, (Microsoft_FStar_Absyn_Syntax.bvvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.aqual) list * (Microsoft_FStar_Absyn_Syntax.ident * Microsoft_FStar_Parser_AST.term option * bool) list * Microsoft_FStar_Parser_AST.term * Microsoft_FStar_Absyn_Syntax.qualifier list), (Microsoft_FStar_Absyn_Syntax.sigelt * (((Microsoft_FStar_Absyn_Syntax.btvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, (Microsoft_FStar_Absyn_Syntax.bvvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.aqual) list * Microsoft_FStar_Parser_AST.term * Microsoft_FStar_Absyn_Syntax.qualifier list)) Support.Microsoft.FStar.Util.either ) -> (match (_41_25) with
| Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Syntax.Sig_tycon ((id, tpars, k, _, _, _, _)), tps, t, quals)) -> begin
(let env_tps = (push_tparams env tps)
in (let t = (desugar_typ env_tps t)
in (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((id, tpars, k, t, [], rng)))::[]))
end
| Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, _, tags, _)), tps, constrs, tconstr, quals)) -> begin
(let tycon = (tname, tpars, k)
in (let env_tps = (push_tparams env tps)
in (let _41_2594 = (let _52_16325 = (Support.Prims.pipe_right constrs (Support.List.map (fun ( _41_2572  :  (Microsoft_FStar_Absyn_Syntax.ident * Microsoft_FStar_Parser_AST.term option * bool) ) -> (match (_41_2572) with
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
in (let t = (let _52_16317 = (Microsoft_FStar_Parser_DesugarEnv.default_total env_tps)
in (let _52_16316 = (close env_tps t)
in (desugar_typ _52_16317 _52_16316)))
in (let name = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (let quals = (Support.Prims.pipe_right tags (Support.List.collect (fun ( _41_24  :  Microsoft_FStar_Absyn_Syntax.qualifier ) -> (match (_41_24) with
| Microsoft_FStar_Absyn_Syntax.RecordType (fns) -> begin
(Microsoft_FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _ -> begin
[]
end))))
in (let _52_16324 = (let _52_16323 = (let _52_16322 = (let _52_16321 = (let _52_16320 = (Support.List.map (fun ( _41_2591  :  (((Microsoft_FStar_Absyn_Syntax.btvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, (Microsoft_FStar_Absyn_Syntax.bvvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.aqual) ) -> (match (_41_2591) with
| (x, _) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end)) tps)
in (Microsoft_FStar_Absyn_Util.close_typ _52_16320 t))
in (Support.Prims.pipe_right _52_16321 Microsoft_FStar_Absyn_Util.name_function_binders))
in (name, _52_16322, tycon, quals, mutuals, rng))
in Microsoft_FStar_Absyn_Syntax.Sig_datacon (_52_16323))
in (name, _52_16324))))))
end))))
in (Support.Prims.pipe_left Support.List.split _52_16325))
in (match (_41_2594) with
| (constrNames, constrs) -> begin
(Microsoft_FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, constrNames, tags, rng)))::constrs
end))))
end
| _ -> begin
(failwith ("impossible"))
end))))
in (let bundle = (let _52_16327 = (let _52_16326 = (Support.List.collect Microsoft_FStar_Absyn_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _52_16326, rng))
in Microsoft_FStar_Absyn_Syntax.Sig_bundle (_52_16327))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (let data_ops = (Support.Prims.pipe_right sigelts (Support.List.collect (mk_data_projectors env)))
in (let discs = (Support.Prims.pipe_right sigelts (Support.List.collect (fun ( _41_26  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (match (_41_26) with
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

let desugar_binders = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( binders  :  Microsoft_FStar_Parser_AST.binder list ) -> (let _41_2645 = (Support.List.fold_left (fun ( _41_2623  :  (Microsoft_FStar_Parser_DesugarEnv.env * Microsoft_FStar_Absyn_Syntax.binder list) ) ( b  :  Microsoft_FStar_Parser_AST.binder ) -> (match (_41_2623) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| Support.Microsoft.FStar.Util.Inl ((Some (a), k)) -> begin
(let _41_2632 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_41_2632) with
| (env, a) -> begin
(let _52_16336 = (let _52_16335 = (Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_52_16335)::binders)
in (env, _52_16336))
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _41_2640 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_41_2640) with
| (env, x) -> begin
(let _52_16338 = (let _52_16337 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_52_16337)::binders)
in (env, _52_16338))
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

let rec desugar_decl = (fun ( env  :  env_t ) ( d  :  Microsoft_FStar_Parser_AST.decl ) -> (match (d.Microsoft_FStar_Parser_AST.d) with
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
(match ((let _52_16344 = (let _52_16343 = (desugar_exp_maybe_top true env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Let ((isrec, lets, (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Const (Microsoft_FStar_Absyn_Syntax.Const_unit)) d.Microsoft_FStar_Parser_AST.drange Microsoft_FStar_Parser_AST.Expr)))) d.Microsoft_FStar_Parser_AST.drange Microsoft_FStar_Parser_AST.Expr))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Util.compress_exp _52_16343))
in _52_16344.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, _)) -> begin
(let lids = (Support.Prims.pipe_right (Support.Prims.snd lbs) (Support.List.map (fun ( lb  :  Microsoft_FStar_Absyn_Syntax.letbinding ) -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inr (l) -> begin
l
end
| _ -> begin
(failwith ("impossible"))
end))))
in (let quals = (Support.Prims.pipe_right (Support.Prims.snd lbs) (Support.List.collect (fun ( _41_27  :  Microsoft_FStar_Absyn_Syntax.letbinding ) -> (match (_41_27) with
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
in (let _52_16350 = (let _52_16349 = (let _52_16348 = (let _52_16347 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (_52_16347, f, (Microsoft_FStar_Absyn_Syntax.Assumption)::[], d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Sig_assume (_52_16348))
in (_52_16349)::[])
in (env, _52_16350)))
end
| Microsoft_FStar_Parser_AST.Val ((quals, id, t)) -> begin
(let t = (let _52_16351 = (close_fun env t)
in (desugar_typ env _52_16351))
in (let quals = (match ((env.Microsoft_FStar_Parser_DesugarEnv.iface && env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.Assumption)::quals
end
| false -> begin
quals
end)
in (let se = (let _52_16353 = (let _52_16352 = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (_52_16352, t, quals, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_52_16353))
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
in (let t = (let _52_16358 = (let _52_16357 = (let _52_16354 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_52_16354)::[])
in (let _52_16356 = (let _52_16355 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) Microsoft_FStar_Absyn_Const.exn_lid)
in (Microsoft_FStar_Absyn_Syntax.mk_Total _52_16355))
in (_52_16357, _52_16356)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _52_16358 None d.Microsoft_FStar_Parser_AST.drange))
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
(let _52_16363 = (let _52_16362 = (let _52_16361 = (let _52_16360 = (let _52_16359 = (Microsoft_FStar_Absyn_Print.sli eff.Microsoft_FStar_Absyn_Syntax.v)
in (Support.String.strcat "Effect " _52_16359))
in (Support.String.strcat _52_16360 " not found"))
in (_52_16361, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Error (_52_16362))
in (raise (_52_16363)))
end
| Some (ed) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.subst_of_list ed.Microsoft_FStar_Absyn_Syntax.binders args)
in (let sub = (Microsoft_FStar_Absyn_Util.subst_typ subst)
in (let ed = (let _52_16380 = (Microsoft_FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _52_16379 = (Microsoft_FStar_Absyn_Util.subst_kind subst ed.Microsoft_FStar_Absyn_Syntax.signature)
in (let _52_16378 = (sub ed.Microsoft_FStar_Absyn_Syntax.ret)
in (let _52_16377 = (sub ed.Microsoft_FStar_Absyn_Syntax.bind_wp)
in (let _52_16376 = (sub ed.Microsoft_FStar_Absyn_Syntax.bind_wlp)
in (let _52_16375 = (sub ed.Microsoft_FStar_Absyn_Syntax.if_then_else)
in (let _52_16374 = (sub ed.Microsoft_FStar_Absyn_Syntax.ite_wp)
in (let _52_16373 = (sub ed.Microsoft_FStar_Absyn_Syntax.ite_wlp)
in (let _52_16372 = (sub ed.Microsoft_FStar_Absyn_Syntax.wp_binop)
in (let _52_16371 = (sub ed.Microsoft_FStar_Absyn_Syntax.wp_as_type)
in (let _52_16370 = (sub ed.Microsoft_FStar_Absyn_Syntax.close_wp)
in (let _52_16369 = (sub ed.Microsoft_FStar_Absyn_Syntax.close_wp_t)
in (let _52_16368 = (sub ed.Microsoft_FStar_Absyn_Syntax.assert_p)
in (let _52_16367 = (sub ed.Microsoft_FStar_Absyn_Syntax.assume_p)
in (let _52_16366 = (sub ed.Microsoft_FStar_Absyn_Syntax.null_wp)
in (let _52_16365 = (sub ed.Microsoft_FStar_Absyn_Syntax.trivial)
in {Microsoft_FStar_Absyn_Syntax.mname = _52_16380; Microsoft_FStar_Absyn_Syntax.binders = binders; Microsoft_FStar_Absyn_Syntax.qualifiers = quals; Microsoft_FStar_Absyn_Syntax.signature = _52_16379; Microsoft_FStar_Absyn_Syntax.ret = _52_16378; Microsoft_FStar_Absyn_Syntax.bind_wp = _52_16377; Microsoft_FStar_Absyn_Syntax.bind_wlp = _52_16376; Microsoft_FStar_Absyn_Syntax.if_then_else = _52_16375; Microsoft_FStar_Absyn_Syntax.ite_wp = _52_16374; Microsoft_FStar_Absyn_Syntax.ite_wlp = _52_16373; Microsoft_FStar_Absyn_Syntax.wp_binop = _52_16372; Microsoft_FStar_Absyn_Syntax.wp_as_type = _52_16371; Microsoft_FStar_Absyn_Syntax.close_wp = _52_16370; Microsoft_FStar_Absyn_Syntax.close_wp_t = _52_16369; Microsoft_FStar_Absyn_Syntax.assert_p = _52_16368; Microsoft_FStar_Absyn_Syntax.assume_p = _52_16367; Microsoft_FStar_Absyn_Syntax.null_wp = _52_16366; Microsoft_FStar_Absyn_Syntax.trivial = _52_16365}))))))))))))))))
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ed, d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)
end
| _ -> begin
(let _52_16384 = (let _52_16383 = (let _52_16382 = (let _52_16381 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (Support.String.strcat _52_16381 " is not an effect"))
in (_52_16382, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Error (_52_16383))
in (raise (_52_16384)))
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
in (let _41_2807 = (Support.Prims.pipe_right eff_decls (Support.List.fold_left (fun ( _41_2800  :  (env_t * Microsoft_FStar_Absyn_Syntax.sigelt list) ) ( decl  :  Microsoft_FStar_Parser_AST.decl ) -> (match (_41_2800) with
| (env, out) -> begin
(let _41_2804 = (desugar_decl env decl)
in (match (_41_2804) with
| (env, ses) -> begin
(let _52_16388 = (let _52_16387 = (Support.List.hd ses)
in (_52_16387)::out)
in (env, _52_16388))
end))
end)) (env, [])))
in (match (_41_2807) with
| (env, decls) -> begin
(let decls = (Support.List.rev decls)
in (let lookup = (fun ( s  :  string ) -> (match ((let _52_16392 = (let _52_16391 = (Microsoft_FStar_Absyn_Syntax.mk_ident (s, d.Microsoft_FStar_Parser_AST.drange))
in (Microsoft_FStar_Parser_DesugarEnv.qualify env _52_16391))
in (Microsoft_FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _52_16392))) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat (Support.String.strcat (Support.String.strcat "Monad " eff_name.Microsoft_FStar_Absyn_Syntax.idText) " expects definition of ") s), d.Microsoft_FStar_Parser_AST.drange))))
end
| Some (t) -> begin
t
end))
in (let ed = (let _52_16407 = (Microsoft_FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _52_16406 = (lookup "return")
in (let _52_16405 = (lookup "bind_wp")
in (let _52_16404 = (lookup "bind_wlp")
in (let _52_16403 = (lookup "if_then_else")
in (let _52_16402 = (lookup "ite_wp")
in (let _52_16401 = (lookup "ite_wlp")
in (let _52_16400 = (lookup "wp_binop")
in (let _52_16399 = (lookup "wp_as_type")
in (let _52_16398 = (lookup "close_wp")
in (let _52_16397 = (lookup "close_wp_t")
in (let _52_16396 = (lookup "assert_p")
in (let _52_16395 = (lookup "assume_p")
in (let _52_16394 = (lookup "null_wp")
in (let _52_16393 = (lookup "trivial")
in {Microsoft_FStar_Absyn_Syntax.mname = _52_16407; Microsoft_FStar_Absyn_Syntax.binders = binders; Microsoft_FStar_Absyn_Syntax.qualifiers = quals; Microsoft_FStar_Absyn_Syntax.signature = eff_k; Microsoft_FStar_Absyn_Syntax.ret = _52_16406; Microsoft_FStar_Absyn_Syntax.bind_wp = _52_16405; Microsoft_FStar_Absyn_Syntax.bind_wlp = _52_16404; Microsoft_FStar_Absyn_Syntax.if_then_else = _52_16403; Microsoft_FStar_Absyn_Syntax.ite_wp = _52_16402; Microsoft_FStar_Absyn_Syntax.ite_wlp = _52_16401; Microsoft_FStar_Absyn_Syntax.wp_binop = _52_16400; Microsoft_FStar_Absyn_Syntax.wp_as_type = _52_16399; Microsoft_FStar_Absyn_Syntax.close_wp = _52_16398; Microsoft_FStar_Absyn_Syntax.close_wp_t = _52_16397; Microsoft_FStar_Absyn_Syntax.assert_p = _52_16396; Microsoft_FStar_Absyn_Syntax.assume_p = _52_16395; Microsoft_FStar_Absyn_Syntax.null_wp = _52_16394; Microsoft_FStar_Absyn_Syntax.trivial = _52_16393})))))))))))))))
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ed, d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)))
end))))
end
| Microsoft_FStar_Parser_AST.SubEffect (l) -> begin
(let lookup = (fun ( l  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_effect_name env l)) with
| None -> begin
(let _52_16414 = (let _52_16413 = (let _52_16412 = (let _52_16411 = (let _52_16410 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.String.strcat "Effect name " _52_16410))
in (Support.String.strcat _52_16411 " not found"))
in (_52_16412, d.Microsoft_FStar_Parser_AST.drange))
in Microsoft_FStar_Absyn_Syntax.Error (_52_16413))
in (raise (_52_16414)))
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

let desugar_decls = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( decls  :  Microsoft_FStar_Parser_AST.decl list ) -> (Support.List.fold_left (fun ( _41_2832  :  (env_t * Microsoft_FStar_Absyn_Syntax.sigelt list) ) ( d  :  Microsoft_FStar_Parser_AST.decl ) -> (match (_41_2832) with
| (env, sigelts) -> begin
(let _41_2836 = (desugar_decl env d)
in (match (_41_2836) with
| (env, se) -> begin
(env, (Support.List.append sigelts se))
end))
end)) (env, []) decls))

let desugar_partial_modul = (fun ( curmod  :  (Microsoft_FStar_Absyn_Syntax.modul * 'a) option ) ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( m  :  Microsoft_FStar_Parser_AST.modul ) -> (let open_ns = (fun ( mname  :  Microsoft_FStar_Absyn_Syntax.lident ) ( d  :  Microsoft_FStar_Parser_AST.decl list ) -> (match (((Support.List.length mname.Microsoft_FStar_Absyn_Syntax.ns) <> 0)) with
| true -> begin
(let _52_16431 = (let _52_16430 = (let _52_16428 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids mname.Microsoft_FStar_Absyn_Syntax.ns)
in Microsoft_FStar_Parser_AST.Open (_52_16428))
in (let _52_16429 = (Microsoft_FStar_Absyn_Syntax.range_of_lid mname)
in (Microsoft_FStar_Parser_AST.mk_decl _52_16430 _52_16429)))
in (_52_16431)::d)
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
(let _52_16433 = (Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _52_16432 = (open_ns mname decls)
in (_52_16433, mname, _52_16432, true)))
end
| Microsoft_FStar_Parser_AST.Module ((mname, decls)) -> begin
(let _52_16435 = (Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _52_16434 = (open_ns mname decls)
in (_52_16435, mname, _52_16434, false)))
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

let desugar_modul = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( m  :  Microsoft_FStar_Parser_AST.modul ) -> (let _41_2872 = (desugar_partial_modul None env m)
in (match (_41_2872) with
| (env, modul) -> begin
(let env = (Microsoft_FStar_Parser_DesugarEnv.finish_module_or_interface env modul)
in (let _41_2874 = (match ((Microsoft_FStar_Options.should_dump modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(let _52_16440 = (Microsoft_FStar_Absyn_Print.modul_to_string modul)
in (Support.Microsoft.FStar.Util.fprint1 "%s\n" _52_16440))
end
| false -> begin
()
end)
in (env, modul)))
end)))

let desugar_file = (fun ( env  :  Microsoft_FStar_Parser_DesugarEnv.env ) ( f  :  Microsoft_FStar_Parser_AST.file ) -> (let _41_2887 = (Support.List.fold_left (fun ( _41_2880  :  (Microsoft_FStar_Parser_DesugarEnv.env * Microsoft_FStar_Absyn_Syntax.modul list) ) ( m  :  Microsoft_FStar_Parser_AST.modul ) -> (match (_41_2880) with
| (env, mods) -> begin
(let _41_2884 = (desugar_modul env m)
in (match (_41_2884) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_41_2887) with
| (env, mods) -> begin
(env, (Support.List.rev mods))
end)))

let add_modul_to_env = (fun ( m  :  Microsoft_FStar_Absyn_Syntax.modul ) ( en  :  Microsoft_FStar_Parser_DesugarEnv.env ) -> (let en = (Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface false false en m.Microsoft_FStar_Absyn_Syntax.name)
in (let en = (Support.List.fold_left Microsoft_FStar_Parser_DesugarEnv.push_sigelt (let _41_2891 = en
in {Microsoft_FStar_Parser_DesugarEnv.curmodule = Some (m.Microsoft_FStar_Absyn_Syntax.name); Microsoft_FStar_Parser_DesugarEnv.modules = _41_2891.Microsoft_FStar_Parser_DesugarEnv.modules; Microsoft_FStar_Parser_DesugarEnv.open_namespaces = _41_2891.Microsoft_FStar_Parser_DesugarEnv.open_namespaces; Microsoft_FStar_Parser_DesugarEnv.sigaccum = _41_2891.Microsoft_FStar_Parser_DesugarEnv.sigaccum; Microsoft_FStar_Parser_DesugarEnv.localbindings = _41_2891.Microsoft_FStar_Parser_DesugarEnv.localbindings; Microsoft_FStar_Parser_DesugarEnv.recbindings = _41_2891.Microsoft_FStar_Parser_DesugarEnv.recbindings; Microsoft_FStar_Parser_DesugarEnv.phase = _41_2891.Microsoft_FStar_Parser_DesugarEnv.phase; Microsoft_FStar_Parser_DesugarEnv.sigmap = _41_2891.Microsoft_FStar_Parser_DesugarEnv.sigmap; Microsoft_FStar_Parser_DesugarEnv.default_result_effect = _41_2891.Microsoft_FStar_Parser_DesugarEnv.default_result_effect; Microsoft_FStar_Parser_DesugarEnv.iface = _41_2891.Microsoft_FStar_Parser_DesugarEnv.iface; Microsoft_FStar_Parser_DesugarEnv.admitted_iface = _41_2891.Microsoft_FStar_Parser_DesugarEnv.admitted_iface}) m.Microsoft_FStar_Absyn_Syntax.exports)
in (Microsoft_FStar_Parser_DesugarEnv.finish_module_or_interface en m))))




