
let as_imp = (fun _124478 -> (match (_124478) with
| (Microsoft_FStar_Parser_AST.Hash) | (Microsoft_FStar_Parser_AST.FsTypApp) -> begin
Some (Microsoft_FStar_Absyn_Syntax.Implicit)
end
| _ -> begin
None
end))

let arg_withimp_e = (fun imp t -> (t, (as_imp imp)))

let arg_withimp_t = (fun imp t -> (match (imp) with
| Microsoft_FStar_Parser_AST.Hash -> begin
(t, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end
| _ -> begin
(t, None)
end))

let contains_binder = (fun binders -> ((Support.Microsoft.FStar.Util.for_some (fun b -> (match (b.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Annotated (_) -> begin
true
end
| _ -> begin
false
end))) binders))

let rec unparen = (fun t -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _ -> begin
t
end))

let rec unlabel = (fun t -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (t) -> begin
(unlabel t)
end
| Microsoft_FStar_Parser_AST.Labeled ((t, _, _)) -> begin
(unlabel t)
end
| _ -> begin
t
end))

let kind_star = (fun r -> (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name ((Microsoft_FStar_Absyn_Syntax.lid_of_path (("Type")::[]) r))) r Microsoft_FStar_Parser_AST.Kind))

let compile_op = (fun s -> (let name_of_char = (fun _124479 -> (match (_124479) with
| '&' -> begin
"Amp"
end
| '@' -> begin
"At"
end
| '+' -> begin
"Plus"
end
| '-' -> begin
"Minus"
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
| _ -> begin
"UNKNOWN"
end))
in (let rec aux = (fun i -> if (i = (Support.String.length s)) then begin
[]
end else begin
((name_of_char (Support.Microsoft.FStar.Util.char_at s i)))::(aux (i + 1))
end)
in (Support.String.strcat "op_" (Support.String.concat "_" (aux 0))))))

let compile_op_lid = (fun s r -> (Microsoft_FStar_Absyn_Syntax.lid_of_ids (((Microsoft_FStar_Absyn_Syntax.mk_ident ((compile_op s), r)))::[])))

let op_as_vlid = (fun env arity rng s -> (let r = (fun l -> Some ((Microsoft_FStar_Absyn_Util.set_lid_range l rng)))
in (match ((s, env.Microsoft_FStar_Parser_DesugarEnv.phase)) with
| ("=", _) -> begin
(r Microsoft_FStar_Absyn_Const.op_Eq)
end
| (":=", _) -> begin
(r Microsoft_FStar_Absyn_Const.op_ColonEq)
end
| ("<", _) -> begin
(r Microsoft_FStar_Absyn_Const.op_LT)
end
| ("<=", _) -> begin
(r Microsoft_FStar_Absyn_Const.op_LTE)
end
| (">", _) -> begin
(r Microsoft_FStar_Absyn_Const.op_GT)
end
| (">=", _) -> begin
(r Microsoft_FStar_Absyn_Const.op_GTE)
end
| ("&&", _) -> begin
(r Microsoft_FStar_Absyn_Const.op_And)
end
| ("||", _) -> begin
(r Microsoft_FStar_Absyn_Const.op_Or)
end
| ("*", _) -> begin
(r Microsoft_FStar_Absyn_Const.op_Multiply)
end
| ("+", _) -> begin
(r Microsoft_FStar_Absyn_Const.op_Addition)
end
| ("-", _) when (arity = 1) -> begin
(r Microsoft_FStar_Absyn_Const.op_Minus)
end
| ("-", _) -> begin
(r Microsoft_FStar_Absyn_Const.op_Subtraction)
end
| ("/", _) -> begin
(r Microsoft_FStar_Absyn_Const.op_Division)
end
| ("%", _) -> begin
(r Microsoft_FStar_Absyn_Const.op_Modulus)
end
| ("!", _) -> begin
(r Microsoft_FStar_Absyn_Const.read_lid)
end
| ("@", _) -> begin
(r Microsoft_FStar_Absyn_Const.list_append_lid)
end
| ("^", _) -> begin
(r Microsoft_FStar_Absyn_Const.strcat_lid)
end
| ("|>", _) -> begin
(r Microsoft_FStar_Absyn_Const.pipe_right_lid)
end
| ("<|", _) -> begin
(r Microsoft_FStar_Absyn_Const.pipe_left_lid)
end
| ("<>", _) -> begin
(r Microsoft_FStar_Absyn_Const.op_notEq)
end
| (s, _) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env (compile_op_lid s rng))) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}) -> begin
Some (fv.Microsoft_FStar_Absyn_Syntax.v)
end
| _ -> begin
None
end)
end)))

let op_as_tylid = (fun env rng s -> (let r = (fun l -> Some ((Microsoft_FStar_Absyn_Util.set_lid_range l rng)))
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
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env (compile_op_lid s rng))) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (ftv); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}) -> begin
Some (ftv.Microsoft_FStar_Absyn_Syntax.v)
end
| _ -> begin
None
end)
end)))

let rec is_type = (fun env t -> if (t.Microsoft_FStar_Parser_AST.level = Microsoft_FStar_Parser_AST.Type) then begin
true
end else begin
(match ((unparen t).Microsoft_FStar_Parser_AST.tm) with
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
| Microsoft_FStar_Parser_AST.Op ((s, _)) -> begin
(match ((op_as_tylid env t.Microsoft_FStar_Parser_AST.range s)) with
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
(let rec aux = (fun env pats -> (match (pats) with
| [] -> begin
(is_type env t)
end
| hd::pats -> begin
(match (hd.Microsoft_FStar_Parser_AST.pat) with
| (Microsoft_FStar_Parser_AST.PatWild) | (Microsoft_FStar_Parser_AST.PatVar (_)) -> begin
(aux env pats)
end
| Microsoft_FStar_Parser_AST.PatTvar ((id, _)) -> begin
(let _124858 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_124858) with
| (env, _) -> begin
(aux env pats)
end))
end
| Microsoft_FStar_Parser_AST.PatAscribed ((p, tm)) -> begin
(let env = if (is_kind env tm) then begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| (Microsoft_FStar_Parser_AST.PatVar ((id, _))) | (Microsoft_FStar_Parser_AST.PatTvar ((id, _))) -> begin
((Support.Prims.fst) (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id))
end
| _ -> begin
env
end)
end else begin
env
end
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
end)
and is_kind = (fun env t -> if (t.Microsoft_FStar_Parser_AST.level = Microsoft_FStar_Parser_AST.Kind) then begin
true
end else begin
(match ((unparen t).Microsoft_FStar_Parser_AST.tm) with
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
end)

let rec is_type_binder = (fun env b -> if (b.Microsoft_FStar_Parser_AST.blevel = Microsoft_FStar_Parser_AST.Formula) then begin
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
end else begin
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
end)

let sort_ftv = (fun ftv -> ((Support.Microsoft.FStar.Util.sort_with (fun x y -> (Support.String.compare x.Microsoft_FStar_Absyn_Syntax.idText y.Microsoft_FStar_Absyn_Syntax.idText))) (Support.Microsoft.FStar.Util.remove_dups (fun x y -> (x.Microsoft_FStar_Absyn_Syntax.idText = y.Microsoft_FStar_Absyn_Syntax.idText)) ftv)))

let rec free_type_vars_b = (fun env binder -> (match (binder.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Variable (_) -> begin
(env, [])
end
| Microsoft_FStar_Parser_AST.TVariable (x) -> begin
(let _124952 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env x)
in (match (_124952) with
| (env, _) -> begin
(env, (x)::[])
end))
end
| Microsoft_FStar_Parser_AST.Annotated ((_, term)) -> begin
(env, (free_type_vars env term))
end
| Microsoft_FStar_Parser_AST.TAnnotated ((id, _)) -> begin
(let _124966 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_124966) with
| (env, _) -> begin
(env, [])
end))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(env, (free_type_vars env t))
end))
and free_type_vars = (fun env t -> (match ((unparen t).Microsoft_FStar_Parser_AST.tm) with
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
(Support.List.collect (fun _125018 -> (match (_125018) with
| (t, _) -> begin
(free_type_vars env t)
end)) ts)
end
| Microsoft_FStar_Parser_AST.Op ((_, ts)) -> begin
(Support.List.collect (free_type_vars env) ts)
end
| Microsoft_FStar_Parser_AST.App ((t1, t2, _)) -> begin
(Support.List.append (free_type_vars env t1) (free_type_vars env t2))
end
| Microsoft_FStar_Parser_AST.Refine ((b, t)) -> begin
(let _125036 = (free_type_vars_b env b)
in (match (_125036) with
| (env, f) -> begin
(Support.List.append f (free_type_vars env t))
end))
end
| (Microsoft_FStar_Parser_AST.Product ((binders, body))) | (Microsoft_FStar_Parser_AST.Sum ((binders, body))) -> begin
(let _125052 = (Support.List.fold_left (fun _125045 binder -> (match (_125045) with
| (env, free) -> begin
(let _125049 = (free_type_vars_b env binder)
in (match (_125049) with
| (env, f) -> begin
(env, (Support.List.append f free))
end))
end)) (env, []) binders)
in (match (_125052) with
| (env, free) -> begin
(Support.List.append free (free_type_vars env body))
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

let head_and_args = (fun t -> (let rec aux = (fun args t -> (match ((unparen t).Microsoft_FStar_Parser_AST.tm) with
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

let close = (fun env t -> (let ftv = (sort_ftv (free_type_vars env t))
in if ((Support.List.length ftv) = 0) then begin
t
end else begin
(let binders = ((Support.List.map (fun x -> (Microsoft_FStar_Parser_AST.mk_binder (Microsoft_FStar_Parser_AST.TAnnotated ((x, (kind_star x.Microsoft_FStar_Absyn_Syntax.idRange)))) x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type (Some (Microsoft_FStar_Absyn_Syntax.Implicit))))) ftv)
in (let result = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((binders, t))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
in result))
end))

let close_fun = (fun env t -> (let ftv = (sort_ftv (free_type_vars env t))
in if ((Support.List.length ftv) = 0) then begin
t
end else begin
(let binders = ((Support.List.map (fun x -> (Microsoft_FStar_Parser_AST.mk_binder (Microsoft_FStar_Parser_AST.TAnnotated ((x, (kind_star x.Microsoft_FStar_Absyn_Syntax.idRange)))) x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type (Some (Microsoft_FStar_Absyn_Syntax.Implicit))))) ftv)
in (let t = (match ((unlabel t).Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Product (_) -> begin
t
end
| _ -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.App (((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.tot_effect_lid)) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level), t, Microsoft_FStar_Parser_AST.Nothing))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
end)
in (let result = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((binders, t))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
in result)))
end))

let rec uncurry = (fun bs t -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Product ((binders, t)) -> begin
(uncurry (Support.List.append bs binders) t)
end
| _ -> begin
(bs, t)
end))

let rec is_app_pattern = (fun p -> (match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed ((p, _)) -> begin
(is_app_pattern p)
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar (_); Microsoft_FStar_Parser_AST.prange = _}, _)) -> begin
true
end
| _ -> begin
false
end))

let rec destruct_app_pattern = (fun env is_top_level p -> (match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed ((p, t)) -> begin
(let _125155 = (destruct_app_pattern env is_top_level p)
in (match (_125155) with
| (name, args, _) -> begin
(name, args, Some (t))
end))
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((id, _)); Microsoft_FStar_Parser_AST.prange = _}, args)) when is_top_level -> begin
(Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Parser_DesugarEnv.qualify env id)), args, None)
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

let binder_of_bnd = (fun _124480 -> (match (_124480) with
| TBinder ((a, k, aq)) -> begin
(Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)), aq)
end
| VBinder ((x, t, aq)) -> begin
(Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)), aq)
end
| _ -> begin
(failwith ("Impossible"))
end))

let as_binder = (fun env imp _124481 -> (match (_124481) with
| Support.Microsoft.FStar.Util.Inl ((None, k)) -> begin
((Microsoft_FStar_Absyn_Syntax.null_t_binder k), env)
end
| Support.Microsoft.FStar.Util.Inr ((None, t)) -> begin
((Microsoft_FStar_Absyn_Syntax.null_v_binder t), env)
end
| Support.Microsoft.FStar.Util.Inl ((Some (a), k)) -> begin
(let _125217 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_125217) with
| (env, a) -> begin
((Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)), imp), env)
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _125225 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_125225) with
| (env, x) -> begin
((Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)), imp), env)
end))
end))

type env_t =
Microsoft_FStar_Parser_DesugarEnv.env

type lenv_t =
(Microsoft_FStar_Absyn_Syntax.btvdef, Microsoft_FStar_Absyn_Syntax.bvvdef) Support.Microsoft.FStar.Util.either list

let label_conjuncts = (fun tag polarity label_opt f -> (let label = (fun f -> (let msg = (match (label_opt) with
| Some (l) -> begin
l
end
| _ -> begin
(Support.Microsoft.FStar.Util.format2 "%s at %s" tag (Support.Microsoft.FStar.Range.string_of_range f.Microsoft_FStar_Parser_AST.range))
end)
in (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Labeled ((f, msg, polarity))) f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level)))
in (let rec aux = (fun f -> (match (f.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Paren (g) -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Paren ((aux g))) f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level)
end
| Microsoft_FStar_Parser_AST.Op (("/\\", f1::f2::[])) -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Op (("/\\", ((aux f1))::((aux f2))::[]))) f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level)
end
| Microsoft_FStar_Parser_AST.If ((f1, f2, f3)) -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.If ((f1, (aux f2), (aux f3)))) f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level)
end
| Microsoft_FStar_Parser_AST.Abs ((binders, g)) -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Abs ((binders, (aux g)))) f.Microsoft_FStar_Parser_AST.range f.Microsoft_FStar_Parser_AST.level)
end
| _ -> begin
(label f)
end))
in (aux f))))

let rec desugar_data_pat = (fun env p -> (let resolvex = (fun l e x -> (match (((Support.Microsoft.FStar.Util.find_opt (fun _124482 -> (match (_124482) with
| Support.Microsoft.FStar.Util.Inr (y) -> begin
(y.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText = x.Microsoft_FStar_Absyn_Syntax.idText)
end
| _ -> begin
false
end))) l)) with
| Some (Support.Microsoft.FStar.Util.Inr (y)) -> begin
(l, e, y)
end
| _ -> begin
(let _125276 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding e x)
in (match (_125276) with
| (e, x) -> begin
((Support.Microsoft.FStar.Util.Inr (x))::l, e, x)
end))
end))
in (let resolvea = (fun l e a -> (match (((Support.Microsoft.FStar.Util.find_opt (fun _124483 -> (match (_124483) with
| Support.Microsoft.FStar.Util.Inl (b) -> begin
(b.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText = a.Microsoft_FStar_Absyn_Syntax.idText)
end
| _ -> begin
false
end))) l)) with
| Some (Support.Microsoft.FStar.Util.Inl (b)) -> begin
(l, e, b)
end
| _ -> begin
(let _125293 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding e a)
in (match (_125293) with
| (e, a) -> begin
((Support.Microsoft.FStar.Util.Inl (a))::l, e, a)
end))
end))
in (let rec aux = (fun loc env p -> (let pos = (fun q -> (Microsoft_FStar_Absyn_Syntax.withinfo q None p.Microsoft_FStar_Parser_AST.prange))
in (let pos_r = (fun r q -> (Microsoft_FStar_Absyn_Syntax.withinfo q None r))
in (match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatOr ([]) -> begin
(failwith ("impossible"))
end
| Microsoft_FStar_Parser_AST.PatOr (p::ps) -> begin
(let _125313 = (aux loc env p)
in (match (_125313) with
| (loc, env, var, p) -> begin
(let _125328 = (Support.List.fold_left (fun _125317 p -> (match (_125317) with
| (loc, env, ps) -> begin
(let _125324 = (aux loc env p)
in (match (_125324) with
| (loc, env, _, p) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_125328) with
| (loc, env, ps) -> begin
(let pat = (pos (Microsoft_FStar_Absyn_Syntax.Pat_disj ((p)::(Support.List.rev ps))))
in (let _125330 = (Support.Prims.ignore (Microsoft_FStar_Absyn_Syntax.pat_vars pat))
in (loc, env, var, pat)))
end))
end))
end
| Microsoft_FStar_Parser_AST.PatAscribed ((p, t)) -> begin
(let p = if (is_kind env t) then begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatTvar (_) -> begin
p
end
| Microsoft_FStar_Parser_AST.PatVar ((x, imp)) -> begin
(let _125343 = p
in {Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatTvar ((x, imp)); Microsoft_FStar_Parser_AST.prange = _125343.Microsoft_FStar_Parser_AST.prange})
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern", p.Microsoft_FStar_Parser_AST.prange))))
end)
end else begin
p
end
in (let _125352 = (aux loc env p)
in (match (_125352) with
| (loc, env', binder, p) -> begin
(let binder = (match (binder) with
| LetBinder (_) -> begin
(failwith ("impossible"))
end
| TBinder ((x, _, aq)) -> begin
TBinder ((x, (desugar_kind env t), aq))
end
| VBinder ((x, _, aq)) -> begin
(let t = (close_fun env t)
in VBinder ((x, (desugar_typ env t), aq)))
end)
in (loc, env', binder, p))
end)))
end
| Microsoft_FStar_Parser_AST.PatTvar ((a, imp)) -> begin
(let aq = if imp then begin
Some (Microsoft_FStar_Absyn_Syntax.Implicit)
end else begin
None
end
in if (a.Microsoft_FStar_Absyn_Syntax.idText = "\'_") then begin
(let a = ((Microsoft_FStar_Absyn_Util.new_bvd) (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (loc, env, TBinder ((a, Microsoft_FStar_Absyn_Syntax.kun, aq)), (pos (Microsoft_FStar_Absyn_Syntax.Pat_twild ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a Microsoft_FStar_Absyn_Syntax.kun))))))
end else begin
(let _125379 = (resolvea loc env a)
in (match (_125379) with
| (loc, env, abvd) -> begin
(loc, env, TBinder ((abvd, Microsoft_FStar_Absyn_Syntax.kun, aq)), (pos (Microsoft_FStar_Absyn_Syntax.Pat_tvar ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s abvd Microsoft_FStar_Absyn_Syntax.kun)))))
end))
end)
end
| Microsoft_FStar_Parser_AST.PatWild -> begin
(let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (let y = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), (pos (Microsoft_FStar_Absyn_Syntax.Pat_wild ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s y Microsoft_FStar_Absyn_Syntax.tun)))))))
end
| Microsoft_FStar_Parser_AST.PatConst (c) -> begin
(let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), (pos (Microsoft_FStar_Absyn_Syntax.Pat_constant (c)))))
end
| Microsoft_FStar_Parser_AST.PatVar ((x, imp)) -> begin
(let aq = if imp then begin
Some (Microsoft_FStar_Absyn_Syntax.Implicit)
end else begin
None
end
in (let _125394 = (resolvex loc env x)
in (match (_125394) with
| (loc, env, xbvd) -> begin
(loc, env, VBinder ((xbvd, Microsoft_FStar_Absyn_Syntax.tun, aq)), (pos (Microsoft_FStar_Absyn_Syntax.Pat_var (((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s xbvd Microsoft_FStar_Absyn_Syntax.tun), imp)))))
end)))
end
| Microsoft_FStar_Parser_AST.PatName (l) -> begin
(let l = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), (pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, [])))))))
end
| Microsoft_FStar_Parser_AST.PatApp (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatName (l); Microsoft_FStar_Parser_AST.prange = _}, args)) -> begin
(let _125421 = (Support.List.fold_right (fun arg _125411 -> (match (_125411) with
| (loc, env, args) -> begin
(let _125417 = (aux loc env arg)
in (match (_125417) with
| (loc, env, _, arg) -> begin
(loc, env, (arg)::args)
end))
end)) args (loc, env, []))
in (match (_125421) with
| (loc, env, args) -> begin
(let l = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), (pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, args)))))))
end))
end
| Microsoft_FStar_Parser_AST.PatApp (_) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern", p.Microsoft_FStar_Parser_AST.prange))))
end
| Microsoft_FStar_Parser_AST.PatList (pats) -> begin
(let _125443 = (Support.List.fold_right (fun pat _125433 -> (match (_125433) with
| (loc, env, pats) -> begin
(let _125439 = (aux loc env pat)
in (match (_125439) with
| (loc, env, _, pat) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_125443) with
| (loc, env, pats) -> begin
(let pat = (Support.List.fold_right (fun hd tl -> (let r = (Support.Microsoft.FStar.Range.union_ranges hd.Microsoft_FStar_Absyn_Syntax.p tl.Microsoft_FStar_Absyn_Syntax.p)
in ((pos_r r) (Microsoft_FStar_Absyn_Syntax.Pat_cons (((Microsoft_FStar_Absyn_Util.fv Microsoft_FStar_Absyn_Const.cons_lid), (hd)::(tl)::[])))))) pats ((pos_r (Support.Microsoft.FStar.Range.end_range p.Microsoft_FStar_Parser_AST.prange)) (Microsoft_FStar_Absyn_Syntax.Pat_cons (((Microsoft_FStar_Absyn_Util.fv Microsoft_FStar_Absyn_Const.nil_lid), [])))))
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), pat)))
end))
end
| Microsoft_FStar_Parser_AST.PatTuple ((args, dep)) -> begin
(let _125467 = (Support.List.fold_left (fun _125456 p -> (match (_125456) with
| (loc, env, pats) -> begin
(let _125463 = (aux loc env p)
in (match (_125463) with
| (loc, env, _, pat) -> begin
(loc, env, (pat)::pats)
end))
end)) (loc, env, []) args)
in (match (_125467) with
| (loc, env, args) -> begin
(let args = (Support.List.rev args)
in (let l = if dep then begin
(Microsoft_FStar_Absyn_Util.mk_dtuple_data_lid (Support.List.length args) p.Microsoft_FStar_Parser_AST.prange)
end else begin
(Microsoft_FStar_Absyn_Util.mk_tuple_data_lid (Support.List.length args) p.Microsoft_FStar_Parser_AST.prange)
end
in (let constr = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (let l = (match (constr.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, _)) -> begin
v
end
| _ -> begin
(failwith ("impossible"))
end)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd (Some (p.Microsoft_FStar_Parser_AST.prange)))
in (loc, env, VBinder ((x, Microsoft_FStar_Absyn_Syntax.tun, None)), (pos (Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, args))))))))))
end))
end
| Microsoft_FStar_Parser_AST.PatRecord ([]) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern", p.Microsoft_FStar_Parser_AST.prange))))
end
| Microsoft_FStar_Parser_AST.PatRecord (fields) -> begin
(let _125487 = (Support.List.hd fields)
in (match (_125487) with
| (f, _) -> begin
(let _125491 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_125491) with
| (record, _) -> begin
(let fields = ((Support.List.map (fun _125494 -> (match (_125494) with
| (f, p) -> begin
((Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.qualify_field_to_record env record) f), p)
end))) fields)
in (let args = ((Support.List.map (fun _125499 -> (match (_125499) with
| (f, _) -> begin
(match (((Support.List.tryFind (fun _125503 -> (match (_125503) with
| (g, _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals f g)
end))) fields)) with
| None -> begin
(Microsoft_FStar_Parser_AST.mk_pattern Microsoft_FStar_Parser_AST.PatWild p.Microsoft_FStar_Parser_AST.prange)
end
| Some ((_, p)) -> begin
p
end)
end))) record.Microsoft_FStar_Parser_DesugarEnv.fields)
in (let app = (Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatApp (((Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatName (record.Microsoft_FStar_Parser_DesugarEnv.constrname)) p.Microsoft_FStar_Parser_AST.prange), args))) p.Microsoft_FStar_Parser_AST.prange)
in (aux loc env app))))
end))
end))
end))))
in (let _125517 = (aux [] env p)
in (match (_125517) with
| (_, env, b, p) -> begin
(env, b, p)
end))))))
and desugar_binding_pat_maybe_top = (fun top env p -> if top then begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatVar ((x, _)) -> begin
(env, LetBinder (((Microsoft_FStar_Parser_DesugarEnv.qualify env x), Microsoft_FStar_Absyn_Syntax.tun)), None)
end
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((x, _)); Microsoft_FStar_Parser_AST.prange = _}, t)) -> begin
(env, LetBinder (((Microsoft_FStar_Parser_DesugarEnv.qualify env x), (desugar_typ env t))), None)
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected pattern at the top-level", p.Microsoft_FStar_Parser_AST.prange))))
end)
end else begin
(let _125542 = (desugar_data_pat env p)
in (match (_125542) with
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
end)
and desugar_binding_pat = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top = (fun _125557 env pat -> (let _125565 = (desugar_data_pat env pat)
in (match (_125565) with
| (env, _, pat) -> begin
(env, pat)
end)))
and desugar_match_pat = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_typ_or_exp = (fun env t -> if (is_type env t) then begin
Support.Microsoft.FStar.Util.Inl ((desugar_typ env t))
end else begin
Support.Microsoft.FStar.Util.Inr ((desugar_exp env t))
end)
and desugar_exp = (fun env e -> (desugar_exp_maybe_top false env e))
and desugar_exp_maybe_top = (fun top_level env top -> (let pos = (fun e -> (e None top.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun e -> (let _125579 = e
in {Microsoft_FStar_Absyn_Syntax.n = _125579.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _125579.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = top.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _125579.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _125579.Microsoft_FStar_Absyn_Syntax.uvs}))
in (match ((unparen top).Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Const (c) -> begin
(pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match ((op_as_vlid env (Support.List.length args) top.Microsoft_FStar_Parser_AST.range s)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat "Unexpected operator: " s), top.Microsoft_FStar_Parser_AST.range))))
end
| Some (l) -> begin
(let op = (Microsoft_FStar_Absyn_Util.fvar false l (Microsoft_FStar_Absyn_Syntax.range_of_lid l))
in (let args = ((Support.List.map (fun t -> ((desugar_typ_or_exp env t), None))) args)
in (setpos (Microsoft_FStar_Absyn_Util.mk_exp_app op args))))
end)
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) -> begin
if (l.Microsoft_FStar_Absyn_Syntax.str = "ref") then begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env Microsoft_FStar_Absyn_Const.alloc_lid)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Identifier \'ref\' not found; include lib/st.fst in your path", (Microsoft_FStar_Absyn_Syntax.range_of_lid l)))))
end
| Some (e) -> begin
(setpos e)
end)
end else begin
(setpos (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_lid env) l))
end
end
| Microsoft_FStar_Parser_AST.Construct ((l, args)) -> begin
(let dt = (pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar ((Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_datacon env) l), true)))
in (match (args) with
| [] -> begin
dt
end
| _ -> begin
(let args = (Support.List.map (fun _125609 -> (match (_125609) with
| (t, imp) -> begin
(let te = (desugar_typ_or_exp env t)
in (arg_withimp_e imp te))
end)) args)
in (setpos (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared (((Microsoft_FStar_Absyn_Util.mk_exp_app dt args), Microsoft_FStar_Absyn_Syntax.Data_app))))))
end))
end
| Microsoft_FStar_Parser_AST.Abs ((binders, body)) -> begin
(let _125646 = (Support.List.fold_left (fun _125618 pat -> (match (_125618) with
| (env, ftvs) -> begin
(match (pat.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatTvar ((a, imp)); Microsoft_FStar_Parser_AST.prange = _}, t)) -> begin
(let ftvs = (Support.List.append (free_type_vars env t) ftvs)
in (((Support.Prims.fst) (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)), ftvs))
end
| Microsoft_FStar_Parser_AST.PatTvar ((a, _)) -> begin
(((Support.Prims.fst) (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)), ftvs)
end
| Microsoft_FStar_Parser_AST.PatAscribed ((_, t)) -> begin
(env, (Support.List.append (free_type_vars env t) ftvs))
end
| _ -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_125646) with
| (_, ftv) -> begin
(let ftv = (sort_ftv ftv)
in (let binders = (Support.List.append ((Support.List.map (fun a -> (Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatTvar ((a, true))) top.Microsoft_FStar_Parser_AST.range))) ftv) binders)
in (let rec aux = (fun env bs sc_pat_opt _124484 -> (match (_124484) with
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
(let _125669 = (desugar_binding_pat env p)
in (match (_125669) with
| (env, b, pat) -> begin
(let _125727 = (match (b) with
| LetBinder (_) -> begin
(failwith ("Impossible"))
end
| TBinder ((a, k, aq)) -> begin
((binder_of_bnd b), sc_pat_opt)
end
| VBinder ((x, t, aq)) -> begin
(let b = (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)
in (let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
Some (((Microsoft_FStar_Absyn_Util.bvar_to_exp b), p))
end
| (Some (p), Some ((sc, p'))) -> begin
(match ((sc.Microsoft_FStar_Absyn_Syntax.n, p'.Microsoft_FStar_Absyn_Syntax.v)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_), _) -> begin
(let tup = (Microsoft_FStar_Absyn_Util.mk_tuple_data_lid 2 top.Microsoft_FStar_Parser_AST.range)
in (let sc = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app ((Microsoft_FStar_Absyn_Util.fvar true tup top.Microsoft_FStar_Parser_AST.range), ((Microsoft_FStar_Absyn_Syntax.varg sc))::((Microsoft_FStar_Absyn_Syntax.varg (Microsoft_FStar_Absyn_Util.bvar_to_exp b)))::[]) None top.Microsoft_FStar_Parser_AST.range)
in (let p = (Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_cons (((Microsoft_FStar_Absyn_Util.fv tup), (p')::(p)::[]))) None (Support.Microsoft.FStar.Range.union_ranges p'.Microsoft_FStar_Absyn_Syntax.p p.Microsoft_FStar_Absyn_Syntax.p))
in Some ((sc, p)))))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app ((_, args)), Microsoft_FStar_Absyn_Syntax.Pat_cons ((_, pats))) -> begin
(let tup = (Microsoft_FStar_Absyn_Util.mk_tuple_data_lid (1 + (Support.List.length args)) top.Microsoft_FStar_Parser_AST.range)
in (let sc = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app ((Microsoft_FStar_Absyn_Util.fvar true tup top.Microsoft_FStar_Parser_AST.range), (Support.List.append args (((Microsoft_FStar_Absyn_Syntax.varg (Microsoft_FStar_Absyn_Util.bvar_to_exp b)))::[]))) None top.Microsoft_FStar_Parser_AST.range)
in (let p = (Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_cons (((Microsoft_FStar_Absyn_Util.fv tup), (Support.List.append pats ((p)::[]))))) None (Support.Microsoft.FStar.Range.union_ranges p'.Microsoft_FStar_Absyn_Syntax.p p.Microsoft_FStar_Absyn_Syntax.p))
in Some ((sc, p)))))
end
| _ -> begin
(failwith ("Impossible"))
end)
end)
in ((Support.Microsoft.FStar.Util.Inr (b), aq), sc_pat_opt)))
end)
in (match (_125727) with
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
in (pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_app ((Microsoft_FStar_Absyn_Util.fvar false a (Microsoft_FStar_Absyn_Syntax.range_of_lid a)), ((Microsoft_FStar_Absyn_Syntax.targ phi))::((Microsoft_FStar_Absyn_Syntax.varg (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant Microsoft_FStar_Absyn_Syntax.Const_unit None top.Microsoft_FStar_Parser_AST.range)))::[]))))
end
| Microsoft_FStar_Parser_AST.App (_) -> begin
(let rec aux = (fun args e -> (match ((unparen e).Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.App ((e, t, imp)) -> begin
(let arg = ((arg_withimp_e imp) (desugar_typ_or_exp env t))
in (aux ((arg)::args) e))
end
| _ -> begin
(let head = (desugar_exp env e)
in (pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (head, args))))
end))
in (aux [] top))
end
| Microsoft_FStar_Parser_AST.Seq ((t1, t2)) -> begin
(setpos (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared (((desugar_exp env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Let ((false, (((Microsoft_FStar_Parser_AST.mk_pattern Microsoft_FStar_Parser_AST.PatWild t1.Microsoft_FStar_Parser_AST.range), t1))::[], t2))) top.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Expr)), Microsoft_FStar_Absyn_Syntax.Sequence)))))
end
| Microsoft_FStar_Parser_AST.Let ((is_rec, (pat, _snd)::_tl, body)) -> begin
(let ds_let_rec = (fun _125770 -> (match (_125770) with
| () -> begin
(let bindings = ((pat, _snd))::_tl
in (let funs = ((Support.List.map (fun _125774 -> (match (_125774) with
| (p, def) -> begin
if (is_app_pattern p) then begin
((destruct_app_pattern env top_level p), def)
end else begin
(match ((Microsoft_FStar_Parser_AST.un_function p def)) with
| Some ((p, def)) -> begin
((destruct_app_pattern env top_level p), def)
end
| _ -> begin
(match (p.Microsoft_FStar_Parser_AST.pat) with
| Microsoft_FStar_Parser_AST.PatAscribed (({Microsoft_FStar_Parser_AST.pat = Microsoft_FStar_Parser_AST.PatVar ((id, _)); Microsoft_FStar_Parser_AST.prange = _}, t)) -> begin
if top_level then begin
((Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Parser_DesugarEnv.qualify env id)), [], Some (t)), def)
end else begin
((Support.Microsoft.FStar.Util.Inl (id), [], Some (t)), def)
end
end
| Microsoft_FStar_Parser_AST.PatVar ((id, _)) -> begin
if top_level then begin
((Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Parser_DesugarEnv.qualify env id)), [], None), def)
end else begin
((Support.Microsoft.FStar.Util.Inl (id), [], None), def)
end
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected let binding", p.Microsoft_FStar_Parser_AST.prange))))
end)
end)
end
end))) bindings)
in (let _125824 = (Support.List.fold_left (fun _125802 _125811 -> (match ((_125802, _125811)) with
| ((env, fnames), ((f, _, _), _)) -> begin
(let _125821 = (match (f) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(let _125816 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_125816) with
| (env, xx) -> begin
(env, Support.Microsoft.FStar.Util.Inl (xx))
end))
end
| Support.Microsoft.FStar.Util.Inr (l) -> begin
((Microsoft_FStar_Parser_DesugarEnv.push_rec_binding env (Microsoft_FStar_Parser_DesugarEnv.Binding_let (l))), Support.Microsoft.FStar.Util.Inr (l))
end)
in (match (_125821) with
| (env, lbname) -> begin
(env, (lbname)::fnames)
end))
end)) (env, []) funs)
in (match (_125824) with
| (env', fnames) -> begin
(let fnames = (Support.List.rev fnames)
in (let desugar_one_def = (fun env lbname _125835 -> (match (_125835) with
| ((_, args, result_t), def) -> begin
(let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Ascribed ((def, t))) (Support.Microsoft.FStar.Range.union_ranges t.Microsoft_FStar_Parser_AST.range def.Microsoft_FStar_Parser_AST.range) Microsoft_FStar_Parser_AST.Expr)
end)
in (let def = (match (args) with
| [] -> begin
def
end
| _ -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.un_curry_abs args def) top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level)
end)
in (let body = (desugar_exp env def)
in (lbname, Microsoft_FStar_Absyn_Syntax.tun, body))))
end))
in (let lbs = (Support.List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (let body = (desugar_exp env' body)
in (pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), body)))))))
end))))
end))
in (let ds_non_rec = (fun pat t1 t2 -> (let t1 = (desugar_exp env t1)
in (let _125855 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_125855) with
| (env, binder, pat) -> begin
(match (binder) with
| TBinder (_) -> begin
(failwith ("Unexpected type binder in let"))
end
| LetBinder ((l, t)) -> begin
(let body = (desugar_exp env t2)
in (pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((false, ((Support.Microsoft.FStar.Util.Inr (l), t, t1))::[]), body))))
end
| VBinder ((x, t, _)) -> begin
(let body = (desugar_exp env t2)
in (let body = (match (pat) with
| (None) | (Some ({Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_wild (_); Microsoft_FStar_Absyn_Syntax.sort = _; Microsoft_FStar_Absyn_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_match ((Microsoft_FStar_Absyn_Util.bvd_to_exp x t), ((pat, None, body))::[]) None body.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((false, ((Support.Microsoft.FStar.Util.Inl (x), t, t1))::[]), body)))))
end)
end))))
in if (is_rec || (is_app_pattern pat)) then begin
(ds_let_rec ())
end else begin
(ds_non_rec pat _snd body)
end))
end
| Microsoft_FStar_Parser_AST.If ((t1, t2, t3)) -> begin
(pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_match ((desugar_exp env t1), (((Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (true))) None t2.Microsoft_FStar_Parser_AST.range), None, (desugar_exp env t2)))::(((Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (false))) None t3.Microsoft_FStar_Parser_AST.range), None, (desugar_exp env t3)))::[])))
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
(let desugar_branch = (fun _125906 -> (match (_125906) with
| (pat, wopt, b) -> begin
(let _125909 = (desugar_match_pat env pat)
in (match (_125909) with
| (env, pat) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
Some ((desugar_exp env e))
end)
in (let b = (desugar_exp env b)
in (pat, wopt, b)))
end))
end))
in (pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_match ((desugar_exp env e), (Support.List.map desugar_branch branches)))))
end
| Microsoft_FStar_Parser_AST.Ascribed ((e, t)) -> begin
(pos (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed' ((desugar_exp env e), (desugar_typ env t))))
end
| Microsoft_FStar_Parser_AST.Record ((_, [])) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected empty record", top.Microsoft_FStar_Parser_AST.range))))
end
| Microsoft_FStar_Parser_AST.Record ((eopt, fields)) -> begin
(let _125931 = (Support.List.hd fields)
in (match (_125931) with
| (f, _) -> begin
(let _125935 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_125935) with
| (record, _) -> begin
(let get_field = (fun xopt f -> (let fn = f.Microsoft_FStar_Absyn_Syntax.ident
in (let found = ((Support.Microsoft.FStar.Util.find_opt (fun _125943 -> (match (_125943) with
| (g, _) -> begin
(let gn = g.Microsoft_FStar_Absyn_Syntax.ident
in (fn.Microsoft_FStar_Absyn_Syntax.idText = gn.Microsoft_FStar_Absyn_Syntax.idText))
end))) fields)
in (match (found) with
| Some ((_, e)) -> begin
e
end
| None -> begin
(match (xopt) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.Microsoft.FStar.Util.format1 "Field %s is missing" (Microsoft_FStar_Absyn_Syntax.text_of_lid f)), top.Microsoft_FStar_Parser_AST.range))))
end
| Some (x) -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Project ((x, f))) x.Microsoft_FStar_Parser_AST.range x.Microsoft_FStar_Parser_AST.level)
end)
end))))
in (let recterm = (match (eopt) with
| None -> begin
Microsoft_FStar_Parser_AST.Construct ((record.Microsoft_FStar_Parser_DesugarEnv.constrname, ((Support.List.map (fun _125959 -> (match (_125959) with
| (f, _) -> begin
((get_field None f), Microsoft_FStar_Parser_AST.Nothing)
end))) record.Microsoft_FStar_Parser_DesugarEnv.fields)))
end
| Some (e) -> begin
(let x = (Microsoft_FStar_Absyn_Util.genident (Some (e.Microsoft_FStar_Parser_AST.range)))
in (let xterm = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Var ((Microsoft_FStar_Absyn_Syntax.lid_of_ids ((x)::[])))) x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr)
in (let record = Microsoft_FStar_Parser_AST.Construct ((record.Microsoft_FStar_Parser_DesugarEnv.constrname, ((Support.List.map (fun _125967 -> (match (_125967) with
| (f, _) -> begin
((get_field (Some (xterm)) f), Microsoft_FStar_Parser_AST.Nothing)
end))) record.Microsoft_FStar_Parser_DesugarEnv.fields)))
in Microsoft_FStar_Parser_AST.Let ((false, (((Microsoft_FStar_Parser_AST.mk_pattern (Microsoft_FStar_Parser_AST.PatVar ((x, false))) x.Microsoft_FStar_Absyn_Syntax.idRange), e))::[], (Microsoft_FStar_Parser_AST.mk_term record top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))))))
end)
in (let recterm = (Microsoft_FStar_Parser_AST.mk_term recterm top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level)
in (desugar_exp env recterm))))
end))
end))
end
| Microsoft_FStar_Parser_AST.Project ((e, f)) -> begin
(let _125978 = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_125978) with
| (_, fieldname) -> begin
(let proj = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.App (((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Var (fieldname)) (Microsoft_FStar_Absyn_Syntax.range_of_lid f) Microsoft_FStar_Parser_AST.Expr), e, Microsoft_FStar_Parser_AST.Nothing))) top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level)
in (desugar_exp env proj))
end))
end
| Microsoft_FStar_Parser_AST.Paren (e) -> begin
(desugar_exp env e)
end
| _ -> begin
(Microsoft_FStar_Parser_AST.error "Unexpected term" top top.Microsoft_FStar_Parser_AST.range)
end))))
and desugar_typ = (fun env top -> (let wpos = (fun t -> (t None top.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun t -> (let _125990 = t
in {Microsoft_FStar_Absyn_Syntax.n = _125990.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _125990.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = top.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _125990.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _125990.Microsoft_FStar_Absyn_Syntax.uvs}))
in (let top = (unparen top)
in (let head_and_args = (fun t -> (let rec aux = (fun args t -> (match ((unparen t).Microsoft_FStar_Parser_AST.tm) with
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
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(Microsoft_FStar_Absyn_Util.b2t (desugar_exp env t))
end)
end
| Microsoft_FStar_Parser_AST.Ensures ((t, lopt)) -> begin
(let t = (label_conjuncts "post-condition" false lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(Microsoft_FStar_Absyn_Util.b2t (desugar_exp env t))
end)
end
| Microsoft_FStar_Parser_AST.Op (("*", t1::_::[])) -> begin
if (is_type env t1) then begin
(let rec flatten = (fun t -> (match (t.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Op (("*", t1::t2::[])) -> begin
(let rest = (flatten t2)
in (t1)::rest)
end
| _ -> begin
(t)::[]
end))
in (let targs = ((Support.List.map (fun t -> (Microsoft_FStar_Absyn_Syntax.targ (desugar_typ env t)))) (flatten top))
in (let tup = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) (Microsoft_FStar_Absyn_Util.mk_tuple_lid (Support.List.length targs) top.Microsoft_FStar_Parser_AST.range))
in (wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))))
end else begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.Microsoft.FStar.Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" (Microsoft_FStar_Parser_AST.term_to_string t1)), top.Microsoft_FStar_Parser_AST.range))))
end
end
| Microsoft_FStar_Parser_AST.Op (("=!=", args)) -> begin
(desugar_typ env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Op (("~", ((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Op (("==", args))) top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))::[]))) top.Microsoft_FStar_Parser_AST.range top.Microsoft_FStar_Parser_AST.level))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match ((op_as_tylid env top.Microsoft_FStar_Parser_AST.range s)) with
| None -> begin
(Microsoft_FStar_Absyn_Util.b2t (desugar_exp env top))
end
| Some (l) -> begin
(let args = (Support.List.map (fun t -> ((arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) (desugar_typ_or_exp env t))) args)
in (Microsoft_FStar_Absyn_Util.mk_typ_app (Microsoft_FStar_Absyn_Util.ftv l Microsoft_FStar_Absyn_Syntax.kun) args))
end)
end
| Microsoft_FStar_Parser_AST.Tvar (a) -> begin
(setpos (Microsoft_FStar_Parser_DesugarEnv.fail_or2 (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env) a))
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) when ((Support.List.length l.Microsoft_FStar_Absyn_Syntax.ns) = 0) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env l.Microsoft_FStar_Absyn_Syntax.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(setpos (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l))
end)
end
| (Microsoft_FStar_Parser_AST.Var (l)) | (Microsoft_FStar_Parser_AST.Name (l)) -> begin
(let l = (Microsoft_FStar_Absyn_Util.set_lid_range l top.Microsoft_FStar_Parser_AST.range)
in (setpos (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)))
end
| Microsoft_FStar_Parser_AST.Construct ((l, args)) -> begin
(let t = (setpos (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) l))
in (let args = (Support.List.map (fun _126073 -> (match (_126073) with
| (t, imp) -> begin
((arg_withimp_t imp) (desugar_typ_or_exp env t))
end)) args)
in (Microsoft_FStar_Absyn_Util.mk_typ_app t args)))
end
| Microsoft_FStar_Parser_AST.Abs ((binders, body)) -> begin
(let rec aux = (fun env bs _124485 -> (match (_124485) with
| [] -> begin
(let body = (desugar_typ env body)
in (wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam ((Support.List.rev bs), body))))
end
| hd::tl -> begin
(let _126091 = (desugar_binding_pat env hd)
in (match (_126091) with
| (env, bnd, pat) -> begin
(match (pat) with
| Some (q) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.Microsoft.FStar.Util.format1 "Pattern matching at the type level is not supported; got %s\n" (Microsoft_FStar_Absyn_Print.pat_to_string q)), hd.Microsoft_FStar_Parser_AST.prange))))
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
(let rec aux = (fun args e -> (match ((unparen e).Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.App ((e, arg, imp)) -> begin
(let arg = ((arg_withimp_t imp) (desugar_typ_or_exp env arg))
in (aux ((arg)::args) e))
end
| _ -> begin
(let head = (desugar_typ env e)
in (wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (head, args))))
end))
in (aux [] top))
end
| Microsoft_FStar_Parser_AST.Product (([], t)) -> begin
(failwith ("Impossible: product with no binders"))
end
| Microsoft_FStar_Parser_AST.Product ((binders, t)) -> begin
(let _126121 = (uncurry binders t)
in (match (_126121) with
| (bs, t) -> begin
(let rec aux = (fun env bs _124486 -> (match (_124486) with
| [] -> begin
(let cod = (desugar_comp top.Microsoft_FStar_Parser_AST.range true env t)
in (wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun ((Support.List.rev bs), cod))))
end
| hd::tl -> begin
(let mlenv = (Microsoft_FStar_Parser_DesugarEnv.default_ml env)
in (let bb = (desugar_binder mlenv hd)
in (let _126135 = (as_binder env hd.Microsoft_FStar_Parser_AST.aqual bb)
in (match (_126135) with
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
(let _126156 = (match ((as_binder env None (Support.Microsoft.FStar.Util.Inr (b)))) with
| ((Support.Microsoft.FStar.Util.Inr (x), _), env) -> begin
(x, env)
end
| _ -> begin
(failwith ("impossible"))
end)
in (match (_126156) with
| (b, env) -> begin
(let f = if (is_type env f) then begin
(desugar_formula env f)
end else begin
(Microsoft_FStar_Absyn_Util.b2t (desugar_exp env f))
end
in (wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (b, f))))
end))
end)
end
| (Microsoft_FStar_Parser_AST.NamedTyp ((_, t))) | (Microsoft_FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| Microsoft_FStar_Parser_AST.Ascribed ((t, k)) -> begin
(wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed' ((desugar_typ env t), (desugar_kind env k))))
end
| Microsoft_FStar_Parser_AST.Sum ((binders, t)) -> begin
(let _126190 = (Support.List.fold_left (fun _126175 b -> (match (_126175) with
| (env, tparams, typs) -> begin
(let _126179 = (desugar_exp_binder env b)
in (match (_126179) with
| (xopt, t) -> begin
(let _126185 = (match (xopt) with
| None -> begin
(env, (Microsoft_FStar_Absyn_Util.new_bvd (Some (top.Microsoft_FStar_Parser_AST.range))))
end
| Some (x) -> begin
(Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_126185) with
| (env, x) -> begin
(env, (Support.List.append tparams (((Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)), None))::[])), (Support.List.append typs (((Microsoft_FStar_Absyn_Syntax.targ (Microsoft_FStar_Absyn_Util.close_with_lam tparams t)))::[])))
end))
end))
end)) (env, [], []) (Support.List.append binders (((Microsoft_FStar_Parser_AST.mk_binder (Microsoft_FStar_Parser_AST.NoName (t)) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Type None))::[])))
in (match (_126190) with
| (env, _, targs) -> begin
(let tup = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) (Microsoft_FStar_Absyn_Util.mk_dtuple_lid (Support.List.length targs) top.Microsoft_FStar_Parser_AST.range))
in (wpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))
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
and desugar_comp = (fun r default_ok env t -> (let fail = (fun msg -> (raise (Microsoft_FStar_Absyn_Syntax.Error ((msg, r)))))
in (let pre_process_comp_typ = (fun t -> (let _126215 = (head_and_args t)
in (match (_126215) with
| (head, args) -> begin
(match (head.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Name (lemma) when (lemma.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "Lemma") -> begin
(let unit = ((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.unit_lid)) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Type), Microsoft_FStar_Parser_AST.Nothing)
in (let nil_pat = ((Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.nil_lid)) t.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Expr), Microsoft_FStar_Parser_AST.Nothing)
in (let _126241 = ((Support.List.partition (fun _126223 -> (match (_126223) with
| (arg, _) -> begin
(match ((unparen arg).Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.App (({Microsoft_FStar_Parser_AST.tm = Microsoft_FStar_Parser_AST.Var (d); Microsoft_FStar_Parser_AST.range = _; Microsoft_FStar_Parser_AST.level = _}, _, _)) -> begin
(d.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "decreases")
end
| _ -> begin
false
end)
end))) args)
in (match (_126241) with
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
in (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Construct ((lemma, (Support.List.append args decreases_clause)))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level))
end))))
end
| _ -> begin
t
end)
end)))
in (let t = (desugar_typ env (pre_process_comp_typ t))
in (let _126256 = (Microsoft_FStar_Absyn_Util.head_and_args t)
in (match (_126256) with
| (head, args) -> begin
(match (((Microsoft_FStar_Absyn_Util.compress_typ head).Microsoft_FStar_Absyn_Syntax.n, args)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_const (eff), (Support.Microsoft.FStar.Util.Inl (result_typ), _)::rest) -> begin
(let _126303 = ((Support.List.partition (fun _124487 -> (match (_124487) with
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
end))) rest)
in (match (_126303) with
| (dec, rest) -> begin
(let decreases_clause = ((Support.List.map (fun _124488 -> (match (_124488) with
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
end))) dec)
in if (Microsoft_FStar_Parser_DesugarEnv.is_effect_name env eff.Microsoft_FStar_Absyn_Syntax.v) then begin
if ((Microsoft_FStar_Absyn_Syntax.lid_equals eff.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.tot_effect_lid) && ((Support.List.length decreases_clause) = 0)) then begin
(Microsoft_FStar_Absyn_Syntax.mk_Total result_typ)
end else begin
(let flags = if (Microsoft_FStar_Absyn_Syntax.lid_equals eff.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.lemma_lid) then begin
(Microsoft_FStar_Absyn_Syntax.LEMMA)::[]
end else begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals eff.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.tot_effect_lid) then begin
(Microsoft_FStar_Absyn_Syntax.TOTAL)::[]
end else begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals eff.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.ml_effect_lid) then begin
(Microsoft_FStar_Absyn_Syntax.MLEFFECT)::[]
end else begin
[]
end
end
end
in (Microsoft_FStar_Absyn_Syntax.mk_Comp {Microsoft_FStar_Absyn_Syntax.effect_name = eff.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.result_typ = result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = rest; Microsoft_FStar_Absyn_Syntax.flags = (Support.List.append flags decreases_clause)}))
end
end else begin
if default_ok then begin
(env.Microsoft_FStar_Parser_DesugarEnv.default_result_effect t r)
end else begin
(fail (Support.Microsoft.FStar.Util.format1 "%s is not an effect" (Microsoft_FStar_Absyn_Print.typ_to_string t)))
end
end)
end))
end
| _ -> begin
if default_ok then begin
(env.Microsoft_FStar_Parser_DesugarEnv.default_result_effect t r)
end else begin
(fail (Support.Microsoft.FStar.Util.format1 "%s is not an effect" (Microsoft_FStar_Absyn_Print.typ_to_string t)))
end
end)
end))))))
and desugar_kind = (fun env k -> (let pos = (fun f -> (f k.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun kk -> (let _126334 = kk
in {Microsoft_FStar_Absyn_Syntax.n = _126334.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _126334.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = k.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _126334.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _126334.Microsoft_FStar_Absyn_Syntax.uvs}))
in (let k = (unparen k)
in (match (k.Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Name ({Microsoft_FStar_Absyn_Syntax.ns = _; Microsoft_FStar_Absyn_Syntax.ident = _; Microsoft_FStar_Absyn_Syntax.nsstr = _; Microsoft_FStar_Absyn_Syntax.str = "Type"}) -> begin
(setpos Microsoft_FStar_Absyn_Syntax.mk_Kind_type)
end
| Microsoft_FStar_Parser_AST.Name ({Microsoft_FStar_Absyn_Syntax.ns = _; Microsoft_FStar_Absyn_Syntax.ident = _; Microsoft_FStar_Absyn_Syntax.nsstr = _; Microsoft_FStar_Absyn_Syntax.str = "Effect"}) -> begin
(setpos Microsoft_FStar_Absyn_Syntax.mk_Kind_effect)
end
| Microsoft_FStar_Parser_AST.Name (l) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.find_kind_abbrev env (Microsoft_FStar_Parser_DesugarEnv.qualify_lid env l))) with
| Some (l) -> begin
(pos (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev ((l, []), Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown)))
end
| _ -> begin
(Microsoft_FStar_Parser_AST.error "Unexpected term where kind was expected" k k.Microsoft_FStar_Parser_AST.range)
end)
end
| Microsoft_FStar_Parser_AST.Wild -> begin
(setpos Microsoft_FStar_Absyn_Syntax.kun)
end
| Microsoft_FStar_Parser_AST.Product ((bs, k)) -> begin
(let _126368 = (uncurry bs k)
in (match (_126368) with
| (bs, k) -> begin
(let rec aux = (fun env bs _124489 -> (match (_124489) with
| [] -> begin
(pos (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow ((Support.List.rev bs), (desugar_kind env k))))
end
| hd::tl -> begin
(let _126379 = ((as_binder env hd.Microsoft_FStar_Parser_AST.aqual) (desugar_binder (Microsoft_FStar_Parser_DesugarEnv.default_ml env) hd))
in (match (_126379) with
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
(let args = (Support.List.map (fun _126389 -> (match (_126389) with
| (t, b) -> begin
(let qual = if (b = Microsoft_FStar_Parser_AST.Hash) then begin
Some (Microsoft_FStar_Absyn_Syntax.Implicit)
end else begin
None
end
in ((desugar_typ_or_exp env t), qual))
end)) args)
in (pos (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown))))
end)
end
| _ -> begin
(Microsoft_FStar_Parser_AST.error "Unexpected term where kind was expected" k k.Microsoft_FStar_Parser_AST.range)
end)))))
and desugar_formula' = (fun env f -> (let connective = (fun s -> (match (s) with
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
in (let pos = (fun t -> (t None f.Microsoft_FStar_Parser_AST.range))
in (let setpos = (fun t -> (let _126409 = t
in {Microsoft_FStar_Absyn_Syntax.n = _126409.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _126409.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = f.Microsoft_FStar_Parser_AST.range; Microsoft_FStar_Absyn_Syntax.fvs = _126409.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _126409.Microsoft_FStar_Absyn_Syntax.uvs}))
in (let desugar_quant = (fun q qt b pats body -> (let tk = (desugar_binder env (let _126417 = b
in {Microsoft_FStar_Parser_AST.b = _126417.Microsoft_FStar_Parser_AST.b; Microsoft_FStar_Parser_AST.brange = _126417.Microsoft_FStar_Parser_AST.brange; Microsoft_FStar_Parser_AST.blevel = Microsoft_FStar_Parser_AST.Formula; Microsoft_FStar_Parser_AST.aqual = _126417.Microsoft_FStar_Parser_AST.aqual}))
in (match (tk) with
| Support.Microsoft.FStar.Util.Inl ((Some (a), k)) -> begin
(let _126427 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_126427) with
| (env, a) -> begin
(let pats = (Support.List.map (fun e -> ((arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) (desugar_typ_or_exp env e))) pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _ -> begin
(setpos (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((body, pats)))))
end)
in (let body = (pos (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (((Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)))::[], body)))
in (setpos (Microsoft_FStar_Absyn_Util.mk_typ_app (Microsoft_FStar_Absyn_Util.ftv (Microsoft_FStar_Absyn_Util.set_lid_range qt b.Microsoft_FStar_Parser_AST.brange) Microsoft_FStar_Absyn_Syntax.kun) (((Microsoft_FStar_Absyn_Syntax.targ body))::[])))))))
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _126443 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_126443) with
| (env, x) -> begin
(let pats = (Support.List.map (fun e -> ((arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) (desugar_typ_or_exp env e))) pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
end)
in (let body = (pos (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (((Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)))::[], body)))
in (setpos (Microsoft_FStar_Absyn_Util.mk_typ_app (Microsoft_FStar_Absyn_Util.ftv (Microsoft_FStar_Absyn_Util.set_lid_range q b.Microsoft_FStar_Parser_AST.brange) Microsoft_FStar_Absyn_Syntax.kun) (((Microsoft_FStar_Absyn_Syntax.targ body))::[])))))))
end))
end
| _ -> begin
(failwith ("impossible"))
end)))
in (let push_quant = (fun q binders pats body -> (match (binders) with
| b::b'::_rest -> begin
(let rest = (b')::_rest
in (let body = (Microsoft_FStar_Parser_AST.mk_term (q (rest, pats, body)) (Support.Microsoft.FStar.Range.union_ranges b'.Microsoft_FStar_Parser_AST.brange body.Microsoft_FStar_Parser_AST.range) Microsoft_FStar_Parser_AST.Formula)
in (Microsoft_FStar_Parser_AST.mk_term (q ((b)::[], [], body)) f.Microsoft_FStar_Parser_AST.range Microsoft_FStar_Parser_AST.Formula)))
end
| _ -> begin
(failwith ("impossible"))
end))
in (match ((unparen f).Microsoft_FStar_Parser_AST.tm) with
| Microsoft_FStar_Parser_AST.Labeled ((f, l, p)) -> begin
(let f = (desugar_formula env f)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((f, l, Microsoft_FStar_Absyn_Syntax.dummyRange, p)))))
end
| Microsoft_FStar_Parser_AST.Op (("==", hd::_args)) -> begin
(let args = (hd)::_args
in (let args = (Support.List.map (fun t -> ((arg_withimp_t Microsoft_FStar_Parser_AST.Nothing) (desugar_typ_or_exp env t))) args)
in (let eq = if (is_type env hd) then begin
(Microsoft_FStar_Absyn_Util.ftv (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.eqT_lid f.Microsoft_FStar_Parser_AST.range) Microsoft_FStar_Absyn_Syntax.kun)
end else begin
(Microsoft_FStar_Absyn_Util.ftv (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.eq2_lid f.Microsoft_FStar_Parser_AST.range) Microsoft_FStar_Absyn_Syntax.kun)
end
in (Microsoft_FStar_Absyn_Util.mk_typ_app eq args))))
end
| Microsoft_FStar_Parser_AST.Op ((s, args)) -> begin
(match (((connective s), args)) with
| (Some (conn), _::_::[]) -> begin
(Microsoft_FStar_Absyn_Util.mk_typ_app (Microsoft_FStar_Absyn_Util.ftv (Microsoft_FStar_Absyn_Util.set_lid_range conn f.Microsoft_FStar_Parser_AST.range) Microsoft_FStar_Absyn_Syntax.kun) (Support.List.map (fun x -> (Microsoft_FStar_Absyn_Syntax.targ (desugar_formula env x))) args))
end
| _ -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(Microsoft_FStar_Absyn_Util.b2t (desugar_exp env f))
end
end)
end
| Microsoft_FStar_Parser_AST.If ((f1, f2, f3)) -> begin
(Microsoft_FStar_Absyn_Util.mk_typ_app (Microsoft_FStar_Absyn_Util.ftv (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.ite_lid f.Microsoft_FStar_Parser_AST.range) Microsoft_FStar_Absyn_Syntax.kun) (Support.List.map (fun x -> (match ((desugar_typ_or_exp env x)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| Support.Microsoft.FStar.Util.Inr (v) -> begin
(Microsoft_FStar_Absyn_Syntax.targ (Microsoft_FStar_Absyn_Util.b2t v))
end)) ((f1)::(f2)::(f3)::[])))
end
| Microsoft_FStar_Parser_AST.QForall ((_1::_2::_3, pats, body)) -> begin
(let binders = (_1)::(_2)::_3
in (desugar_formula env (push_quant (fun x -> Microsoft_FStar_Parser_AST.QForall (x)) binders pats body)))
end
| Microsoft_FStar_Parser_AST.QExists ((_1::_2::_3, pats, body)) -> begin
(let binders = (_1)::(_2)::_3
in (desugar_formula env (push_quant (fun x -> Microsoft_FStar_Parser_AST.QExists (x)) binders pats body)))
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
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(Microsoft_FStar_Absyn_Util.b2t (desugar_exp env f))
end
end)))))))
and desugar_formula = (fun env t -> (desugar_formula' (let _126549 = env
in {Microsoft_FStar_Parser_DesugarEnv.curmodule = _126549.Microsoft_FStar_Parser_DesugarEnv.curmodule; Microsoft_FStar_Parser_DesugarEnv.modules = _126549.Microsoft_FStar_Parser_DesugarEnv.modules; Microsoft_FStar_Parser_DesugarEnv.open_namespaces = _126549.Microsoft_FStar_Parser_DesugarEnv.open_namespaces; Microsoft_FStar_Parser_DesugarEnv.sigaccum = _126549.Microsoft_FStar_Parser_DesugarEnv.sigaccum; Microsoft_FStar_Parser_DesugarEnv.localbindings = _126549.Microsoft_FStar_Parser_DesugarEnv.localbindings; Microsoft_FStar_Parser_DesugarEnv.recbindings = _126549.Microsoft_FStar_Parser_DesugarEnv.recbindings; Microsoft_FStar_Parser_DesugarEnv.phase = Microsoft_FStar_Parser_AST.Formula; Microsoft_FStar_Parser_DesugarEnv.sigmap = _126549.Microsoft_FStar_Parser_DesugarEnv.sigmap; Microsoft_FStar_Parser_DesugarEnv.default_result_effect = _126549.Microsoft_FStar_Parser_DesugarEnv.default_result_effect; Microsoft_FStar_Parser_DesugarEnv.iface = _126549.Microsoft_FStar_Parser_DesugarEnv.iface; Microsoft_FStar_Parser_DesugarEnv.admitted_iface = _126549.Microsoft_FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder = (fun env b -> if (is_type_binder env b) then begin
Support.Microsoft.FStar.Util.Inl ((desugar_type_binder env b))
end else begin
Support.Microsoft.FStar.Util.Inr ((desugar_exp_binder env b))
end)
and typars_of_binders = (fun env bs -> (let _126582 = (Support.List.fold_left (fun _126557 b -> (match (_126557) with
| (env, out) -> begin
(let tk = (desugar_binder env (let _126559 = b
in {Microsoft_FStar_Parser_AST.b = _126559.Microsoft_FStar_Parser_AST.b; Microsoft_FStar_Parser_AST.brange = _126559.Microsoft_FStar_Parser_AST.brange; Microsoft_FStar_Parser_AST.blevel = Microsoft_FStar_Parser_AST.Formula; Microsoft_FStar_Parser_AST.aqual = _126559.Microsoft_FStar_Parser_AST.aqual}))
in (match (tk) with
| Support.Microsoft.FStar.Util.Inl ((Some (a), k)) -> begin
(let _126569 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_126569) with
| (env, a) -> begin
(env, ((Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)), b.Microsoft_FStar_Parser_AST.aqual))::out)
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _126577 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_126577) with
| (env, x) -> begin
(env, ((Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)), b.Microsoft_FStar_Parser_AST.aqual))::out)
end))
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected binder", b.Microsoft_FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_126582) with
| (env, tpars) -> begin
(env, (Support.List.rev tpars))
end)))
and desugar_exp_binder = (fun env b -> (match (b.Microsoft_FStar_Parser_AST.b) with
| Microsoft_FStar_Parser_AST.Annotated ((x, t)) -> begin
(Some (x), (desugar_typ env t))
end
| Microsoft_FStar_Parser_AST.TVariable (t) -> begin
(None, (Microsoft_FStar_Parser_DesugarEnv.fail_or2 (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_var env) t))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(None, (desugar_typ env t))
end
| Microsoft_FStar_Parser_AST.Variable (x) -> begin
(Some (x), Microsoft_FStar_Absyn_Syntax.tun)
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a type)", b.Microsoft_FStar_Parser_AST.brange))))
end))
and desugar_type_binder = (fun env b -> (let fail = (fun _126600 -> (match (_126600) with
| () -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a kind)", b.Microsoft_FStar_Parser_AST.brange))))
end))
in (match (b.Microsoft_FStar_Parser_AST.b) with
| (Microsoft_FStar_Parser_AST.Annotated ((x, t))) | (Microsoft_FStar_Parser_AST.TAnnotated ((x, t))) -> begin
(Some (x), (desugar_kind env t))
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
(None, (desugar_kind env t))
end
| Microsoft_FStar_Parser_AST.TVariable (x) -> begin
(Some (x), (let _126611 = Microsoft_FStar_Absyn_Syntax.mk_Kind_type
in {Microsoft_FStar_Absyn_Syntax.n = _126611.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _126611.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = b.Microsoft_FStar_Parser_AST.brange; Microsoft_FStar_Absyn_Syntax.fvs = _126611.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _126611.Microsoft_FStar_Absyn_Syntax.uvs}))
end
| _ -> begin
(fail ())
end)))

let gather_tc_binders = (fun tps k -> (let rec aux = (fun bs k -> (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((binders, k)) -> begin
(aux (Support.List.append bs binders) k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(aux bs k)
end
| _ -> begin
bs
end))
in (Microsoft_FStar_Absyn_Util.name_binders (aux tps k))))

let mk_data_discriminators = (fun env t tps k datas -> (let quals = (fun q -> if ((not (env.Microsoft_FStar_Parser_DesugarEnv.iface)) || env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface) then begin
(Microsoft_FStar_Absyn_Syntax.Assumption)::q
end else begin
q
end)
in (let binders = (gather_tc_binders tps k)
in (let p = (Microsoft_FStar_Absyn_Syntax.range_of_lid t)
in (let imp_binders = ((Support.List.map (fun _126643 -> (match (_126643) with
| (x, _) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end))) binders)
in (let binders = (Support.List.append imp_binders (((Microsoft_FStar_Absyn_Syntax.null_v_binder (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' ((Microsoft_FStar_Absyn_Util.ftv t Microsoft_FStar_Absyn_Syntax.kun), (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)) None p)))::[]))
in (let disc_type = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (binders, (Microsoft_FStar_Absyn_Util.total_comp (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.bool_lid Microsoft_FStar_Absyn_Syntax.ktype) p)) None p)
in ((Support.List.map (fun d -> (let disc_name = (Microsoft_FStar_Absyn_Util.mk_discriminator d)
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((disc_name, disc_type, (quals ((Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Discriminator (d))::[])), (Microsoft_FStar_Absyn_Syntax.range_of_lid disc_name)))))) datas))))))))

let mk_indexed_projectors = (fun refine_domain env _126654 lid formals t -> (match (_126654) with
| (tc, tps, k) -> begin
(let binders = (gather_tc_binders tps k)
in (let p = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (let arg_binder = (let arg_typ = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' ((Microsoft_FStar_Absyn_Util.ftv tc Microsoft_FStar_Absyn_Syntax.kun), (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)) None p)
in (let projectee = {Microsoft_FStar_Absyn_Syntax.ppname = (Microsoft_FStar_Absyn_Syntax.mk_ident ("projectee", p)); Microsoft_FStar_Absyn_Syntax.realname = (Microsoft_FStar_Absyn_Util.genident (Some (p)))}
in if (not (refine_domain)) then begin
(Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end else begin
(let disc_name = (Microsoft_FStar_Absyn_Util.mk_discriminator lid)
in (let x = (Microsoft_FStar_Absyn_Util.gen_bvar arg_typ)
in (Microsoft_FStar_Absyn_Syntax.v_binder ((Microsoft_FStar_Absyn_Util.bvd_to_bvar_s projectee) (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (x, (Microsoft_FStar_Absyn_Util.b2t (Microsoft_FStar_Absyn_Syntax.mk_Exp_app ((Microsoft_FStar_Absyn_Util.fvar false disc_name p), ((Microsoft_FStar_Absyn_Syntax.varg (Microsoft_FStar_Absyn_Util.bvar_to_exp x)))::[]) None p))) None p)))))
end))
in (let imp_binders = ((Support.List.map (fun _126668 -> (match (_126668) with
| (x, _) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end))) binders)
in (let binders = (Support.List.append imp_binders ((arg_binder)::[]))
in (let arg = (Microsoft_FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (let subst = ((Support.List.flatten) ((Support.List.mapi (fun i f -> (match ((Support.Prims.fst f)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
if ((Support.Microsoft.FStar.Util.for_some (fun _124490 -> (match (_124490) with
| (Support.Microsoft.FStar.Util.Inl (b), _) -> begin
(Microsoft_FStar_Absyn_Util.bvd_eq a.Microsoft_FStar_Absyn_Syntax.v b.Microsoft_FStar_Absyn_Syntax.v)
end
| _ -> begin
false
end))) binders) then begin
[]
end else begin
(let _126687 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_126687) with
| (field_name, _) -> begin
(let proj = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app ((Microsoft_FStar_Absyn_Util.ftv field_name Microsoft_FStar_Absyn_Syntax.kun), (arg)::[]) None p)
in (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, proj)))::[])
end))
end
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
if ((Support.Microsoft.FStar.Util.for_some (fun _124491 -> (match (_124491) with
| (Support.Microsoft.FStar.Util.Inr (y), _) -> begin
(Microsoft_FStar_Absyn_Util.bvd_eq x.Microsoft_FStar_Absyn_Syntax.v y.Microsoft_FStar_Absyn_Syntax.v)
end
| _ -> begin
false
end))) binders) then begin
[]
end else begin
(let _126702 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_126702) with
| (field_name, _) -> begin
(let proj = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app ((Microsoft_FStar_Absyn_Util.fvar false field_name p), (arg)::[]) None p)
in (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, proj)))::[])
end))
end
end))) formals))
in ((Support.List.mapi (fun i ax -> (match ((Support.Prims.fst ax)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _126712 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_126712) with
| (field_name, _) -> begin
(let kk = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (binders, (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)) p)
in Microsoft_FStar_Absyn_Syntax.Sig_tycon ((field_name, [], kk, [], [], (Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Projector ((lid, Support.Microsoft.FStar.Util.Inl (a.Microsoft_FStar_Absyn_Syntax.v))))::[], (Microsoft_FStar_Absyn_Syntax.range_of_lid field_name))))
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _126719 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_126719) with
| (field_name, _) -> begin
(let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (binders, (Microsoft_FStar_Absyn_Util.total_comp (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort) p)) None p)
in (let quals = (fun q -> if ((not (env.Microsoft_FStar_Parser_DesugarEnv.iface)) || env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface) then begin
(Microsoft_FStar_Absyn_Syntax.Assumption)::q
end else begin
q
end)
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((field_name, t, (quals ((Microsoft_FStar_Absyn_Syntax.Logic)::(Microsoft_FStar_Absyn_Syntax.Projector ((lid, Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.v))))::[])), (Microsoft_FStar_Absyn_Syntax.range_of_lid field_name)))))
end))
end))) formals))))))))
end))

let mk_data_projectors = (fun env _124493 -> (match (_124493) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, _, _)) when (not ((Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.lexcons_lid))) -> begin
(let refine_domain = if ((Support.Microsoft.FStar.Util.for_some (fun _124492 -> (match (_124492) with
| Microsoft_FStar_Absyn_Syntax.RecordConstructor (_) -> begin
true
end
| _ -> begin
false
end))) quals) then begin
false
end else begin
(let _126746 = tycon
in (match (_126746) with
| (l, _, _) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.find_all_datacons env l)) with
| Some (l) -> begin
((Support.List.length l) > 1)
end
| _ -> begin
true
end)
end))
end
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

let rec desugar_tycon = (fun env rng quals tcs -> (let tycon_id = (fun _124494 -> (match (_124494) with
| (Microsoft_FStar_Parser_AST.TyconAbstract ((id, _, _))) | (Microsoft_FStar_Parser_AST.TyconAbbrev ((id, _, _, _))) | (Microsoft_FStar_Parser_AST.TyconRecord ((id, _, _, _))) | (Microsoft_FStar_Parser_AST.TyconVariant ((id, _, _, _))) -> begin
id
end))
in (let binder_to_term = (fun b -> (match (b.Microsoft_FStar_Parser_AST.b) with
| (Microsoft_FStar_Parser_AST.Annotated ((x, _))) | (Microsoft_FStar_Parser_AST.Variable (x)) -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Var ((Microsoft_FStar_Absyn_Syntax.lid_of_ids ((x)::[])))) x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr)
end
| (Microsoft_FStar_Parser_AST.TAnnotated ((a, _))) | (Microsoft_FStar_Parser_AST.TVariable (a)) -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Tvar (a)) a.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type)
end
| Microsoft_FStar_Parser_AST.NoName (t) -> begin
t
end))
in (let tot = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Name (Microsoft_FStar_Absyn_Const.tot_effect_lid)) rng Microsoft_FStar_Parser_AST.Expr)
in (let with_constructor_effect = (fun t -> (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.App ((tot, t, Microsoft_FStar_Parser_AST.Nothing))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level))
in (let apply_binders = (fun t binders -> (Support.List.fold_left (fun out b -> (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.App ((out, (binder_to_term b), Microsoft_FStar_Parser_AST.Nothing))) out.Microsoft_FStar_Parser_AST.range out.Microsoft_FStar_Parser_AST.level)) t binders))
in (let tycon_record_as_variant = (fun _124495 -> (match (_124495) with
| Microsoft_FStar_Parser_AST.TyconRecord ((id, parms, kopt, fields)) -> begin
(let constrName = (Microsoft_FStar_Absyn_Syntax.mk_ident ((Support.String.strcat "Mk" id.Microsoft_FStar_Absyn_Syntax.idText), id.Microsoft_FStar_Absyn_Syntax.idRange))
in (let mfields = (Support.List.map (fun _126832 -> (match (_126832) with
| (x, t) -> begin
(Microsoft_FStar_Parser_AST.mk_binder (Microsoft_FStar_Parser_AST.Annotated (((Microsoft_FStar_Absyn_Util.mangle_field_name x), t))) x.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Expr None)
end)) fields)
in (let result = (apply_binders (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Var ((Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id)::[])))) id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type) parms)
in (let constrTyp = (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type)
in (Microsoft_FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), ((Support.List.map (Support.Prims.fst)) fields))))))
end
| _ -> begin
(failwith ("impossible"))
end))
in (let desugar_abstract_tc = (fun quals _env mutuals _124496 -> (match (_124496) with
| Microsoft_FStar_Parser_AST.TyconAbstract ((id, binders, kopt)) -> begin
(let _126851 = (typars_of_binders _env binders)
in (match (_126851) with
| (_env', typars) -> begin
(let k = (match (kopt) with
| None -> begin
Microsoft_FStar_Absyn_Syntax.kun
end
| Some (k) -> begin
(desugar_kind _env' k)
end)
in (let tconstr = (apply_binders (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Var ((Microsoft_FStar_Absyn_Syntax.lid_of_ids ((id)::[])))) id.Microsoft_FStar_Absyn_Syntax.idRange Microsoft_FStar_Parser_AST.Type) binders)
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
in (let push_tparam = (fun env _124497 -> (match (_124497) with
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
in (let _126889 = (desugar_abstract_tc quals env [] tc)
in (match (_126889) with
| (_, _, se, _) -> begin
(let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))
end)))
end
| Microsoft_FStar_Parser_AST.TyconAbbrev ((id, binders, kopt, t))::[] -> begin
(let _126900 = (typars_of_binders env binders)
in (match (_126900) with
| (env', typars) -> begin
(let k = (match (kopt) with
| None -> begin
if (Support.Microsoft.FStar.Util.for_some (fun _124498 -> (match (_124498) with
| Microsoft_FStar_Absyn_Syntax.Effect -> begin
true
end
| _ -> begin
false
end)) quals) then begin
Microsoft_FStar_Absyn_Syntax.mk_Kind_effect
end else begin
Microsoft_FStar_Absyn_Syntax.kun
end
end
| Some (k) -> begin
(desugar_kind env' k)
end)
in (let t0 = t
in (let quals = if ((Support.Microsoft.FStar.Util.for_some (fun _124499 -> (match (_124499) with
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
true
end
| _ -> begin
false
end))) quals) then begin
quals
end else begin
if (t0.Microsoft_FStar_Parser_AST.level = Microsoft_FStar_Parser_AST.Formula) then begin
(Microsoft_FStar_Absyn_Syntax.Logic)::quals
end else begin
quals
end
end
in (let se = if ((Support.List.contains Microsoft_FStar_Absyn_Syntax.Effect) quals) then begin
(let c = (desugar_comp t.Microsoft_FStar_Parser_AST.range false env' t)
in Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (((Microsoft_FStar_Parser_DesugarEnv.qualify env id), typars, c, ((Support.List.filter (fun _124500 -> (match (_124500) with
| Microsoft_FStar_Absyn_Syntax.Effect -> begin
false
end
| _ -> begin
true
end))) quals), rng)))
end else begin
(let t = (desugar_typ env' t)
in Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (((Microsoft_FStar_Parser_DesugarEnv.qualify env id), typars, k, t, quals, rng)))
end
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| Microsoft_FStar_Parser_AST.TyconRecord (_)::[] -> begin
(let trec = (Support.List.hd tcs)
in (let _126930 = (tycon_record_as_variant trec)
in (match (_126930) with
| (t, fs) -> begin
(desugar_tycon env rng ((Microsoft_FStar_Absyn_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _::_ -> begin
(let env0 = env
in (let mutuals = (Support.List.map (fun x -> ((Microsoft_FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (let rec collect_tcs = (fun quals et tc -> (let _126945 = et
in (match (_126945) with
| (env, tcs) -> begin
(match (tc) with
| Microsoft_FStar_Parser_AST.TyconRecord (_) -> begin
(let trec = tc
in (let _126952 = (tycon_record_as_variant trec)
in (match (_126952) with
| (t, fs) -> begin
(collect_tcs ((Microsoft_FStar_Absyn_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| Microsoft_FStar_Parser_AST.TyconVariant ((id, binders, kopt, constructors)) -> begin
(let _126966 = (desugar_abstract_tc quals env mutuals (Microsoft_FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_126966) with
| (env, (_, tps), se, tconstr) -> begin
(env, (Support.Microsoft.FStar.Util.Inl ((se, tps, constructors, tconstr, quals)))::tcs)
end))
end
| Microsoft_FStar_Parser_AST.TyconAbbrev ((id, binders, kopt, t)) -> begin
(let _126980 = (desugar_abstract_tc quals env mutuals (Microsoft_FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_126980) with
| (env, (_, tps), se, tconstr) -> begin
(env, (Support.Microsoft.FStar.Util.Inr ((se, tps, t, quals)))::tcs)
end))
end
| _ -> begin
(failwith ("Unrecognized mutual type definition"))
end)
end)))
in (let _126985 = (Support.List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_126985) with
| (env, tcs) -> begin
(let tcs = (Support.List.rev tcs)
in (let sigelts = ((Support.List.collect (fun _124502 -> (match (_124502) with
| Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Syntax.Sig_tycon ((id, tpars, k, _, _, _, _)), tps, t, quals)) -> begin
(let env_tps = (push_tparams env tps)
in (let t = (desugar_typ env_tps t)
in (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((id, tpars, k, t, [], rng)))::[]))
end
| Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, _, tags, _)), tps, constrs, tconstr, quals)) -> begin
(let tycon = (tname, tpars, k)
in (let env_tps = (push_tparams env tps)
in (let _127052 = ((Support.List.split) ((Support.List.map (fun _127030 -> (match (_127030) with
| (id, topt, of_notation) -> begin
(let t = if of_notation then begin
(match (topt) with
| Some (t) -> begin
(Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Product ((((Microsoft_FStar_Parser_AST.mk_binder (Microsoft_FStar_Parser_AST.NoName (t)) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level None))::[], tconstr))) t.Microsoft_FStar_Parser_AST.range t.Microsoft_FStar_Parser_AST.level)
end
| None -> begin
tconstr
end)
end else begin
(match (topt) with
| None -> begin
(failwith ("Impossible"))
end
| Some (t) -> begin
t
end)
end
in (let t = (desugar_typ (Microsoft_FStar_Parser_DesugarEnv.default_total env_tps) (close env_tps t))
in (let name = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (let quals = ((Support.List.collect (fun _124501 -> (match (_124501) with
| Microsoft_FStar_Absyn_Syntax.RecordType (fns) -> begin
(Microsoft_FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _ -> begin
[]
end))) tags)
in (name, Microsoft_FStar_Absyn_Syntax.Sig_datacon ((name, (Microsoft_FStar_Absyn_Util.name_function_binders (Microsoft_FStar_Absyn_Util.close_typ (Support.List.map (fun _127049 -> (match (_127049) with
| (x, _) -> begin
(x, Some (Microsoft_FStar_Absyn_Syntax.Implicit))
end)) tps) t)), tycon, quals, mutuals, rng)))))))
end))) constrs))
in (match (_127052) with
| (constrNames, constrs) -> begin
(Microsoft_FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, constrNames, tags, rng)))::constrs
end))))
end
| _ -> begin
(failwith ("impossible"))
end))) tcs)
in (let bundle = Microsoft_FStar_Absyn_Syntax.Sig_bundle ((sigelts, quals, (Support.List.collect Microsoft_FStar_Absyn_Util.lids_of_sigelt sigelts), rng))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (let data_ops = ((Support.List.collect (mk_data_projectors env)) sigelts)
in (let discs = ((Support.List.collect (fun _124503 -> (match (_124503) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((tname, tps, k, _, constrs, _, _)) -> begin
(mk_data_discriminators env tname tps k constrs)
end
| _ -> begin
[]
end))) sigelts)
in (let ops = (Support.List.append discs data_ops)
in (let env = (Support.List.fold_left Microsoft_FStar_Parser_DesugarEnv.push_sigelt env ops)
in (env, (Support.List.append ((bundle)::[]) ops))))))))))
end)))))
end
| [] -> begin
(failwith ("impossible"))
end)))))))))))

let desugar_binders = (fun env binders -> (let _127104 = (Support.List.fold_left (fun _127082 b -> (match (_127082) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| Support.Microsoft.FStar.Util.Inl ((Some (a), k)) -> begin
(let _127091 = (Microsoft_FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_127091) with
| (env, a) -> begin
(env, ((Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)))::binders)
end))
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), t)) -> begin
(let _127099 = (Microsoft_FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_127099) with
| (env, x) -> begin
(env, ((Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)))::binders)
end))
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Missing name in binder", b.Microsoft_FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_127104) with
| (env, binders) -> begin
(env, (Support.List.rev binders))
end)))

let rec desugar_decl = (fun env d -> (match (d.Microsoft_FStar_Parser_AST.d) with
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
(match ((Microsoft_FStar_Absyn_Util.compress_exp (desugar_exp_maybe_top true env (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Let ((isrec, lets, (Microsoft_FStar_Parser_AST.mk_term (Microsoft_FStar_Parser_AST.Const (Microsoft_FStar_Absyn_Syntax.Const_unit)) d.Microsoft_FStar_Parser_AST.drange Microsoft_FStar_Parser_AST.Expr)))) d.Microsoft_FStar_Parser_AST.drange Microsoft_FStar_Parser_AST.Expr))).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, _)) -> begin
(let lids = ((Support.List.map (fun _124504 -> (match (_124504) with
| (Support.Microsoft.FStar.Util.Inr (l), _, _) -> begin
l
end
| _ -> begin
(failwith ("impossible"))
end))) (Support.Prims.snd lbs))
in (let quals = ((Support.List.collect (fun _124505 -> (match (_124505) with
| (Support.Microsoft.FStar.Util.Inl (_), _, _) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (l), _, _) -> begin
(Microsoft_FStar_Parser_DesugarEnv.lookup_letbinding_quals env l)
end))) (Support.Prims.snd lbs))
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
in (env, (Microsoft_FStar_Absyn_Syntax.Sig_assume (((Microsoft_FStar_Parser_DesugarEnv.qualify env id), f, (Microsoft_FStar_Absyn_Syntax.Assumption)::[], d.Microsoft_FStar_Parser_AST.drange)))::[]))
end
| Microsoft_FStar_Parser_AST.Val ((quals, id, t)) -> begin
(let t = (desugar_typ env (close_fun env t))
in (let quals = if (env.Microsoft_FStar_Parser_DesugarEnv.iface && env.Microsoft_FStar_Parser_DesugarEnv.admitted_iface) then begin
(Microsoft_FStar_Absyn_Syntax.Assumption)::quals
end else begin
quals
end
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_val_decl (((Microsoft_FStar_Parser_DesugarEnv.qualify env id), t, quals, d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[])))))
end
| Microsoft_FStar_Parser_AST.Exception ((id, None)) -> begin
(let t = (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) Microsoft_FStar_Absyn_Const.exn_lid)
in (let l = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_datacon ((l, t, (Microsoft_FStar_Absyn_Const.exn_lid, [], Microsoft_FStar_Absyn_Syntax.ktype), (Microsoft_FStar_Absyn_Syntax.ExceptionConstructor)::[], (Microsoft_FStar_Absyn_Const.exn_lid)::[], d.Microsoft_FStar_Parser_AST.drange))
in (let se' = Microsoft_FStar_Absyn_Syntax.Sig_bundle (((se)::[], [], (l)::[], d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env se')
in (let data_ops = (mk_data_projectors env se)
in (let discs = (mk_data_discriminators env Microsoft_FStar_Absyn_Const.exn_lid [] Microsoft_FStar_Absyn_Syntax.ktype ((l)::[]))
in (let env = (Support.List.fold_left Microsoft_FStar_Parser_DesugarEnv.push_sigelt env (Support.List.append discs data_ops))
in (env, (Support.List.append ((se')::discs) data_ops))))))))))
end
| Microsoft_FStar_Parser_AST.Exception ((id, Some (term))) -> begin
(let t = (desugar_typ env term)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (((Microsoft_FStar_Absyn_Syntax.null_v_binder t))::[], (Microsoft_FStar_Absyn_Syntax.mk_Total (Microsoft_FStar_Parser_DesugarEnv.fail_or env (Microsoft_FStar_Parser_DesugarEnv.try_lookup_typ_name env) Microsoft_FStar_Absyn_Const.exn_lid))) None d.Microsoft_FStar_Parser_AST.drange)
in (let l = (Microsoft_FStar_Parser_DesugarEnv.qualify env id)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_datacon ((l, t, (Microsoft_FStar_Absyn_Const.exn_lid, [], Microsoft_FStar_Absyn_Syntax.ktype), (Microsoft_FStar_Absyn_Syntax.ExceptionConstructor)::[], (Microsoft_FStar_Absyn_Const.exn_lid)::[], d.Microsoft_FStar_Parser_AST.drange))
in (let se' = Microsoft_FStar_Absyn_Syntax.Sig_bundle (((se)::[], [], (l)::[], d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env se')
in (let data_ops = (mk_data_projectors env se)
in (let discs = (mk_data_discriminators env Microsoft_FStar_Absyn_Const.exn_lid [] Microsoft_FStar_Absyn_Syntax.ktype ((l)::[]))
in (let env = (Support.List.fold_left Microsoft_FStar_Parser_DesugarEnv.push_sigelt env (Support.List.append discs data_ops))
in (env, (Support.List.append ((se')::discs) data_ops)))))))))))
end
| Microsoft_FStar_Parser_AST.KindAbbrev ((id, binders, k)) -> begin
(let _127210 = (desugar_binders env binders)
in (match (_127210) with
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
in (let _127226 = (desugar_binders env eff_binders)
in (match (_127226) with
| (env, binders) -> begin
(let defn = (desugar_typ env defn)
in (let _127230 = (Microsoft_FStar_Absyn_Util.head_and_args defn)
in (match (_127230) with
| (head, args) -> begin
(match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (eff) -> begin
(match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_effect_defn env eff.Microsoft_FStar_Absyn_Syntax.v)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat (Support.String.strcat "Effect " (Microsoft_FStar_Absyn_Print.sli eff.Microsoft_FStar_Absyn_Syntax.v)) " not found"), d.Microsoft_FStar_Parser_AST.drange))))
end
| Some (ed) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.subst_of_list ed.Microsoft_FStar_Absyn_Syntax.binders args)
in (let sub = (Microsoft_FStar_Absyn_Util.subst_typ subst)
in (let ed = {Microsoft_FStar_Absyn_Syntax.mname = (Microsoft_FStar_Parser_DesugarEnv.qualify env0 eff_name); Microsoft_FStar_Absyn_Syntax.binders = binders; Microsoft_FStar_Absyn_Syntax.qualifiers = quals; Microsoft_FStar_Absyn_Syntax.signature = (Microsoft_FStar_Absyn_Util.subst_kind subst ed.Microsoft_FStar_Absyn_Syntax.signature); Microsoft_FStar_Absyn_Syntax.ret = (sub ed.Microsoft_FStar_Absyn_Syntax.ret); Microsoft_FStar_Absyn_Syntax.bind_wp = (sub ed.Microsoft_FStar_Absyn_Syntax.bind_wp); Microsoft_FStar_Absyn_Syntax.bind_wlp = (sub ed.Microsoft_FStar_Absyn_Syntax.bind_wlp); Microsoft_FStar_Absyn_Syntax.if_then_else = (sub ed.Microsoft_FStar_Absyn_Syntax.if_then_else); Microsoft_FStar_Absyn_Syntax.ite_wp = (sub ed.Microsoft_FStar_Absyn_Syntax.ite_wp); Microsoft_FStar_Absyn_Syntax.ite_wlp = (sub ed.Microsoft_FStar_Absyn_Syntax.ite_wlp); Microsoft_FStar_Absyn_Syntax.wp_binop = (sub ed.Microsoft_FStar_Absyn_Syntax.wp_binop); Microsoft_FStar_Absyn_Syntax.wp_as_type = (sub ed.Microsoft_FStar_Absyn_Syntax.wp_as_type); Microsoft_FStar_Absyn_Syntax.close_wp = (sub ed.Microsoft_FStar_Absyn_Syntax.close_wp); Microsoft_FStar_Absyn_Syntax.close_wp_t = (sub ed.Microsoft_FStar_Absyn_Syntax.close_wp_t); Microsoft_FStar_Absyn_Syntax.assert_p = (sub ed.Microsoft_FStar_Absyn_Syntax.assert_p); Microsoft_FStar_Absyn_Syntax.assume_p = (sub ed.Microsoft_FStar_Absyn_Syntax.assume_p); Microsoft_FStar_Absyn_Syntax.null_wp = (sub ed.Microsoft_FStar_Absyn_Syntax.null_wp); Microsoft_FStar_Absyn_Syntax.trivial = (sub ed.Microsoft_FStar_Absyn_Syntax.trivial)}
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ed, d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat (Microsoft_FStar_Absyn_Print.typ_to_string head) " is not an effect"), d.Microsoft_FStar_Parser_AST.drange))))
end)
end)))
end)))
end
| Microsoft_FStar_Parser_AST.NewEffect ((quals, Microsoft_FStar_Parser_AST.DefineEffect ((eff_name, eff_binders, eff_kind, eff_decls)))) -> begin
(let env0 = env
in (let env = (Microsoft_FStar_Parser_DesugarEnv.enter_monad_scope env eff_name)
in (let _127256 = (desugar_binders env eff_binders)
in (match (_127256) with
| (env, binders) -> begin
(let eff_k = (desugar_kind env eff_kind)
in (let _127267 = ((Support.List.fold_left (fun _127260 decl -> (match (_127260) with
| (env, out) -> begin
(let _127264 = (desugar_decl env decl)
in (match (_127264) with
| (env, ses) -> begin
(env, ((Support.List.hd ses))::out)
end))
end)) (env, [])) eff_decls)
in (match (_127267) with
| (env, decls) -> begin
(let decls = (Support.List.rev decls)
in (let lookup = (fun s -> (match ((Microsoft_FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env (Microsoft_FStar_Parser_DesugarEnv.qualify env (Microsoft_FStar_Absyn_Syntax.mk_ident (s, d.Microsoft_FStar_Parser_AST.drange))))) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat (Support.String.strcat (Support.String.strcat "Monad " eff_name.Microsoft_FStar_Absyn_Syntax.idText) " expects definition of ") s), d.Microsoft_FStar_Parser_AST.drange))))
end
| Some (t) -> begin
t
end))
in (let ed = {Microsoft_FStar_Absyn_Syntax.mname = (Microsoft_FStar_Parser_DesugarEnv.qualify env0 eff_name); Microsoft_FStar_Absyn_Syntax.binders = binders; Microsoft_FStar_Absyn_Syntax.qualifiers = quals; Microsoft_FStar_Absyn_Syntax.signature = eff_k; Microsoft_FStar_Absyn_Syntax.ret = (lookup "return"); Microsoft_FStar_Absyn_Syntax.bind_wp = (lookup "bind_wp"); Microsoft_FStar_Absyn_Syntax.bind_wlp = (lookup "bind_wlp"); Microsoft_FStar_Absyn_Syntax.if_then_else = (lookup "if_then_else"); Microsoft_FStar_Absyn_Syntax.ite_wp = (lookup "ite_wp"); Microsoft_FStar_Absyn_Syntax.ite_wlp = (lookup "ite_wlp"); Microsoft_FStar_Absyn_Syntax.wp_binop = (lookup "wp_binop"); Microsoft_FStar_Absyn_Syntax.wp_as_type = (lookup "wp_as_type"); Microsoft_FStar_Absyn_Syntax.close_wp = (lookup "close_wp"); Microsoft_FStar_Absyn_Syntax.close_wp_t = (lookup "close_wp_t"); Microsoft_FStar_Absyn_Syntax.assert_p = (lookup "assert_p"); Microsoft_FStar_Absyn_Syntax.assume_p = (lookup "assume_p"); Microsoft_FStar_Absyn_Syntax.null_wp = (lookup "null_wp"); Microsoft_FStar_Absyn_Syntax.trivial = (lookup "trivial")}
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ed, d.Microsoft_FStar_Parser_AST.drange))
in (let env = (Microsoft_FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)))
end))))
end
| Microsoft_FStar_Parser_AST.SubEffect (l) -> begin
(let lookup = (fun l -> (match ((Microsoft_FStar_Parser_DesugarEnv.try_lookup_effect_name env l)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat (Support.String.strcat "Effect name " (Microsoft_FStar_Absyn_Print.sli l)) " not found"), d.Microsoft_FStar_Parser_AST.drange))))
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

let desugar_decls = (fun env decls -> (Support.List.fold_left (fun _127292 d -> (match (_127292) with
| (env, sigelts) -> begin
(let _127296 = (desugar_decl env d)
in (match (_127296) with
| (env, se) -> begin
(env, (Support.List.append sigelts se))
end))
end)) (env, []) decls))

let desugar_partial_modul = (fun curmod env m -> (let open_ns = (fun mname d -> if ((Support.List.length mname.Microsoft_FStar_Absyn_Syntax.ns) <> 0) then begin
((Microsoft_FStar_Parser_AST.mk_decl (Microsoft_FStar_Parser_AST.Open ((Microsoft_FStar_Absyn_Syntax.lid_of_ids mname.Microsoft_FStar_Absyn_Syntax.ns))) (Microsoft_FStar_Absyn_Syntax.range_of_lid mname)))::d
end else begin
d
end)
in (let env = (match (curmod) with
| None -> begin
env
end
| Some ((prev_mod, _)) -> begin
(Microsoft_FStar_Parser_DesugarEnv.finish_module_or_interface env prev_mod)
end)
in (let _127323 = (match (m) with
| Microsoft_FStar_Parser_AST.Interface ((mname, decls, admitted)) -> begin
((Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname), mname, (open_ns mname decls), true)
end
| Microsoft_FStar_Parser_AST.Module ((mname, decls)) -> begin
((Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname), mname, (open_ns mname decls), false)
end)
in (match (_127323) with
| (env, mname, decls, intf) -> begin
(let _127326 = (desugar_decls env decls)
in (match (_127326) with
| (env, sigelts) -> begin
(let modul = {Microsoft_FStar_Absyn_Syntax.name = mname; Microsoft_FStar_Absyn_Syntax.declarations = sigelts; Microsoft_FStar_Absyn_Syntax.exports = []; Microsoft_FStar_Absyn_Syntax.is_interface = intf; Microsoft_FStar_Absyn_Syntax.is_deserialized = false}
in (env, modul))
end))
end)))))

let desugar_modul = (fun env m -> (let _127332 = (desugar_partial_modul None env m)
in (match (_127332) with
| (env, modul) -> begin
(let env = (Microsoft_FStar_Parser_DesugarEnv.finish_module_or_interface env modul)
in (let _127334 = if (Microsoft_FStar_Options.should_dump modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str) then begin
(Support.Microsoft.FStar.Util.fprint1 "%s\n" (Microsoft_FStar_Absyn_Print.modul_to_string modul))
end
in (env, modul)))
end)))

let desugar_file = (fun env f -> (let _127347 = (Support.List.fold_left (fun _127340 m -> (match (_127340) with
| (env, mods) -> begin
(let _127344 = (desugar_modul env m)
in (match (_127344) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_127347) with
| (env, mods) -> begin
(env, (Support.List.rev mods))
end)))

let add_modul_to_env = (fun m en -> (let en = (Microsoft_FStar_Parser_DesugarEnv.prepare_module_or_interface false false en m.Microsoft_FStar_Absyn_Syntax.name)
in (let en = (Support.List.fold_left Microsoft_FStar_Parser_DesugarEnv.push_sigelt (let _127351 = en
in {Microsoft_FStar_Parser_DesugarEnv.curmodule = Some (m.Microsoft_FStar_Absyn_Syntax.name); Microsoft_FStar_Parser_DesugarEnv.modules = _127351.Microsoft_FStar_Parser_DesugarEnv.modules; Microsoft_FStar_Parser_DesugarEnv.open_namespaces = _127351.Microsoft_FStar_Parser_DesugarEnv.open_namespaces; Microsoft_FStar_Parser_DesugarEnv.sigaccum = _127351.Microsoft_FStar_Parser_DesugarEnv.sigaccum; Microsoft_FStar_Parser_DesugarEnv.localbindings = _127351.Microsoft_FStar_Parser_DesugarEnv.localbindings; Microsoft_FStar_Parser_DesugarEnv.recbindings = _127351.Microsoft_FStar_Parser_DesugarEnv.recbindings; Microsoft_FStar_Parser_DesugarEnv.phase = _127351.Microsoft_FStar_Parser_DesugarEnv.phase; Microsoft_FStar_Parser_DesugarEnv.sigmap = _127351.Microsoft_FStar_Parser_DesugarEnv.sigmap; Microsoft_FStar_Parser_DesugarEnv.default_result_effect = _127351.Microsoft_FStar_Parser_DesugarEnv.default_result_effect; Microsoft_FStar_Parser_DesugarEnv.iface = _127351.Microsoft_FStar_Parser_DesugarEnv.iface; Microsoft_FStar_Parser_DesugarEnv.admitted_iface = _127351.Microsoft_FStar_Parser_DesugarEnv.admitted_iface}) m.Microsoft_FStar_Absyn_Syntax.exports)
in (Microsoft_FStar_Parser_DesugarEnv.finish_module_or_interface en m))))




