
open Prims
let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _67_1 -> (match (_67_1) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.Implicit)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| _67_29 -> begin
None
end))

let trans_qual : FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun _67_2 -> (match (_67_2) with
| FStar_Parser_AST.Private -> begin
FStar_Syntax_Syntax.Private
end
| FStar_Parser_AST.Assumption -> begin
FStar_Syntax_Syntax.Assumption
end
| FStar_Parser_AST.Inline -> begin
FStar_Syntax_Syntax.Inline
end
| FStar_Parser_AST.Unfoldable -> begin
FStar_Syntax_Syntax.Unfoldable
end
| FStar_Parser_AST.Irreducible -> begin
FStar_Syntax_Syntax.Irreducible
end
| FStar_Parser_AST.Logic -> begin
FStar_Syntax_Syntax.Logic
end
| FStar_Parser_AST.TotalEffect -> begin
FStar_Syntax_Syntax.TotalEffect
end
| FStar_Parser_AST.DefaultEffect -> begin
FStar_Syntax_Syntax.DefaultEffect (None)
end
| FStar_Parser_AST.Effect -> begin
FStar_Syntax_Syntax.Effect
end
| FStar_Parser_AST.New -> begin
FStar_Syntax_Syntax.New
end
| FStar_Parser_AST.Abstract -> begin
FStar_Syntax_Syntax.Abstract
end
| FStar_Parser_AST.Opaque -> begin
(FStar_All.failwith "Impossible")
end))

let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun _67_3 -> (match (_67_3) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions -> begin
FStar_Syntax_Syntax.ResetOptions
end))

let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _67_4 -> (match (_67_4) with
| (FStar_Parser_AST.Hash) | (FStar_Parser_AST.FsTypApp) -> begin
Some (FStar_Syntax_Syntax.Implicit)
end
| _67_51 -> begin
None
end))

let arg_withimp_e = (fun imp t -> (t, (as_imp imp)))

let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
(t, Some (FStar_Syntax_Syntax.Implicit))
end
| _67_58 -> begin
(t, None)
end))

let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_67_62) -> begin
true
end
| _67_65 -> begin
false
end)))))

let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _67_70 -> begin
t
end))

let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _169_21 = (let _169_20 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_169_20))
in (FStar_Parser_AST.mk_term _169_21 r FStar_Parser_AST.Kind)))

let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (let name_of_char = (fun _67_5 -> (match (_67_5) with
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
| _67_93 -> begin
"UNKNOWN"
end))
in (let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _169_32 = (let _169_30 = (FStar_Util.char_at s i)
in (name_of_char _169_30))
in (let _169_31 = (aux (i + 1))
in (_169_32)::_169_31))
end)
in (let _169_34 = (let _169_33 = (aux 0)
in (FStar_String.concat "_" _169_33))
in (Prims.strcat "op_" _169_34)))))

let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _169_44 = (let _169_43 = (let _169_42 = (let _169_41 = (compile_op n s)
in (_169_41, r))
in (FStar_Ident.mk_ident _169_42))
in (_169_43)::[])
in (FStar_All.pipe_right _169_44 FStar_Ident.lid_of_ids)))

let op_as_lid : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (let r = (fun l -> (let _169_55 = (FStar_Ident.set_lid_range l rng)
in Some (_169_55)))
in (let fallback = (fun _67_107 -> (match (()) with
| () -> begin
(match (s) with
| "=" -> begin
(r FStar_Syntax_Const.op_Eq)
end
| ":=" -> begin
(r FStar_Syntax_Const.op_ColonEq)
end
| "<" -> begin
(r FStar_Syntax_Const.op_LT)
end
| "<=" -> begin
(r FStar_Syntax_Const.op_LTE)
end
| ">" -> begin
(r FStar_Syntax_Const.op_GT)
end
| ">=" -> begin
(r FStar_Syntax_Const.op_GTE)
end
| "&&" -> begin
(r FStar_Syntax_Const.op_And)
end
| "||" -> begin
(r FStar_Syntax_Const.op_Or)
end
| "*" -> begin
(r FStar_Syntax_Const.op_Multiply)
end
| "+" -> begin
(r FStar_Syntax_Const.op_Addition)
end
| "-" when (arity = 1) -> begin
(r FStar_Syntax_Const.op_Minus)
end
| "-" -> begin
(r FStar_Syntax_Const.op_Subtraction)
end
| "/" -> begin
(r FStar_Syntax_Const.op_Division)
end
| "%" -> begin
(r FStar_Syntax_Const.op_Modulus)
end
| "!" -> begin
(r FStar_Syntax_Const.read_lid)
end
| "@" -> begin
(r FStar_Syntax_Const.list_append_lid)
end
| "^" -> begin
(r FStar_Syntax_Const.strcat_lid)
end
| "|>" -> begin
(r FStar_Syntax_Const.pipe_right_lid)
end
| "<|" -> begin
(r FStar_Syntax_Const.pipe_left_lid)
end
| "<>" -> begin
(r FStar_Syntax_Const.op_notEq)
end
| "~" -> begin
(r FStar_Syntax_Const.not_lid)
end
| "==" -> begin
(r FStar_Syntax_Const.eq2_lid)
end
| "=!=" -> begin
(r FStar_Syntax_Const.neq2_lid)
end
| "<<" -> begin
(r FStar_Syntax_Const.precedes_lid)
end
| "/\\" -> begin
(r FStar_Syntax_Const.and_lid)
end
| "\\/" -> begin
(r FStar_Syntax_Const.or_lid)
end
| "==>" -> begin
(r FStar_Syntax_Const.imp_lid)
end
| "<==>" -> begin
(r FStar_Syntax_Const.iff_lid)
end
| _67_137 -> begin
None
end)
end))
in (match ((let _169_58 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _169_58))) with
| Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _67_146); FStar_Syntax_Syntax.tk = _67_143; FStar_Syntax_Syntax.pos = _67_141; FStar_Syntax_Syntax.vars = _67_139}) -> begin
Some (fv.FStar_Syntax_Syntax.v)
end
| _67_152 -> begin
(fallback ())
end))))

let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _169_65 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _169_65)))

let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_67_161) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _67_168 = (FStar_Parser_Env.push_bv env x)
in (match (_67_168) with
| (env, _67_167) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_67_170, term) -> begin
(let _169_72 = (free_type_vars env term)
in (env, _169_72))
end
| FStar_Parser_AST.TAnnotated (id, _67_176) -> begin
(let _67_182 = (FStar_Parser_Env.push_bv env id)
in (match (_67_182) with
| (env, _67_181) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _169_73 = (free_type_vars env t)
in (env, _169_73))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _169_76 = (unparen t)
in _169_76.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_67_188) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _67_194 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_67_224, ts) -> begin
(FStar_List.collect (fun _67_231 -> (match (_67_231) with
| (t, _67_230) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_67_233, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _67_240) -> begin
(let _169_79 = (free_type_vars env t1)
in (let _169_78 = (free_type_vars env t2)
in (FStar_List.append _169_79 _169_78)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(let _67_249 = (free_type_vars_b env b)
in (match (_67_249) with
| (env, f) -> begin
(let _169_80 = (free_type_vars env t)
in (FStar_List.append f _169_80))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(let _67_265 = (FStar_List.fold_left (fun _67_258 binder -> (match (_67_258) with
| (env, free) -> begin
(let _67_262 = (free_type_vars_b env binder)
in (match (_67_262) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_67_265) with
| (env, free) -> begin
(let _169_83 = (free_type_vars env body)
in (FStar_List.append free _169_83))
end))
end
| FStar_Parser_AST.Project (t, _67_268) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
(FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.FStar_Parser_AST.range)
end))

let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (let rec aux = (fun args t -> (match ((let _169_90 = (unparen t)
in _169_90.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _67_312 -> begin
(t, args)
end))
in (aux [] t)))

let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (let ftv = (let _169_95 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _169_95))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _169_99 = (let _169_98 = (let _169_97 = (tm_type x.FStar_Ident.idRange)
in (x, _169_97))
in FStar_Parser_AST.TAnnotated (_169_98))
in (FStar_Parser_AST.mk_binder _169_99 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (let ftv = (let _169_104 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _169_104))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _169_108 = (let _169_107 = (let _169_106 = (tm_type x.FStar_Ident.idRange)
in (x, _169_106))
in FStar_Parser_AST.TAnnotated (_169_107))
in (FStar_Parser_AST.mk_binder _169_108 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (let t = (match ((let _169_109 = (unparen t)
in _169_109.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_67_325) -> begin
t
end
| _67_328 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))

let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _67_338 -> begin
(bs, t)
end))

let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _67_342) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_67_348); FStar_Parser_AST.prange = _67_346}, _67_352) -> begin
true
end
| _67_356 -> begin
false
end))

let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(let _67_368 = (destruct_app_pattern env is_top_level p)
in (match (_67_368) with
| (name, args, _67_367) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _67_373); FStar_Parser_AST.prange = _67_370}, args) when is_top_level -> begin
(let _169_123 = (let _169_122 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_169_122))
in (_169_123, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _67_384); FStar_Parser_AST.prange = _67_381}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _67_392 -> begin
(FStar_All.failwith "Not an app pattern")
end))

type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term)

let is_LocalBinder : bnd  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| LocalBinder (_) -> begin
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

let ___LocalBinder____0 : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun projectee -> (match (projectee) with
| LocalBinder (_67_395) -> begin
_67_395
end))

let ___LetBinder____0 : bnd  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| LetBinder (_67_398) -> begin
_67_398
end))

let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _67_6 -> (match (_67_6) with
| LocalBinder (a, aq) -> begin
(a, aq)
end
| _67_405 -> begin
(FStar_All.failwith "Impossible")
end))

let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _67_7 -> (match (_67_7) with
| (None, k) -> begin
(let _169_160 = (FStar_Syntax_Syntax.null_binder k)
in (_169_160, env))
end
| (Some (a), k) -> begin
(let _67_418 = (FStar_Parser_Env.push_bv env a)
in (match (_67_418) with
| (env, a) -> begin
(((let _67_419 = a
in {FStar_Syntax_Syntax.ppname = _67_419.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_419.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}), (trans_aqual imp)), env)
end))
end))

type env_t =
FStar_Parser_Env.env

type lenv_t =
FStar_Syntax_Syntax.bv Prims.list

let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _67_424 -> (match (_67_424) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))

let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))

let rec desugar_data_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat) = (fun env p -> (let check_linear_pattern_variables = (fun p -> (let rec pat_vars = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_dot_term (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_constant (_)) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (_67_445, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _67_453 -> (match (_67_453) with
| (p, _67_452) -> begin
(let _169_206 = (pat_vars p)
in (FStar_Util.set_union out _169_206))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj (hd::tl) -> begin
(let xs = (pat_vars hd)
in if (not ((FStar_Util.for_all (fun p -> (let ys = (pat_vars p)
in ((FStar_Util.set_is_subset_of xs ys) && (FStar_Util.set_is_subset_of ys xs)))) tl))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Disjunctive pattern binds different variables in each case", p.FStar_Syntax_Syntax.p))))
end else begin
xs
end)
end))
in (pat_vars p)))
in (let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))) with
| Some (y) -> begin
(l, e, y)
end
| _67_471 -> begin
(let _67_474 = (FStar_Parser_Env.push_bv e x)
in (match (_67_474) with
| (e, x) -> begin
((x)::l, e, x)
end))
end))
in (let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun b -> (b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText))))) with
| Some (b) -> begin
(l, e, b)
end
| _67_483 -> begin
(let _67_486 = (FStar_Parser_Env.push_bv e a)
in (match (_67_486) with
| (e, a) -> begin
((a)::l, e, a)
end))
end))
in (let rec aux = (fun loc env p -> (let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Parser_AST.prange))
in (let pos_r = (fun r q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr (p::ps) -> begin
(let _67_508 = (aux loc env p)
in (match (_67_508) with
| (loc, env, var, p, _67_507) -> begin
(let _67_525 = (FStar_List.fold_left (fun _67_512 p -> (match (_67_512) with
| (loc, env, ps) -> begin
(let _67_521 = (aux loc env p)
in (match (_67_521) with
| (loc, env, _67_517, p, _67_520) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_67_525) with
| (loc, env, ps) -> begin
(let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (loc, env, var, pat, false))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(let _67_536 = (aux loc env p)
in (match (_67_536) with
| (loc, env', binder, p, imp) -> begin
(let binder = (match (binder) with
| LetBinder (_67_538) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(let t = (let _169_236 = (close_fun env t)
in (desugar_term env _169_236))
in LocalBinder (((let _67_545 = x
in {FStar_Syntax_Syntax.ppname = _67_545.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_545.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), aq)))
end)
in (loc, env', binder, p, imp))
end))
end
| FStar_Parser_AST.PatWild -> begin
(let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _169_237 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in (loc, env, LocalBinder ((x, None)), _169_237, false)))
end
| FStar_Parser_AST.PatConst (c) -> begin
(let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _169_238 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in (loc, env, LocalBinder ((x, None)), _169_238, false)))
end
| (FStar_Parser_AST.PatTvar (x, imp)) | (FStar_Parser_AST.PatVar (x, imp)) -> begin
(let aq = if imp then begin
Some (FStar_Syntax_Syntax.Implicit)
end else begin
None
end
in (let _67_563 = (resolvex loc env x)
in (match (_67_563) with
| (loc, env, xbv) -> begin
(let _169_239 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in (loc, env, LocalBinder ((xbv, aq)), _169_239, imp))
end)))
end
| FStar_Parser_AST.PatName (l) -> begin
(let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _169_240 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, []))))
in (loc, env, LocalBinder ((x, None)), _169_240, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _67_569}, args) -> begin
(let _67_591 = (FStar_List.fold_right (fun arg _67_580 -> (match (_67_580) with
| (loc, env, args) -> begin
(let _67_587 = (aux loc env arg)
in (match (_67_587) with
| (loc, env, _67_584, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_67_591) with
| (loc, env, args) -> begin
(let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _169_243 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _169_243, false))))
end))
end
| FStar_Parser_AST.PatApp (_67_595) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _67_615 = (FStar_List.fold_right (fun pat _67_603 -> (match (_67_603) with
| (loc, env, pats) -> begin
(let _67_611 = (aux loc env pat)
in (match (_67_611) with
| (loc, env, _67_607, pat, _67_610) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_67_615) with
| (loc, env, pats) -> begin
(let pat = (let _169_256 = (let _169_255 = (let _169_251 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _169_251))
in (let _169_254 = (let _169_253 = (let _169_252 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_169_252, []))
in FStar_Syntax_Syntax.Pat_cons (_169_253))
in (FStar_All.pipe_left _169_255 _169_254)))
in (FStar_List.fold_right (fun hd tl -> (let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _169_250 = (let _169_249 = (let _169_248 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_169_248, ((hd, false))::((tl, false))::[]))
in FStar_Syntax_Syntax.Pat_cons (_169_249))
in (FStar_All.pipe_left (pos_r r) _169_250)))) pats _169_256))
in (let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (loc, env, LocalBinder ((x, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(let _67_641 = (FStar_List.fold_left (fun _67_628 p -> (match (_67_628) with
| (loc, env, pats) -> begin
(let _67_637 = (aux loc env p)
in (match (_67_637) with
| (loc, env, _67_633, pat, _67_636) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_67_641) with
| (loc, env, args) -> begin
(let args = (FStar_List.rev args)
in (let l = if dep then begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end else begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
in (let constr = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| _67_648 -> begin
(FStar_All.failwith "impossible")
end)
in (let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _169_259 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _169_259, false)))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(let _67_658 = (FStar_List.hd fields)
in (match (_67_658) with
| (f, _67_657) -> begin
(let _67_662 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_67_662) with
| (record, _67_661) -> begin
(let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _67_665 -> (match (_67_665) with
| (f, p) -> begin
(let _169_261 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.qualify_field_to_record env record) f)
in (_169_261, p))
end))))
in (let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _67_670 -> (match (_67_670) with
| (f, _67_669) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _67_674 -> (match (_67_674) with
| (g, _67_673) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_67_677, p) -> begin
p
end)
end))))
in (let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (let _67_689 = (aux loc env app)
in (match (_67_689) with
| (env, e, b, p, _67_688) -> begin
(let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons ((fv, _67_692), args) -> begin
(let _169_270 = (let _169_269 = (let _169_268 = (let _169_267 = (let _169_266 = (let _169_265 = (let _169_264 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _169_264))
in FStar_Syntax_Syntax.Record_ctor (_169_265))
in Some (_169_266))
in (fv, _169_267))
in (_169_268, args))
in FStar_Syntax_Syntax.Pat_cons (_169_269))
in (FStar_All.pipe_left pos _169_270))
end
| _67_698 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (let _67_707 = (aux [] env p)
in (match (_67_707) with
| (_67_701, env, b, p, _67_706) -> begin
(let _67_708 = (let _169_271 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _169_271))
in (env, b, p))
end)))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _67_715) -> begin
(let _169_277 = (let _169_276 = (let _169_275 = (FStar_Parser_Env.qualify env x)
in (_169_275, FStar_Syntax_Syntax.tun))
in LetBinder (_169_276))
in (env, _169_277, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _67_722); FStar_Parser_AST.prange = _67_719}, t) -> begin
(let _169_281 = (let _169_280 = (let _169_279 = (FStar_Parser_Env.qualify env x)
in (let _169_278 = (desugar_term env t)
in (_169_279, _169_278)))
in LetBinder (_169_280))
in (env, _169_281, None))
end
| _67_730 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(let _67_734 = (desugar_data_pat env p)
in (match (_67_734) with
| (env, binder, p) -> begin
(let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _67_742 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _67_746 env pat -> (let _67_754 = (desugar_data_pat env pat)
in (match (_67_754) with
| (env, _67_752, pat) -> begin
(env, pat)
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (let env = (let _67_759 = env
in {FStar_Parser_Env.curmodule = _67_759.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _67_759.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _67_759.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _67_759.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _67_759.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _67_759.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _67_759.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _67_759.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _67_759.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _67_759.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (let env = (let _67_764 = env
in {FStar_Parser_Env.curmodule = _67_764.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _67_764.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _67_764.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _67_764.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _67_764.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _67_764.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _67_764.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _67_764.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _67_764.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _67_764.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (let setpos = (fun e -> (let _67_774 = e
in {FStar_Syntax_Syntax.n = _67_774.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _67_774.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _67_774.FStar_Syntax_Syntax.vars}))
in (match ((let _169_300 = (unparen top)
in _169_300.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_67_778) -> begin
(desugar_formula env top)
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(desugar_formula env t)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(desugar_formula env t)
end
| FStar_Parser_AST.Const (c) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (c)))
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("~", ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("==", args))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[]))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("*", _67_798::_67_796::[]) when env.FStar_Parser_Env.expect_typ -> begin
(let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(let rest = (flatten t2)
in (t1)::rest)
end
| _67_812 -> begin
(t)::[]
end))
in (let targs = (let _169_306 = (let _169_303 = (unparen top)
in (flatten _169_303))
in (FStar_All.pipe_right _169_306 (FStar_List.map (fun t -> (let _169_305 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _169_305))))))
in (let tup = (let _169_307 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _169_307))
in (mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _169_308 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (FStar_All.pipe_left setpos _169_308))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_lid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Unexpected operator: " s), top.FStar_Parser_AST.range))))
end
| Some (l) -> begin
(let op = (FStar_Syntax_Syntax.fvar None l (FStar_Ident.range_of_lid l))
in (let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _169_310 = (desugar_term env t)
in (_169_310, None)))))
in (mk (FStar_Syntax_Syntax.Tm_app ((op, args))))))
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _67_834; FStar_Ident.ident = _67_832; FStar_Ident.nsstr = _67_830; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _67_843; FStar_Ident.ident = _67_841; FStar_Ident.nsstr = _67_839; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _67_852; FStar_Ident.ident = _67_850; FStar_Ident.nsstr = _67_848; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let _169_311 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _169_311))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(let _67_867 = (match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| None -> begin
(let _169_312 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (_169_312, false))
end
| Some (head) -> begin
(let _169_313 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in (_169_313, true))
end)
in (match (_67_867) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _67_870 -> begin
(let args = (FStar_List.map (fun _67_873 -> (match (_67_873) with
| (t, imp) -> begin
(let te = (desugar_term env t)
in (arg_withimp_e imp te))
end)) args)
in (let app = (mk (FStar_Syntax_Syntax.Tm_app ((head, args))))
in if is_data then begin
(mk (FStar_Syntax_Syntax.Tm_meta ((app, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))
end else begin
app
end))
end)
end))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(let _67_901 = (FStar_List.fold_left (fun _67_884 b -> (match (_67_884) with
| (env, tparams, typs) -> begin
(let _67_888 = (desugar_binder env b)
in (match (_67_888) with
| (xopt, t) -> begin
(let _67_894 = (match (xopt) with
| None -> begin
(let _169_317 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (env, _169_317))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_67_894) with
| (env, x) -> begin
(let _169_321 = (let _169_320 = (let _169_319 = (let _169_318 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _169_318))
in (_169_319)::[])
in (FStar_List.append typs _169_320))
in (env, (FStar_List.append tparams ((((let _67_895 = x
in {FStar_Syntax_Syntax.ppname = _67_895.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_895.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), None))::[])), _169_321))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_67_901) with
| (env, _67_899, targs) -> begin
(let tup = (let _169_322 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _169_322))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(let _67_909 = (uncurry binders t)
in (match (_67_909) with
| (bs, t) -> begin
(let rec aux = (fun env bs _67_8 -> (match (_67_8) with
| [] -> begin
(let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _169_329 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _169_329)))
end
| hd::tl -> begin
(let mlenv = (FStar_Parser_Env.default_ml env)
in (let bb = (desugar_binder mlenv hd)
in (let _67_923 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_67_923) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _67_930) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(let _67_938 = (as_binder env None b)
in (match (_67_938) with
| ((x, _67_935), env) -> begin
(let f = (desugar_formula env f)
in (let _169_330 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _169_330)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(let _67_958 = (FStar_List.fold_left (fun _67_946 pat -> (match (_67_946) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_67_949, t) -> begin
(let _169_334 = (let _169_333 = (free_type_vars env t)
in (FStar_List.append _169_333 ftvs))
in (env, _169_334))
end
| _67_954 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_67_958) with
| (_67_956, ftv) -> begin
(let ftv = (sort_ftv ftv)
in (let binders = (let _169_336 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, true))) top.FStar_Parser_AST.range))))
in (FStar_List.append _169_336 binders))
in (let rec aux = (fun env bs sc_pat_opt _67_9 -> (match (_67_9) with
| [] -> begin
(let body = (desugar_term env body)
in (let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(let body = (let _169_346 = (let _169_345 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _169_345 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _169_346 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((sc, ((pat, None, body))::[]))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _169_347 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _169_347))))
end
| p::rest -> begin
(let _67_982 = (desugar_binding_pat env p)
in (match (_67_982) with
| (env, b, pat) -> begin
(let _67_1033 = (match (b) with
| LetBinder (_67_984) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _67_992) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _169_349 = (let _169_348 = (FStar_Syntax_Syntax.bv_to_name x)
in (_169_348, p))
in Some (_169_349))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Syntax_Syntax.n, p'.FStar_Syntax_Syntax.v)) with
| (FStar_Syntax_Syntax.Tm_name (_67_1006), _67_1009) -> begin
(let tup2 = (let _169_350 = (FStar_Syntax_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _169_350 (Some (FStar_Syntax_Syntax.Data_ctor))))
in (let sc = (let _169_358 = (let _169_357 = (let _169_356 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _169_355 = (let _169_354 = (FStar_Syntax_Syntax.as_arg sc)
in (let _169_353 = (let _169_352 = (let _169_351 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _169_351))
in (_169_352)::[])
in (_169_354)::_169_353))
in (_169_356, _169_355)))
in FStar_Syntax_Syntax.Tm_app (_169_357))
in (FStar_Syntax_Syntax.mk _169_358 None top.FStar_Parser_AST.range))
in (let p = (let _169_359 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tup2, ((p', false))::((p, false))::[]))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _169_359))
in Some ((sc, p)))))
end
| (FStar_Syntax_Syntax.Tm_app (_67_1015, args), FStar_Syntax_Syntax.Pat_cons (_67_1020, pats)) -> begin
(let tupn = (let _169_360 = (FStar_Syntax_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _169_360 (Some (FStar_Syntax_Syntax.Data_ctor))))
in (let sc = (let _169_367 = (let _169_366 = (let _169_365 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _169_364 = (let _169_363 = (let _169_362 = (let _169_361 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _169_361))
in (_169_362)::[])
in (FStar_List.append args _169_363))
in (_169_365, _169_364)))
in FStar_Syntax_Syntax.Tm_app (_169_366))
in (mk _169_367))
in (let p = (let _169_368 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tupn, (FStar_List.append pats (((p, false))::[]))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _169_368))
in Some ((sc, p)))))
end
| _67_1029 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((x, aq), sc_pat_opt))
end)
in (match (_67_1033) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _67_1037; FStar_Parser_AST.level = _67_1035}, phi, _67_1043) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(let phi = (desugar_formula env phi)
in (let _169_376 = (let _169_375 = (let _169_374 = (FStar_Syntax_Syntax.fvar None a (FStar_Ident.range_of_lid a))
in (let _169_373 = (let _169_372 = (FStar_Syntax_Syntax.as_arg phi)
in (let _169_371 = (let _169_370 = (let _169_369 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _169_369))
in (_169_370)::[])
in (_169_372)::_169_371))
in (_169_374, _169_373)))
in FStar_Syntax_Syntax.Tm_app (_169_375))
in (mk _169_376)))
end
| FStar_Parser_AST.App (_67_1048) -> begin
(let rec aux = (fun args e -> (match ((let _169_381 = (unparen e)
in _169_381.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(let arg = (let _169_382 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _169_382))
in (aux ((arg)::args) e))
end
| _67_1060 -> begin
(let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _169_385 = (let _169_384 = (let _169_383 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_169_383, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))
in FStar_Syntax_Syntax.Tm_meta (_169_384))
in (mk _169_385))
end
| FStar_Parser_AST.Let (is_rec, (pat, _snd)::_tl, body) -> begin
(let ds_let_rec = (fun _67_1076 -> (match (()) with
| () -> begin
(let bindings = ((pat, _snd))::_tl
in (let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _67_1080 -> (match (_67_1080) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _169_389 = (destruct_app_pattern env top_level p)
in (_169_389, def))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _169_390 = (destruct_app_pattern env top_level p)
in (_169_390, def))
end
| _67_1086 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _67_1091); FStar_Parser_AST.prange = _67_1088}, t) -> begin
if top_level then begin
(let _169_393 = (let _169_392 = (let _169_391 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_169_391))
in (_169_392, [], Some (t)))
in (_169_393, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _67_1100) -> begin
if top_level then begin
(let _169_396 = (let _169_395 = (let _169_394 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_169_394))
in (_169_395, [], None))
in (_169_396, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _67_1104 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (let _67_1133 = (FStar_List.fold_left (fun _67_1109 _67_1118 -> (match ((_67_1109, _67_1118)) with
| ((env, fnames, rec_bindings), ((f, _67_1112, _67_1114), _67_1117)) -> begin
(let _67_1129 = (match (f) with
| FStar_Util.Inl (x) -> begin
(let _67_1123 = (FStar_Parser_Env.push_bv env x)
in (match (_67_1123) with
| (env, xx) -> begin
(let _169_400 = (let _169_399 = (FStar_Syntax_Syntax.mk_binder xx)
in (_169_399)::rec_bindings)
in (env, FStar_Util.Inl (xx), _169_400))
end))
end
| FStar_Util.Inr (l) -> begin
(let _169_401 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident)
in (_169_401, FStar_Util.Inr (l), rec_bindings))
end)
in (match (_67_1129) with
| (env, lbname, rec_bindings) -> begin
(env, (lbname)::fnames, rec_bindings)
end))
end)) (env, [], []) funs)
in (match (_67_1133) with
| (env', fnames, rec_bindings) -> begin
(let fnames = (FStar_List.rev fnames)
in (let desugar_one_def = (fun env lbname _67_1144 -> (match (_67_1144) with
| ((_67_1139, args, result_t), def) -> begin
(let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _169_408 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _169_408 FStar_Parser_AST.Expr))
end)
in (let def = (match (args) with
| [] -> begin
def
end
| _67_1151 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args def) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (let body = (desugar_term env def)
in (let body = if is_rec then begin
(FStar_Syntax_Subst.close rec_bindings body)
end else begin
body
end
in (mk_lb (lbname, FStar_Syntax_Syntax.tun, body))))))
end))
in (let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (let body = (desugar_term env' body)
in (let _169_411 = (let _169_410 = (let _169_409 = (FStar_Syntax_Subst.close rec_bindings body)
in ((is_rec, lbs), _169_409))
in FStar_Syntax_Syntax.Tm_let (_169_410))
in (FStar_All.pipe_left mk _169_411))))))
end))))
end))
in (let ds_non_rec = (fun pat t1 t2 -> (let t1 = (desugar_term env t1)
in (let _67_1165 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_67_1165) with
| (env, binder, pat) -> begin
(match (binder) with
| LetBinder (l, t) -> begin
(let body = (desugar_term env t2)
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (l); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]), body)))))
end
| LocalBinder (x, _67_1173) -> begin
(let body = (desugar_term env t2)
in (let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _169_422 = (let _169_421 = (let _169_420 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _169_419 = (let _169_418 = (FStar_Syntax_Util.branch (pat, None, body))
in (_169_418)::[])
in (_169_420, _169_419)))
in FStar_Syntax_Syntax.Tm_match (_169_421))
in (FStar_Syntax_Syntax.mk _169_422 None body.FStar_Syntax_Syntax.pos))
end)
in (let _169_427 = (let _169_426 = (let _169_425 = (let _169_424 = (let _169_423 = (FStar_Syntax_Syntax.mk_binder x)
in (_169_423)::[])
in (FStar_Syntax_Subst.close _169_424 body))
in ((false, ((mk_lb (FStar_Util.Inl (x), x.FStar_Syntax_Syntax.sort, t1)))::[]), _169_425))
in FStar_Syntax_Syntax.Tm_let (_169_426))
in (FStar_All.pipe_left mk _169_427))))
end)
end))))
in if (is_rec || (is_app_pattern pat)) then begin
(ds_let_rec ())
end else begin
(ds_non_rec pat _snd body)
end))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(let _169_438 = (let _169_437 = (let _169_436 = (desugar_term env t1)
in (let _169_435 = (let _169_434 = (let _169_429 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _169_428 = (desugar_term env t2)
in (_169_429, None, _169_428)))
in (let _169_433 = (let _169_432 = (let _169_431 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _169_430 = (desugar_term env t3)
in (_169_431, None, _169_430)))
in (_169_432)::[])
in (_169_434)::_169_433))
in (_169_436, _169_435)))
in FStar_Syntax_Syntax.Tm_match (_169_437))
in (mk _169_438))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(let r = top.FStar_Parser_AST.range
in (let handler = (FStar_Parser_AST.mk_function branches r r)
in (let body = (FStar_Parser_AST.mk_function ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r), None, e))::[]) r r)
in (let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Syntax_Const.try_with_lid)) r top.FStar_Parser_AST.level), body, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((a1, handler, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (desugar_term env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(let desugar_branch = (fun _67_1212 -> (match (_67_1212) with
| (pat, wopt, b) -> begin
(let _67_1215 = (desugar_match_pat env pat)
in (match (_67_1215) with
| (env, pat) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _169_441 = (desugar_term env e)
in Some (_169_441))
end)
in (let b = (desugar_term env b)
in (FStar_Syntax_Util.branch (pat, wopt, b))))
end))
end))
in (let _169_445 = (let _169_444 = (let _169_443 = (desugar_term env e)
in (let _169_442 = (FStar_List.map desugar_branch branches)
in (_169_443, _169_442)))
in FStar_Syntax_Syntax.Tm_match (_169_444))
in (FStar_All.pipe_left mk _169_445)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _169_449 = (let _169_448 = (let _169_447 = (desugar_term env e)
in (let _169_446 = (desugar_typ env t)
in (_169_447, _169_446, None)))
in FStar_Syntax_Syntax.Tm_ascribed (_169_448))
in (FStar_All.pipe_left mk _169_449))
end
| FStar_Parser_AST.Record (_67_1226, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(let _67_1237 = (FStar_List.hd fields)
in (match (_67_1237) with
| (f, _67_1236) -> begin
(let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (let _67_1243 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_67_1243) with
| (record, _67_1242) -> begin
(let get_field = (fun xopt f -> (let fn = f.FStar_Ident.ident
in (let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _67_1251 -> (match (_67_1251) with
| (g, _67_1250) -> begin
(let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_67_1255, e) -> begin
(let _169_457 = (qfn fn)
in (_169_457, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _169_460 = (let _169_459 = (let _169_458 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in (_169_458, top.FStar_Parser_AST.range))
in FStar_Syntax_Syntax.Error (_169_459))
in (Prims.raise _169_460))
end
| Some (x) -> begin
(let _169_461 = (qfn fn)
in (_169_461, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (let recterm = (match (eopt) with
| None -> begin
(let _169_466 = (let _169_465 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _67_1267 -> (match (_67_1267) with
| (f, _67_1266) -> begin
(let _169_464 = (let _169_463 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _169_463))
in (_169_464, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_Env.constrname, _169_465))
in FStar_Parser_AST.Construct (_169_466))
end
| Some (e) -> begin
(let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (let xterm = (let _169_468 = (let _169_467 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_169_467))
in (FStar_Parser_AST.mk_term _169_468 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (let record = (let _169_471 = (let _169_470 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _67_1275 -> (match (_67_1275) with
| (f, _67_1274) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _169_470))
in FStar_Parser_AST.Record (_169_471))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, false))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _67_1294); FStar_Syntax_Syntax.tk = _67_1291; FStar_Syntax_Syntax.pos = _67_1289; FStar_Syntax_Syntax.vars = _67_1287}, args); FStar_Syntax_Syntax.tk = _67_1285; FStar_Syntax_Syntax.pos = _67_1283; FStar_Syntax_Syntax.vars = _67_1281}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(let e = (let _169_478 = (let _169_477 = (let _169_476 = (let _169_475 = (let _169_474 = (let _169_473 = (let _169_472 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _169_472))
in FStar_Syntax_Syntax.Record_ctor (_169_473))
in Some (_169_474))
in (FStar_Syntax_Syntax.fvar _169_475 fv.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos))
in (_169_476, args))
in FStar_Syntax_Syntax.Tm_app (_169_477))
in (FStar_All.pipe_left mk _169_478))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| _67_1308 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(let _67_1315 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_67_1315) with
| (fieldname, is_rec) -> begin
(let e = (desugar_term env e)
in (let fn = (let _67_1320 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_67_1320) with
| (ns, _67_1319) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (fn))
end else begin
None
end
in (let _169_483 = (let _169_482 = (let _169_481 = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Record_projector (fn))) fieldname (FStar_Ident.range_of_lid f))
in (let _169_480 = (let _169_479 = (FStar_Syntax_Syntax.as_arg e)
in (_169_479)::[])
in (_169_481, _169_480)))
in FStar_Syntax_Syntax.Tm_app (_169_482))
in (FStar_All.pipe_left mk _169_483)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _67_1330 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _67_1332 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _67_1337 -> (match (_67_1337) with
| (a, imp) -> begin
(let _169_487 = (desugar_term env a)
in (arg_withimp_e imp _169_487))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error ((msg, r)))))
in (let is_requires = (fun _67_1349 -> (match (_67_1349) with
| (t, _67_1348) -> begin
(match ((let _169_495 = (unparen t)
in _169_495.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_67_1351) -> begin
true
end
| _67_1354 -> begin
false
end)
end))
in (let is_ensures = (fun _67_1359 -> (match (_67_1359) with
| (t, _67_1358) -> begin
(match ((let _169_498 = (unparen t)
in _169_498.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_67_1361) -> begin
true
end
| _67_1364 -> begin
false
end)
end))
in (let is_app = (fun head _67_1370 -> (match (_67_1370) with
| (t, _67_1369) -> begin
(match ((let _169_503 = (unparen t)
in _169_503.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _67_1374; FStar_Parser_AST.level = _67_1372}, _67_1379, _67_1381) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _67_1385 -> begin
false
end)
end))
in (let pre_process_comp_typ = (fun t -> (let _67_1390 = (head_and_args t)
in (match (_67_1390) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(let unit_tm = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (let nil_pat = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr), FStar_Parser_AST.Nothing)
in (let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to \'Lemma\'", t.FStar_Parser_AST.range))))
end
| ens::[] -> begin
(let req_true = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Requires (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.true_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Formula), None))) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (unit_tm)::(req_true)::(ens)::(nil_pat)::[])
end
| req::ens::[] when ((is_requires req) && (is_ensures ens)) -> begin
(unit_tm)::(req)::(ens)::(nil_pat)::[]
end
| req::ens::dec::[] when (((is_requires req) && (is_ensures ens)) && (is_app "decreases" dec)) -> begin
(unit_tm)::(req)::(ens)::(nil_pat)::(dec)::[]
end
| more -> begin
(unit_tm)::more
end)
in (let head = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_name env) lemma)
in (head, args)))))
end
| FStar_Parser_AST.Name (l) when (FStar_Parser_Env.is_effect_name env l) -> begin
(let _169_506 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_name env) l)
in (_169_506, args))
end
| FStar_Parser_AST.Name (l) when ((let _169_507 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _169_507 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(let _169_508 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_169_508, args))
end
| FStar_Parser_AST.Name (l) when ((let _169_509 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _169_509 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(let _169_510 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)
in (_169_510, args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(let _169_511 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_169_511, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _67_1418 when default_ok -> begin
(let _169_512 = (FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)
in (_169_512, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _67_1420 -> begin
(let _169_514 = (let _169_513 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _169_513))
in (fail _169_514))
end)
end)))
in (let _67_1423 = (pre_process_comp_typ t)
in (match (_67_1423) with
| (eff, args) -> begin
(let _67_1424 = if ((FStar_List.length args) = 0) then begin
(let _169_516 = (let _169_515 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _169_515))
in (fail _169_516))
end else begin
()
end
in (let _67_1428 = (let _169_518 = (FStar_List.hd args)
in (let _169_517 = (FStar_List.tl args)
in (_169_518, _169_517)))
in (match (_67_1428) with
| (result_arg, rest) -> begin
(let result_typ = (desugar_typ env (Prims.fst result_arg))
in (let rest = (desugar_args env rest)
in (let _67_1456 = (FStar_All.pipe_right rest (FStar_List.partition (fun _67_1434 -> (match (_67_1434) with
| (t, _67_1433) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _67_1443); FStar_Syntax_Syntax.tk = _67_1440; FStar_Syntax_Syntax.pos = _67_1438; FStar_Syntax_Syntax.vars = _67_1436}, _67_1448::[]) -> begin
(FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.decreases_lid)
end
| _67_1453 -> begin
false
end)
end))))
in (match (_67_1456) with
| (dec, rest) -> begin
(let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _67_1460 -> (match (_67_1460) with
| (t, _67_1459) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_67_1462, (arg, _67_1465)::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _67_1471 -> begin
(FStar_All.failwith "impos")
end)
end))))
in if ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) && ((FStar_List.length decreases_clause) = 0)) then begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end else begin
if ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid) && ((FStar_List.length decreases_clause) = 0)) then begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end else begin
(let flags = if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid) then begin
(FStar_Syntax_Syntax.LEMMA)::[]
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) then begin
(FStar_Syntax_Syntax.TOTAL)::[]
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_ML_lid) then begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid) then begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end else begin
[]
end
end
end
end
in (let rest = if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid) then begin
(match (rest) with
| req::ens::(pat, aq)::[] -> begin
(let pat = (match (pat.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _67_1482) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.nil_lid) -> begin
(let nil = (FStar_Syntax_Syntax.mk_Tm_uinst pat ((FStar_Syntax_Syntax.U_succ (FStar_Syntax_Syntax.U_zero))::[]))
in (let pattern = (let _169_521 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _169_521 ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil (((pattern, Some (FStar_Syntax_Syntax.Implicit)))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _67_1488 -> begin
pat
end)
in (let _169_525 = (let _169_524 = (let _169_523 = (let _169_522 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((pat, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))) None pat.FStar_Syntax_Syntax.pos)
in (_169_522, aq))
in (_169_523)::[])
in (ens)::_169_524)
in (req)::_169_525))
end
| _67_1491 -> begin
rest
end)
end else begin
rest
end
in (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.effect_name = eff; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = rest; FStar_Syntax_Syntax.flags = (FStar_List.append flags decreases_clause)})))
end
end)
end))))
end)))
end))))))))
and desugar_formula : env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env f -> (let connective = (fun s -> (match (s) with
| "/\\" -> begin
Some (FStar_Syntax_Const.and_lid)
end
| "\\/" -> begin
Some (FStar_Syntax_Const.or_lid)
end
| "==>" -> begin
Some (FStar_Syntax_Const.imp_lid)
end
| "<==>" -> begin
Some (FStar_Syntax_Const.iff_lid)
end
| "~" -> begin
Some (FStar_Syntax_Const.not_lid)
end
| _67_1503 -> begin
None
end))
in (let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (let setpos = (fun t -> (let _67_1510 = t
in {FStar_Syntax_Syntax.n = _67_1510.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _67_1510.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _67_1510.FStar_Syntax_Syntax.vars}))
in (let desugar_quant = (fun q b pats body -> (let tk = (desugar_binder env (let _67_1517 = b
in {FStar_Parser_AST.b = _67_1517.FStar_Parser_AST.b; FStar_Parser_AST.brange = _67_1517.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _67_1517.FStar_Parser_AST.aqual}))
in (let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _169_560 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _169_560)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(let _67_1531 = (FStar_Parser_Env.push_bv env a)
in (match (_67_1531) with
| (env, a) -> begin
(let a = (let _67_1532 = a
in {FStar_Syntax_Syntax.ppname = _67_1532.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_1532.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (let pats = (desugar_pats env pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _67_1539 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((body, FStar_Syntax_Syntax.Meta_pattern (pats)))))
end)
in (let body = (let _169_563 = (let _169_562 = (let _169_561 = (FStar_Syntax_Syntax.mk_binder a)
in (_169_561)::[])
in (no_annot_abs _169_562 body))
in (FStar_All.pipe_left setpos _169_563))
in (let _169_569 = (let _169_568 = (let _169_567 = (let _169_564 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar None _169_564 b.FStar_Parser_AST.brange))
in (let _169_566 = (let _169_565 = (FStar_Syntax_Syntax.as_arg body)
in (_169_565)::[])
in (_169_567, _169_566)))
in FStar_Syntax_Syntax.Tm_app (_169_568))
in (FStar_All.pipe_left mk _169_569)))))))
end))
end
| _67_1543 -> begin
(FStar_All.failwith "impossible")
end))))
in (let push_quant = (fun q binders pats body -> (match (binders) with
| b::b'::_rest -> begin
(let rest = (b')::_rest
in (let body = (let _169_584 = (q (rest, pats, body))
in (let _169_583 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _169_584 _169_583 FStar_Parser_AST.Formula)))
in (let _169_585 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _169_585 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _67_1557 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _169_586 = (unparen f)
in _169_586.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(let f = (desugar_formula env f)
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((l, f.FStar_Syntax_Syntax.pos, p)))))))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall (_1::_2::_3, pats, body) -> begin
(let binders = (_1)::(_2)::_3
in (let _169_588 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _169_588)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(let binders = (_1)::(_2)::_3
in (let _169_590 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _169_590)))
end
| FStar_Parser_AST.QForall (b::[], pats, body) -> begin
(desugar_quant FStar_Syntax_Const.forall_lid b pats body)
end
| FStar_Parser_AST.QExists (b::[], pats, body) -> begin
(desugar_quant FStar_Syntax_Const.exists_lid b pats body)
end
| FStar_Parser_AST.Paren (f) -> begin
(desugar_formula env f)
end
| _67_1615 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (let _67_1639 = (FStar_List.fold_left (fun _67_1620 b -> (match (_67_1620) with
| (env, out) -> begin
(let tk = (desugar_binder env (let _67_1622 = b
in {FStar_Parser_AST.b = _67_1622.FStar_Parser_AST.b; FStar_Parser_AST.brange = _67_1622.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _67_1622.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(let _67_1631 = (FStar_Parser_Env.push_bv env a)
in (match (_67_1631) with
| (env, a) -> begin
(let a = (let _67_1632 = a
in {FStar_Syntax_Syntax.ppname = _67_1632.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_1632.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (env, ((a, (trans_aqual b.FStar_Parser_AST.aqual)))::out))
end))
end
| _67_1636 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_67_1639) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _169_597 = (desugar_typ env t)
in (Some (x), _169_597))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _169_598 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in (Some (x), _169_598))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _169_599 = (desugar_typ env t)
in (None, _169_599))
end
| FStar_Parser_AST.Variable (x) -> begin
(Some (x), FStar_Syntax_Syntax.tun)
end))

let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  FStar_Ident.lid  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_Env.iface) || env.FStar_Parser_Env.admitted_iface) then begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (let binders = (let _169_615 = (let _169_614 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _169_614))
in (FStar_List.append tps _169_615))
in (let p = (FStar_Ident.range_of_lid t)
in (let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _67_1667 -> (match (_67_1667) with
| (x, _67_1666) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit))
end))))
in (let binders = (let _169_622 = (let _169_621 = (let _169_620 = (let _169_619 = (let _169_617 = (FStar_Syntax_Syntax.lid_as_fv t None)
in (FStar_Syntax_Syntax.fv_to_tm _169_617))
in (let _169_618 = (FStar_Syntax_Util.args_of_non_null_binders binders)
in (FStar_Syntax_Syntax.mk_Tm_app _169_619 _169_618 None p)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _169_620))
in (_169_621)::[])
in (FStar_List.append imp_binders _169_622))
in (let disc_type = (let _169_625 = (let _169_624 = (let _169_623 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid None)
in (FStar_Syntax_Syntax.fv_to_tm _169_623))
in (FStar_Syntax_Syntax.mk_Total _169_624))
in (FStar_Syntax_Util.arrow binders _169_625))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _169_628 = (let _169_627 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in (disc_name, [], disc_type, _169_627, (FStar_Ident.range_of_lid disc_name)))
in FStar_Syntax_Syntax.Sig_declare_typ (_169_628)))))))))))))

let mk_indexed_projectors : FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun fvq refine_domain env tc lid inductive_tps imp_tps fields t -> (let p = (FStar_Ident.range_of_lid lid)
in (let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (Some (p)) ptyp))
in (let tps = (FStar_List.map2 (fun _67_1690 _67_1694 -> (match ((_67_1690, _67_1694)) with
| ((_67_1688, imp), (x, _67_1693)) -> begin
(x, imp)
end)) inductive_tps imp_tps)
in (let _67_1787 = (let _67_1698 = (FStar_Syntax_Util.head_and_args t)
in (match (_67_1698) with
| (head, args0) -> begin
(let args = (let rec arguments = (fun tps args -> (match ((tps, args)) with
| ([], _67_1704) -> begin
args
end
| (_67_1707, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to type", (FStar_Ident.range_of_lid lid)))))
end
| ((_67_1712, Some (FStar_Syntax_Syntax.Implicit))::tps', (_67_1719, Some (FStar_Syntax_Syntax.Implicit))::args') -> begin
(arguments tps' args')
end
| ((_67_1727, Some (FStar_Syntax_Syntax.Implicit))::tps', (_67_1735, _67_1737)::_67_1733) -> begin
(arguments tps' args)
end
| ((_67_1744, _67_1746)::_67_1742, (a, Some (FStar_Syntax_Syntax.Implicit))::_67_1750) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected implicit annotation on argument", a.FStar_Syntax_Syntax.pos))))
end
| ((_67_1759, _67_1761)::tps', (_67_1766, _67_1768)::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (let indices = (FStar_All.pipe_right args (FStar_List.map (fun _67_1773 -> (let _169_658 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _169_658 FStar_Syntax_Syntax.mk_binder)))))
in (let arg_typ = (let _169_663 = (let _169_659 = (FStar_Syntax_Syntax.lid_as_fv tc None)
in (FStar_Syntax_Syntax.fv_to_tm _169_659))
in (let _169_662 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _67_1778 -> (match (_67_1778) with
| (x, imp) -> begin
(let _169_661 = (FStar_Syntax_Syntax.bv_to_name x)
in (_169_661, imp))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _169_663 _169_662 None p)))
in (let arg_binder = if (not (refine_domain)) then begin
(let _169_664 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _169_664))
end else begin
(let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _169_672 = (let _67_1782 = (projectee arg_typ)
in (let _169_671 = (let _169_670 = (let _169_669 = (let _169_668 = (FStar_Syntax_Syntax.fvar None disc_name p)
in (let _169_667 = (let _169_666 = (let _169_665 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _169_665))
in (_169_666)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _169_668 _169_667 None p)))
in (FStar_Syntax_Util.b2t _169_669))
in (FStar_Syntax_Util.refine x _169_670))
in {FStar_Syntax_Syntax.ppname = _67_1782.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_1782.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _169_671}))
in (FStar_Syntax_Syntax.mk_binder _169_672))))
end
in (arg_binder, indices)))))
end))
in (match (_67_1787) with
| (arg_binder, indices) -> begin
(let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (let imp_binders = (let _169_674 = (FStar_All.pipe_right indices (FStar_List.map (fun _67_1792 -> (match (_67_1792) with
| (x, _67_1791) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit))
end))))
in (FStar_List.append imp_tps _169_674))
in (let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _67_1800 -> (match (_67_1800) with
| (a, _67_1799) -> begin
(let _67_1804 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_67_1804) with
| (field_name, _67_1803) -> begin
(let proj = (let _169_678 = (let _169_677 = (FStar_Syntax_Syntax.lid_as_fv field_name None)
in (FStar_Syntax_Syntax.fv_to_tm _169_677))
in (FStar_Syntax_Syntax.mk_Tm_app _169_678 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT ((a, proj)))
end))
end))))
in (let ntps = (FStar_List.length tps)
in (let all_params = (FStar_List.append imp_tps fields)
in (let _169_712 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _67_1813 -> (match (_67_1813) with
| (x, _67_1812) -> begin
(let _67_1817 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_67_1817) with
| (field_name, _67_1816) -> begin
(let t = (let _169_682 = (let _169_681 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _169_681))
in (FStar_Syntax_Util.arrow binders _169_682))
in (let only_decl = (((let _169_683 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _169_683)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _169_685 = (let _169_684 = (FStar_Parser_Env.current_module env)
in _169_684.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _169_685)))
in (let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (let quals = (fun q -> if only_decl then begin
(FStar_Syntax_Syntax.Assumption)::q
end else begin
q
end)
in (let quals = (quals ((FStar_Syntax_Syntax.Projector ((lid, x.FStar_Syntax_Syntax.ppname)))::[]))
in (let decl = FStar_Syntax_Syntax.Sig_declare_typ ((field_name, [], t, quals, (FStar_Ident.range_of_lid field_name)))
in if only_decl then begin
(decl)::[]
end else begin
(let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (let as_imp = (fun _67_10 -> (match (_67_10) with
| Some (FStar_Syntax_Syntax.Implicit) -> begin
true
end
| _67_1830 -> begin
false
end))
in (let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _67_1835 -> (match (_67_1835) with
| (x, imp) -> begin
if ((i + ntps) = j) then begin
(let _169_692 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in (_169_692, (as_imp imp)))
end else begin
(let b = (as_imp imp)
in if (b && (j < ntps)) then begin
(let _169_696 = (let _169_695 = (let _169_694 = (let _169_693 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (_169_693, FStar_Syntax_Syntax.tun))
in FStar_Syntax_Syntax.Pat_dot_term (_169_694))
in (pos _169_695))
in (_169_696, b))
end else begin
(let _169_699 = (let _169_698 = (let _169_697 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_169_697))
in (pos _169_698))
in (_169_699, b))
end)
end
end))))
in (let pat = (let _169_704 = (let _169_702 = (let _169_701 = (let _169_700 = (FStar_Syntax_Syntax.lid_as_fv lid (Some (fvq)))
in (_169_700, arg_pats))
in FStar_Syntax_Syntax.Pat_cons (_169_701))
in (FStar_All.pipe_right _169_702 pos))
in (let _169_703 = (FStar_Syntax_Syntax.bv_to_name projection)
in (_169_704, None, _169_703)))
in (let body = (let _169_708 = (let _169_707 = (let _169_706 = (let _169_705 = (FStar_Syntax_Util.branch pat)
in (_169_705)::[])
in (arg_exp, _169_706))
in FStar_Syntax_Syntax.Tm_match (_169_707))
in (FStar_Syntax_Syntax.mk _169_708 None p))
in (let imp = (no_annot_abs binders body)
in (let lb = {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (field_name); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp}
in (let impl = (let _169_711 = (let _169_710 = (let _169_709 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (_169_709)::[])
in ((false, (lb)::[]), p, _169_710, quals))
in FStar_Syntax_Syntax.Sig_let (_169_711))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end))))))))
end))))))
end))
end))))
in (FStar_All.pipe_right _169_712 FStar_List.flatten)))))))))
end)))))))

let mk_data_projectors : FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env _67_1846 -> (match (_67_1846) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _67_1849, t, l, n, quals, _67_1855, _67_1857) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _67_11 -> (match (_67_11) with
| FStar_Syntax_Syntax.RecordConstructor (_67_1862) -> begin
true
end
| _67_1865 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _67_1869 -> begin
true
end)
end
in (let _67_1873 = (FStar_Syntax_Util.arrow_formals t)
in (match (_67_1873) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _67_1876 -> begin
(let qual = (match ((FStar_Util.find_map quals (fun _67_12 -> (match (_67_12) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((lid, fns)))
end
| _67_1881 -> begin
None
end)))) with
| None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)
in (let _67_1888 = (FStar_Util.first_N n formals)
in (match (_67_1888) with
| (tps, rest) -> begin
(mk_indexed_projectors qual refine_domain env l lid inductive_tps tps rest cod)
end)))
end)
end)))
end
| _67_1890 -> begin
[]
end)
end))

let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (let lb = (let _169_737 = (let _169_735 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _169_735))
in (let _169_736 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (lid); FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _169_737; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _169_736}))
in FStar_Syntax_Syntax.Sig_let (((false, (lb)::[]), rng, lids, quals))))

let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (let tycon_id = (fun _67_13 -> (match (_67_13) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _169_751 = (let _169_750 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_169_750))
in (FStar_Parser_AST.mk_term _169_751 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((tot, t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (let apply_binders = (fun t binders -> (let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _67_1964 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _169_764 = (let _169_763 = (let _169_762 = (binder_to_term b)
in (out, _169_762, (imp_of_aqual b)))
in FStar_Parser_AST.App (_169_763))
in (FStar_Parser_AST.mk_term _169_764 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (let tycon_record_as_variant = (fun _67_14 -> (match (_67_14) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (let mfields = (FStar_List.map (fun _67_1977 -> (match (_67_1977) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Syntax_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (let result = (let _169_770 = (let _169_769 = (let _169_768 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_169_768))
in (FStar_Parser_AST.mk_term _169_769 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _169_770 parms))
in (let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _169_772 = (FStar_All.pipe_right fields (FStar_List.map (fun _67_1984 -> (match (_67_1984) with
| (x, _67_1983) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _169_772))))))
end
| _67_1986 -> begin
(FStar_All.failwith "impossible")
end))
in (let desugar_abstract_tc = (fun quals _env mutuals _67_15 -> (match (_67_15) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(let _67_2000 = (typars_of_binders _env binders)
in (match (_67_2000) with
| (_env', typars) -> begin
(let k = (match (kopt) with
| None -> begin
FStar_Syntax_Util.ktype
end
| Some (k) -> begin
(desugar_term _env' k)
end)
in (let tconstr = (let _169_783 = (let _169_782 = (let _169_781 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_169_781))
in (FStar_Parser_AST.mk_term _169_782 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _169_783 binders))
in (let qlid = (FStar_Parser_Env.qualify _env id)
in (let typars = (FStar_Syntax_Subst.close_binders typars)
in (let k = (FStar_Syntax_Subst.close typars k)
in (let se = FStar_Syntax_Syntax.Sig_inductive_typ ((qlid, [], typars, k, mutuals, [], quals, rng))
in (let _env = (FStar_Parser_Env.push_top_level_rec_binding _env id)
in (let _env2 = (FStar_Parser_Env.push_top_level_rec_binding _env' id)
in (_env, _env2, se, tconstr)))))))))
end))
end
| _67_2013 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (let push_tparams = (fun env bs -> (let _67_2028 = (FStar_List.fold_left (fun _67_2019 _67_2022 -> (match ((_67_2019, _67_2022)) with
| ((env, tps), (x, imp)) -> begin
(let _67_2025 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_67_2025) with
| (env, y) -> begin
(env, ((y, imp))::tps)
end))
end)) (env, []) bs)
in (match (_67_2028) with
| (env, bs) -> begin
(env, (FStar_List.rev bs))
end)))
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (_67_2030)::[] -> begin
(let tc = (FStar_List.hd tcs)
in (let _67_2041 = (desugar_abstract_tc quals env [] tc)
in (match (_67_2041) with
| (_67_2035, _67_2037, se, _67_2040) -> begin
(let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _67_2044, typars, k, [], [], quals, rng) -> begin
(let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(let _67_2053 = (let _169_791 = (FStar_Range.string_of_range rng)
in (let _169_790 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _169_791 _169_790)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (let t = (match (typars) with
| [] -> begin
k
end
| _67_2058 -> begin
(let _169_794 = (let _169_793 = (let _169_792 = (FStar_Syntax_Syntax.mk_Total k)
in (typars, _169_792))
in FStar_Syntax_Syntax.Tm_arrow (_169_793))
in (FStar_Syntax_Syntax.mk _169_794 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ ((l, [], t, quals, rng))))
end
| _67_2061 -> begin
se
end)
in (let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))
end)))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t)::[] -> begin
(let _67_2073 = (typars_of_binders env binders)
in (match (_67_2073) with
| (env', typars) -> begin
(let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _67_16 -> (match (_67_16) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _67_2078 -> begin
false
end)) quals) then begin
FStar_Syntax_Syntax.teff
end else begin
FStar_Syntax_Syntax.tun
end
end
| Some (k) -> begin
(desugar_term env' k)
end)
in (let t0 = t
in (let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _67_17 -> (match (_67_17) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _67_2086 -> begin
false
end)))) then begin
quals
end else begin
if (t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
end
in (let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Effect)) then begin
(let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (let typars = (FStar_Syntax_Subst.close_binders typars)
in (let c = (FStar_Syntax_Subst.close_comp typars c)
in (let _169_800 = (let _169_799 = (FStar_Parser_Env.qualify env id)
in (let _169_798 = (FStar_All.pipe_right quals (FStar_List.filter (fun _67_18 -> (match (_67_18) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _67_2094 -> begin
true
end))))
in (_169_799, [], typars, c, _169_798, rng)))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_169_800)))))
end else begin
(let t = (desugar_typ env' t)
in (let nm = (FStar_Parser_Env.qualify env id)
in (mk_typ_abbrev nm [] typars k t ((nm)::[]) quals rng)))
end
in (let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| FStar_Parser_AST.TyconRecord (_67_2100)::[] -> begin
(let trec = (FStar_List.hd tcs)
in (let _67_2106 = (tycon_record_as_variant trec)
in (match (_67_2106) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _67_2110::_67_2108 -> begin
(let env0 = env
in (let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (let rec collect_tcs = (fun quals et tc -> (let _67_2121 = et
in (match (_67_2121) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_67_2123) -> begin
(let trec = tc
in (let _67_2128 = (tycon_record_as_variant trec)
in (match (_67_2128) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(let _67_2140 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_67_2140) with
| (env, _67_2137, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(let _67_2152 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_67_2152) with
| (env, _67_2149, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _67_2154 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (let _67_2157 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_67_2157) with
| (env, tcs) -> begin
(let tcs = (FStar_List.rev tcs)
in (let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _67_20 -> (match (_67_20) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _67_2165, _67_2167, _67_2169, _67_2171), t, quals) -> begin
(let _67_2181 = (push_tparams env tpars)
in (match (_67_2181) with
| (env_tps, _67_2180) -> begin
(let t = (desugar_term env_tps t)
in (let _169_810 = (let _169_809 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in ([], _169_809))
in (_169_810)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _67_2189, tags, _67_2192), constrs, tconstr, quals) -> begin
(let tycon = (tname, tpars, k)
in (let _67_2203 = (push_tparams env tpars)
in (match (_67_2203) with
| (env_tps, tps) -> begin
(let data_tpars = (FStar_List.map (fun _67_2207 -> (match (_67_2207) with
| (x, _67_2206) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit))
end)) tps)
in (let _67_2231 = (let _169_822 = (FStar_All.pipe_right constrs (FStar_List.map (fun _67_2212 -> (match (_67_2212) with
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
in (let t = (let _169_814 = (FStar_Parser_Env.default_total env_tps)
in (let _169_813 = (close env_tps t)
in (desugar_term _169_814 _169_813)))
in (let name = (FStar_Parser_Env.qualify env id)
in (let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _67_19 -> (match (_67_19) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _67_2226 -> begin
[]
end))))
in (let ntps = (FStar_List.length data_tpars)
in (let _169_821 = (let _169_820 = (let _169_819 = (let _169_818 = (let _169_817 = (let _169_816 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _169_816))
in (FStar_Syntax_Util.arrow data_tpars _169_817))
in (name, univs, _169_818, tname, ntps, quals, mutuals, rng))
in FStar_Syntax_Syntax.Sig_datacon (_169_819))
in (tps, _169_820))
in (name, _169_821)))))))
end))))
in (FStar_All.pipe_left FStar_List.split _169_822))
in (match (_67_2231) with
| (constrNames, constrs) -> begin
(([], FStar_Syntax_Syntax.Sig_inductive_typ ((tname, univs, tpars, k, mutuals, constrNames, tags, rng))))::constrs
end)))
end)))
end
| _67_2233 -> begin
(FStar_All.failwith "impossible")
end))))
in (let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (let bundle = (let _169_824 = (let _169_823 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _169_823, rng))
in FStar_Syntax_Syntax.Sig_bundle (_169_824))
in (let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors env)))
in (let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _67_21 -> (match (_67_21) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _67_2242, tps, k, _67_2246, constrs, quals, _67_2250) when ((FStar_List.length constrs) > 1) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _67_2254 -> begin
[]
end))))
in (let ops = (FStar_List.append discs data_ops)
in (let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env ops)
in (env, (FStar_List.append ((bundle)::[]) ops)))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end))))))))))

let desugar_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (let _67_2278 = (FStar_List.fold_left (fun _67_2263 b -> (match (_67_2263) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(let _67_2271 = (FStar_Parser_Env.push_bv env a)
in (match (_67_2271) with
| (env, a) -> begin
(let _169_833 = (let _169_832 = (FStar_Syntax_Syntax.mk_binder (let _67_2272 = a
in {FStar_Syntax_Syntax.ppname = _67_2272.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_2272.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_169_832)::binders)
in (env, _169_833))
end))
end
| _67_2275 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_67_2278) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))

let rec desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(let se = FStar_Syntax_Syntax.Sig_pragma (((trans_pragma p), d.FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| FStar_Parser_AST.Open (lid) -> begin
(let env = (FStar_Parser_Env.push_namespace env lid)
in (env, []))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _169_838 = (FStar_List.map trans_qual qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _169_838 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _169_840 = (let _169_839 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _169_839))
in _169_840.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _67_2298) -> begin
(let lids = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (let quals = (match (quals) with
| _67_2306::_67_2304 -> begin
(FStar_List.map trans_qual quals)
end
| _67_2309 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _67_22 -> (match (_67_22) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_67_2320); FStar_Syntax_Syntax.lbunivs = _67_2318; FStar_Syntax_Syntax.lbtyp = _67_2316; FStar_Syntax_Syntax.lbeff = _67_2314; FStar_Syntax_Syntax.lbdef = _67_2312} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (l); FStar_Syntax_Syntax.lbunivs = _67_2330; FStar_Syntax_Syntax.lbtyp = _67_2328; FStar_Syntax_Syntax.lbeff = _67_2326; FStar_Syntax_Syntax.lbdef = _67_2324} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env l)
end))))
end)
in (let s = FStar_Syntax_Syntax.Sig_let ((lbs, d.FStar_Parser_AST.drange, lids, quals))
in (let env = (FStar_Parser_Env.push_sigelt env s)
in (env, (s)::[])))))
end
| _67_2338 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(let e = (desugar_term env t)
in (let se = FStar_Syntax_Syntax.Sig_main ((e, d.FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(let f = (desugar_formula env t)
in (let _169_846 = (let _169_845 = (let _169_844 = (let _169_843 = (FStar_Parser_Env.qualify env id)
in (_169_843, f, (FStar_Syntax_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_assume (_169_844))
in (_169_845)::[])
in (env, _169_846)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(let t = (let _169_847 = (close_fun env t)
in (desugar_term env _169_847))
in (let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (let se = (let _169_850 = (let _169_849 = (FStar_Parser_Env.qualify env id)
in (let _169_848 = (FStar_List.map trans_qual quals)
in (_169_849, [], t, _169_848, d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_declare_typ (_169_850))
in (let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(let t = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (let l = (FStar_Parser_Env.qualify env id)
in (let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_Env.push_sigelt env se')
in (let data_ops = (mk_data_projectors env ([], se))
in (let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(let t = (desugar_term env term)
in (let t = (let _169_854 = (let _169_851 = (FStar_Syntax_Syntax.null_binder t)
in (_169_851)::[])
in (let _169_853 = (let _169_852 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _169_852))
in (FStar_Syntax_Util.arrow _169_854 _169_853)))
in (let l = (FStar_Parser_Env.qualify env id)
in (let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_Env.push_sigelt env se')
in (let data_ops = (mk_data_projectors env ([], se))
in (let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(let _67_2391 = (desugar_binders env binders)
in (match (_67_2391) with
| (env_k, binders) -> begin
(let k = (desugar_term env_k k)
in (let name = (FStar_Parser_Env.qualify env id)
in (let se = (mk_typ_abbrev name [] binders FStar_Syntax_Syntax.tun k ((name)::[]) [] d.FStar_Parser_AST.drange)
in (let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(let env0 = env
in (let _67_2407 = (desugar_binders env eff_binders)
in (match (_67_2407) with
| (env, binders) -> begin
(let _67_2418 = (let _67_2410 = (head_and_args defn)
in (match (_67_2410) with
| (head, args) -> begin
(let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _67_2414 -> begin
(let _169_859 = (let _169_858 = (let _169_857 = (let _169_856 = (let _169_855 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat "Effect " _169_855))
in (Prims.strcat _169_856 " not found"))
in (_169_857, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_169_858))
in (Prims.raise _169_859))
end)
in (let _169_860 = (desugar_args env args)
in (ed, _169_860)))
end))
in (match (_67_2418) with
| (ed, args) -> begin
(let binders = (FStar_Syntax_Subst.close_binders binders)
in (let subst = (FStar_Syntax_Util.subst_of_list ed.FStar_Syntax_Syntax.binders args)
in (let sub = (fun x -> (let _169_864 = (let _169_863 = (FStar_Syntax_Subst.subst subst (Prims.snd x))
in (FStar_Syntax_Subst.close binders _169_863))
in ([], _169_864)))
in (let ed = (let _169_881 = (FStar_List.map trans_qual quals)
in (let _169_880 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _169_879 = (let _169_865 = (sub ([], ed.FStar_Syntax_Syntax.signature))
in (Prims.snd _169_865))
in (let _169_878 = (sub ed.FStar_Syntax_Syntax.ret)
in (let _169_877 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _169_876 = (sub ed.FStar_Syntax_Syntax.bind_wlp)
in (let _169_875 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _169_874 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _169_873 = (sub ed.FStar_Syntax_Syntax.ite_wlp)
in (let _169_872 = (sub ed.FStar_Syntax_Syntax.wp_binop)
in (let _169_871 = (sub ed.FStar_Syntax_Syntax.wp_as_type)
in (let _169_870 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _169_869 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _169_868 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _169_867 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _169_866 = (sub ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _169_881; FStar_Syntax_Syntax.mname = _169_880; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _169_879; FStar_Syntax_Syntax.ret = _169_878; FStar_Syntax_Syntax.bind_wp = _169_877; FStar_Syntax_Syntax.bind_wlp = _169_876; FStar_Syntax_Syntax.if_then_else = _169_875; FStar_Syntax_Syntax.ite_wp = _169_874; FStar_Syntax_Syntax.ite_wlp = _169_873; FStar_Syntax_Syntax.wp_binop = _169_872; FStar_Syntax_Syntax.wp_as_type = _169_871; FStar_Syntax_Syntax.close_wp = _169_870; FStar_Syntax_Syntax.assert_p = _169_869; FStar_Syntax_Syntax.assume_p = _169_868; FStar_Syntax_Syntax.null_wp = _169_867; FStar_Syntax_Syntax.trivial = _169_866}))))))))))))))))
in (let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[])))))))
end))
end)))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(let env0 = env
in (let env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (let _67_2439 = (desugar_binders env eff_binders)
in (match (_67_2439) with
| (env, binders) -> begin
(let eff_k = (let _169_882 = (FStar_Parser_Env.default_total env)
in (desugar_term _169_882 eff_kind))
in (let _67_2450 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _67_2443 decl -> (match (_67_2443) with
| (env, out) -> begin
(let _67_2447 = (desugar_decl env decl)
in (match (_67_2447) with
| (env, ses) -> begin
(let _169_886 = (let _169_885 = (FStar_List.hd ses)
in (_169_885)::out)
in (env, _169_886))
end))
end)) (env, [])))
in (match (_67_2450) with
| (env, decls) -> begin
(let binders = (FStar_Syntax_Subst.close_binders binders)
in (let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (let lookup = (fun s -> (let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident (s, d.FStar_Parser_AST.drange)))
in (let _169_890 = (let _169_889 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _169_889))
in ([], _169_890))))
in (let ed = (let _169_905 = (FStar_List.map trans_qual quals)
in (let _169_904 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _169_903 = (lookup "return")
in (let _169_902 = (lookup "bind_wp")
in (let _169_901 = (lookup "bind_wlp")
in (let _169_900 = (lookup "if_then_else")
in (let _169_899 = (lookup "ite_wp")
in (let _169_898 = (lookup "ite_wlp")
in (let _169_897 = (lookup "wp_binop")
in (let _169_896 = (lookup "wp_as_type")
in (let _169_895 = (lookup "close_wp")
in (let _169_894 = (lookup "assert_p")
in (let _169_893 = (lookup "assume_p")
in (let _169_892 = (lookup "null_wp")
in (let _169_891 = (lookup "trivial")
in {FStar_Syntax_Syntax.qualifiers = _169_905; FStar_Syntax_Syntax.mname = _169_904; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret = _169_903; FStar_Syntax_Syntax.bind_wp = _169_902; FStar_Syntax_Syntax.bind_wlp = _169_901; FStar_Syntax_Syntax.if_then_else = _169_900; FStar_Syntax_Syntax.ite_wp = _169_899; FStar_Syntax_Syntax.ite_wlp = _169_898; FStar_Syntax_Syntax.wp_binop = _169_897; FStar_Syntax_Syntax.wp_as_type = _169_896; FStar_Syntax_Syntax.close_wp = _169_895; FStar_Syntax_Syntax.assert_p = _169_894; FStar_Syntax_Syntax.assume_p = _169_893; FStar_Syntax_Syntax.null_wp = _169_892; FStar_Syntax_Syntax.trivial = _169_891})))))))))))))))
in (let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[])))))))
end)))
end))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(let lookup = (fun l -> (match ((FStar_Parser_Env.try_lookup_effect_name env l)) with
| None -> begin
(let _169_912 = (let _169_911 = (let _169_910 = (let _169_909 = (let _169_908 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat "Effect name " _169_908))
in (Prims.strcat _169_909 " not found"))
in (_169_910, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_169_911))
in (Prims.raise _169_912))
end
| Some (l) -> begin
l
end))
in (let src = (lookup l.FStar_Parser_AST.msource)
in (let dst = (lookup l.FStar_Parser_AST.mdest)
in (let lift = (let _169_913 = (desugar_term env l.FStar_Parser_AST.lift_op)
in ([], _169_913))
in (let se = FStar_Syntax_Syntax.Sig_sub_effect (({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end))

let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _67_2474 d -> (match (_67_2474) with
| (env, sigelts) -> begin
(let _67_2478 = (desugar_decl env d)
in (match (_67_2478) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))

let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]

let desugar_modul_common = (fun curmod env m -> (let open_ns = (fun mname d -> (let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _169_929 = (let _169_928 = (let _169_927 = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_169_927))
in (FStar_Parser_AST.mk_decl _169_928 (FStar_Ident.range_of_lid mname)))
in (_169_929)::d)
end else begin
d
end
in d))
in (let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod, _67_2489) -> begin
(FStar_Parser_Env.finish_module_or_interface env prev_mod)
end)
in (let _67_2508 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _169_931 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in (let _169_930 = (open_ns mname decls)
in (_169_931, mname, _169_930, true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _169_933 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in (let _169_932 = (open_ns mname decls)
in (_169_933, mname, _169_932, false)))
end)
in (match (_67_2508) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(let _67_2511 = (desugar_decls env decls)
in (match (_67_2511) with
| (env, sigelts) -> begin
(let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in (env, modul, pop_when_done))
end))
end)))))

let desugar_partial_modul = (fun curmod env m -> (let m = if (FStar_ST.read FStar_Options.interactive_fsi) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _169_940 = (let _169_939 = (let _169_938 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_Util.for_some (fun m -> (m = mname.FStar_Ident.str)) _169_938))
in (mname, decls, _169_939))
in FStar_Parser_AST.Interface (_169_940))
end
| FStar_Parser_AST.Interface (mname, _67_2523, _67_2525) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (let _67_2533 = (desugar_modul_common curmod env m)
in (match (_67_2533) with
| (x, y, _67_2532) -> begin
(x, y)
end))))

let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul) = (fun env m -> (let _67_2539 = (desugar_modul_common None env m)
in (match (_67_2539) with
| (env, modul, pop_when_done) -> begin
(let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (let _67_2541 = if (FStar_Options.should_dump modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _169_945 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _169_945))
end else begin
()
end
in (let _169_946 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in (_169_946, modul))))
end)))

let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (let _67_2554 = (FStar_List.fold_left (fun _67_2547 m -> (match (_67_2547) with
| (env, mods) -> begin
(let _67_2551 = (desugar_modul env m)
in (match (_67_2551) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_67_2554) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))

let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (let _67_2559 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_67_2559) with
| (en, pop_when_done) -> begin
(let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (let _67_2560 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.modules = _67_2560.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _67_2560.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _67_2560.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _67_2560.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _67_2560.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _67_2560.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _67_2560.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _67_2560.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _67_2560.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _67_2560.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




