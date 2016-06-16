
open Prims

let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _63_1 -> (match (_63_1) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| _63_28 -> begin
None
end))


let trans_qual : FStar_Range.range  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r _63_2 -> (match (_63_2) with
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
(

let _63_42 = (FStar_TypeChecker_Errors.warn r "The \'opaque\' qualifier is deprecated; use \'unfoldable\', which is also the default")
in FStar_Syntax_Syntax.Unfoldable)
end
| FStar_Parser_AST.DefaultEffect -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("The \'default\' qualifier on effects is no longer supported", r))))
end))


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun _63_3 -> (match (_63_3) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _63_4 -> (match (_63_4) with
| FStar_Parser_AST.Hash -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| _63_53 -> begin
None
end))


let arg_withimp_e = (fun imp t -> (t, (as_imp imp)))


let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
(t, Some (FStar_Syntax_Syntax.imp_tag))
end
| _63_60 -> begin
(t, None)
end))


let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_63_64) -> begin
true
end
| _63_67 -> begin
false
end)))))


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _63_72 -> begin
t
end))


let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _153_23 = (let _153_22 = (FStar_Ident.lid_of_path (("Type0")::[]) r)
in FStar_Parser_AST.Name (_153_22))
in (FStar_Parser_AST.mk_term _153_23 r FStar_Parser_AST.Kind)))


let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _153_27 = (let _153_26 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_153_26))
in (FStar_Parser_AST.mk_term _153_27 r FStar_Parser_AST.Kind)))


let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_63_78) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_delta
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| (FStar_Syntax_Syntax.Tm_uinst (t, _)) | (FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}, _)) | (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) | (FStar_Syntax_Syntax.Tm_app (t, _)) | (FStar_Syntax_Syntax.Tm_abs (_, t, _)) | (FStar_Syntax_Syntax.Tm_let (_, t)) -> begin
(delta_qualifier t)
end)))


let incr_delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let d = (delta_qualifier t)
in (

let rec aux = (fun d -> (match (d) with
| FStar_Syntax_Syntax.Delta_equational -> begin
d
end
| FStar_Syntax_Syntax.Delta_constant -> begin
FStar_Syntax_Syntax.Delta_unfoldable (1)
end
| FStar_Syntax_Syntax.Delta_unfoldable (i) -> begin
FStar_Syntax_Syntax.Delta_unfoldable ((i + 1))
end
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(aux d)
end))
in (aux d))))


let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (

let name_of_char = (fun _63_5 -> (match (_63_5) with
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
| _63_173 -> begin
"UNKNOWN"
end))
in (

let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _153_47 = (let _153_45 = (FStar_Util.char_at s i)
in (name_of_char _153_45))
in (let _153_46 = (aux (i + 1))
in (_153_47)::_153_46))
end)
in (let _153_49 = (let _153_48 = (aux 0)
in (FStar_String.concat "_" _153_48))
in (Prims.strcat "op_" _153_49)))))


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _153_59 = (let _153_58 = (let _153_57 = (let _153_56 = (compile_op n s)
in (_153_56, r))
in (FStar_Ident.mk_ident _153_57))
in (_153_58)::[])
in (FStar_All.pipe_right _153_59 FStar_Ident.lid_of_ids)))


let op_as_term : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (

let r = (fun l dd -> (let _153_74 = (let _153_73 = (let _153_72 = (FStar_Ident.set_lid_range l rng)
in (FStar_Syntax_Syntax.lid_as_fv _153_72 dd None))
in (FStar_All.pipe_right _153_73 FStar_Syntax_Syntax.fv_to_tm))
in Some (_153_74)))
in (

let fallback = (fun _63_188 -> (match (()) with
| () -> begin
(match (s) with
| "=" -> begin
(r FStar_Syntax_Const.op_Eq FStar_Syntax_Syntax.Delta_equational)
end
| ":=" -> begin
(r FStar_Syntax_Const.op_ColonEq FStar_Syntax_Syntax.Delta_equational)
end
| "<" -> begin
(r FStar_Syntax_Const.op_LT FStar_Syntax_Syntax.Delta_equational)
end
| "<=" -> begin
(r FStar_Syntax_Const.op_LTE FStar_Syntax_Syntax.Delta_equational)
end
| ">" -> begin
(r FStar_Syntax_Const.op_GT FStar_Syntax_Syntax.Delta_equational)
end
| ">=" -> begin
(r FStar_Syntax_Const.op_GTE FStar_Syntax_Syntax.Delta_equational)
end
| "&&" -> begin
(r FStar_Syntax_Const.op_And FStar_Syntax_Syntax.Delta_equational)
end
| "||" -> begin
(r FStar_Syntax_Const.op_Or FStar_Syntax_Syntax.Delta_equational)
end
| "+" -> begin
(r FStar_Syntax_Const.op_Addition FStar_Syntax_Syntax.Delta_equational)
end
| "-" when (arity = 1) -> begin
(r FStar_Syntax_Const.op_Minus FStar_Syntax_Syntax.Delta_equational)
end
| "-" -> begin
(r FStar_Syntax_Const.op_Subtraction FStar_Syntax_Syntax.Delta_equational)
end
| "/" -> begin
(r FStar_Syntax_Const.op_Division FStar_Syntax_Syntax.Delta_equational)
end
| "%" -> begin
(r FStar_Syntax_Const.op_Modulus FStar_Syntax_Syntax.Delta_equational)
end
| "!" -> begin
(r FStar_Syntax_Const.read_lid FStar_Syntax_Syntax.Delta_equational)
end
| "@" -> begin
(r FStar_Syntax_Const.list_append_lid FStar_Syntax_Syntax.Delta_equational)
end
| "^" -> begin
(r FStar_Syntax_Const.strcat_lid FStar_Syntax_Syntax.Delta_equational)
end
| "|>" -> begin
(r FStar_Syntax_Const.pipe_right_lid FStar_Syntax_Syntax.Delta_equational)
end
| "<|" -> begin
(r FStar_Syntax_Const.pipe_left_lid FStar_Syntax_Syntax.Delta_equational)
end
| "<>" -> begin
(r FStar_Syntax_Const.op_notEq FStar_Syntax_Syntax.Delta_equational)
end
| "~" -> begin
(r FStar_Syntax_Const.not_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)))
end
| "==" -> begin
(r FStar_Syntax_Const.eq2_lid FStar_Syntax_Syntax.Delta_constant)
end
| "<<" -> begin
(r FStar_Syntax_Const.precedes_lid FStar_Syntax_Syntax.Delta_constant)
end
| "/\\" -> begin
(r FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)))
end
| "\\/" -> begin
(r FStar_Syntax_Const.or_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)))
end
| "==>" -> begin
(r FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)))
end
| "<==>" -> begin
(r FStar_Syntax_Const.iff_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)))
end
| _63_216 -> begin
None
end)
end))
in (match ((let _153_77 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _153_77))) with
| Some (t) -> begin
Some (t)
end
| _63_220 -> begin
(fallback ())
end))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _153_84 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _153_84)))


let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_63_229) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let _63_236 = (FStar_Parser_Env.push_bv env x)
in (match (_63_236) with
| (env, _63_235) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_63_238, term) -> begin
(let _153_91 = (free_type_vars env term)
in (env, _153_91))
end
| FStar_Parser_AST.TAnnotated (id, _63_244) -> begin
(

let _63_250 = (FStar_Parser_Env.push_bv env id)
in (match (_63_250) with
| (env, _63_249) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _153_92 = (free_type_vars env t)
in (env, _153_92))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _153_95 = (unparen t)
in _153_95.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_63_256) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _63_262 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_63_292, ts) -> begin
(FStar_List.collect (fun _63_299 -> (match (_63_299) with
| (t, _63_298) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_63_301, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _63_308) -> begin
(let _153_98 = (free_type_vars env t1)
in (let _153_97 = (free_type_vars env t2)
in (FStar_List.append _153_98 _153_97)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(

let _63_317 = (free_type_vars_b env b)
in (match (_63_317) with
| (env, f) -> begin
(let _153_99 = (free_type_vars env t)
in (FStar_List.append f _153_99))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(

let _63_333 = (FStar_List.fold_left (fun _63_326 binder -> (match (_63_326) with
| (env, free) -> begin
(

let _63_330 = (free_type_vars_b env binder)
in (match (_63_330) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_63_333) with
| (env, free) -> begin
(let _153_102 = (free_type_vars env body)
in (FStar_List.append free _153_102))
end))
end
| FStar_Parser_AST.Project (t, _63_336) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t -> (match ((let _153_109 = (unparen t)
in _153_109.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _63_380 -> begin
(t, args)
end))
in (aux [] t)))


let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _153_114 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _153_114))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _153_118 = (let _153_117 = (let _153_116 = (tm_type x.FStar_Ident.idRange)
in (x, _153_116))
in FStar_Parser_AST.TAnnotated (_153_117))
in (FStar_Parser_AST.mk_binder _153_118 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))


let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _153_123 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _153_123))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _153_127 = (let _153_126 = (let _153_125 = (tm_type x.FStar_Ident.idRange)
in (x, _153_125))
in FStar_Parser_AST.TAnnotated (_153_126))
in (FStar_Parser_AST.mk_binder _153_127 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let t = (match ((let _153_128 = (unparen t)
in _153_128.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_63_393) -> begin
t
end
| _63_396 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))


let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _63_406 -> begin
(bs, t)
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _63_410) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_63_416); FStar_Parser_AST.prange = _63_414}, _63_420) -> begin
true
end
| _63_424 -> begin
false
end))


let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _63_436 = (destruct_app_pattern env is_top_level p)
in (match (_63_436) with
| (name, args, _63_435) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _63_441); FStar_Parser_AST.prange = _63_438}, args) when is_top_level -> begin
(let _153_142 = (let _153_141 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_153_141))
in (_153_142, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _63_452); FStar_Parser_AST.prange = _63_449}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _63_460 -> begin
(FStar_All.failwith "Not an app pattern")
end))


type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term)


let is_LocalBinder = (fun _discr_ -> (match (_discr_) with
| LocalBinder (_) -> begin
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


let ___LocalBinder____0 = (fun projectee -> (match (projectee) with
| LocalBinder (_63_463) -> begin
_63_463
end))


let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_63_466) -> begin
_63_466
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _63_6 -> (match (_63_6) with
| LocalBinder (a, aq) -> begin
(a, aq)
end
| _63_473 -> begin
(FStar_All.failwith "Impossible")
end))


let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _63_7 -> (match (_63_7) with
| (None, k) -> begin
(let _153_179 = (FStar_Syntax_Syntax.null_binder k)
in (_153_179, env))
end
| (Some (a), k) -> begin
(

let _63_486 = (FStar_Parser_Env.push_bv env a)
in (match (_63_486) with
| (env, a) -> begin
(((

let _63_487 = a
in {FStar_Syntax_Syntax.ppname = _63_487.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_487.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}), (trans_aqual imp)), env)
end))
end))


type env_t =
FStar_Parser_Env.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _63_492 -> (match (_63_492) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))


let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))


let rec desugar_data_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat) = (fun env p -> (

let check_linear_pattern_variables = (fun p -> (

let rec pat_vars = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_dot_term (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_constant (_)) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (_63_513, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _63_521 -> (match (_63_521) with
| (p, _63_520) -> begin
(let _153_229 = (pat_vars p)
in (FStar_Util.set_union out _153_229))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let xs = (pat_vars hd)
in if (not ((FStar_Util.for_all (fun p -> (

let ys = (pat_vars p)
in ((FStar_Util.set_is_subset_of xs ys) && (FStar_Util.set_is_subset_of ys xs)))) tl))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Disjunctive pattern binds different variables in each case", p.FStar_Syntax_Syntax.p))))
end else begin
xs
end)
end))
in (pat_vars p)))
in (

let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))) with
| Some (y) -> begin
(l, e, y)
end
| _63_539 -> begin
(

let _63_542 = (FStar_Parser_Env.push_bv e x)
in (match (_63_542) with
| (e, x) -> begin
((x)::l, e, x)
end))
end))
in (

let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun b -> (b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText))))) with
| Some (b) -> begin
(l, e, b)
end
| _63_551 -> begin
(

let _63_554 = (FStar_Parser_Env.push_bv e a)
in (match (_63_554) with
| (e, a) -> begin
((a)::l, e, a)
end))
end))
in (

let rec aux = (fun loc env p -> (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Parser_AST.prange))
in (

let pos_r = (fun r q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(

let _63_576 = (aux loc env p)
in (match (_63_576) with
| (loc, env, var, p, _63_575) -> begin
(

let _63_593 = (FStar_List.fold_left (fun _63_580 p -> (match (_63_580) with
| (loc, env, ps) -> begin
(

let _63_589 = (aux loc env p)
in (match (_63_589) with
| (loc, env, _63_585, p, _63_588) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_63_593) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (loc, env, var, pat, false))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _63_604 = (aux loc env p)
in (match (_63_604) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (_63_606) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t = (let _153_259 = (close_fun env t)
in (desugar_term env _153_259))
in LocalBinder (((

let _63_613 = x
in {FStar_Syntax_Syntax.ppname = _63_613.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_613.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), aq)))
end)
in (loc, env', binder, p, imp))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _153_260 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in (loc, env, LocalBinder ((x, None)), _153_260, false)))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _153_261 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in (loc, env, LocalBinder ((x, None)), _153_261, false)))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let _63_632 = (resolvex loc env x)
in (match (_63_632) with
| (loc, env, xbv) -> begin
(let _153_262 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in (loc, env, LocalBinder ((xbv, aq)), _153_262, imp))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _153_263 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, []))))
in (loc, env, LocalBinder ((x, None)), _153_263, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _63_638}, args) -> begin
(

let _63_660 = (FStar_List.fold_right (fun arg _63_649 -> (match (_63_649) with
| (loc, env, args) -> begin
(

let _63_656 = (aux loc env arg)
in (match (_63_656) with
| (loc, env, _63_653, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_63_660) with
| (loc, env, args) -> begin
(

let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _153_266 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _153_266, false))))
end))
end
| FStar_Parser_AST.PatApp (_63_664) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let _63_684 = (FStar_List.fold_right (fun pat _63_672 -> (match (_63_672) with
| (loc, env, pats) -> begin
(

let _63_680 = (aux loc env pat)
in (match (_63_680) with
| (loc, env, _63_676, pat, _63_679) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_63_684) with
| (loc, env, pats) -> begin
(

let pat = (let _153_279 = (let _153_278 = (let _153_274 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _153_274))
in (let _153_277 = (let _153_276 = (let _153_275 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_153_275, []))
in FStar_Syntax_Syntax.Pat_cons (_153_276))
in (FStar_All.pipe_left _153_278 _153_277)))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _153_273 = (let _153_272 = (let _153_271 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_153_271, ((hd, false))::((tl, false))::[]))
in FStar_Syntax_Syntax.Pat_cons (_153_272))
in (FStar_All.pipe_left (pos_r r) _153_273)))) pats _153_279))
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (loc, env, LocalBinder ((x, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let _63_710 = (FStar_List.fold_left (fun _63_697 p -> (match (_63_697) with
| (loc, env, pats) -> begin
(

let _63_706 = (aux loc env p)
in (match (_63_706) with
| (loc, env, _63_702, pat, _63_705) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_63_710) with
| (loc, env, args) -> begin
(

let args = (FStar_List.rev args)
in (

let l = if dep then begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end else begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
in (

let constr = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (

let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| _63_717 -> begin
(FStar_All.failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _153_282 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _153_282, false)))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let _63_727 = (FStar_List.hd fields)
in (match (_63_727) with
| (f, _63_726) -> begin
(

let _63_731 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_63_731) with
| (record, _63_730) -> begin
(

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _63_734 -> (match (_63_734) with
| (f, p) -> begin
(let _153_284 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.qualify_field_to_record env record) f)
in (_153_284, p))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _63_739 -> (match (_63_739) with
| (f, _63_738) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _63_743 -> (match (_63_743) with
| (g, _63_742) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_63_746, p) -> begin
p
end)
end))))
in (

let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (

let _63_758 = (aux loc env app)
in (match (_63_758) with
| (env, e, b, p, _63_757) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _153_293 = (let _153_292 = (let _153_291 = (

let _63_763 = fv
in (let _153_290 = (let _153_289 = (let _153_288 = (let _153_287 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _153_287))
in FStar_Syntax_Syntax.Record_ctor (_153_288))
in Some (_153_289))
in {FStar_Syntax_Syntax.fv_name = _63_763.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _63_763.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _153_290}))
in (_153_291, args))
in FStar_Syntax_Syntax.Pat_cons (_153_292))
in (FStar_All.pipe_left pos _153_293))
end
| _63_766 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (

let _63_775 = (aux [] env p)
in (match (_63_775) with
| (_63_769, env, b, p, _63_774) -> begin
(

let _63_776 = (let _153_294 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _153_294))
in (env, b, p))
end)))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _63_783) -> begin
(let _153_300 = (let _153_299 = (let _153_298 = (FStar_Parser_Env.qualify env x)
in (_153_298, FStar_Syntax_Syntax.tun))
in LetBinder (_153_299))
in (env, _153_300, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _63_790); FStar_Parser_AST.prange = _63_787}, t) -> begin
(let _153_304 = (let _153_303 = (let _153_302 = (FStar_Parser_Env.qualify env x)
in (let _153_301 = (desugar_term env t)
in (_153_302, _153_301)))
in LetBinder (_153_303))
in (env, _153_304, None))
end
| _63_798 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(

let _63_802 = (desugar_data_pat env p)
in (match (_63_802) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _63_810 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _63_814 env pat -> (

let _63_822 = (desugar_data_pat env pat)
in (match (_63_822) with
| (env, _63_820, pat) -> begin
(env, pat)
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _63_827 = env
in {FStar_Parser_Env.curmodule = _63_827.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _63_827.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _63_827.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _63_827.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _63_827.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _63_827.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _63_827.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _63_827.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _63_827.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _63_827.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _63_827.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _63_832 = env
in {FStar_Parser_Env.curmodule = _63_832.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _63_832.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _63_832.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _63_832.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _63_832.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _63_832.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _63_832.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _63_832.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _63_832.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _63_832.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _63_832.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_machine_integer : FStar_Parser_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env repr _63_839 range -> (match (_63_839) with
| (signedness, width) -> begin
(

let lid = (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "FStar." (match (signedness) with
| FStar_Const.Unsigned -> begin
"U"
end
| FStar_Const.Signed -> begin
""
end)) "Int") (match (width) with
| FStar_Const.Int8 -> begin
"8"
end
| FStar_Const.Int16 -> begin
"16"
end
| FStar_Const.Int32 -> begin
"32"
end
| FStar_Const.Int64 -> begin
"64"
end)) ".") (match (signedness) with
| FStar_Const.Unsigned -> begin
"u"
end
| FStar_Const.Signed -> begin
""
end)) "int_to_t")
in (

let lid = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text lid) range)
in (

let lid = (match ((FStar_Parser_Env.try_lookup_lid env lid)) with
| Some (lid) -> begin
lid
end
| None -> begin
(let _153_320 = (FStar_Util.format1 "%s not in scope\n" (FStar_Ident.text_of_lid lid))
in (FStar_All.failwith _153_320))
end)
in (

let repr = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int ((repr, None)))) None range)
in (let _153_325 = (let _153_324 = (let _153_323 = (let _153_322 = (let _153_321 = (FStar_Syntax_Syntax.as_implicit false)
in (repr, _153_321))
in (_153_322)::[])
in (lid, _153_323))
in FStar_Syntax_Syntax.Tm_app (_153_324))
in (FStar_Syntax_Syntax.mk _153_325 None range))))))
end))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let _63_863 = e
in {FStar_Syntax_Syntax.n = _63_863.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _63_863.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _63_863.FStar_Syntax_Syntax.vars}))
in (match ((let _153_333 = (unparen top)
in _153_333.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_63_867) -> begin
(desugar_formula env top)
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(desugar_formula env t)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(desugar_formula env t)
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (i, Some (size))) -> begin
(desugar_machine_integer env i size top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Const (c) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (c)))
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("~", ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("==", args))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[]))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("*", (_63_893)::(_63_891)::[]) when (let _153_334 = (op_as_term env 2 top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _153_334 FStar_Option.isNone)) -> begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(

let rest = (flatten t2)
in (t1)::rest)
end
| _63_907 -> begin
(t)::[]
end))
in (

let targs = (let _153_340 = (let _153_337 = (unparen top)
in (flatten _153_337))
in (FStar_All.pipe_right _153_340 (FStar_List.map (fun t -> (let _153_339 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _153_339))))))
in (

let tup = (let _153_341 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _153_341))
in (mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _153_342 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (FStar_All.pipe_left setpos _153_342))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Unexpected operator: " s), top.FStar_Parser_AST.range))))
end
| Some (op) -> begin
(

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _153_344 = (desugar_term env t)
in (_153_344, None)))))
in (mk (FStar_Syntax_Syntax.Tm_app ((op, args)))))
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _63_928; FStar_Ident.ident = _63_926; FStar_Ident.nsstr = _63_924; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _63_937; FStar_Ident.ident = _63_935; FStar_Ident.nsstr = _63_933; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _63_946; FStar_Ident.ident = _63_944; FStar_Ident.nsstr = _63_942; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _63_955; FStar_Ident.ident = _63_953; FStar_Ident.nsstr = _63_951; FStar_Ident.str = "True"}) -> begin
(let _153_345 = (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _153_345 FStar_Syntax_Syntax.Delta_constant None))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _63_964; FStar_Ident.ident = _63_962; FStar_Ident.nsstr = _63_960; FStar_Ident.str = "False"}) -> begin
(let _153_346 = (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _153_346 FStar_Syntax_Syntax.Delta_constant None))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let _153_347 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _153_347))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(

let _63_979 = (match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| None -> begin
(let _153_348 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (_153_348, false))
end
| Some (head) -> begin
(let _153_349 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in (_153_349, true))
end)
in (match (_63_979) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _63_982 -> begin
(

let args = (FStar_List.map (fun _63_985 -> (match (_63_985) with
| (t, imp) -> begin
(

let te = (desugar_term env t)
in (arg_withimp_e imp te))
end)) args)
in (

let app = (mk (FStar_Syntax_Syntax.Tm_app ((head, args))))
in if is_data then begin
(mk (FStar_Syntax_Syntax.Tm_meta ((app, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))
end else begin
app
end))
end)
end))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let _63_1013 = (FStar_List.fold_left (fun _63_996 b -> (match (_63_996) with
| (env, tparams, typs) -> begin
(

let _63_1000 = (desugar_binder env b)
in (match (_63_1000) with
| (xopt, t) -> begin
(

let _63_1006 = (match (xopt) with
| None -> begin
(let _153_353 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (env, _153_353))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_63_1006) with
| (env, x) -> begin
(let _153_357 = (let _153_356 = (let _153_355 = (let _153_354 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_354))
in (_153_355)::[])
in (FStar_List.append typs _153_356))
in (env, (FStar_List.append tparams ((((

let _63_1007 = x
in {FStar_Syntax_Syntax.ppname = _63_1007.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_1007.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), None))::[])), _153_357))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_63_1013) with
| (env, _63_1011, targs) -> begin
(

let tup = (let _153_358 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _153_358))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let _63_1021 = (uncurry binders t)
in (match (_63_1021) with
| (bs, t) -> begin
(

let rec aux = (fun env bs _63_8 -> (match (_63_8) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _153_365 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _153_365)))
end
| (hd)::tl -> begin
(

let mlenv = (FStar_Parser_Env.default_ml env)
in (

let bb = (desugar_binder mlenv hd)
in (

let _63_1035 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_63_1035) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _63_1042) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(

let _63_1050 = (as_binder env None b)
in (match (_63_1050) with
| ((x, _63_1047), env) -> begin
(

let f = (desugar_formula env f)
in (let _153_366 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _153_366)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let _63_1070 = (FStar_List.fold_left (fun _63_1058 pat -> (match (_63_1058) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_63_1061, t) -> begin
(let _153_370 = (let _153_369 = (free_type_vars env t)
in (FStar_List.append _153_369 ftvs))
in (env, _153_370))
end
| _63_1066 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_63_1070) with
| (_63_1068, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (let _153_372 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, Some (FStar_Parser_AST.Implicit)))) top.FStar_Parser_AST.range))))
in (FStar_List.append _153_372 binders))
in (

let rec aux = (fun env bs sc_pat_opt _63_9 -> (match (_63_9) with
| [] -> begin
(

let body = (desugar_term env body)
in (

let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(

let body = (let _153_382 = (let _153_381 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _153_381 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _153_382 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((sc, ((pat, None, body))::[]))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _153_383 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _153_383))))
end
| (p)::rest -> begin
(

let _63_1094 = (desugar_binding_pat env p)
in (match (_63_1094) with
| (env, b, pat) -> begin
(

let _63_1145 = (match (b) with
| LetBinder (_63_1096) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _63_1104) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _153_385 = (let _153_384 = (FStar_Syntax_Syntax.bv_to_name x)
in (_153_384, p))
in Some (_153_385))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Syntax_Syntax.n, p'.FStar_Syntax_Syntax.v)) with
| (FStar_Syntax_Syntax.Tm_name (_63_1118), _63_1121) -> begin
(

let tup2 = (let _153_386 = (FStar_Syntax_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _153_386 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _153_394 = (let _153_393 = (let _153_392 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _153_391 = (let _153_390 = (FStar_Syntax_Syntax.as_arg sc)
in (let _153_389 = (let _153_388 = (let _153_387 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_387))
in (_153_388)::[])
in (_153_390)::_153_389))
in (_153_392, _153_391)))
in FStar_Syntax_Syntax.Tm_app (_153_393))
in (FStar_Syntax_Syntax.mk _153_394 None top.FStar_Parser_AST.range))
in (

let p = (let _153_395 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tup2, ((p', false))::((p, false))::[]))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _153_395))
in Some ((sc, p)))))
end
| (FStar_Syntax_Syntax.Tm_app (_63_1127, args), FStar_Syntax_Syntax.Pat_cons (_63_1132, pats)) -> begin
(

let tupn = (let _153_396 = (FStar_Syntax_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _153_396 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _153_403 = (let _153_402 = (let _153_401 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _153_400 = (let _153_399 = (let _153_398 = (let _153_397 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_397))
in (_153_398)::[])
in (FStar_List.append args _153_399))
in (_153_401, _153_400)))
in FStar_Syntax_Syntax.Tm_app (_153_402))
in (mk _153_403))
in (

let p = (let _153_404 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tupn, (FStar_List.append pats (((p, false))::[]))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _153_404))
in Some ((sc, p)))))
end
| _63_1141 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((x, aq), sc_pat_opt))
end)
in (match (_63_1145) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _63_1149; FStar_Parser_AST.level = _63_1147}, phi, _63_1155) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env phi)
in (let _153_412 = (let _153_411 = (let _153_410 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _153_409 = (let _153_408 = (FStar_Syntax_Syntax.as_arg phi)
in (let _153_407 = (let _153_406 = (let _153_405 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_405))
in (_153_406)::[])
in (_153_408)::_153_407))
in (_153_410, _153_409)))
in FStar_Syntax_Syntax.Tm_app (_153_411))
in (mk _153_412)))
end
| FStar_Parser_AST.App (_63_1160) -> begin
(

let rec aux = (fun args e -> (match ((let _153_417 = (unparen e)
in _153_417.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(

let arg = (let _153_418 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _153_418))
in (aux ((arg)::args) e))
end
| _63_1172 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _153_421 = (let _153_420 = (let _153_419 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_153_419, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))
in FStar_Syntax_Syntax.Tm_meta (_153_420))
in (mk _153_421))
end
| FStar_Parser_AST.Let (is_rec, ((pat, _snd))::_tl, body) -> begin
(

let ds_let_rec_or_app = (fun _63_1188 -> (match (()) with
| () -> begin
(

let bindings = ((pat, _snd))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _63_1192 -> (match (_63_1192) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _153_425 = (destruct_app_pattern env top_level p)
in (_153_425, def))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _153_426 = (destruct_app_pattern env top_level p)
in (_153_426, def))
end
| _63_1198 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _63_1203); FStar_Parser_AST.prange = _63_1200}, t) -> begin
if top_level then begin
(let _153_429 = (let _153_428 = (let _153_427 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_153_427))
in (_153_428, [], Some (t)))
in (_153_429, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _63_1212) -> begin
if top_level then begin
(let _153_432 = (let _153_431 = (let _153_430 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_153_430))
in (_153_431, [], None))
in (_153_432, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _63_1216 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (

let _63_1245 = (FStar_List.fold_left (fun _63_1221 _63_1230 -> (match ((_63_1221, _63_1230)) with
| ((env, fnames, rec_bindings), ((f, _63_1224, _63_1226), _63_1229)) -> begin
(

let _63_1241 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let _63_1235 = (FStar_Parser_Env.push_bv env x)
in (match (_63_1235) with
| (env, xx) -> begin
(let _153_436 = (let _153_435 = (FStar_Syntax_Syntax.mk_binder xx)
in (_153_435)::rec_bindings)
in (env, FStar_Util.Inl (xx), _153_436))
end))
end
| FStar_Util.Inr (l) -> begin
(let _153_437 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in (_153_437, FStar_Util.Inr (l), rec_bindings))
end)
in (match (_63_1241) with
| (env, lbname, rec_bindings) -> begin
(env, (lbname)::fnames, rec_bindings)
end))
end)) (env, [], []) funs)
in (match (_63_1245) with
| (env', fnames, rec_bindings) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let desugar_one_def = (fun env lbname _63_1256 -> (match (_63_1256) with
| ((_63_1251, args, result_t), def) -> begin
(

let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _153_444 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _153_444 FStar_Parser_AST.Expr))
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| _63_1263 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args def) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (

let body = (desugar_term env def)
in (

let lbname = (match (lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl (x)
end
| FStar_Util.Inr (l) -> begin
(let _153_446 = (let _153_445 = (incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _153_445 None))
in FStar_Util.Inr (_153_446))
end)
in (

let body = if is_rec then begin
(FStar_Syntax_Subst.close rec_bindings body)
end else begin
body
end
in (mk_lb (lbname, FStar_Syntax_Syntax.tun, body)))))))
end))
in (

let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (

let body = (desugar_term env' body)
in (let _153_449 = (let _153_448 = (let _153_447 = (FStar_Syntax_Subst.close rec_bindings body)
in ((is_rec, lbs), _153_447))
in FStar_Syntax_Syntax.Tm_let (_153_448))
in (FStar_All.pipe_left mk _153_449))))))
end))))
end))
in (

let ds_non_rec = (fun pat t1 t2 -> (

let t1 = (desugar_term env t1)
in (

let _63_1282 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_63_1282) with
| (env, binder, pat) -> begin
(match (binder) with
| LetBinder (l, t) -> begin
(

let body = (desugar_term env t2)
in (

let fv = (let _153_456 = (incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _153_456 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]), body))))))
end
| LocalBinder (x, _63_1291) -> begin
(

let body = (desugar_term env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _153_461 = (let _153_460 = (let _153_459 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _153_458 = (let _153_457 = (FStar_Syntax_Util.branch (pat, None, body))
in (_153_457)::[])
in (_153_459, _153_458)))
in FStar_Syntax_Syntax.Tm_match (_153_460))
in (FStar_Syntax_Syntax.mk _153_461 None body.FStar_Syntax_Syntax.pos))
end)
in (let _153_466 = (let _153_465 = (let _153_464 = (let _153_463 = (let _153_462 = (FStar_Syntax_Syntax.mk_binder x)
in (_153_462)::[])
in (FStar_Syntax_Subst.close _153_463 body))
in ((false, ((mk_lb (FStar_Util.Inl (x), x.FStar_Syntax_Syntax.sort, t1)))::[]), _153_464))
in FStar_Syntax_Syntax.Tm_let (_153_465))
in (FStar_All.pipe_left mk _153_466))))
end)
end))))
in if (is_rec || (is_app_pattern pat)) then begin
(ds_let_rec_or_app ())
end else begin
(ds_non_rec pat _snd body)
end))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (let _153_477 = (let _153_476 = (let _153_475 = (desugar_term env t1)
in (let _153_474 = (let _153_473 = (let _153_468 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _153_467 = (desugar_term env t2)
in (_153_468, None, _153_467)))
in (let _153_472 = (let _153_471 = (let _153_470 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _153_469 = (desugar_term env t3)
in (_153_470, None, _153_469)))
in (_153_471)::[])
in (_153_473)::_153_472))
in (_153_475, _153_474)))
in FStar_Syntax_Syntax.Tm_match (_153_476))
in (mk _153_477)))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(

let r = top.FStar_Parser_AST.range
in (

let handler = (FStar_Parser_AST.mk_function branches r r)
in (

let body = (FStar_Parser_AST.mk_function ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r), None, e))::[]) r r)
in (

let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Syntax_Const.try_with_lid)) r top.FStar_Parser_AST.level), body, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (

let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((a1, handler, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (desugar_term env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(

let desugar_branch = (fun _63_1331 -> (match (_63_1331) with
| (pat, wopt, b) -> begin
(

let _63_1334 = (desugar_match_pat env pat)
in (match (_63_1334) with
| (env, pat) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _153_480 = (desugar_term env e)
in Some (_153_480))
end)
in (

let b = (desugar_term env b)
in (FStar_Syntax_Util.branch (pat, wopt, b))))
end))
end))
in (let _153_484 = (let _153_483 = (let _153_482 = (desugar_term env e)
in (let _153_481 = (FStar_List.map desugar_branch branches)
in (_153_482, _153_481)))
in FStar_Syntax_Syntax.Tm_match (_153_483))
in (FStar_All.pipe_left mk _153_484)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(

let env = (FStar_Parser_Env.default_ml env)
in (

let c = (desugar_comp t.FStar_Parser_AST.range true env t)
in (

let annot = if (FStar_Syntax_Util.is_ml_comp c) then begin
FStar_Util.Inl ((FStar_Syntax_Util.comp_result c))
end else begin
FStar_Util.Inr (c)
end
in (let _153_487 = (let _153_486 = (let _153_485 = (desugar_term env e)
in (_153_485, annot, None))
in FStar_Syntax_Syntax.Tm_ascribed (_153_486))
in (FStar_All.pipe_left mk _153_487)))))
end
| FStar_Parser_AST.Record (_63_1348, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let _63_1359 = (FStar_List.hd fields)
in (match (_63_1359) with
| (f, _63_1358) -> begin
(

let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (

let _63_1365 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_63_1365) with
| (record, _63_1364) -> begin
(

let get_field = (fun xopt f -> (

let fn = f.FStar_Ident.ident
in (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _63_1373 -> (match (_63_1373) with
| (g, _63_1372) -> begin
(

let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_63_1377, e) -> begin
(let _153_495 = (qfn fn)
in (_153_495, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _153_498 = (let _153_497 = (let _153_496 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in (_153_496, top.FStar_Parser_AST.range))
in FStar_Syntax_Syntax.Error (_153_497))
in (Prims.raise _153_498))
end
| Some (x) -> begin
(let _153_499 = (qfn fn)
in (_153_499, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (

let recterm = (match (eopt) with
| None -> begin
(let _153_504 = (let _153_503 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _63_1389 -> (match (_63_1389) with
| (f, _63_1388) -> begin
(let _153_502 = (let _153_501 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _153_501))
in (_153_502, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_Env.constrname, _153_503))
in FStar_Parser_AST.Construct (_153_504))
end
| Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (let _153_506 = (let _153_505 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_153_505))
in (FStar_Parser_AST.mk_term _153_506 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = (let _153_509 = (let _153_508 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _63_1397 -> (match (_63_1397) with
| (f, _63_1396) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _153_508))
in FStar_Parser_AST.Record (_153_509))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, None))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _63_1413; FStar_Syntax_Syntax.pos = _63_1411; FStar_Syntax_Syntax.vars = _63_1409}, args); FStar_Syntax_Syntax.tk = _63_1407; FStar_Syntax_Syntax.pos = _63_1405; FStar_Syntax_Syntax.vars = _63_1403}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e = (let _153_517 = (let _153_516 = (let _153_515 = (let _153_514 = (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos)
in (let _153_513 = (let _153_512 = (let _153_511 = (let _153_510 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _153_510))
in FStar_Syntax_Syntax.Record_ctor (_153_511))
in Some (_153_512))
in (FStar_Syntax_Syntax.fvar _153_514 FStar_Syntax_Syntax.Delta_constant _153_513)))
in (_153_515, args))
in FStar_Syntax_Syntax.Tm_app (_153_516))
in (FStar_All.pipe_left mk _153_517))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| _63_1427 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let _63_1434 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_63_1434) with
| (fieldname, is_rec) -> begin
(

let e = (desugar_term env e)
in (

let fn = (

let _63_1439 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_63_1439) with
| (ns, _63_1438) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (

let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (fn))
end else begin
None
end
in (let _153_523 = (let _153_522 = (let _153_521 = (let _153_518 = (FStar_Ident.set_lid_range fieldname (FStar_Ident.range_of_lid f))
in (FStar_Syntax_Syntax.fvar _153_518 FStar_Syntax_Syntax.Delta_equational qual))
in (let _153_520 = (let _153_519 = (FStar_Syntax_Syntax.as_arg e)
in (_153_519)::[])
in (_153_521, _153_520)))
in FStar_Syntax_Syntax.Tm_app (_153_522))
in (FStar_All.pipe_left mk _153_523)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _63_1449 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _63_1451 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _63_1456 -> (match (_63_1456) with
| (a, imp) -> begin
(let _153_527 = (desugar_term env a)
in (arg_withimp_e imp _153_527))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error ((msg, r)))))
in (

let is_requires = (fun _63_1468 -> (match (_63_1468) with
| (t, _63_1467) -> begin
(match ((let _153_535 = (unparen t)
in _153_535.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_63_1470) -> begin
true
end
| _63_1473 -> begin
false
end)
end))
in (

let is_ensures = (fun _63_1478 -> (match (_63_1478) with
| (t, _63_1477) -> begin
(match ((let _153_538 = (unparen t)
in _153_538.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_63_1480) -> begin
true
end
| _63_1483 -> begin
false
end)
end))
in (

let is_app = (fun head _63_1489 -> (match (_63_1489) with
| (t, _63_1488) -> begin
(match ((let _153_543 = (unparen t)
in _153_543.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _63_1493; FStar_Parser_AST.level = _63_1491}, _63_1498, _63_1500) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _63_1504 -> begin
false
end)
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t -> (

let _63_1510 = (head_and_args t)
in (match (_63_1510) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(

let unit_tm = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (

let nil_pat = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr), FStar_Parser_AST.Nothing)
in (

let req_true = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Requires (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.true_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Formula), None))) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (

let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to \'Lemma\'", t.FStar_Parser_AST.range))))
end
| (ens)::[] -> begin
(unit_tm)::(req_true)::(ens)::(nil_pat)::[]
end
| (req)::(ens)::[] when ((is_requires req) && (is_ensures ens)) -> begin
(unit_tm)::(req)::(ens)::(nil_pat)::[]
end
| (ens)::(dec)::[] when ((is_ensures ens) && (is_decreases dec)) -> begin
(unit_tm)::(req_true)::(ens)::(nil_pat)::(dec)::[]
end
| (req)::(ens)::(dec)::[] when (((is_requires req) && (is_ensures ens)) && (is_app "decreases" dec)) -> begin
(unit_tm)::(req)::(ens)::(nil_pat)::(dec)::[]
end
| more -> begin
(unit_tm)::more
end)
in (

let head = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_name env) lemma)
in (head, args))))))
end
| FStar_Parser_AST.Name (l) when (FStar_Parser_Env.is_effect_name env l) -> begin
(let _153_547 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_name env) l)
in (_153_547, args))
end
| FStar_Parser_AST.Name (l) when ((let _153_548 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _153_548 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(let _153_549 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_153_549, args))
end
| FStar_Parser_AST.Name (l) when ((let _153_550 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _153_550 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(let _153_551 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)
in (_153_551, args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(let _153_552 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_153_552, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _63_1541 when default_ok -> begin
(let _153_553 = (FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)
in (_153_553, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _63_1543 -> begin
(let _153_555 = (let _153_554 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _153_554))
in (fail _153_555))
end)
end)))
in (

let _63_1546 = (pre_process_comp_typ t)
in (match (_63_1546) with
| (eff, args) -> begin
(

let _63_1547 = if ((FStar_List.length args) = 0) then begin
(let _153_557 = (let _153_556 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _153_556))
in (fail _153_557))
end else begin
()
end
in (

let _63_1551 = (let _153_559 = (FStar_List.hd args)
in (let _153_558 = (FStar_List.tl args)
in (_153_559, _153_558)))
in (match (_63_1551) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (Prims.fst result_arg))
in (

let rest = (desugar_args env rest)
in (

let _63_1576 = (FStar_All.pipe_right rest (FStar_List.partition (fun _63_1557 -> (match (_63_1557) with
| (t, _63_1556) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _63_1563; FStar_Syntax_Syntax.pos = _63_1561; FStar_Syntax_Syntax.vars = _63_1559}, (_63_1568)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _63_1573 -> begin
false
end)
end))))
in (match (_63_1576) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _63_1580 -> (match (_63_1580) with
| (t, _63_1579) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_63_1582, ((arg, _63_1585))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _63_1591 -> begin
(FStar_All.failwith "impos")
end)
end))))
in (

let no_additional_args = (((FStar_List.length decreases_clause) = 0) && ((FStar_List.length rest) = 0))
in if (no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) then begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end else begin
if (no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) then begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end else begin
(

let flags = if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid) then begin
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
in (

let rest = if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid) then begin
(match (rest) with
| (req)::(ens)::((pat, aq))::[] -> begin
(

let pat = (match (pat.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
(

let nil = (FStar_Syntax_Syntax.mk_Tm_uinst pat ((FStar_Syntax_Syntax.U_succ (FStar_Syntax_Syntax.U_zero))::[]))
in (

let pattern = (let _153_563 = (let _153_562 = (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _153_562 FStar_Syntax_Syntax.Delta_constant None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _153_563 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil (((pattern, Some (FStar_Syntax_Syntax.imp_tag)))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _63_1606 -> begin
pat
end)
in (let _153_567 = (let _153_566 = (let _153_565 = (let _153_564 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((pat, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))) None pat.FStar_Syntax_Syntax.pos)
in (_153_564, aq))
in (_153_565)::[])
in (ens)::_153_566)
in (req)::_153_567))
end
| _63_1609 -> begin
rest
end)
end else begin
rest
end
in (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.effect_name = eff; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = rest; FStar_Syntax_Syntax.flags = (FStar_List.append flags decreases_clause)})))
end
end))
end))))
end)))
end)))))))))
and desugar_formula : env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env f -> (

let connective = (fun s -> (match (s) with
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
| _63_1621 -> begin
None
end))
in (

let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _63_1628 = t
in {FStar_Syntax_Syntax.n = _63_1628.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _63_1628.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _63_1628.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let _63_1635 = b
in {FStar_Parser_AST.b = _63_1635.FStar_Parser_AST.b; FStar_Parser_AST.brange = _63_1635.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _63_1635.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _153_602 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _153_602)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(

let _63_1649 = (FStar_Parser_Env.push_bv env a)
in (match (_63_1649) with
| (env, a) -> begin
(

let a = (

let _63_1650 = a
in {FStar_Syntax_Syntax.ppname = _63_1650.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_1650.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats = (desugar_pats env pats)
in (

let body = (desugar_formula env body)
in (

let body = (match (pats) with
| [] -> begin
body
end
| _63_1657 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((body, FStar_Syntax_Syntax.Meta_pattern (pats)))))
end)
in (

let body = (let _153_605 = (let _153_604 = (let _153_603 = (FStar_Syntax_Syntax.mk_binder a)
in (_153_603)::[])
in (no_annot_abs _153_604 body))
in (FStar_All.pipe_left setpos _153_605))
in (let _153_611 = (let _153_610 = (let _153_609 = (let _153_606 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar _153_606 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (let _153_608 = (let _153_607 = (FStar_Syntax_Syntax.as_arg body)
in (_153_607)::[])
in (_153_609, _153_608)))
in FStar_Syntax_Syntax.Tm_app (_153_610))
in (FStar_All.pipe_left mk _153_611)))))))
end))
end
| _63_1661 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (let _153_626 = (q (rest, pats, body))
in (let _153_625 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _153_626 _153_625 FStar_Parser_AST.Formula)))
in (let _153_627 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _153_627 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _63_1675 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _153_628 = (unparen f)
in _153_628.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(

let f = (desugar_formula env f)
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((l, f.FStar_Syntax_Syntax.pos, p)))))))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _153_630 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _153_630)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _153_632 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _153_632)))
end
| FStar_Parser_AST.QForall ((b)::[], pats, body) -> begin
(desugar_quant FStar_Syntax_Const.forall_lid b pats body)
end
| FStar_Parser_AST.QExists ((b)::[], pats, body) -> begin
(desugar_quant FStar_Syntax_Const.exists_lid b pats body)
end
| FStar_Parser_AST.Paren (f) -> begin
(desugar_formula env f)
end
| _63_1733 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let _63_1757 = (FStar_List.fold_left (fun _63_1738 b -> (match (_63_1738) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let _63_1740 = b
in {FStar_Parser_AST.b = _63_1740.FStar_Parser_AST.b; FStar_Parser_AST.brange = _63_1740.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _63_1740.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(

let _63_1749 = (FStar_Parser_Env.push_bv env a)
in (match (_63_1749) with
| (env, a) -> begin
(

let a = (

let _63_1750 = a
in {FStar_Syntax_Syntax.ppname = _63_1750.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_1750.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (env, ((a, (trans_aqual b.FStar_Parser_AST.aqual)))::out))
end))
end
| _63_1754 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_63_1757) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _153_639 = (desugar_typ env t)
in (Some (x), _153_639))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _153_640 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in (Some (x), _153_640))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _153_641 = (desugar_typ env t)
in (None, _153_641))
end
| FStar_Parser_AST.Variable (x) -> begin
(Some (x), FStar_Syntax_Syntax.tun)
end))


let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  FStar_Ident.lid  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (

let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_Env.iface) || env.FStar_Parser_Env.admitted_iface) then begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (

let binders = (let _153_657 = (let _153_656 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _153_656))
in (FStar_List.append tps _153_657))
in (

let p = (FStar_Ident.range_of_lid t)
in (

let _63_1784 = (FStar_Syntax_Util.args_of_binders binders)
in (match (_63_1784) with
| (binders, args) -> begin
(

let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _63_1788 -> (match (_63_1788) with
| (x, _63_1787) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (

let binders = (let _153_663 = (let _153_662 = (let _153_661 = (let _153_660 = (let _153_659 = (FStar_Syntax_Syntax.lid_as_fv t FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _153_659))
in (FStar_Syntax_Syntax.mk_Tm_app _153_660 args None p))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _153_661))
in (_153_662)::[])
in (FStar_List.append imp_binders _153_663))
in (

let disc_type = (let _153_666 = (let _153_665 = (let _153_664 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _153_664))
in (FStar_Syntax_Syntax.mk_Total _153_665))
in (FStar_Syntax_Util.arrow binders _153_666))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _153_669 = (let _153_668 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in (disc_name, [], disc_type, _153_668, (FStar_Ident.range_of_lid disc_name)))
in FStar_Syntax_Syntax.Sig_declare_typ (_153_669)))))))))
end))))))


let mk_indexed_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq refine_domain env tc lid inductive_tps imp_tps fields t -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (

let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (Some (p)) ptyp))
in (

let tps = (FStar_List.map2 (fun _63_1812 _63_1816 -> (match ((_63_1812, _63_1816)) with
| ((_63_1810, imp), (x, _63_1815)) -> begin
(x, imp)
end)) inductive_tps imp_tps)
in (

let _63_1917 = (

let _63_1820 = (FStar_Syntax_Util.head_and_args t)
in (match (_63_1820) with
| (head, args0) -> begin
(

let args = (

let rec arguments = (fun tps args -> (match ((tps, args)) with
| ([], _63_1826) -> begin
args
end
| (_63_1829, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to type", (FStar_Ident.range_of_lid lid)))))
end
| (((_63_1834, Some (FStar_Syntax_Syntax.Implicit (_63_1836))))::tps', ((_63_1843, Some (FStar_Syntax_Syntax.Implicit (_63_1845))))::args') -> begin
(arguments tps' args')
end
| (((_63_1853, Some (FStar_Syntax_Syntax.Implicit (_63_1855))))::tps', ((_63_1863, _63_1865))::_63_1861) -> begin
(arguments tps' args)
end
| (((_63_1872, _63_1874))::_63_1870, ((a, Some (FStar_Syntax_Syntax.Implicit (_63_1881))))::_63_1878) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected implicit annotation on argument", a.FStar_Syntax_Syntax.pos))))
end
| (((_63_1889, _63_1891))::tps', ((_63_1896, _63_1898))::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (

let indices = (FStar_All.pipe_right args (FStar_List.map (fun _63_1903 -> (let _153_701 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _153_701 FStar_Syntax_Syntax.mk_binder)))))
in (

let arg_typ = (let _153_706 = (let _153_702 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _153_702))
in (let _153_705 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _63_1908 -> (match (_63_1908) with
| (x, imp) -> begin
(let _153_704 = (FStar_Syntax_Syntax.bv_to_name x)
in (_153_704, imp))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _153_706 _153_705 None p)))
in (

let arg_binder = if (not (refine_domain)) then begin
(let _153_707 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _153_707))
end else begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _153_716 = (

let _63_1912 = (projectee arg_typ)
in (let _153_715 = (let _153_714 = (let _153_713 = (let _153_712 = (let _153_708 = (FStar_Ident.set_lid_range disc_name p)
in (FStar_Syntax_Syntax.fvar _153_708 FStar_Syntax_Syntax.Delta_equational None))
in (let _153_711 = (let _153_710 = (let _153_709 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_709))
in (_153_710)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _153_712 _153_711 None p)))
in (FStar_Syntax_Util.b2t _153_713))
in (FStar_Syntax_Util.refine x _153_714))
in {FStar_Syntax_Syntax.ppname = _63_1912.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_1912.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_715}))
in (FStar_Syntax_Syntax.mk_binder _153_716))))
end
in (arg_binder, indices)))))
end))
in (match (_63_1917) with
| (arg_binder, indices) -> begin
(

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (

let imp_binders = (let _153_718 = (FStar_All.pipe_right indices (FStar_List.map (fun _63_1922 -> (match (_63_1922) with
| (x, _63_1921) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (FStar_List.append imp_tps _153_718))
in (

let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (

let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (

let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _63_1930 -> (match (_63_1930) with
| (a, _63_1929) -> begin
(

let _63_1934 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_63_1934) with
| (field_name, _63_1933) -> begin
(

let proj = (let _153_722 = (let _153_721 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _153_721))
in (FStar_Syntax_Syntax.mk_Tm_app _153_722 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT ((a, proj)))
end))
end))))
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (FStar_List.append imp_tps fields)
in (let _153_758 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _63_1943 -> (match (_63_1943) with
| (x, _63_1942) -> begin
(

let _63_1947 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_63_1947) with
| (field_name, _63_1946) -> begin
(

let t = (let _153_726 = (let _153_725 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _153_725))
in (FStar_Syntax_Util.arrow binders _153_726))
in (

let only_decl = (((let _153_727 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _153_727)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _153_729 = (let _153_728 = (FStar_Parser_Env.current_module env)
in _153_728.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _153_729)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> if only_decl then begin
(FStar_Syntax_Syntax.Assumption)::q
end else begin
q
end)
in (

let quals = (quals ((FStar_Syntax_Syntax.Projector ((lid, x.FStar_Syntax_Syntax.ppname)))::iquals))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ ((field_name, [], t, quals, (FStar_Ident.range_of_lid field_name)))
in if only_decl then begin
(decl)::[]
end else begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _63_1959 -> (match (_63_1959) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _153_734 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in (_153_734, b))
end else begin
if (b && (j < ntps)) then begin
(let _153_738 = (let _153_737 = (let _153_736 = (let _153_735 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (_153_735, FStar_Syntax_Syntax.tun))
in FStar_Syntax_Syntax.Pat_dot_term (_153_736))
in (pos _153_737))
in (_153_738, b))
end else begin
(let _153_741 = (let _153_740 = (let _153_739 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_153_739))
in (pos _153_740))
in (_153_741, b))
end
end)
end))))
in (

let pat = (let _153_746 = (let _153_744 = (let _153_743 = (let _153_742 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in (_153_742, arg_pats))
in FStar_Syntax_Syntax.Pat_cons (_153_743))
in (FStar_All.pipe_right _153_744 pos))
in (let _153_745 = (FStar_Syntax_Syntax.bv_to_name projection)
in (_153_746, None, _153_745)))
in (

let body = (let _153_750 = (let _153_749 = (let _153_748 = (let _153_747 = (FStar_Syntax_Util.branch pat)
in (_153_747)::[])
in (arg_exp, _153_748))
in FStar_Syntax_Syntax.Tm_match (_153_749))
in (FStar_Syntax_Syntax.mk _153_750 None p))
in (

let imp = (no_annot_abs binders body)
in (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end else begin
FStar_Syntax_Syntax.Delta_equational
end
in (

let lb = (let _153_752 = (let _153_751 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_153_751))
in {FStar_Syntax_Syntax.lbname = _153_752; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp})
in (

let impl = (let _153_757 = (let _153_756 = (let _153_755 = (let _153_754 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _153_754 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_153_755)::[])
in ((false, (lb)::[]), p, _153_756, quals))
in FStar_Syntax_Syntax.Sig_let (_153_757))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end))))))))
end))))))
end))
end))))
in (FStar_All.pipe_right _153_758 FStar_List.flatten)))))))))
end)))))))


let mk_data_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env _63_1973 -> (match (_63_1973) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _63_1976, t, l, n, quals, _63_1982, _63_1984) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_10 -> (match (_63_10) with
| FStar_Syntax_Syntax.RecordConstructor (_63_1989) -> begin
true
end
| _63_1992 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _63_1996 -> begin
true
end)
end
in (

let _63_2000 = (FStar_Syntax_Util.arrow_formals t)
in (match (_63_2000) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _63_2003 -> begin
(

let fv_qual = (match ((FStar_Util.find_map quals (fun _63_11 -> (match (_63_11) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((lid, fns)))
end
| _63_2008 -> begin
None
end)))) with
| None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)
in (

let iquals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract iquals) then begin
(FStar_Syntax_Syntax.Private)::iquals
end else begin
iquals
end
in (

let _63_2016 = (FStar_Util.first_N n formals)
in (match (_63_2016) with
| (tps, rest) -> begin
(mk_indexed_projectors iquals fv_qual refine_domain env l lid inductive_tps tps rest cod)
end))))
end)
end)))
end
| _63_2018 -> begin
[]
end)
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _153_783 = (incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (_153_783))
end else begin
(incr_delta_qualifier t)
end
in (

let lb = (let _153_788 = (let _153_784 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (_153_784))
in (let _153_787 = (let _153_785 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _153_785))
in (let _153_786 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _153_788; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _153_787; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _153_786})))
in FStar_Syntax_Syntax.Sig_let (((false, (lb)::[]), rng, lids, quals)))))


let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (

let tycon_id = (fun _63_12 -> (match (_63_12) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _153_802 = (let _153_801 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_153_801))
in (FStar_Parser_AST.mk_term _153_802 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (

let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (

let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((tot, t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (

let apply_binders = (fun t binders -> (

let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _63_2093 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _153_815 = (let _153_814 = (let _153_813 = (binder_to_term b)
in (out, _153_813, (imp_of_aqual b)))
in FStar_Parser_AST.App (_153_814))
in (FStar_Parser_AST.mk_term _153_815 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun _63_13 -> (match (_63_13) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (

let mfields = (FStar_List.map (fun _63_2106 -> (match (_63_2106) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Syntax_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (let _153_821 = (let _153_820 = (let _153_819 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_153_819))
in (FStar_Parser_AST.mk_term _153_820 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _153_821 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _153_823 = (FStar_All.pipe_right fields (FStar_List.map (fun _63_2113 -> (match (_63_2113) with
| (x, _63_2112) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _153_823))))))
end
| _63_2115 -> begin
(FStar_All.failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals _63_14 -> (match (_63_14) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let _63_2129 = (typars_of_binders _env binders)
in (match (_63_2129) with
| (_env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
FStar_Syntax_Util.ktype
end
| Some (k) -> begin
(desugar_term _env' k)
end)
in (

let tconstr = (let _153_834 = (let _153_833 = (let _153_832 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_153_832))
in (FStar_Parser_AST.mk_term _153_833 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _153_834 binders))
in (

let qlid = (FStar_Parser_Env.qualify _env id)
in (

let typars = (FStar_Syntax_Subst.close_binders typars)
in (

let k = (FStar_Syntax_Subst.close typars k)
in (

let se = FStar_Syntax_Syntax.Sig_inductive_typ ((qlid, [], typars, k, mutuals, [], quals, rng))
in (

let _env = (FStar_Parser_Env.push_top_level_rec_binding _env id FStar_Syntax_Syntax.Delta_constant)
in (

let _env2 = (FStar_Parser_Env.push_top_level_rec_binding _env' id FStar_Syntax_Syntax.Delta_constant)
in (_env, _env2, se, tconstr)))))))))
end))
end
| _63_2142 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env bs -> (

let _63_2157 = (FStar_List.fold_left (fun _63_2148 _63_2151 -> (match ((_63_2148, _63_2151)) with
| ((env, tps), (x, imp)) -> begin
(

let _63_2154 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_63_2154) with
| (env, y) -> begin
(env, ((y, imp))::tps)
end))
end)) (env, []) bs)
in (match (_63_2157) with
| (env, bs) -> begin
(env, (FStar_List.rev bs))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt = (match (kopt) with
| None -> begin
(let _153_841 = (tm_type_z id.FStar_Ident.idRange)
in Some (_153_841))
end
| _63_2166 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract ((id, bs, kopt))
in (

let _63_2176 = (desugar_abstract_tc quals env [] tc)
in (match (_63_2176) with
| (_63_2170, _63_2172, se, _63_2175) -> begin
(

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _63_2179, typars, k, [], [], quals, rng) -> begin
(

let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(

let _63_2188 = (let _153_843 = (FStar_Range.string_of_range rng)
in (let _153_842 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _153_843 _153_842)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (

let t = (match (typars) with
| [] -> begin
k
end
| _63_2193 -> begin
(let _153_846 = (let _153_845 = (let _153_844 = (FStar_Syntax_Syntax.mk_Total k)
in (typars, _153_844))
in FStar_Syntax_Syntax.Tm_arrow (_153_845))
in (FStar_Syntax_Syntax.mk _153_846 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ ((l, [], t, quals, rng))))
end
| _63_2196 -> begin
se
end)
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let _63_2208 = (typars_of_binders env binders)
in (match (_63_2208) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _63_15 -> (match (_63_15) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _63_2213 -> begin
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
in (

let t0 = t
in (

let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_16 -> (match (_63_16) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _63_2221 -> begin
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
in (

let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Effect)) then begin
(

let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (

let typars = (FStar_Syntax_Subst.close_binders typars)
in (

let c = (FStar_Syntax_Subst.close_comp typars c)
in (let _153_852 = (let _153_851 = (FStar_Parser_Env.qualify env id)
in (let _153_850 = (FStar_All.pipe_right quals (FStar_List.filter (fun _63_17 -> (match (_63_17) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _63_2229 -> begin
true
end))))
in (_153_851, [], typars, c, _153_850, rng)))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_153_852)))))
end else begin
(

let t = (desugar_typ env' t)
in (

let nm = (FStar_Parser_Env.qualify env id)
in (mk_typ_abbrev nm [] typars k t ((nm)::[]) quals rng)))
end
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| (FStar_Parser_AST.TyconRecord (_63_2235))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let _63_2241 = (tycon_record_as_variant trec)
in (match (_63_2241) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| (_63_2245)::_63_2243 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let _63_2256 = et
in (match (_63_2256) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_63_2258) -> begin
(

let trec = tc
in (

let _63_2263 = (tycon_record_as_variant trec)
in (match (_63_2263) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let _63_2275 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_63_2275) with
| (env, _63_2272, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let _63_2287 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_63_2287) with
| (env, _63_2284, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _63_2289 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (

let _63_2292 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_63_2292) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _63_19 -> (match (_63_19) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _63_2300, _63_2302, _63_2304, _63_2306), t, quals) -> begin
(

let _63_2316 = (push_tparams env tpars)
in (match (_63_2316) with
| (env_tps, _63_2315) -> begin
(

let t = (desugar_term env_tps t)
in (let _153_862 = (let _153_861 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in ([], _153_861))
in (_153_862)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _63_2324, tags, _63_2327), constrs, tconstr, quals) -> begin
(

let tycon = (tname, tpars, k)
in (

let _63_2338 = (push_tparams env tpars)
in (match (_63_2338) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun _63_2342 -> (match (_63_2342) with
| (x, _63_2341) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end)) tps)
in (

let _63_2366 = (let _153_874 = (FStar_All.pipe_right constrs (FStar_List.map (fun _63_2347 -> (match (_63_2347) with
| (id, topt, of_notation) -> begin
(

let t = if of_notation then begin
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
in (

let t = (let _153_866 = (FStar_Parser_Env.default_total env_tps)
in (let _153_865 = (close env_tps t)
in (desugar_term _153_866 _153_865)))
in (

let name = (FStar_Parser_Env.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _63_18 -> (match (_63_18) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _63_2361 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (let _153_873 = (let _153_872 = (let _153_871 = (let _153_870 = (let _153_869 = (let _153_868 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _153_868))
in (FStar_Syntax_Util.arrow data_tpars _153_869))
in (name, univs, _153_870, tname, ntps, quals, mutuals, rng))
in FStar_Syntax_Syntax.Sig_datacon (_153_871))
in (tps, _153_872))
in (name, _153_873)))))))
end))))
in (FStar_All.pipe_left FStar_List.split _153_874))
in (match (_63_2366) with
| (constrNames, constrs) -> begin
(([], FStar_Syntax_Syntax.Sig_inductive_typ ((tname, univs, tpars, k, mutuals, constrNames, tags, rng))))::constrs
end)))
end)))
end
| _63_2368 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (

let bundle = (let _153_876 = (let _153_875 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _153_875, rng))
in FStar_Syntax_Syntax.Sig_bundle (_153_876))
in (

let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (

let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors quals env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _63_20 -> (match (_63_20) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _63_2377, tps, k, _63_2381, constrs, quals, _63_2385) when ((FStar_List.length constrs) > 1) -> begin
(

let quals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract quals) then begin
(FStar_Syntax_Syntax.Private)::quals
end else begin
quals
end
in (mk_data_discriminators quals env tname tps k constrs))
end
| _63_2390 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env ops)
in (env, (FStar_List.append ((bundle)::[]) ops)))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end))))))))))


let desugar_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (

let _63_2414 = (FStar_List.fold_left (fun _63_2399 b -> (match (_63_2399) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(

let _63_2407 = (FStar_Parser_Env.push_bv env a)
in (match (_63_2407) with
| (env, a) -> begin
(let _153_885 = (let _153_884 = (FStar_Syntax_Syntax.mk_binder (

let _63_2408 = a
in {FStar_Syntax_Syntax.ppname = _63_2408.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_2408.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_153_884)::binders)
in (env, _153_885))
end))
end
| _63_2411 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_63_2414) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))


let rec desugar_effect : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (Prims.string  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term))  ->  FStar_Syntax_Syntax.sigelt)  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_kind eff_decls mk -> (

let env0 = env
in (

let env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (

let _63_2427 = (desugar_binders env eff_binders)
in (match (_63_2427) with
| (env, binders) -> begin
(

let eff_k = (let _153_937 = (FStar_Parser_Env.default_total env)
in (desugar_term _153_937 eff_kind))
in (

let _63_2438 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _63_2431 decl -> (match (_63_2431) with
| (env, out) -> begin
(

let _63_2435 = (desugar_decl env decl)
in (match (_63_2435) with
| (env, ses) -> begin
(let _153_941 = (let _153_940 = (FStar_List.hd ses)
in (_153_940)::out)
in (env, _153_941))
end))
end)) (env, [])))
in (match (_63_2438) with
| (env, decls) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (

let lookup = (fun s -> (

let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident (s, d.FStar_Parser_AST.drange)))
in (let _153_945 = (let _153_944 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _153_944))
in ([], _153_945))))
in (

let mname = (FStar_Parser_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange) quals)
in (

let se = (mk mname qualifiers binders eff_k lookup)
in (

let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[]))))))))
end)))
end)))))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let trans_qual = (trans_qual d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(

let se = FStar_Syntax_Syntax.Sig_pragma (((trans_pragma p), d.FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| FStar_Parser_AST.TopLevelModule (_63_2455) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Multiple modules in a file are no longer supported", d.FStar_Parser_AST.drange))))
end
| FStar_Parser_AST.Open (lid) -> begin
(

let env = (FStar_Parser_Env.push_namespace env lid)
in (env, []))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _153_949 = (FStar_Parser_Env.push_module_abbrev env x l)
in (_153_949, []))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _153_950 = (FStar_List.map trans_qual qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _153_950 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _153_952 = (let _153_951 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _153_951))
in _153_952.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _63_2475) -> begin
(

let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals = (match (quals) with
| (_63_2483)::_63_2481 -> begin
(FStar_List.map trans_qual quals)
end
| _63_2486 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _63_21 -> (match (_63_21) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_63_2497); FStar_Syntax_Syntax.lbunivs = _63_2495; FStar_Syntax_Syntax.lbtyp = _63_2493; FStar_Syntax_Syntax.lbeff = _63_2491; FStar_Syntax_Syntax.lbdef = _63_2489} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _63_2507; FStar_Syntax_Syntax.lbtyp = _63_2505; FStar_Syntax_Syntax.lbeff = _63_2503; FStar_Syntax_Syntax.lbdef = _63_2501} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _63_2515 -> (match (_63_2515) with
| (_63_2513, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (

let lbs = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _153_957 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _63_2519 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let _63_2521 = fv
in {FStar_Syntax_Syntax.fv_name = _63_2521.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = _63_2521.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = _63_2519.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _63_2519.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _63_2519.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _63_2519.FStar_Syntax_Syntax.lbdef})))))
in ((Prims.fst lbs), _153_957))
end else begin
lbs
end
in (

let s = (let _153_960 = (let _153_959 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (lbs, d.FStar_Parser_AST.drange, _153_959, quals))
in FStar_Syntax_Syntax.Sig_let (_153_960))
in (

let env = (FStar_Parser_Env.push_sigelt env s)
in (env, (s)::[])))))))
end
| _63_2528 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(

let e = (desugar_term env t)
in (

let se = FStar_Syntax_Syntax.Sig_main ((e, d.FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(

let f = (desugar_formula env t)
in (let _153_964 = (let _153_963 = (let _153_962 = (let _153_961 = (FStar_Parser_Env.qualify env id)
in (_153_961, f, (FStar_Syntax_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_assume (_153_962))
in (_153_963)::[])
in (env, _153_964)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(

let t = (let _153_965 = (close_fun env t)
in (desugar_term env _153_965))
in (

let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (

let se = (let _153_968 = (let _153_967 = (FStar_Parser_Env.qualify env id)
in (let _153_966 = (FStar_List.map trans_qual quals)
in (_153_967, [], t, _153_966, d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_declare_typ (_153_968))
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(

let t = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (

let l = (FStar_Parser_Env.qualify env id)
in (

let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (

let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (

let env = (FStar_Parser_Env.push_sigelt env se')
in (

let data_ops = (mk_data_projectors [] env ([], se))
in (

let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (

let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(

let t = (desugar_term env term)
in (

let t = (let _153_972 = (let _153_969 = (FStar_Syntax_Syntax.null_binder t)
in (_153_969)::[])
in (let _153_971 = (let _153_970 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _153_970))
in (FStar_Syntax_Util.arrow _153_972 _153_971)))
in (

let l = (FStar_Parser_Env.qualify env id)
in (

let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (

let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (

let env = (FStar_Parser_Env.push_sigelt env se')
in (

let data_ops = (mk_data_projectors [] env ([], se))
in (

let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (

let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(

let _63_2581 = (desugar_binders env binders)
in (match (_63_2581) with
| (env_k, binders) -> begin
(

let k = (desugar_term env_k k)
in (

let name = (FStar_Parser_Env.qualify env id)
in (

let se = (mk_typ_abbrev name [] binders FStar_Syntax_Syntax.tun k ((name)::[]) [] d.FStar_Parser_AST.drange)
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(

let env0 = env
in (

let _63_2597 = (desugar_binders env eff_binders)
in (match (_63_2597) with
| (env, binders) -> begin
(

let _63_2608 = (

let _63_2600 = (head_and_args defn)
in (match (_63_2600) with
| (head, args) -> begin
(

let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _63_2604 -> begin
(let _153_977 = (let _153_976 = (let _153_975 = (let _153_974 = (let _153_973 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat "Effect " _153_973))
in (Prims.strcat _153_974 " not found"))
in (_153_975, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_153_976))
in (Prims.raise _153_977))
end)
in (let _153_978 = (desugar_args env args)
in (ed, _153_978)))
end))
in (match (_63_2608) with
| (ed, args) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let sub = (fun _63_2614 -> (match (_63_2614) with
| (_63_2612, x) -> begin
(

let _63_2617 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_63_2617) with
| (edb, x) -> begin
(

let _63_2618 = if ((FStar_List.length args) <> (FStar_List.length edb)) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected number of arguments to effect constructor", defn.FStar_Parser_AST.range))))
end else begin
()
end
in (

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _153_982 = (let _153_981 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _153_981))
in ([], _153_982))))
end))
end))
in (

let ed = (let _153_996 = (FStar_List.map trans_qual quals)
in (let _153_995 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _153_994 = (let _153_983 = (sub ([], ed.FStar_Syntax_Syntax.signature))
in (Prims.snd _153_983))
in (let _153_993 = (sub ed.FStar_Syntax_Syntax.ret)
in (let _153_992 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _153_991 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _153_990 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _153_989 = (sub ed.FStar_Syntax_Syntax.stronger)
in (let _153_988 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _153_987 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _153_986 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _153_985 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _153_984 = (sub ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _153_996; FStar_Syntax_Syntax.mname = _153_995; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _153_994; FStar_Syntax_Syntax.ret = _153_993; FStar_Syntax_Syntax.bind_wp = _153_992; FStar_Syntax_Syntax.if_then_else = _153_991; FStar_Syntax_Syntax.ite_wp = _153_990; FStar_Syntax_Syntax.stronger = _153_989; FStar_Syntax_Syntax.close_wp = _153_988; FStar_Syntax_Syntax.assert_p = _153_987; FStar_Syntax_Syntax.assume_p = _153_986; FStar_Syntax_Syntax.null_wp = _153_985; FStar_Syntax_Syntax.trivial = _153_984})))))))))))))
in (

let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (

let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[]))))))
end))
end)))
end
| FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.RedefineEffect (_63_2625)) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(desugar_effect env d [] eff_name eff_binders eff_kind eff_decls (fun mname qualifiers binders eff_k lookup -> (

let dummy_tscheme = (let _153_1006 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in ([], _153_1006))
in (let _153_1013 = (let _153_1012 = (let _153_1011 = (lookup "return")
in (let _153_1010 = (lookup "bind_wp")
in (let _153_1009 = (lookup "ite_wp")
in (let _153_1008 = (lookup "stronger")
in (let _153_1007 = (lookup "null_wp")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret = _153_1011; FStar_Syntax_Syntax.bind_wp = _153_1010; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = _153_1009; FStar_Syntax_Syntax.stronger = _153_1008; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = _153_1007; FStar_Syntax_Syntax.trivial = dummy_tscheme})))))
in (_153_1012, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (_153_1013)))))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(desugar_effect env d quals eff_name eff_binders eff_kind eff_decls (fun mname qualifiers binders eff_k lookup -> (let _153_1034 = (let _153_1033 = (let _153_1032 = (lookup "return")
in (let _153_1031 = (lookup "bind_wp")
in (let _153_1030 = (lookup "if_then_else")
in (let _153_1029 = (lookup "ite_wp")
in (let _153_1028 = (lookup "stronger")
in (let _153_1027 = (lookup "close_wp")
in (let _153_1026 = (lookup "assert_p")
in (let _153_1025 = (lookup "assume_p")
in (let _153_1024 = (lookup "null_wp")
in (let _153_1023 = (lookup "trivial")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret = _153_1032; FStar_Syntax_Syntax.bind_wp = _153_1031; FStar_Syntax_Syntax.if_then_else = _153_1030; FStar_Syntax_Syntax.ite_wp = _153_1029; FStar_Syntax_Syntax.stronger = _153_1028; FStar_Syntax_Syntax.close_wp = _153_1027; FStar_Syntax_Syntax.assert_p = _153_1026; FStar_Syntax_Syntax.assume_p = _153_1025; FStar_Syntax_Syntax.null_wp = _153_1024; FStar_Syntax_Syntax.trivial = _153_1023}))))))))))
in (_153_1033, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_new_effect (_153_1034))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(

let lookup = (fun l -> (match ((FStar_Parser_Env.try_lookup_effect_name env l)) with
| None -> begin
(let _153_1041 = (let _153_1040 = (let _153_1039 = (let _153_1038 = (let _153_1037 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat "Effect name " _153_1037))
in (Prims.strcat _153_1038 " not found"))
in (_153_1039, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_153_1040))
in (Prims.raise _153_1041))
end
| Some (l) -> begin
l
end))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let lift = (let _153_1042 = (desugar_term env l.FStar_Parser_AST.lift_op)
in ([], _153_1042))
in (

let se = FStar_Syntax_Syntax.Sig_sub_effect (({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end)))


let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _63_2670 d -> (match (_63_2670) with
| (env, sigelts) -> begin
(

let _63_2674 = (desugar_decl env d)
in (match (_63_2674) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))


let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]


let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_Env.finish_module_or_interface env prev_mod)
end)
in (

let _63_2697 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _153_1055 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in (_153_1055, mname, decls, true))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _153_1056 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in (_153_1056, mname, decls, false))
end)
in (match (_63_2697) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let _63_2700 = (desugar_decls env decls)
in (match (_63_2700) with
| (env, sigelts) -> begin
(

let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in (env, modul, pop_when_done))
end))
end))))


let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (

let m = if (FStar_Options.interactive_fsi ()) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface ((mname, decls, true))
end
| FStar_Parser_AST.Interface (mname, _63_2711, _63_2713) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (

let _63_2721 = (desugar_modul_common curmod env m)
in (match (_63_2721) with
| (x, y, _63_2720) -> begin
(x, y)
end))))


let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (

let _63_2727 = (desugar_modul_common None env m)
in (match (_63_2727) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (

let _63_2729 = if (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _153_1067 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _153_1067))
end else begin
()
end
in (let _153_1068 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in (_153_1068, modul))))
end)))


let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (

let _63_2742 = (FStar_List.fold_left (fun _63_2735 m -> (match (_63_2735) with
| (env, mods) -> begin
(

let _63_2739 = (desugar_modul env m)
in (match (_63_2739) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_63_2742) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (

let _63_2747 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_63_2747) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (

let _63_2748 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.modules = _63_2748.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _63_2748.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _63_2748.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _63_2748.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _63_2748.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _63_2748.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _63_2748.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _63_2748.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _63_2748.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _63_2748.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _63_2748.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (

let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




