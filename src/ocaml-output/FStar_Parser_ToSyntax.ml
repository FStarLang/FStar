
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
Some ((Prims.fst t))
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
| (FStar_Parser_AST.Assign (_, t)) | (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_63_296, ts) -> begin
(FStar_List.collect (fun _63_303 -> (match (_63_303) with
| (t, _63_302) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_63_305, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _63_312) -> begin
(let _153_98 = (free_type_vars env t1)
in (let _153_97 = (free_type_vars env t2)
in (FStar_List.append _153_98 _153_97)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(

let _63_321 = (free_type_vars_b env b)
in (match (_63_321) with
| (env, f) -> begin
(let _153_99 = (free_type_vars env t)
in (FStar_List.append f _153_99))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(

let _63_337 = (FStar_List.fold_left (fun _63_330 binder -> (match (_63_330) with
| (env, free) -> begin
(

let _63_334 = (free_type_vars_b env binder)
in (match (_63_334) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_63_337) with
| (env, free) -> begin
(let _153_102 = (free_type_vars env body)
in (FStar_List.append free _153_102))
end))
end
| FStar_Parser_AST.Project (t, _63_340) -> begin
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
| _63_384 -> begin
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
| FStar_Parser_AST.Product (_63_397) -> begin
t
end
| _63_400 -> begin
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
| _63_410 -> begin
(bs, t)
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _63_414) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_63_420); FStar_Parser_AST.prange = _63_418}, _63_424) -> begin
true
end
| _63_428 -> begin
false
end))


let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _63_440 = (destruct_app_pattern env is_top_level p)
in (match (_63_440) with
| (name, args, _63_439) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _63_445); FStar_Parser_AST.prange = _63_442}, args) when is_top_level -> begin
(let _153_142 = (let _153_141 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_153_141))
in (_153_142, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _63_456); FStar_Parser_AST.prange = _63_453}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _63_464 -> begin
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
| LocalBinder (_63_467) -> begin
_63_467
end))


let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_63_470) -> begin
_63_470
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _63_6 -> (match (_63_6) with
| LocalBinder (a, aq) -> begin
(a, aq)
end
| _63_477 -> begin
(FStar_All.failwith "Impossible")
end))


let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _63_7 -> (match (_63_7) with
| (None, k) -> begin
(let _153_179 = (FStar_Syntax_Syntax.null_binder k)
in (_153_179, env))
end
| (Some (a), k) -> begin
(

let _63_490 = (FStar_Parser_Env.push_bv env a)
in (match (_63_490) with
| (env, a) -> begin
(((

let _63_491 = a
in {FStar_Syntax_Syntax.ppname = _63_491.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_491.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}), (trans_aqual imp)), env)
end))
end))


type env_t =
FStar_Parser_Env.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _63_496 -> (match (_63_496) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))


let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))


let mk_ref_read = (fun tm -> (

let tm' = (let _153_192 = (let _153_191 = (let _153_187 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.read_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _153_187))
in (let _153_190 = (let _153_189 = (let _153_188 = (FStar_Syntax_Syntax.as_implicit false)
in (tm, _153_188))
in (_153_189)::[])
in (_153_191, _153_190)))
in FStar_Syntax_Syntax.Tm_app (_153_192))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc = (fun tm -> (

let tm' = (let _153_199 = (let _153_198 = (let _153_194 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.alloc_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _153_194))
in (let _153_197 = (let _153_196 = (let _153_195 = (FStar_Syntax_Syntax.as_implicit false)
in (tm, _153_195))
in (_153_196)::[])
in (_153_198, _153_197)))
in FStar_Syntax_Syntax.Tm_app (_153_199))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign = (fun t1 t2 pos -> (

let tm = (let _153_211 = (let _153_210 = (let _153_203 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.write_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _153_203))
in (let _153_209 = (let _153_208 = (let _153_204 = (FStar_Syntax_Syntax.as_implicit false)
in (t1, _153_204))
in (let _153_207 = (let _153_206 = (let _153_205 = (FStar_Syntax_Syntax.as_implicit false)
in (t2, _153_205))
in (_153_206)::[])
in (_153_208)::_153_207))
in (_153_210, _153_209)))
in FStar_Syntax_Syntax.Tm_app (_153_211))
in (FStar_Syntax_Syntax.mk tm None pos)))


let rec desugar_data_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat) = (fun env p is_mut -> (

let check_linear_pattern_variables = (fun p -> (

let rec pat_vars = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_dot_term (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_constant (_)) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (_63_526, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _63_534 -> (match (_63_534) with
| (p, _63_533) -> begin
(let _153_254 = (pat_vars p)
in (FStar_Util.set_union out _153_254))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj (hd::tl) -> begin
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

let _63_557 = (match ((is_mut, p.FStar_Parser_AST.pat)) with
| ((false, _)) | ((true, FStar_Parser_AST.PatVar (_))) -> begin
()
end
| (true, _63_555) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("let-mutable is for variables only", p.FStar_Parser_AST.prange))))
end)
in (

let push_bv_maybe_mut = if is_mut then begin
FStar_Parser_Env.push_bv_mutable
end else begin
FStar_Parser_Env.push_bv
end
in (

let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))) with
| Some (y) -> begin
(l, e, y)
end
| _63_568 -> begin
(

let _63_571 = (push_bv_maybe_mut e x)
in (match (_63_571) with
| (e, x) -> begin
((x)::l, e, x)
end))
end))
in (

let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun b -> (b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText))))) with
| Some (b) -> begin
(l, e, b)
end
| _63_580 -> begin
(

let _63_583 = (push_bv_maybe_mut e a)
in (match (_63_583) with
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
| FStar_Parser_AST.PatOr (p::ps) -> begin
(

let _63_605 = (aux loc env p)
in (match (_63_605) with
| (loc, env, var, p, _63_604) -> begin
(

let _63_622 = (FStar_List.fold_left (fun _63_609 p -> (match (_63_609) with
| (loc, env, ps) -> begin
(

let _63_618 = (aux loc env p)
in (match (_63_618) with
| (loc, env, _63_614, p, _63_617) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_63_622) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (loc, env, var, pat, false))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _63_633 = (aux loc env p)
in (match (_63_633) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (_63_635) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t = (let _153_288 = (close_fun env t)
in (desugar_term env _153_288))
in LocalBinder (((

let _63_642 = x
in {FStar_Syntax_Syntax.ppname = _63_642.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_642.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), aq)))
end)
in (loc, env', binder, p, imp))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _153_289 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in (loc, env, LocalBinder ((x, None)), _153_289, false)))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _153_290 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in (loc, env, LocalBinder ((x, None)), _153_290, false)))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let _63_661 = (resolvex loc env x)
in (match (_63_661) with
| (loc, env, xbv) -> begin
(let _153_291 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in (loc, env, LocalBinder ((xbv, aq)), _153_291, imp))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _153_292 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, []))))
in (loc, env, LocalBinder ((x, None)), _153_292, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _63_667}, args) -> begin
(

let _63_689 = (FStar_List.fold_right (fun arg _63_678 -> (match (_63_678) with
| (loc, env, args) -> begin
(

let _63_685 = (aux loc env arg)
in (match (_63_685) with
| (loc, env, _63_682, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_63_689) with
| (loc, env, args) -> begin
(

let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _153_295 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _153_295, false))))
end))
end
| FStar_Parser_AST.PatApp (_63_693) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let _63_713 = (FStar_List.fold_right (fun pat _63_701 -> (match (_63_701) with
| (loc, env, pats) -> begin
(

let _63_709 = (aux loc env pat)
in (match (_63_709) with
| (loc, env, _63_705, pat, _63_708) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_63_713) with
| (loc, env, pats) -> begin
(

let pat = (let _153_308 = (let _153_307 = (let _153_303 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _153_303))
in (let _153_306 = (let _153_305 = (let _153_304 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_153_304, []))
in FStar_Syntax_Syntax.Pat_cons (_153_305))
in (FStar_All.pipe_left _153_307 _153_306)))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _153_302 = (let _153_301 = (let _153_300 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_153_300, ((hd, false))::((tl, false))::[]))
in FStar_Syntax_Syntax.Pat_cons (_153_301))
in (FStar_All.pipe_left (pos_r r) _153_302)))) pats _153_308))
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (loc, env, LocalBinder ((x, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let _63_739 = (FStar_List.fold_left (fun _63_726 p -> (match (_63_726) with
| (loc, env, pats) -> begin
(

let _63_735 = (aux loc env p)
in (match (_63_735) with
| (loc, env, _63_731, pat, _63_734) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_63_739) with
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

let _63_745 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (match (_63_745) with
| (constr, _63_744) -> begin
(

let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| _63_749 -> begin
(FStar_All.failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _153_311 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _153_311, false))))
end))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let _63_759 = (FStar_List.hd fields)
in (match (_63_759) with
| (f, _63_758) -> begin
(

let _63_763 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_63_763) with
| (record, _63_762) -> begin
(

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _63_766 -> (match (_63_766) with
| (f, p) -> begin
(let _153_313 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.qualify_field_to_record env record) f)
in (_153_313, p))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _63_771 -> (match (_63_771) with
| (f, _63_770) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _63_775 -> (match (_63_775) with
| (g, _63_774) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_63_778, p) -> begin
p
end)
end))))
in (

let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (

let _63_790 = (aux loc env app)
in (match (_63_790) with
| (env, e, b, p, _63_789) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _153_322 = (let _153_321 = (let _153_320 = (

let _63_795 = fv
in (let _153_319 = (let _153_318 = (let _153_317 = (let _153_316 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _153_316))
in FStar_Syntax_Syntax.Record_ctor (_153_317))
in Some (_153_318))
in {FStar_Syntax_Syntax.fv_name = _63_795.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _63_795.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _153_319}))
in (_153_320, args))
in FStar_Syntax_Syntax.Pat_cons (_153_321))
in (FStar_All.pipe_left pos _153_322))
end
| _63_798 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (

let _63_807 = (aux [] env p)
in (match (_63_807) with
| (_63_801, env, b, p, _63_806) -> begin
(

let _63_808 = (let _153_323 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _153_323))
in (env, b, p))
end)))))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p is_mut -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _63_816) -> begin
(let _153_330 = (let _153_329 = (let _153_328 = (FStar_Parser_Env.qualify env x)
in (_153_328, FStar_Syntax_Syntax.tun))
in LetBinder (_153_329))
in (env, _153_330, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _63_823); FStar_Parser_AST.prange = _63_820}, t) -> begin
(let _153_334 = (let _153_333 = (let _153_332 = (FStar_Parser_Env.qualify env x)
in (let _153_331 = (desugar_term env t)
in (_153_332, _153_331)))
in LetBinder (_153_333))
in (env, _153_334, None))
end
| _63_831 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(

let _63_835 = (desugar_data_pat env p is_mut)
in (match (_63_835) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _63_843 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _63_847 env pat -> (

let _63_855 = (desugar_data_pat env pat false)
in (match (_63_855) with
| (env, _63_853, pat) -> begin
(env, pat)
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _63_860 = env
in {FStar_Parser_Env.curmodule = _63_860.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _63_860.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _63_860.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _63_860.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _63_860.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _63_860.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _63_860.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _63_860.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _63_860.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _63_860.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _63_860.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _63_865 = env
in {FStar_Parser_Env.curmodule = _63_865.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _63_865.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _63_865.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _63_865.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _63_865.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _63_865.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _63_865.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _63_865.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _63_865.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _63_865.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _63_865.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let _63_875 = e
in {FStar_Syntax_Syntax.n = _63_875.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _63_875.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _63_875.FStar_Syntax_Syntax.vars}))
in (match ((let _153_353 = (unparen top)
in _153_353.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_63_879) -> begin
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
| FStar_Parser_AST.Op ("*", _63_899::_63_897::[]) when (let _153_354 = (op_as_term env 2 top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _153_354 FStar_Option.isNone)) -> begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(

let rest = (flatten t2)
in (t1)::rest)
end
| _63_913 -> begin
(t)::[]
end))
in (

let targs = (let _153_360 = (let _153_357 = (unparen top)
in (flatten _153_357))
in (FStar_All.pipe_right _153_360 (FStar_List.map (fun t -> (let _153_359 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _153_359))))))
in (

let _63_919 = (let _153_361 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _153_361))
in (match (_63_919) with
| (tup, _63_918) -> begin
(mk (FStar_Syntax_Syntax.Tm_app ((tup, targs))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _153_363 = (let _153_362 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (Prims.fst _153_362))
in (FStar_All.pipe_left setpos _153_363))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Unexpected operator: " s), top.FStar_Parser_AST.range))))
end
| Some (op) -> begin
(

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _153_365 = (desugar_term env t)
in (_153_365, None)))))
in (mk (FStar_Syntax_Syntax.Tm_app ((op, args)))))
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _63_937; FStar_Ident.ident = _63_935; FStar_Ident.nsstr = _63_933; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _63_946; FStar_Ident.ident = _63_944; FStar_Ident.nsstr = _63_942; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _63_955; FStar_Ident.ident = _63_953; FStar_Ident.nsstr = _63_951; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _63_964; FStar_Ident.ident = _63_962; FStar_Ident.nsstr = _63_960; FStar_Ident.str = "True"}) -> begin
(let _153_366 = (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _153_366 FStar_Syntax_Syntax.Delta_constant None))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _63_973; FStar_Ident.ident = _63_971; FStar_Ident.nsstr = _63_969; FStar_Ident.str = "False"}) -> begin
(let _153_367 = (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _153_367 FStar_Syntax_Syntax.Delta_constant None))
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t2 = (desugar_term env t2)
in (

let _63_983 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) ident)
in (match (_63_983) with
| (t1, mut) -> begin
(

let _63_984 = if (not (mut)) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Can only assign to mutable values", top.FStar_Parser_AST.range))))
end else begin
()
end
in (mk_ref_assign t1 t2 top.FStar_Parser_AST.range))
end)))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(

let _63_991 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (match (_63_991) with
| (tm, mut) -> begin
(

let tm = (setpos tm)
in if mut then begin
(let _153_370 = (let _153_369 = (let _153_368 = (mk_ref_read tm)
in (_153_368, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval)))
in FStar_Syntax_Syntax.Tm_meta (_153_369))
in (FStar_All.pipe_left mk _153_370))
end else begin
tm
end)
end))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(

let _63_1002 = (match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| None -> begin
(let _153_372 = (let _153_371 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (FStar_All.pipe_left Prims.fst _153_371))
in (_153_372, false))
end
| Some (head) -> begin
(let _153_373 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in (_153_373, true))
end)
in (match (_63_1002) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _63_1005 -> begin
(

let args = (FStar_List.map (fun _63_1008 -> (match (_63_1008) with
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

let _63_1036 = (FStar_List.fold_left (fun _63_1019 b -> (match (_63_1019) with
| (env, tparams, typs) -> begin
(

let _63_1023 = (desugar_binder env b)
in (match (_63_1023) with
| (xopt, t) -> begin
(

let _63_1029 = (match (xopt) with
| None -> begin
(let _153_377 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (env, _153_377))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_63_1029) with
| (env, x) -> begin
(let _153_381 = (let _153_380 = (let _153_379 = (let _153_378 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_378))
in (_153_379)::[])
in (FStar_List.append typs _153_380))
in (env, (FStar_List.append tparams ((((

let _63_1030 = x
in {FStar_Syntax_Syntax.ppname = _63_1030.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_1030.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), None))::[])), _153_381))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_63_1036) with
| (env, _63_1034, targs) -> begin
(

let _63_1040 = (let _153_382 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _153_382))
in (match (_63_1040) with
| (tup, _63_1039) -> begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app ((tup, targs))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let _63_1047 = (uncurry binders t)
in (match (_63_1047) with
| (bs, t) -> begin
(

let rec aux = (fun env bs _63_8 -> (match (_63_8) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _153_389 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _153_389)))
end
| hd::tl -> begin
(

let mlenv = (FStar_Parser_Env.default_ml env)
in (

let bb = (desugar_binder mlenv hd)
in (

let _63_1061 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_63_1061) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _63_1068) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(

let _63_1076 = (as_binder env None b)
in (match (_63_1076) with
| ((x, _63_1073), env) -> begin
(

let f = (desugar_formula env f)
in (let _153_390 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _153_390)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let _63_1096 = (FStar_List.fold_left (fun _63_1084 pat -> (match (_63_1084) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_63_1087, t) -> begin
(let _153_394 = (let _153_393 = (free_type_vars env t)
in (FStar_List.append _153_393 ftvs))
in (env, _153_394))
end
| _63_1092 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_63_1096) with
| (_63_1094, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (let _153_396 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, Some (FStar_Parser_AST.Implicit)))) top.FStar_Parser_AST.range))))
in (FStar_List.append _153_396 binders))
in (

let rec aux = (fun env bs sc_pat_opt _63_9 -> (match (_63_9) with
| [] -> begin
(

let body = (desugar_term env body)
in (

let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(

let body = (let _153_406 = (let _153_405 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _153_405 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _153_406 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((sc, ((pat, None, body))::[]))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _153_407 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _153_407))))
end
| p::rest -> begin
(

let _63_1120 = (desugar_binding_pat env p)
in (match (_63_1120) with
| (env, b, pat) -> begin
(

let _63_1171 = (match (b) with
| LetBinder (_63_1122) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _63_1130) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _153_409 = (let _153_408 = (FStar_Syntax_Syntax.bv_to_name x)
in (_153_408, p))
in Some (_153_409))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Syntax_Syntax.n, p'.FStar_Syntax_Syntax.v)) with
| (FStar_Syntax_Syntax.Tm_name (_63_1144), _63_1147) -> begin
(

let tup2 = (let _153_410 = (FStar_Syntax_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _153_410 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _153_418 = (let _153_417 = (let _153_416 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _153_415 = (let _153_414 = (FStar_Syntax_Syntax.as_arg sc)
in (let _153_413 = (let _153_412 = (let _153_411 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_411))
in (_153_412)::[])
in (_153_414)::_153_413))
in (_153_416, _153_415)))
in FStar_Syntax_Syntax.Tm_app (_153_417))
in (FStar_Syntax_Syntax.mk _153_418 None top.FStar_Parser_AST.range))
in (

let p = (let _153_419 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tup2, ((p', false))::((p, false))::[]))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _153_419))
in Some ((sc, p)))))
end
| (FStar_Syntax_Syntax.Tm_app (_63_1153, args), FStar_Syntax_Syntax.Pat_cons (_63_1158, pats)) -> begin
(

let tupn = (let _153_420 = (FStar_Syntax_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _153_420 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _153_427 = (let _153_426 = (let _153_425 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _153_424 = (let _153_423 = (let _153_422 = (let _153_421 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_421))
in (_153_422)::[])
in (FStar_List.append args _153_423))
in (_153_425, _153_424)))
in FStar_Syntax_Syntax.Tm_app (_153_426))
in (mk _153_427))
in (

let p = (let _153_428 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tupn, (FStar_List.append pats (((p, false))::[]))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _153_428))
in Some ((sc, p)))))
end
| _63_1167 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((x, aq), sc_pat_opt))
end)
in (match (_63_1171) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _63_1175; FStar_Parser_AST.level = _63_1173}, phi, _63_1181) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env phi)
in (let _153_436 = (let _153_435 = (let _153_434 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _153_433 = (let _153_432 = (FStar_Syntax_Syntax.as_arg phi)
in (let _153_431 = (let _153_430 = (let _153_429 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_429))
in (_153_430)::[])
in (_153_432)::_153_431))
in (_153_434, _153_433)))
in FStar_Syntax_Syntax.Tm_app (_153_435))
in (mk _153_436)))
end
| FStar_Parser_AST.App (_63_1186) -> begin
(

let rec aux = (fun args e -> (match ((let _153_441 = (unparen e)
in _153_441.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(

let arg = (let _153_442 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _153_442))
in (aux ((arg)::args) e))
end
| _63_1198 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _153_445 = (let _153_444 = (let _153_443 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((FStar_Parser_AST.NoLetQualifier, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_153_443, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))
in FStar_Syntax_Syntax.Tm_meta (_153_444))
in (mk _153_445))
end
| FStar_Parser_AST.Let (qual, (pat, _snd)::_tl, body) -> begin
(

let is_rec = (qual = FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun _63_1215 -> (match (()) with
| () -> begin
(

let bindings = ((pat, _snd))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _63_1219 -> (match (_63_1219) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _153_449 = (destruct_app_pattern env top_level p)
in (_153_449, def))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _153_450 = (destruct_app_pattern env top_level p)
in (_153_450, def))
end
| _63_1225 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _63_1230); FStar_Parser_AST.prange = _63_1227}, t) -> begin
if top_level then begin
(let _153_453 = (let _153_452 = (let _153_451 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_153_451))
in (_153_452, [], Some (t)))
in (_153_453, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _63_1239) -> begin
if top_level then begin
(let _153_456 = (let _153_455 = (let _153_454 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_153_454))
in (_153_455, [], None))
in (_153_456, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _63_1243 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (

let _63_1272 = (FStar_List.fold_left (fun _63_1248 _63_1257 -> (match ((_63_1248, _63_1257)) with
| ((env, fnames, rec_bindings), ((f, _63_1251, _63_1253), _63_1256)) -> begin
(

let _63_1268 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let _63_1262 = (FStar_Parser_Env.push_bv env x)
in (match (_63_1262) with
| (env, xx) -> begin
(let _153_460 = (let _153_459 = (FStar_Syntax_Syntax.mk_binder xx)
in (_153_459)::rec_bindings)
in (env, FStar_Util.Inl (xx), _153_460))
end))
end
| FStar_Util.Inr (l) -> begin
(let _153_461 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in (_153_461, FStar_Util.Inr (l), rec_bindings))
end)
in (match (_63_1268) with
| (env, lbname, rec_bindings) -> begin
(env, (lbname)::fnames, rec_bindings)
end))
end)) (env, [], []) funs)
in (match (_63_1272) with
| (env', fnames, rec_bindings) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let desugar_one_def = (fun env lbname _63_1283 -> (match (_63_1283) with
| ((_63_1278, args, result_t), def) -> begin
(

let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _153_468 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _153_468 FStar_Parser_AST.Expr))
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| _63_1290 -> begin
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
(let _153_470 = (let _153_469 = (incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _153_469 None))
in FStar_Util.Inr (_153_470))
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
in (let _153_473 = (let _153_472 = (let _153_471 = (FStar_Syntax_Subst.close rec_bindings body)
in ((is_rec, lbs), _153_471))
in FStar_Syntax_Syntax.Tm_let (_153_472))
in (FStar_All.pipe_left mk _153_473))))))
end))))
end))
in (

let ds_non_rec = (fun pat t1 t2 -> (

let t1 = (desugar_term env t1)
in (

let is_mutable = (qual = FStar_Parser_AST.Mutable)
in (

let t1 = if is_mutable then begin
(mk_ref_alloc t1)
end else begin
t1
end
in (

let _63_1311 = (desugar_binding_pat_maybe_top top_level env pat is_mutable)
in (match (_63_1311) with
| (env, binder, pat) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body = (desugar_term env t2)
in (

let fv = (let _153_480 = (incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _153_480 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]), body))))))
end
| LocalBinder (x, _63_1320) -> begin
(

let body = (desugar_term env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _153_485 = (let _153_484 = (let _153_483 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _153_482 = (let _153_481 = (FStar_Syntax_Util.branch (pat, None, body))
in (_153_481)::[])
in (_153_483, _153_482)))
in FStar_Syntax_Syntax.Tm_match (_153_484))
in (FStar_Syntax_Syntax.mk _153_485 None body.FStar_Syntax_Syntax.pos))
end)
in (let _153_490 = (let _153_489 = (let _153_488 = (let _153_487 = (let _153_486 = (FStar_Syntax_Syntax.mk_binder x)
in (_153_486)::[])
in (FStar_Syntax_Subst.close _153_487 body))
in ((false, ((mk_lb (FStar_Util.Inl (x), x.FStar_Syntax_Syntax.sort, t1)))::[]), _153_488))
in FStar_Syntax_Syntax.Tm_let (_153_489))
in (FStar_All.pipe_left mk _153_490))))
end)
in if is_mutable then begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((tm, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc)))))
end else begin
tm
end)
end))))))
in if (is_rec || (is_app_pattern pat)) then begin
(ds_let_rec_or_app ())
end else begin
(ds_non_rec pat _snd body)
end)))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (let _153_501 = (let _153_500 = (let _153_499 = (desugar_term env t1)
in (let _153_498 = (let _153_497 = (let _153_492 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _153_491 = (desugar_term env t2)
in (_153_492, None, _153_491)))
in (let _153_496 = (let _153_495 = (let _153_494 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _153_493 = (desugar_term env t3)
in (_153_494, None, _153_493)))
in (_153_495)::[])
in (_153_497)::_153_496))
in (_153_499, _153_498)))
in FStar_Syntax_Syntax.Tm_match (_153_500))
in (mk _153_501)))
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

let desugar_branch = (fun _63_1361 -> (match (_63_1361) with
| (pat, wopt, b) -> begin
(

let _63_1364 = (desugar_match_pat env pat)
in (match (_63_1364) with
| (env, pat) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _153_504 = (desugar_term env e)
in Some (_153_504))
end)
in (

let b = (desugar_term env b)
in (FStar_Syntax_Util.branch (pat, wopt, b))))
end))
end))
in (let _153_508 = (let _153_507 = (let _153_506 = (desugar_term env e)
in (let _153_505 = (FStar_List.map desugar_branch branches)
in (_153_506, _153_505)))
in FStar_Syntax_Syntax.Tm_match (_153_507))
in (FStar_All.pipe_left mk _153_508)))
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
in (let _153_511 = (let _153_510 = (let _153_509 = (desugar_term env e)
in (_153_509, annot, None))
in FStar_Syntax_Syntax.Tm_ascribed (_153_510))
in (FStar_All.pipe_left mk _153_511)))))
end
| FStar_Parser_AST.Record (_63_1378, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let _63_1389 = (FStar_List.hd fields)
in (match (_63_1389) with
| (f, _63_1388) -> begin
(

let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (

let _63_1395 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_63_1395) with
| (record, _63_1394) -> begin
(

let get_field = (fun xopt f -> (

let fn = f.FStar_Ident.ident
in (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _63_1403 -> (match (_63_1403) with
| (g, _63_1402) -> begin
(

let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_63_1407, e) -> begin
(let _153_519 = (qfn fn)
in (_153_519, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _153_522 = (let _153_521 = (let _153_520 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in (_153_520, top.FStar_Parser_AST.range))
in FStar_Syntax_Syntax.Error (_153_521))
in (Prims.raise _153_522))
end
| Some (x) -> begin
(let _153_523 = (qfn fn)
in (_153_523, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (

let recterm = (match (eopt) with
| None -> begin
(let _153_528 = (let _153_527 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _63_1419 -> (match (_63_1419) with
| (f, _63_1418) -> begin
(let _153_526 = (let _153_525 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _153_525))
in (_153_526, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_Env.constrname, _153_527))
in FStar_Parser_AST.Construct (_153_528))
end
| Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (let _153_530 = (let _153_529 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_153_529))
in (FStar_Parser_AST.mk_term _153_530 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = (let _153_533 = (let _153_532 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _63_1427 -> (match (_63_1427) with
| (f, _63_1426) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _153_532))
in FStar_Parser_AST.Record (_153_533))
in FStar_Parser_AST.Let ((FStar_Parser_AST.NoLetQualifier, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, None))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _63_1443; FStar_Syntax_Syntax.pos = _63_1441; FStar_Syntax_Syntax.vars = _63_1439}, args); FStar_Syntax_Syntax.tk = _63_1437; FStar_Syntax_Syntax.pos = _63_1435; FStar_Syntax_Syntax.vars = _63_1433}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e = (let _153_541 = (let _153_540 = (let _153_539 = (let _153_538 = (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos)
in (let _153_537 = (let _153_536 = (let _153_535 = (let _153_534 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _153_534))
in FStar_Syntax_Syntax.Record_ctor (_153_535))
in Some (_153_536))
in (FStar_Syntax_Syntax.fvar _153_538 FStar_Syntax_Syntax.Delta_constant _153_537)))
in (_153_539, args))
in FStar_Syntax_Syntax.Tm_app (_153_540))
in (FStar_All.pipe_left mk _153_541))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| _63_1457 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let _63_1464 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_63_1464) with
| (fieldname, is_rec) -> begin
(

let e = (desugar_term env e)
in (

let fn = (

let _63_1469 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_63_1469) with
| (ns, _63_1468) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (

let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (fn))
end else begin
None
end
in (let _153_547 = (let _153_546 = (let _153_545 = (let _153_542 = (FStar_Ident.set_lid_range fieldname (FStar_Ident.range_of_lid f))
in (FStar_Syntax_Syntax.fvar _153_542 FStar_Syntax_Syntax.Delta_equational qual))
in (let _153_544 = (let _153_543 = (FStar_Syntax_Syntax.as_arg e)
in (_153_543)::[])
in (_153_545, _153_544)))
in FStar_Syntax_Syntax.Tm_app (_153_546))
in (FStar_All.pipe_left mk _153_547)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _63_1479 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _63_1481 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _63_1486 -> (match (_63_1486) with
| (a, imp) -> begin
(let _153_551 = (desugar_term env a)
in (arg_withimp_e imp _153_551))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error ((msg, r)))))
in (

let is_requires = (fun _63_1498 -> (match (_63_1498) with
| (t, _63_1497) -> begin
(match ((let _153_559 = (unparen t)
in _153_559.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_63_1500) -> begin
true
end
| _63_1503 -> begin
false
end)
end))
in (

let is_ensures = (fun _63_1508 -> (match (_63_1508) with
| (t, _63_1507) -> begin
(match ((let _153_562 = (unparen t)
in _153_562.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_63_1510) -> begin
true
end
| _63_1513 -> begin
false
end)
end))
in (

let is_app = (fun head _63_1519 -> (match (_63_1519) with
| (t, _63_1518) -> begin
(match ((let _153_567 = (unparen t)
in _153_567.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _63_1523; FStar_Parser_AST.level = _63_1521}, _63_1528, _63_1530) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _63_1534 -> begin
false
end)
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t -> (

let _63_1540 = (head_and_args t)
in (match (_63_1540) with
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
| ens::[] -> begin
(unit_tm)::(req_true)::(ens)::(nil_pat)::[]
end
| req::ens::[] when ((is_requires req) && (is_ensures ens)) -> begin
(unit_tm)::(req)::(ens)::(nil_pat)::[]
end
| ens::dec::[] when ((is_ensures ens) && (is_decreases dec)) -> begin
(unit_tm)::(req_true)::(ens)::(nil_pat)::(dec)::[]
end
| req::ens::dec::[] when (((is_requires req) && (is_ensures ens)) && (is_app "decreases" dec)) -> begin
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
(let _153_571 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_name env) l)
in (_153_571, args))
end
| FStar_Parser_AST.Name (l) when ((let _153_572 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _153_572 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(let _153_573 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_153_573, args))
end
| FStar_Parser_AST.Name (l) when ((let _153_574 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _153_574 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(let _153_575 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)
in (_153_575, args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(let _153_576 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_153_576, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _63_1571 when default_ok -> begin
(let _153_577 = (FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)
in (_153_577, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _63_1573 -> begin
(let _153_579 = (let _153_578 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _153_578))
in (fail _153_579))
end)
end)))
in (

let _63_1576 = (pre_process_comp_typ t)
in (match (_63_1576) with
| (eff, args) -> begin
(

let _63_1577 = if ((FStar_List.length args) = 0) then begin
(let _153_581 = (let _153_580 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _153_580))
in (fail _153_581))
end else begin
()
end
in (

let _63_1581 = (let _153_583 = (FStar_List.hd args)
in (let _153_582 = (FStar_List.tl args)
in (_153_583, _153_582)))
in (match (_63_1581) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (Prims.fst result_arg))
in (

let rest = (desugar_args env rest)
in (

let _63_1606 = (FStar_All.pipe_right rest (FStar_List.partition (fun _63_1587 -> (match (_63_1587) with
| (t, _63_1586) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _63_1593; FStar_Syntax_Syntax.pos = _63_1591; FStar_Syntax_Syntax.vars = _63_1589}, _63_1598::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _63_1603 -> begin
false
end)
end))))
in (match (_63_1606) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _63_1610 -> (match (_63_1610) with
| (t, _63_1609) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_63_1612, (arg, _63_1615)::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _63_1621 -> begin
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
| req::ens::(pat, aq)::[] -> begin
(

let pat = (match (pat.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
(

let nil = (FStar_Syntax_Syntax.mk_Tm_uinst pat ((FStar_Syntax_Syntax.U_succ (FStar_Syntax_Syntax.U_zero))::[]))
in (

let pattern = (let _153_587 = (let _153_586 = (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _153_586 FStar_Syntax_Syntax.Delta_constant None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _153_587 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil (((pattern, Some (FStar_Syntax_Syntax.imp_tag)))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _63_1636 -> begin
pat
end)
in (let _153_591 = (let _153_590 = (let _153_589 = (let _153_588 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((pat, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))) None pat.FStar_Syntax_Syntax.pos)
in (_153_588, aq))
in (_153_589)::[])
in (ens)::_153_590)
in (req)::_153_591))
end
| _63_1639 -> begin
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
| _63_1651 -> begin
None
end))
in (

let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _63_1658 = t
in {FStar_Syntax_Syntax.n = _63_1658.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _63_1658.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _63_1658.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let _63_1665 = b
in {FStar_Parser_AST.b = _63_1665.FStar_Parser_AST.b; FStar_Parser_AST.brange = _63_1665.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _63_1665.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _153_626 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _153_626)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(

let _63_1679 = (FStar_Parser_Env.push_bv env a)
in (match (_63_1679) with
| (env, a) -> begin
(

let a = (

let _63_1680 = a
in {FStar_Syntax_Syntax.ppname = _63_1680.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_1680.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats = (desugar_pats env pats)
in (

let body = (desugar_formula env body)
in (

let body = (match (pats) with
| [] -> begin
body
end
| _63_1687 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((body, FStar_Syntax_Syntax.Meta_pattern (pats)))))
end)
in (

let body = (let _153_629 = (let _153_628 = (let _153_627 = (FStar_Syntax_Syntax.mk_binder a)
in (_153_627)::[])
in (no_annot_abs _153_628 body))
in (FStar_All.pipe_left setpos _153_629))
in (let _153_635 = (let _153_634 = (let _153_633 = (let _153_630 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar _153_630 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (let _153_632 = (let _153_631 = (FStar_Syntax_Syntax.as_arg body)
in (_153_631)::[])
in (_153_633, _153_632)))
in FStar_Syntax_Syntax.Tm_app (_153_634))
in (FStar_All.pipe_left mk _153_635)))))))
end))
end
| _63_1691 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| b::b'::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (let _153_650 = (q (rest, pats, body))
in (let _153_649 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _153_650 _153_649 FStar_Parser_AST.Formula)))
in (let _153_651 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _153_651 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _63_1705 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _153_652 = (unparen f)
in _153_652.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(

let f = (desugar_formula env f)
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((l, f.FStar_Syntax_Syntax.pos, p)))))))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall (_1::_2::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _153_654 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _153_654)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _153_656 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _153_656)))
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
| _63_1763 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let _63_1787 = (FStar_List.fold_left (fun _63_1768 b -> (match (_63_1768) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let _63_1770 = b
in {FStar_Parser_AST.b = _63_1770.FStar_Parser_AST.b; FStar_Parser_AST.brange = _63_1770.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _63_1770.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(

let _63_1779 = (FStar_Parser_Env.push_bv env a)
in (match (_63_1779) with
| (env, a) -> begin
(

let a = (

let _63_1780 = a
in {FStar_Syntax_Syntax.ppname = _63_1780.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_1780.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (env, ((a, (trans_aqual b.FStar_Parser_AST.aqual)))::out))
end))
end
| _63_1784 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_63_1787) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _153_663 = (desugar_typ env t)
in (Some (x), _153_663))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _153_664 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in (Some (x), _153_664))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _153_665 = (desugar_typ env t)
in (None, _153_665))
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

let binders = (let _153_681 = (let _153_680 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _153_680))
in (FStar_List.append tps _153_681))
in (

let p = (FStar_Ident.range_of_lid t)
in (

let _63_1814 = (FStar_Syntax_Util.args_of_binders binders)
in (match (_63_1814) with
| (binders, args) -> begin
(

let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _63_1818 -> (match (_63_1818) with
| (x, _63_1817) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (

let binders = (let _153_687 = (let _153_686 = (let _153_685 = (let _153_684 = (let _153_683 = (FStar_Syntax_Syntax.lid_as_fv t FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _153_683))
in (FStar_Syntax_Syntax.mk_Tm_app _153_684 args None p))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _153_685))
in (_153_686)::[])
in (FStar_List.append imp_binders _153_687))
in (

let disc_type = (let _153_690 = (let _153_689 = (let _153_688 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _153_688))
in (FStar_Syntax_Syntax.mk_Total _153_689))
in (FStar_Syntax_Util.arrow binders _153_690))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _153_693 = (let _153_692 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in (disc_name, [], disc_type, _153_692, (FStar_Ident.range_of_lid disc_name)))
in FStar_Syntax_Syntax.Sig_declare_typ (_153_693)))))))))
end))))))


let mk_indexed_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq refine_domain env tc lid inductive_tps imp_tps fields t -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (

let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (Some (p)) ptyp))
in (

let tps = (FStar_List.map2 (fun _63_1842 _63_1846 -> (match ((_63_1842, _63_1846)) with
| ((_63_1840, imp), (x, _63_1845)) -> begin
(x, imp)
end)) inductive_tps imp_tps)
in (

let _63_1947 = (

let _63_1850 = (FStar_Syntax_Util.head_and_args t)
in (match (_63_1850) with
| (head, args0) -> begin
(

let args = (

let rec arguments = (fun tps args -> (match ((tps, args)) with
| ([], _63_1856) -> begin
args
end
| (_63_1859, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to type", (FStar_Ident.range_of_lid lid)))))
end
| ((_63_1864, Some (FStar_Syntax_Syntax.Implicit (_63_1866)))::tps', (_63_1873, Some (FStar_Syntax_Syntax.Implicit (_63_1875)))::args') -> begin
(arguments tps' args')
end
| ((_63_1883, Some (FStar_Syntax_Syntax.Implicit (_63_1885)))::tps', (_63_1893, _63_1895)::_63_1891) -> begin
(arguments tps' args)
end
| ((_63_1902, _63_1904)::_63_1900, (a, Some (FStar_Syntax_Syntax.Implicit (_63_1911)))::_63_1908) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected implicit annotation on argument", a.FStar_Syntax_Syntax.pos))))
end
| ((_63_1919, _63_1921)::tps', (_63_1926, _63_1928)::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (

let indices = (FStar_All.pipe_right args (FStar_List.map (fun _63_1933 -> (let _153_725 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _153_725 FStar_Syntax_Syntax.mk_binder)))))
in (

let arg_typ = (let _153_730 = (let _153_726 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _153_726))
in (let _153_729 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _63_1938 -> (match (_63_1938) with
| (x, imp) -> begin
(let _153_728 = (FStar_Syntax_Syntax.bv_to_name x)
in (_153_728, imp))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _153_730 _153_729 None p)))
in (

let arg_binder = if (not (refine_domain)) then begin
(let _153_731 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _153_731))
end else begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _153_740 = (

let _63_1942 = (projectee arg_typ)
in (let _153_739 = (let _153_738 = (let _153_737 = (let _153_736 = (let _153_732 = (FStar_Ident.set_lid_range disc_name p)
in (FStar_Syntax_Syntax.fvar _153_732 FStar_Syntax_Syntax.Delta_equational None))
in (let _153_735 = (let _153_734 = (let _153_733 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_733))
in (_153_734)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _153_736 _153_735 None p)))
in (FStar_Syntax_Util.b2t _153_737))
in (FStar_Syntax_Util.refine x _153_738))
in {FStar_Syntax_Syntax.ppname = _63_1942.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_1942.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_739}))
in (FStar_Syntax_Syntax.mk_binder _153_740))))
end
in (arg_binder, indices)))))
end))
in (match (_63_1947) with
| (arg_binder, indices) -> begin
(

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (

let imp_binders = (let _153_742 = (FStar_All.pipe_right indices (FStar_List.map (fun _63_1952 -> (match (_63_1952) with
| (x, _63_1951) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (FStar_List.append imp_tps _153_742))
in (

let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (

let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (

let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _63_1960 -> (match (_63_1960) with
| (a, _63_1959) -> begin
(

let _63_1964 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_63_1964) with
| (field_name, _63_1963) -> begin
(

let proj = (let _153_746 = (let _153_745 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _153_745))
in (FStar_Syntax_Syntax.mk_Tm_app _153_746 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT ((a, proj)))
end))
end))))
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (FStar_List.append imp_tps fields)
in (let _153_782 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _63_1973 -> (match (_63_1973) with
| (x, _63_1972) -> begin
(

let _63_1977 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_63_1977) with
| (field_name, _63_1976) -> begin
(

let t = (let _153_750 = (let _153_749 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _153_749))
in (FStar_Syntax_Util.arrow binders _153_750))
in (

let only_decl = (((let _153_751 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _153_751)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _153_753 = (let _153_752 = (FStar_Parser_Env.current_module env)
in _153_752.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _153_753)))
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

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _63_1989 -> (match (_63_1989) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _153_758 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in (_153_758, b))
end else begin
if (b && (j < ntps)) then begin
(let _153_762 = (let _153_761 = (let _153_760 = (let _153_759 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (_153_759, FStar_Syntax_Syntax.tun))
in FStar_Syntax_Syntax.Pat_dot_term (_153_760))
in (pos _153_761))
in (_153_762, b))
end else begin
(let _153_765 = (let _153_764 = (let _153_763 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_153_763))
in (pos _153_764))
in (_153_765, b))
end
end)
end))))
in (

let pat = (let _153_770 = (let _153_768 = (let _153_767 = (let _153_766 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in (_153_766, arg_pats))
in FStar_Syntax_Syntax.Pat_cons (_153_767))
in (FStar_All.pipe_right _153_768 pos))
in (let _153_769 = (FStar_Syntax_Syntax.bv_to_name projection)
in (_153_770, None, _153_769)))
in (

let body = (let _153_774 = (let _153_773 = (let _153_772 = (let _153_771 = (FStar_Syntax_Util.branch pat)
in (_153_771)::[])
in (arg_exp, _153_772))
in FStar_Syntax_Syntax.Tm_match (_153_773))
in (FStar_Syntax_Syntax.mk _153_774 None p))
in (

let imp = (no_annot_abs binders body)
in (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end else begin
FStar_Syntax_Syntax.Delta_equational
end
in (

let lb = (let _153_776 = (let _153_775 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_153_775))
in {FStar_Syntax_Syntax.lbname = _153_776; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp})
in (

let impl = (let _153_781 = (let _153_780 = (let _153_779 = (let _153_778 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _153_778 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_153_779)::[])
in ((false, (lb)::[]), p, _153_780, quals))
in FStar_Syntax_Syntax.Sig_let (_153_781))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end))))))))
end))))))
end))
end))))
in (FStar_All.pipe_right _153_782 FStar_List.flatten)))))))))
end)))))))


let mk_data_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env _63_2003 -> (match (_63_2003) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _63_2006, t, l, n, quals, _63_2012, _63_2014) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_10 -> (match (_63_10) with
| FStar_Syntax_Syntax.RecordConstructor (_63_2019) -> begin
true
end
| _63_2022 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _63_2026 -> begin
true
end)
end
in (

let _63_2030 = (FStar_Syntax_Util.arrow_formals t)
in (match (_63_2030) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _63_2033 -> begin
(

let fv_qual = (match ((FStar_Util.find_map quals (fun _63_11 -> (match (_63_11) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((lid, fns)))
end
| _63_2038 -> begin
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

let _63_2046 = (FStar_Util.first_N n formals)
in (match (_63_2046) with
| (tps, rest) -> begin
(mk_indexed_projectors iquals fv_qual refine_domain env l lid inductive_tps tps rest cod)
end))))
end)
end)))
end
| _63_2048 -> begin
[]
end)
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _153_807 = (incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (_153_807))
end else begin
(incr_delta_qualifier t)
end
in (

let lb = (let _153_812 = (let _153_808 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (_153_808))
in (let _153_811 = (let _153_809 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _153_809))
in (let _153_810 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _153_812; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _153_811; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _153_810})))
in FStar_Syntax_Syntax.Sig_let (((false, (lb)::[]), rng, lids, quals)))))


let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (

let tycon_id = (fun _63_12 -> (match (_63_12) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _153_826 = (let _153_825 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_153_825))
in (FStar_Parser_AST.mk_term _153_826 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| _63_2123 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _153_839 = (let _153_838 = (let _153_837 = (binder_to_term b)
in (out, _153_837, (imp_of_aqual b)))
in FStar_Parser_AST.App (_153_838))
in (FStar_Parser_AST.mk_term _153_839 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun _63_13 -> (match (_63_13) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (

let mfields = (FStar_List.map (fun _63_2136 -> (match (_63_2136) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Syntax_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (let _153_845 = (let _153_844 = (let _153_843 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_153_843))
in (FStar_Parser_AST.mk_term _153_844 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _153_845 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _153_847 = (FStar_All.pipe_right fields (FStar_List.map (fun _63_2143 -> (match (_63_2143) with
| (x, _63_2142) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _153_847))))))
end
| _63_2145 -> begin
(FStar_All.failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals _63_14 -> (match (_63_14) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let _63_2159 = (typars_of_binders _env binders)
in (match (_63_2159) with
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

let tconstr = (let _153_858 = (let _153_857 = (let _153_856 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_153_856))
in (FStar_Parser_AST.mk_term _153_857 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _153_858 binders))
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
| _63_2172 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env bs -> (

let _63_2187 = (FStar_List.fold_left (fun _63_2178 _63_2181 -> (match ((_63_2178, _63_2181)) with
| ((env, tps), (x, imp)) -> begin
(

let _63_2184 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_63_2184) with
| (env, y) -> begin
(env, ((y, imp))::tps)
end))
end)) (env, []) bs)
in (match (_63_2187) with
| (env, bs) -> begin
(env, (FStar_List.rev bs))
end)))
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (id, bs, kopt)::[] -> begin
(

let kopt = (match (kopt) with
| None -> begin
(let _153_865 = (tm_type_z id.FStar_Ident.idRange)
in Some (_153_865))
end
| _63_2196 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract ((id, bs, kopt))
in (

let _63_2206 = (desugar_abstract_tc quals env [] tc)
in (match (_63_2206) with
| (_63_2200, _63_2202, se, _63_2205) -> begin
(

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _63_2209, typars, k, [], [], quals, rng) -> begin
(

let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(

let _63_2218 = (let _153_867 = (FStar_Range.string_of_range rng)
in (let _153_866 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _153_867 _153_866)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (

let t = (match (typars) with
| [] -> begin
k
end
| _63_2223 -> begin
(let _153_870 = (let _153_869 = (let _153_868 = (FStar_Syntax_Syntax.mk_Total k)
in (typars, _153_868))
in FStar_Syntax_Syntax.Tm_arrow (_153_869))
in (FStar_Syntax_Syntax.mk _153_870 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ ((l, [], t, quals, rng))))
end
| _63_2226 -> begin
se
end)
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))
end))))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t)::[] -> begin
(

let _63_2238 = (typars_of_binders env binders)
in (match (_63_2238) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _63_15 -> (match (_63_15) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _63_2243 -> begin
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
| _63_2251 -> begin
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
in (let _153_876 = (let _153_875 = (FStar_Parser_Env.qualify env id)
in (let _153_874 = (FStar_All.pipe_right quals (FStar_List.filter (fun _63_17 -> (match (_63_17) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _63_2259 -> begin
true
end))))
in (_153_875, [], typars, c, _153_874, rng)))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_153_876)))))
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
| FStar_Parser_AST.TyconRecord (_63_2265)::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let _63_2271 = (tycon_record_as_variant trec)
in (match (_63_2271) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _63_2275::_63_2273 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let _63_2286 = et
in (match (_63_2286) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_63_2288) -> begin
(

let trec = tc
in (

let _63_2293 = (tycon_record_as_variant trec)
in (match (_63_2293) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let _63_2305 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_63_2305) with
| (env, _63_2302, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let _63_2317 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_63_2317) with
| (env, _63_2314, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _63_2319 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (

let _63_2322 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_63_2322) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _63_19 -> (match (_63_19) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _63_2330, _63_2332, _63_2334, _63_2336), t, quals) -> begin
(

let _63_2346 = (push_tparams env tpars)
in (match (_63_2346) with
| (env_tps, _63_2345) -> begin
(

let t = (desugar_term env_tps t)
in (let _153_886 = (let _153_885 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in ([], _153_885))
in (_153_886)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _63_2354, tags, _63_2357), constrs, tconstr, quals) -> begin
(

let tycon = (tname, tpars, k)
in (

let _63_2368 = (push_tparams env tpars)
in (match (_63_2368) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun _63_2372 -> (match (_63_2372) with
| (x, _63_2371) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end)) tps)
in (

let _63_2396 = (let _153_898 = (FStar_All.pipe_right constrs (FStar_List.map (fun _63_2377 -> (match (_63_2377) with
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

let t = (let _153_890 = (FStar_Parser_Env.default_total env_tps)
in (let _153_889 = (close env_tps t)
in (desugar_term _153_890 _153_889)))
in (

let name = (FStar_Parser_Env.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _63_18 -> (match (_63_18) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _63_2391 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (let _153_897 = (let _153_896 = (let _153_895 = (let _153_894 = (let _153_893 = (let _153_892 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _153_892))
in (FStar_Syntax_Util.arrow data_tpars _153_893))
in (name, univs, _153_894, tname, ntps, quals, mutuals, rng))
in FStar_Syntax_Syntax.Sig_datacon (_153_895))
in (tps, _153_896))
in (name, _153_897)))))))
end))))
in (FStar_All.pipe_left FStar_List.split _153_898))
in (match (_63_2396) with
| (constrNames, constrs) -> begin
(([], FStar_Syntax_Syntax.Sig_inductive_typ ((tname, univs, tpars, k, mutuals, constrNames, tags, rng))))::constrs
end)))
end)))
end
| _63_2398 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (

let bundle = (let _153_900 = (let _153_899 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _153_899, rng))
in FStar_Syntax_Syntax.Sig_bundle (_153_900))
in (

let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (

let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors quals env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _63_20 -> (match (_63_20) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _63_2407, tps, k, _63_2411, constrs, quals, _63_2415) when ((FStar_List.length constrs) > 1) -> begin
(

let quals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract quals) then begin
(FStar_Syntax_Syntax.Private)::quals
end else begin
quals
end
in (mk_data_discriminators quals env tname tps k constrs))
end
| _63_2420 -> begin
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

let _63_2444 = (FStar_List.fold_left (fun _63_2429 b -> (match (_63_2429) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(

let _63_2437 = (FStar_Parser_Env.push_bv env a)
in (match (_63_2437) with
| (env, a) -> begin
(let _153_909 = (let _153_908 = (FStar_Syntax_Syntax.mk_binder (

let _63_2438 = a
in {FStar_Syntax_Syntax.ppname = _63_2438.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_2438.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_153_908)::binders)
in (env, _153_909))
end))
end
| _63_2441 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_63_2444) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))


let rec desugar_effect : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (Prims.string  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term))  ->  FStar_Syntax_Syntax.sigelt)  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_kind eff_decls mk -> (

let env0 = env
in (

let env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (

let _63_2457 = (desugar_binders env eff_binders)
in (match (_63_2457) with
| (env, binders) -> begin
(

let eff_k = (let _153_961 = (FStar_Parser_Env.default_total env)
in (desugar_term _153_961 eff_kind))
in (

let _63_2468 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _63_2461 decl -> (match (_63_2461) with
| (env, out) -> begin
(

let _63_2465 = (desugar_decl env decl)
in (match (_63_2465) with
| (env, ses) -> begin
(let _153_965 = (let _153_964 = (FStar_List.hd ses)
in (_153_964)::out)
in (env, _153_965))
end))
end)) (env, [])))
in (match (_63_2468) with
| (env, decls) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (

let lookup = (fun s -> (

let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident (s, d.FStar_Parser_AST.drange)))
in (let _153_969 = (let _153_968 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _153_968))
in ([], _153_969))))
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
| FStar_Parser_AST.TopLevelModule (_63_2485) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Multiple modules in a file are no longer supported", d.FStar_Parser_AST.drange))))
end
| FStar_Parser_AST.Open (lid) -> begin
(

let env = (FStar_Parser_Env.push_namespace env lid)
in (env, []))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _153_973 = (FStar_Parser_Env.push_module_abbrev env x l)
in (_153_973, []))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _153_974 = (FStar_List.map trans_qual qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _153_974 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _153_976 = (let _153_975 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _153_975))
in _153_976.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _63_2505) -> begin
(

let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals = (match (quals) with
| _63_2513::_63_2511 -> begin
(FStar_List.map trans_qual quals)
end
| _63_2516 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _63_21 -> (match (_63_21) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_63_2527); FStar_Syntax_Syntax.lbunivs = _63_2525; FStar_Syntax_Syntax.lbtyp = _63_2523; FStar_Syntax_Syntax.lbeff = _63_2521; FStar_Syntax_Syntax.lbdef = _63_2519} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _63_2537; FStar_Syntax_Syntax.lbtyp = _63_2535; FStar_Syntax_Syntax.lbeff = _63_2533; FStar_Syntax_Syntax.lbdef = _63_2531} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _63_2545 -> (match (_63_2545) with
| (_63_2543, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (

let lbs = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _153_981 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _63_2549 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let _63_2551 = fv
in {FStar_Syntax_Syntax.fv_name = _63_2551.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = _63_2551.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = _63_2549.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _63_2549.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _63_2549.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _63_2549.FStar_Syntax_Syntax.lbdef})))))
in ((Prims.fst lbs), _153_981))
end else begin
lbs
end
in (

let s = (let _153_984 = (let _153_983 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (lbs, d.FStar_Parser_AST.drange, _153_983, quals))
in FStar_Syntax_Syntax.Sig_let (_153_984))
in (

let env = (FStar_Parser_Env.push_sigelt env s)
in (env, (s)::[])))))))
end
| _63_2558 -> begin
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
in (let _153_988 = (let _153_987 = (let _153_986 = (let _153_985 = (FStar_Parser_Env.qualify env id)
in (_153_985, f, (FStar_Syntax_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_assume (_153_986))
in (_153_987)::[])
in (env, _153_988)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(

let t = (let _153_989 = (close_fun env t)
in (desugar_term env _153_989))
in (

let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (

let se = (let _153_992 = (let _153_991 = (FStar_Parser_Env.qualify env id)
in (let _153_990 = (FStar_List.map trans_qual quals)
in (_153_991, [], t, _153_990, d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_declare_typ (_153_992))
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(

let _63_2585 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (match (_63_2585) with
| (t, _63_2584) -> begin
(

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
in (env, (FStar_List.append ((se')::discs) data_ops)))))))))
end))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(

let t = (desugar_term env term)
in (

let t = (let _153_997 = (let _153_993 = (FStar_Syntax_Syntax.null_binder t)
in (_153_993)::[])
in (let _153_996 = (let _153_995 = (let _153_994 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (Prims.fst _153_994))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _153_995))
in (FStar_Syntax_Util.arrow _153_997 _153_996)))
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

let _63_2614 = (desugar_binders env binders)
in (match (_63_2614) with
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

let _63_2630 = (desugar_binders env eff_binders)
in (match (_63_2630) with
| (env, binders) -> begin
(

let _63_2641 = (

let _63_2633 = (head_and_args defn)
in (match (_63_2633) with
| (head, args) -> begin
(

let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _63_2637 -> begin
(let _153_1002 = (let _153_1001 = (let _153_1000 = (let _153_999 = (let _153_998 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat "Effect " _153_998))
in (Prims.strcat _153_999 " not found"))
in (_153_1000, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_153_1001))
in (Prims.raise _153_1002))
end)
in (let _153_1003 = (desugar_args env args)
in (ed, _153_1003)))
end))
in (match (_63_2641) with
| (ed, args) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let sub = (fun _63_2647 -> (match (_63_2647) with
| (_63_2645, x) -> begin
(

let _63_2650 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_63_2650) with
| (edb, x) -> begin
(

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _153_1007 = (let _153_1006 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _153_1006))
in ([], _153_1007)))
end))
end))
in (

let ed = (let _153_1024 = (FStar_List.map trans_qual quals)
in (let _153_1023 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _153_1022 = (let _153_1008 = (sub ([], ed.FStar_Syntax_Syntax.signature))
in (Prims.snd _153_1008))
in (let _153_1021 = (sub ed.FStar_Syntax_Syntax.ret)
in (let _153_1020 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _153_1019 = (sub ed.FStar_Syntax_Syntax.bind_wlp)
in (let _153_1018 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _153_1017 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _153_1016 = (sub ed.FStar_Syntax_Syntax.ite_wlp)
in (let _153_1015 = (sub ed.FStar_Syntax_Syntax.wp_binop)
in (let _153_1014 = (sub ed.FStar_Syntax_Syntax.wp_as_type)
in (let _153_1013 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _153_1012 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _153_1011 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _153_1010 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _153_1009 = (sub ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _153_1024; FStar_Syntax_Syntax.mname = _153_1023; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _153_1022; FStar_Syntax_Syntax.ret = _153_1021; FStar_Syntax_Syntax.bind_wp = _153_1020; FStar_Syntax_Syntax.bind_wlp = _153_1019; FStar_Syntax_Syntax.if_then_else = _153_1018; FStar_Syntax_Syntax.ite_wp = _153_1017; FStar_Syntax_Syntax.ite_wlp = _153_1016; FStar_Syntax_Syntax.wp_binop = _153_1015; FStar_Syntax_Syntax.wp_as_type = _153_1014; FStar_Syntax_Syntax.close_wp = _153_1013; FStar_Syntax_Syntax.assert_p = _153_1012; FStar_Syntax_Syntax.assume_p = _153_1011; FStar_Syntax_Syntax.null_wp = _153_1010; FStar_Syntax_Syntax.trivial = _153_1009}))))))))))))))))
in (

let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (

let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[]))))))
end))
end)))
end
| FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.RedefineEffect (_63_2656)) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(desugar_effect env d [] eff_name eff_binders eff_kind eff_decls (fun mname qualifiers binders eff_k lookup -> (

let dummy_tscheme = (let _153_1034 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in ([], _153_1034))
in (let _153_1043 = (let _153_1042 = (let _153_1041 = (lookup "return")
in (let _153_1040 = (lookup "bind_wp")
in (let _153_1039 = (lookup "bind_wlp")
in (let _153_1038 = (lookup "ite_wp")
in (let _153_1037 = (lookup "ite_wlp")
in (let _153_1036 = (lookup "wp_as_type")
in (let _153_1035 = (lookup "null_wp")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret = _153_1041; FStar_Syntax_Syntax.bind_wp = _153_1040; FStar_Syntax_Syntax.bind_wlp = _153_1039; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = _153_1038; FStar_Syntax_Syntax.ite_wlp = _153_1037; FStar_Syntax_Syntax.wp_binop = dummy_tscheme; FStar_Syntax_Syntax.wp_as_type = _153_1036; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = _153_1035; FStar_Syntax_Syntax.trivial = dummy_tscheme})))))))
in (_153_1042, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (_153_1043)))))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(desugar_effect env d quals eff_name eff_binders eff_kind eff_decls (fun mname qualifiers binders eff_k lookup -> (let _153_1067 = (let _153_1066 = (let _153_1065 = (lookup "return")
in (let _153_1064 = (lookup "bind_wp")
in (let _153_1063 = (lookup "bind_wlp")
in (let _153_1062 = (lookup "if_then_else")
in (let _153_1061 = (lookup "ite_wp")
in (let _153_1060 = (lookup "ite_wlp")
in (let _153_1059 = (lookup "wp_binop")
in (let _153_1058 = (lookup "wp_as_type")
in (let _153_1057 = (lookup "close_wp")
in (let _153_1056 = (lookup "assert_p")
in (let _153_1055 = (lookup "assume_p")
in (let _153_1054 = (lookup "null_wp")
in (let _153_1053 = (lookup "trivial")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret = _153_1065; FStar_Syntax_Syntax.bind_wp = _153_1064; FStar_Syntax_Syntax.bind_wlp = _153_1063; FStar_Syntax_Syntax.if_then_else = _153_1062; FStar_Syntax_Syntax.ite_wp = _153_1061; FStar_Syntax_Syntax.ite_wlp = _153_1060; FStar_Syntax_Syntax.wp_binop = _153_1059; FStar_Syntax_Syntax.wp_as_type = _153_1058; FStar_Syntax_Syntax.close_wp = _153_1057; FStar_Syntax_Syntax.assert_p = _153_1056; FStar_Syntax_Syntax.assume_p = _153_1055; FStar_Syntax_Syntax.null_wp = _153_1054; FStar_Syntax_Syntax.trivial = _153_1053})))))))))))))
in (_153_1066, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_new_effect (_153_1067))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(

let lookup = (fun l -> (match ((FStar_Parser_Env.try_lookup_effect_name env l)) with
| None -> begin
(let _153_1074 = (let _153_1073 = (let _153_1072 = (let _153_1071 = (let _153_1070 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat "Effect name " _153_1070))
in (Prims.strcat _153_1071 " not found"))
in (_153_1072, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_153_1073))
in (Prims.raise _153_1074))
end
| Some (l) -> begin
l
end))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let lift = (let _153_1075 = (desugar_term env l.FStar_Parser_AST.lift_op)
in ([], _153_1075))
in (

let se = FStar_Syntax_Syntax.Sig_sub_effect (({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end)))


let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _63_2701 d -> (match (_63_2701) with
| (env, sigelts) -> begin
(

let _63_2705 = (desugar_decl env d)
in (match (_63_2705) with
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

let _63_2728 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _153_1088 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in (_153_1088, mname, decls, true))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _153_1089 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in (_153_1089, mname, decls, false))
end)
in (match (_63_2728) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let _63_2731 = (desugar_decls env decls)
in (match (_63_2731) with
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
| FStar_Parser_AST.Interface (mname, _63_2742, _63_2744) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (

let _63_2752 = (desugar_modul_common curmod env m)
in (match (_63_2752) with
| (x, y, _63_2751) -> begin
(x, y)
end))))


let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (

let _63_2758 = (desugar_modul_common None env m)
in (match (_63_2758) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (

let _63_2760 = if (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _153_1100 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _153_1100))
end else begin
()
end
in (let _153_1101 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in (_153_1101, modul))))
end)))


let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (

let _63_2773 = (FStar_List.fold_left (fun _63_2766 m -> (match (_63_2766) with
| (env, mods) -> begin
(

let _63_2770 = (desugar_modul env m)
in (match (_63_2770) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_63_2773) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (

let _63_2778 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_63_2778) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (

let _63_2779 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.modules = _63_2779.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _63_2779.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _63_2779.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _63_2779.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _63_2779.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _63_2779.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _63_2779.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _63_2779.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _63_2779.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _63_2779.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _63_2779.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (

let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




