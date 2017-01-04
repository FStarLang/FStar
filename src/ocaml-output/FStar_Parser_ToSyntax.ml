
open Prims

let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _67_1 -> (match (_67_1) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| _67_33 -> begin
None
end))


let trans_qual : FStar_Range.range  ->  FStar_Ident.lident Prims.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r maybe_effect_id _67_2 -> (match (_67_2) with
| FStar_Parser_AST.Private -> begin
FStar_Syntax_Syntax.Private
end
| FStar_Parser_AST.Assumption -> begin
FStar_Syntax_Syntax.Assumption
end
| FStar_Parser_AST.Unfold_for_unification_and_vcgen -> begin
FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
end
| FStar_Parser_AST.Inline_for_extraction -> begin
FStar_Syntax_Syntax.Inline_for_extraction
end
| FStar_Parser_AST.NoExtract -> begin
FStar_Syntax_Syntax.NoExtract
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

let _67_49 = (FStar_TypeChecker_Errors.warn r "The \'opaque\' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given \'opaque val f : t\', the behavior was to exclude the definition of \'f\' to the SMT solver. This corresponds roughly to the new \'irreducible\' qualifier. (2) Given \'opaque type t = t\'\', the behavior was to provide the definition of \'t\' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of \'unfoldable\' (which is currently the default).")
in FStar_Syntax_Syntax.Visible_default)
end
| FStar_Parser_AST.Reflectable -> begin
(match (maybe_effect_id) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Qualifier reflect only supported on effects"), (r)))))
end
| Some (effect_id) -> begin
FStar_Syntax_Syntax.Reflectable (effect_id)
end)
end
| FStar_Parser_AST.Reifiable -> begin
FStar_Syntax_Syntax.Reifiable
end
| FStar_Parser_AST.Noeq -> begin
FStar_Syntax_Syntax.Noeq
end
| FStar_Parser_AST.Unopteq -> begin
FStar_Syntax_Syntax.Unopteq
end
| FStar_Parser_AST.DefaultEffect -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("The \'default\' qualifier on effects is no longer supported"), (r)))))
end
| (FStar_Parser_AST.Inline) | (FStar_Parser_AST.Visible) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unsupported qualifier"), (r)))))
end))


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun _67_3 -> (match (_67_3) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _67_4 -> (match (_67_4) with
| FStar_Parser_AST.Hash -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| _67_69 -> begin
None
end))


let arg_withimp_e = (fun imp t -> ((t), ((as_imp imp))))


let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| _67_76 -> begin
((t), (None))
end))


let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_67_80) -> begin
true
end
| _67_83 -> begin
false
end)))))


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _67_88 -> begin
t
end))


let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _165_25 = (let _165_24 = (FStar_Ident.lid_of_path (("Type0")::[]) r)
in FStar_Parser_AST.Name (_165_24))
in (FStar_Parser_AST.mk_term _165_25 r FStar_Parser_AST.Kind)))


let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _165_29 = (let _165_28 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_165_28))
in (FStar_Parser_AST.mk_term _165_29 r FStar_Parser_AST.Kind)))


let rec is_comp_type : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> (match (t.FStar_Parser_AST.tm) with
| (FStar_Parser_AST.Name (l)) | (FStar_Parser_AST.Construct (l, _)) -> begin
(let _165_34 = (FStar_Parser_Env.try_lookup_effect_name env l)
in (FStar_All.pipe_right _165_34 FStar_Option.isSome))
end
| FStar_Parser_AST.App (head, _67_101, _67_103) -> begin
(is_comp_type env head)
end
| (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) | (FStar_Parser_AST.LetOpen (_, t)) -> begin
(is_comp_type env t)
end
| _67_117 -> begin
false
end))


let unit_ty : FStar_Parser_AST.term = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) FStar_Range.dummyRange FStar_Parser_AST.Type)


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _165_44 = (let _165_43 = (let _165_42 = (let _165_41 = (FStar_Parser_AST.compile_op n s)
in ((_165_41), (r)))
in (FStar_Ident.mk_ident _165_42))
in (_165_43)::[])
in (FStar_All.pipe_right _165_44 FStar_Ident.lid_of_ids)))


let op_as_term : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (

let r = (fun l dd -> (let _165_58 = (let _165_57 = (FStar_Syntax_Syntax.lid_as_fv (FStar_Ident.set_lid_range l rng) dd None)
in (FStar_All.pipe_right _165_57 FStar_Syntax_Syntax.fv_to_tm))
in Some (_165_58)))
in (

let fallback = (fun _67_129 -> (match (()) with
| () -> begin
(match (s) with
| "=" -> begin
(r FStar_Syntax_Const.op_Eq FStar_Syntax_Syntax.Delta_equational)
end
| ":=" -> begin
(r FStar_Syntax_Const.write_lid FStar_Syntax_Syntax.Delta_equational)
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
| "-" when (arity = (Prims.parse_int "1")) -> begin
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
(r FStar_Syntax_Const.not_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))))
end
| "==" -> begin
(r FStar_Syntax_Const.eq2_lid FStar_Syntax_Syntax.Delta_constant)
end
| "<<" -> begin
(r FStar_Syntax_Const.precedes_lid FStar_Syntax_Syntax.Delta_constant)
end
| "/\\" -> begin
(r FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))))
end
| "\\/" -> begin
(r FStar_Syntax_Const.or_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))))
end
| "==>" -> begin
(r FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))))
end
| "<==>" -> begin
(r FStar_Syntax_Const.iff_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))))
end
| _67_157 -> begin
None
end)
end))
in (match ((let _165_61 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _165_61))) with
| Some (t) -> begin
Some ((Prims.fst t))
end
| _67_161 -> begin
(fallback ())
end))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _165_68 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _165_68)))


let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_67_170) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let _67_177 = (FStar_Parser_Env.push_bv env x)
in (match (_67_177) with
| (env, _67_176) -> begin
((env), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (_67_179, term) -> begin
(let _165_75 = (free_type_vars env term)
in ((env), (_165_75)))
end
| FStar_Parser_AST.TAnnotated (id, _67_185) -> begin
(

let _67_191 = (FStar_Parser_Env.push_bv env id)
in (match (_67_191) with
| (env, _67_190) -> begin
((env), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _165_76 = (free_type_vars env t)
in ((env), (_165_76)))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _165_79 = (unparen t)
in _165_79.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_67_197) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _67_203 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Projector (_)) | (FStar_Parser_AST.Discrim (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Assign (_, t)) | (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_67_246, ts) -> begin
(FStar_List.collect (fun _67_253 -> (match (_67_253) with
| (t, _67_252) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_67_255, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _67_262) -> begin
(let _165_82 = (free_type_vars env t1)
in (let _165_81 = (free_type_vars env t2)
in (FStar_List.append _165_82 _165_81)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(

let _67_271 = (free_type_vars_b env b)
in (match (_67_271) with
| (env, f) -> begin
(let _165_83 = (free_type_vars env t)
in (FStar_List.append f _165_83))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(

let _67_287 = (FStar_List.fold_left (fun _67_280 binder -> (match (_67_280) with
| (env, free) -> begin
(

let _67_284 = (free_type_vars_b env binder)
in (match (_67_284) with
| (env, f) -> begin
((env), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (_67_287) with
| (env, free) -> begin
(let _165_86 = (free_type_vars env body)
in (FStar_List.append free _165_86))
end))
end
| FStar_Parser_AST.Project (t, _67_290) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.collect (free_type_vars env) cattributes)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t -> (match ((let _165_93 = (unparen t)
in _165_93.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _67_339 -> begin
((t), (args))
end))
in (aux [] t)))


let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _165_98 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _165_98))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _165_102 = (let _165_101 = (let _165_100 = (tm_type x.FStar_Ident.idRange)
in ((x), (_165_100)))
in FStar_Parser_AST.TAnnotated (_165_101))
in (FStar_Parser_AST.mk_binder _165_102 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))


let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _165_107 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _165_107))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _165_111 = (let _165_110 = (let _165_109 = (tm_type x.FStar_Ident.idRange)
in ((x), (_165_109)))
in FStar_Parser_AST.TAnnotated (_165_110))
in (FStar_Parser_AST.mk_binder _165_111 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let t = (match ((let _165_112 = (unparen t)
in _165_112.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_67_352) -> begin
t
end
| _67_355 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))


let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _67_365 -> begin
((bs), (t))
end))


let rec is_var_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatTvar (_, _)) | (FStar_Parser_AST.PatVar (_, _)) -> begin
true
end
| FStar_Parser_AST.PatAscribed (p, _67_382) -> begin
(is_var_pattern p)
end
| _67_386 -> begin
false
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _67_390) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_67_396); FStar_Parser_AST.prange = _67_394}, _67_400) -> begin
true
end
| _67_404 -> begin
false
end))


let replace_unit_pattern : FStar_Parser_AST.pattern  ->  FStar_Parser_AST.pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatConst (FStar_Const.Const_unit) -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatAscribed ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)), (unit_ty)))) p.FStar_Parser_AST.prange)
end
| _67_409 -> begin
p
end))


let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _67_421 = (destruct_app_pattern env is_top_level p)
in (match (_67_421) with
| (name, args, _67_420) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _67_426); FStar_Parser_AST.prange = _67_423}, args) when is_top_level -> begin
(let _165_130 = (let _165_129 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_165_129))
in ((_165_130), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _67_437); FStar_Parser_AST.prange = _67_434}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| _67_445 -> begin
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
| LocalBinder (_67_448) -> begin
_67_448
end))


let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_67_451) -> begin
_67_451
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _67_5 -> (match (_67_5) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| _67_458 -> begin
(FStar_All.failwith "Impossible")
end))


let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _67_6 -> (match (_67_6) with
| (None, k) -> begin
(let _165_167 = (FStar_Syntax_Syntax.null_binder k)
in ((_165_167), (env)))
end
| (Some (a), k) -> begin
(

let _67_471 = (FStar_Parser_Env.push_bv env a)
in (match (_67_471) with
| (env, a) -> begin
(((((

let _67_472 = a
in {FStar_Syntax_Syntax.ppname = _67_472.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_472.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env))
end))
end))


type env_t =
FStar_Parser_Env.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _67_477 -> (match (_67_477) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))


let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))


let mk_ref_read = (fun tm -> (

let tm' = (let _165_180 = (let _165_179 = (let _165_175 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _165_175))
in (let _165_178 = (let _165_177 = (let _165_176 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_165_176)))
in (_165_177)::[])
in ((_165_179), (_165_178))))
in FStar_Syntax_Syntax.Tm_app (_165_180))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc = (fun tm -> (

let tm' = (let _165_187 = (let _165_186 = (let _165_182 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _165_182))
in (let _165_185 = (let _165_184 = (let _165_183 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_165_183)))
in (_165_184)::[])
in ((_165_186), (_165_185))))
in FStar_Syntax_Syntax.Tm_app (_165_187))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign = (fun t1 t2 pos -> (

let tm = (let _165_199 = (let _165_198 = (let _165_191 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _165_191))
in (let _165_197 = (let _165_196 = (let _165_192 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (_165_192)))
in (let _165_195 = (let _165_194 = (let _165_193 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (_165_193)))
in (_165_194)::[])
in (_165_196)::_165_195))
in ((_165_198), (_165_197))))
in FStar_Syntax_Syntax.Tm_app (_165_199))
in (FStar_Syntax_Syntax.mk tm None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun _67_7 -> (match (_67_7) with
| ("repr") | ("post") | ("pre") | ("wp") -> begin
true
end
| _67_494 -> begin
false
end))


let rec sum_to_universe : FStar_Syntax_Syntax.universe  ->  Prims.int  ->  FStar_Syntax_Syntax.universe = (fun u n -> if (n = (Prims.parse_int "0")) then begin
u
end else begin
(let _165_206 = (sum_to_universe u (n - (Prims.parse_int "1")))
in FStar_Syntax_Syntax.U_succ (_165_206))
end)


let int_to_universe : Prims.int  ->  FStar_Syntax_Syntax.universe = (fun n -> (sum_to_universe FStar_Syntax_Syntax.U_zero n))


let rec desugar_maybe_non_constant_universe : FStar_Parser_AST.term  ->  (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun t -> (match ((let _165_211 = (unparen t)
in _165_211.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(let _165_212 = (FStar_TypeChecker_Env.new_u_univ ())
in FStar_Util.Inr (_165_212))
end
| FStar_Parser_AST.Uvar (u) -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_name (u))
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (repr, _67_504)) -> begin
(

let n = (FStar_Util.int_of_string repr)
in (

let _67_509 = if (n < (Prims.parse_int "0")) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Negative universe constant  are not supported : " repr)), (t.FStar_Parser_AST.range)))))
end else begin
()
end
in FStar_Util.Inl (n)))
end
| FStar_Parser_AST.Op (op_plus, (t1)::(t2)::[]) -> begin
(

let _67_517 = ()
in (

let u1 = (desugar_maybe_non_constant_universe t1)
in (

let u2 = (desugar_maybe_non_constant_universe t2)
in (match (((u1), (u2))) with
| (FStar_Util.Inl (n1), FStar_Util.Inl (n2)) -> begin
FStar_Util.Inl ((n1 + n2))
end
| ((FStar_Util.Inl (n), FStar_Util.Inr (u))) | ((FStar_Util.Inr (u), FStar_Util.Inl (n))) -> begin
(let _165_213 = (sum_to_universe u n)
in FStar_Util.Inr (_165_213))
end
| (FStar_Util.Inr (u1), FStar_Util.Inr (u2)) -> begin
(let _165_217 = (let _165_216 = (let _165_215 = (let _165_214 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "This universe might contain a sum of two universe variables " _165_214))
in ((_165_215), (t.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_165_216))
in (Prims.raise _165_217))
end))))
end
| FStar_Parser_AST.App (_67_540) -> begin
(

let rec aux = (fun t univargs -> (match ((let _165_222 = (unparen t)
in _165_222.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, targ, _67_548) -> begin
(

let uarg = (desugar_maybe_non_constant_universe targ)
in (aux t ((uarg)::univargs)))
end
| FStar_Parser_AST.Var (max_lid) -> begin
(

let _67_554 = ()
in if (FStar_List.existsb (fun _67_8 -> (match (_67_8) with
| FStar_Util.Inr (_67_558) -> begin
true
end
| _67_561 -> begin
false
end)) univargs) then begin
(let _165_226 = (let _165_225 = (FStar_List.map (fun _67_9 -> (match (_67_9) with
| FStar_Util.Inl (n) -> begin
(int_to_universe n)
end
| FStar_Util.Inr (u) -> begin
u
end)) univargs)
in FStar_Syntax_Syntax.U_max (_165_225))
in FStar_Util.Inr (_165_226))
end else begin
(

let nargs = (FStar_List.map (fun _67_10 -> (match (_67_10) with
| FStar_Util.Inl (n) -> begin
n
end
| FStar_Util.Inr (_67_571) -> begin
(FStar_All.failwith "impossible")
end)) univargs)
in (let _165_230 = (FStar_List.fold_left (fun m n -> if (m > n) then begin
m
end else begin
n
end) (Prims.parse_int "0") nargs)
in FStar_Util.Inl (_165_230)))
end)
end
| _67_577 -> begin
(let _165_235 = (let _165_234 = (let _165_233 = (let _165_232 = (let _165_231 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat _165_231 " in universe context"))
in (Prims.strcat "Unexpected term " _165_232))
in ((_165_233), (t.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_165_234))
in (Prims.raise _165_235))
end))
in (aux t []))
end
| _67_579 -> begin
(let _165_240 = (let _165_239 = (let _165_238 = (let _165_237 = (let _165_236 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat _165_236 " in universe context"))
in (Prims.strcat "Unexpected term " _165_237))
in ((_165_238), (t.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_165_239))
in (Prims.raise _165_240))
end))


let rec desugar_universe : FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.universe = (fun t -> (

let u = (desugar_maybe_non_constant_universe t)
in (match (u) with
| FStar_Util.Inl (n) -> begin
(int_to_universe n)
end
| FStar_Util.Inr (u) -> begin
u
end)))


let check_fields = (fun env fields rg -> (

let _67_592 = (FStar_List.hd fields)
in (match (_67_592) with
| (f, _67_591) -> begin
(

let record = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (

let check_field = (fun _67_598 -> (match (_67_598) with
| (f', _67_597) -> begin
if (FStar_Parser_Env.belongs_to_record env f' record) then begin
()
end else begin
(

let msg = (FStar_Util.format3 "Field %s belongs to record type %s, whereas field %s does not" f.FStar_Ident.str record.FStar_Parser_Env.typename.FStar_Ident.str f'.FStar_Ident.str)
in (Prims.raise (FStar_Syntax_Syntax.Error (((msg), (rg))))))
end
end))
in (

let _67_600 = (let _165_248 = (FStar_List.tl fields)
in (FStar_List.iter check_field _165_248))
in (match (()) with
| () -> begin
record
end))))
end)))


let rec desugar_data_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat) = (fun env p is_mut -> (

let check_linear_pattern_variables = (fun p -> (

let rec pat_vars = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_dot_term (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_constant (_)) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (_67_620, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _67_628 -> (match (_67_628) with
| (p, _67_627) -> begin
(let _165_305 = (pat_vars p)
in (FStar_Util.set_union out _165_305))
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
(Prims.raise (FStar_Syntax_Syntax.Error ((("Disjunctive pattern binds different variables in each case"), (p.FStar_Syntax_Syntax.p)))))
end else begin
xs
end)
end))
in (pat_vars p)))
in (

let _67_651 = (match (((is_mut), (p.FStar_Parser_AST.pat))) with
| ((false, _)) | ((true, FStar_Parser_AST.PatVar (_))) -> begin
()
end
| (true, _67_649) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("let-mutable is for variables only"), (p.FStar_Parser_AST.prange)))))
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
((l), (e), (y))
end
| _67_662 -> begin
(

let _67_665 = (push_bv_maybe_mut e x)
in (match (_67_665) with
| (e, x) -> begin
(((x)::l), (e), (x))
end))
end))
in (

let rec aux = (fun loc env p -> (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Parser_AST.prange))
in (

let pos_r = (fun r q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (op) -> begin
(let _165_334 = (let _165_333 = (let _165_332 = (let _165_331 = (let _165_330 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") op)
in (FStar_Ident.id_of_text _165_330))
in ((_165_331), (None)))
in FStar_Parser_AST.PatVar (_165_332))
in {FStar_Parser_AST.pat = _165_333; FStar_Parser_AST.prange = p.FStar_Parser_AST.prange})
in (aux loc env _165_334))
end
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(

let _67_689 = (aux loc env p)
in (match (_67_689) with
| (loc, env, var, p, _67_688) -> begin
(

let _67_706 = (FStar_List.fold_left (fun _67_693 p -> (match (_67_693) with
| (loc, env, ps) -> begin
(

let _67_702 = (aux loc env p)
in (match (_67_702) with
| (loc, env, _67_698, p, _67_701) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (_67_706) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in ((loc), (env), (var), (pat), (false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _67_717 = (aux loc env p)
in (match (_67_717) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (_67_719) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t = (let _165_337 = (close_fun env t)
in (desugar_term env _165_337))
in LocalBinder ((((

let _67_726 = x
in {FStar_Syntax_Syntax.ppname = _67_726.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_726.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (aq))))
end)
in ((loc), (env'), (binder), (p), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _165_338 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_165_338), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _165_339 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_165_339), (false))))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let _67_745 = (resolvex loc env x)
in (match (_67_745) with
| (loc, env, xbv) -> begin
(let _165_340 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc), (env), (LocalBinder (((xbv), (aq)))), (_165_340), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _165_341 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), ([])))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_165_341), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _67_751}, args) -> begin
(

let _67_773 = (FStar_List.fold_right (fun arg _67_762 -> (match (_67_762) with
| (loc, env, args) -> begin
(

let _67_769 = (aux loc env arg)
in (match (_67_769) with
| (loc, env, _67_766, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (_67_773) with
| (loc, env, args) -> begin
(

let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _165_344 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_165_344), (false)))))
end))
end
| FStar_Parser_AST.PatApp (_67_777) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let _67_797 = (FStar_List.fold_right (fun pat _67_785 -> (match (_67_785) with
| (loc, env, pats) -> begin
(

let _67_793 = (aux loc env pat)
in (match (_67_793) with
| (loc, env, _67_789, pat, _67_792) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (_67_797) with
| (loc, env, pats) -> begin
(

let pat = (let _165_357 = (let _165_356 = (let _165_352 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _165_352))
in (let _165_355 = (let _165_354 = (let _165_353 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_165_353), ([])))
in FStar_Syntax_Syntax.Pat_cons (_165_354))
in (FStar_All.pipe_left _165_356 _165_355)))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _165_351 = (let _165_350 = (let _165_349 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_165_349), ((((hd), (false)))::(((tl), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (_165_350))
in (FStar_All.pipe_left (pos_r r) _165_351)))) pats _165_357))
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc), (env), (LocalBinder (((x), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let _67_823 = (FStar_List.fold_left (fun _67_810 p -> (match (_67_810) with
| (loc, env, pats) -> begin
(

let _67_819 = (aux loc env p)
in (match (_67_819) with
| (loc, env, _67_815, pat, _67_818) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (_67_823) with
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

let _67_829 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (match (_67_829) with
| (constr, _67_828) -> begin
(

let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| _67_833 -> begin
(FStar_All.failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _165_360 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_165_360), (false)))))
end))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let record = (check_fields env fields p.FStar_Parser_AST.prange)
in (

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _67_843 -> (match (_67_843) with
| (f, p) -> begin
((f.FStar_Ident.ident), (p))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _67_848 -> (match (_67_848) with
| (f, _67_847) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _67_852 -> (match (_67_852) with
| (g, _67_851) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.idText)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_67_855, p) -> begin
p
end)
end))))
in (

let app = (let _165_368 = (let _165_367 = (let _165_366 = (let _165_365 = (let _165_364 = (FStar_Ident.lid_of_ids (FStar_List.append record.FStar_Parser_Env.typename.FStar_Ident.ns ((record.FStar_Parser_Env.constrname)::[])))
in FStar_Parser_AST.PatName (_165_364))
in (FStar_Parser_AST.mk_pattern _165_365 p.FStar_Parser_AST.prange))
in ((_165_366), (args)))
in FStar_Parser_AST.PatApp (_165_367))
in (FStar_Parser_AST.mk_pattern _165_368 p.FStar_Parser_AST.prange))
in (

let _67_867 = (aux loc env app)
in (match (_67_867) with
| (env, e, b, p, _67_866) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _165_375 = (let _165_374 = (let _165_373 = (

let _67_872 = fv
in (let _165_372 = (let _165_371 = (let _165_370 = (let _165_369 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_Env.typename), (_165_369)))
in FStar_Syntax_Syntax.Record_ctor (_165_370))
in Some (_165_371))
in {FStar_Syntax_Syntax.fv_name = _67_872.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _67_872.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _165_372}))
in ((_165_373), (args)))
in FStar_Syntax_Syntax.Pat_cons (_165_374))
in (FStar_All.pipe_left pos _165_375))
end
| _67_875 -> begin
p
end)
in ((env), (e), (b), (p), (false)))
end))))))
end))))
in (

let _67_884 = (aux [] env p)
in (match (_67_884) with
| (_67_878, env, b, p, _67_883) -> begin
(

let _67_885 = (let _165_376 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _165_376))
in ((env), (b), (p)))
end))))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p is_mut -> (

let mklet = (fun x -> (let _165_385 = (let _165_384 = (let _165_383 = (FStar_Parser_Env.qualify env x)
in ((_165_383), (FStar_Syntax_Syntax.tun)))
in LetBinder (_165_384))
in ((env), (_165_385), (None))))
in if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(let _165_387 = (let _165_386 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") x)
in (FStar_Ident.id_of_text _165_386))
in (mklet _165_387))
end
| FStar_Parser_AST.PatVar (x, _67_897) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _67_904); FStar_Parser_AST.prange = _67_901}, t) -> begin
(let _165_391 = (let _165_390 = (let _165_389 = (FStar_Parser_Env.qualify env x)
in (let _165_388 = (desugar_term env t)
in ((_165_389), (_165_388))))
in LetBinder (_165_390))
in ((env), (_165_391), (None)))
end
| _67_912 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
(

let _67_916 = (desugar_data_pat env p is_mut)
in (match (_67_916) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _67_924 -> begin
Some (p)
end)
in ((env), (binder), (p)))
end))
end))
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _67_928 env pat -> (

let _67_936 = (desugar_data_pat env pat false)
in (match (_67_936) with
| (env, _67_934, pat) -> begin
((env), (pat))
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _67_941 = env
in {FStar_Parser_Env.curmodule = _67_941.FStar_Parser_Env.curmodule; FStar_Parser_Env.curmonad = _67_941.FStar_Parser_Env.curmonad; FStar_Parser_Env.modules = _67_941.FStar_Parser_Env.modules; FStar_Parser_Env.scope_mods = _67_941.FStar_Parser_Env.scope_mods; FStar_Parser_Env.sigaccum = _67_941.FStar_Parser_Env.sigaccum; FStar_Parser_Env.sigmap = _67_941.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _67_941.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _67_941.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _67_941.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _67_946 = env
in {FStar_Parser_Env.curmodule = _67_946.FStar_Parser_Env.curmodule; FStar_Parser_Env.curmonad = _67_946.FStar_Parser_Env.curmonad; FStar_Parser_Env.modules = _67_946.FStar_Parser_Env.modules; FStar_Parser_Env.scope_mods = _67_946.FStar_Parser_Env.scope_mods; FStar_Parser_Env.sigaccum = _67_946.FStar_Parser_Env.sigaccum; FStar_Parser_Env.sigmap = _67_946.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _67_946.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _67_946.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _67_946.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_machine_integer : FStar_Parser_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env repr _67_953 range -> (match (_67_953) with
| (signedness, width) -> begin
(

let lid = (Prims.strcat "FStar." (Prims.strcat (match (signedness) with
| FStar_Const.Unsigned -> begin
"U"
end
| FStar_Const.Signed -> begin
""
end) (Prims.strcat "Int" (Prims.strcat (match (width) with
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
end) (Prims.strcat "." (Prims.strcat (match (signedness) with
| FStar_Const.Unsigned -> begin
"u"
end
| FStar_Const.Signed -> begin
""
end) "int_to_t"))))))
in (

let lid = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text lid) range)
in (

let lid = (match ((FStar_Parser_Env.try_lookup_lid env lid)) with
| Some (lid) -> begin
(Prims.fst lid)
end
| None -> begin
(let _165_407 = (FStar_Util.format1 "%s not in scope\n" (FStar_Ident.text_of_lid lid))
in (FStar_All.failwith _165_407))
end)
in (

let repr = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (None))))) None range)
in (let _165_412 = (let _165_411 = (let _165_410 = (let _165_409 = (let _165_408 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr), (_165_408)))
in (_165_409)::[])
in ((lid), (_165_410)))
in FStar_Syntax_Syntax.Tm_app (_165_411))
in (FStar_Syntax_Syntax.mk _165_412 None range))))))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env_t  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk setpos env l -> (

let _67_976 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (match (_67_976) with
| (tm, mut) -> begin
(

let tm = (setpos tm)
in if mut then begin
(let _165_425 = (let _165_424 = (let _165_423 = (mk_ref_read tm)
in ((_165_423), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (_165_424))
in (FStar_All.pipe_left mk _165_425))
end else begin
tm
end)
end)))
and desugar_attributes : FStar_Parser_Env.env  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (match ((let _165_430 = (unparen t)
in _165_430.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = _67_988; FStar_Ident.ident = _67_986; FStar_Ident.nsstr = _67_984; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| _67_992 -> begin
(let _165_434 = (let _165_433 = (let _165_432 = (let _165_431 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " _165_431))
in ((_165_432), (t.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_165_433))
in (Prims.raise _165_434))
end))
in (FStar_List.map desugar_attribute cattributes)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let _67_1000 = e
in {FStar_Syntax_Syntax.n = _67_1000.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _67_1000.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _67_1000.FStar_Syntax_Syntax.vars}))
in (match ((let _165_442 = (unparen top)
in _165_442.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_67_1004) -> begin
(desugar_formula env top)
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(desugar_formula env t)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(desugar_formula env t)
end
| FStar_Parser_AST.Attributes (ts) -> begin
(FStar_All.failwith "Attributes should not be desugared by desugar_term_maybe_top")
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (i, Some (size))) -> begin
(desugar_machine_integer env i size top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Const (c) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (c)))
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("~"), (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("=="), (args)))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[])))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("*", (_67_1032)::(_67_1030)::[]) when (let _165_443 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _165_443 FStar_Option.isNone)) -> begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(let _165_446 = (flatten t1)
in (FStar_List.append _165_446 ((t2)::[])))
end
| _67_1045 -> begin
(t)::[]
end))
in (

let targs = (let _165_450 = (let _165_447 = (unparen top)
in (flatten _165_447))
in (FStar_All.pipe_right _165_450 (FStar_List.map (fun t -> (let _165_449 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _165_449))))))
in (

let _67_1051 = (let _165_451 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _165_451))
in (match (_67_1051) with
| (tup, _67_1050) -> begin
(mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _165_453 = (let _165_452 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (Prims.fst _165_452))
in (FStar_All.pipe_left setpos _165_453))
end
| FStar_Parser_AST.Uvar (u) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Unexpected universe variable " (Prims.strcat (FStar_Ident.text_of_id u) " in non-universe context"))), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Unexpected or unbound operator: " s)), (top.FStar_Parser_AST.range)))))
end
| Some (op) -> begin
if ((FStar_List.length args) > (Prims.parse_int "0")) then begin
(

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _165_455 = (desugar_term env t)
in ((_165_455), (None))))))
in (mk (FStar_Syntax_Syntax.Tm_app (((op), (args))))))
end else begin
op
end
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _67_1071; FStar_Ident.ident = _67_1069; FStar_Ident.nsstr = _67_1067; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _67_1080; FStar_Ident.ident = _67_1078; FStar_Ident.nsstr = _67_1076; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = _67_1089; FStar_Ident.ident = _67_1087; FStar_Ident.nsstr = _67_1085; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(let _165_457 = (let _165_456 = (desugar_universe t)
in FStar_Syntax_Syntax.Tm_type (_165_456))
in (mk _165_457))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _67_1103; FStar_Ident.ident = _67_1101; FStar_Ident.nsstr = _67_1099; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _67_1112; FStar_Ident.ident = _67_1110; FStar_Ident.nsstr = _67_1108; FStar_Ident.str = "True"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _67_1121; FStar_Ident.ident = _67_1119; FStar_Ident.nsstr = _67_1117; FStar_Ident.str = "False"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = _67_1126}) when ((is_special_effect_combinator txt) && (FStar_Parser_Env.is_effect_name env eff_name)) -> begin
(match ((FStar_Parser_Env.try_lookup_effect_defn env eff_name)) with
| Some (ed) -> begin
(let _165_458 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" txt))) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.fvar _165_458 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
end
| None -> begin
(FStar_All.failwith "immpossible special_effect_combinator")
end)
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t2 = (desugar_term env t2)
in (

let _67_1141 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) ident)
in (match (_67_1141) with
| (t1, mut) -> begin
(

let _67_1142 = if (not (mut)) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
end else begin
()
end
in (mk_ref_assign t1 t2 top.FStar_Parser_AST.range))
end)))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(desugar_name mk setpos env l)
end
| FStar_Parser_AST.Projector (l, i) -> begin
(

let found = ((let _165_459 = (FStar_Parser_Env.try_lookup_datacon env l)
in (FStar_Option.isSome _165_459)) || (let _165_460 = (FStar_Parser_Env.try_lookup_effect_defn env l)
in (FStar_Option.isSome _165_460)))
in if found then begin
(let _165_461 = (FStar_Syntax_Util.mk_field_projector_name_from_ident l i)
in (desugar_name mk setpos env _165_461))
end else begin
(let _165_464 = (let _165_463 = (let _165_462 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((_165_462), (top.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_165_463))
in (Prims.raise _165_464))
end)
end
| FStar_Parser_AST.Discrim (lid) -> begin
(match ((FStar_Parser_Env.try_lookup_datacon env lid)) with
| None -> begin
(let _165_467 = (let _165_466 = (let _165_465 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((_165_465), (top.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_165_466))
in (Prims.raise _165_467))
end
| _67_1156 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (desugar_name mk setpos env lid'))
end)
end
| FStar_Parser_AST.Construct (l, args) -> begin
(match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| Some (head) -> begin
(

let _67_1166 = (let _165_468 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in ((_165_468), (true)))
in (match (_67_1166) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _67_1169 -> begin
(

let args = (FStar_List.map (fun _67_1172 -> (match (_67_1172) with
| (t, imp) -> begin
(

let te = (desugar_term env t)
in (arg_withimp_e imp te))
end)) args)
in (

let app = (mk (FStar_Syntax_Syntax.Tm_app (((head), (args)))))
in if is_data then begin
(mk (FStar_Syntax_Syntax.Tm_meta (((app), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end else begin
app
end))
end)
end))
end
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Constructor " (Prims.strcat l.FStar_Ident.str " not found"))), (top.FStar_Parser_AST.range)))))
end)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let _67_1201 = (FStar_List.fold_left (fun _67_1184 b -> (match (_67_1184) with
| (env, tparams, typs) -> begin
(

let _67_1188 = (desugar_binder env b)
in (match (_67_1188) with
| (xopt, t) -> begin
(

let _67_1194 = (match (xopt) with
| None -> begin
(let _165_472 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env), (_165_472)))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_67_1194) with
| (env, x) -> begin
(let _165_476 = (let _165_475 = (let _165_474 = (let _165_473 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _165_473))
in (_165_474)::[])
in (FStar_List.append typs _165_475))
in ((env), ((FStar_List.append tparams (((((

let _67_1195 = x
in {FStar_Syntax_Syntax.ppname = _67_1195.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_1195.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (None)))::[]))), (_165_476)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_67_1201) with
| (env, _67_1199, targs) -> begin
(

let _67_1205 = (let _165_477 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _165_477))
in (match (_67_1205) with
| (tup, _67_1204) -> begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let _67_1212 = (uncurry binders t)
in (match (_67_1212) with
| (bs, t) -> begin
(

let rec aux = (fun env bs _67_11 -> (match (_67_11) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _165_484 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _165_484)))
end
| (hd)::tl -> begin
(

let mlenv = (FStar_Parser_Env.default_ml env)
in (

let bb = (desugar_binder mlenv hd)
in (

let _67_1226 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_67_1226) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _67_1233) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(

let _67_1241 = (as_binder env None b)
in (match (_67_1241) with
| ((x, _67_1238), env) -> begin
(

let f = (desugar_formula env f)
in (let _165_485 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _165_485)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let _67_1262 = (FStar_List.fold_left (fun _67_1250 pat -> (match (_67_1250) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_67_1253, t) -> begin
(let _165_489 = (let _165_488 = (free_type_vars env t)
in (FStar_List.append _165_488 ftvs))
in ((env), (_165_489)))
end
| _67_1258 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (_67_1262) with
| (_67_1260, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (let _165_491 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append _165_491 binders))
in (

let rec aux = (fun env bs sc_pat_opt _67_12 -> (match (_67_12) with
| [] -> begin
(

let body = (desugar_term env body)
in (

let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(

let body = (let _165_501 = (let _165_500 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _165_500 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _165_501 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (None), (body)))::[])))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _165_502 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _165_502))))
end
| (p)::rest -> begin
(

let _67_1286 = (desugar_binding_pat env p)
in (match (_67_1286) with
| (env, b, pat) -> begin
(

let _67_1337 = (match (b) with
| LetBinder (_67_1288) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, _67_1296) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _165_504 = (let _165_503 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_165_503), (p)))
in Some (_165_504))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (_67_1310), _67_1313) -> begin
(

let tup2 = (let _165_505 = (FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _165_505 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _165_513 = (let _165_512 = (let _165_511 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _165_510 = (let _165_509 = (FStar_Syntax_Syntax.as_arg sc)
in (let _165_508 = (let _165_507 = (let _165_506 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _165_506))
in (_165_507)::[])
in (_165_509)::_165_508))
in ((_165_511), (_165_510))))
in FStar_Syntax_Syntax.Tm_app (_165_512))
in (FStar_Syntax_Syntax.mk _165_513 None top.FStar_Parser_AST.range))
in (

let p = (let _165_514 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p), (false)))::[])))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _165_514))
in Some (((sc), (p))))))
end
| (FStar_Syntax_Syntax.Tm_app (_67_1319, args), FStar_Syntax_Syntax.Pat_cons (_67_1324, pats)) -> begin
(

let tupn = (let _165_515 = (FStar_Syntax_Util.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _165_515 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _165_522 = (let _165_521 = (let _165_520 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _165_519 = (let _165_518 = (let _165_517 = (let _165_516 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _165_516))
in (_165_517)::[])
in (FStar_List.append args _165_518))
in ((_165_520), (_165_519))))
in FStar_Syntax_Syntax.Tm_app (_165_521))
in (mk _165_522))
in (

let p = (let _165_523 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p), (false)))::[])))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _165_523))
in Some (((sc), (p))))))
end
| _67_1333 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt)))
end)
in (match (_67_1337) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end)))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = rng; FStar_Parser_AST.level = _67_1339}, phi, _67_1346) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env phi)
in (

let a = (FStar_Ident.set_lid_range a rng)
in (let _165_531 = (let _165_530 = (let _165_529 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _165_528 = (let _165_527 = (FStar_Syntax_Syntax.as_arg phi)
in (let _165_526 = (let _165_525 = (let _165_524 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _165_524))
in (_165_525)::[])
in (_165_527)::_165_526))
in ((_165_529), (_165_528))))
in FStar_Syntax_Syntax.Tm_app (_165_530))
in (mk _165_531))))
end
| FStar_Parser_AST.App (_67_1352, _67_1354, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (match ((let _165_536 = (unparen e)
in _165_536.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e))
end
| _67_1368 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_uinst (((head), (universes))))))
end))
in (aux [] top))
end
| FStar_Parser_AST.App (_67_1371) -> begin
(

let rec aux = (fun args e -> (match ((let _165_541 = (unparen e)
in _165_541.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) when (imp <> FStar_Parser_AST.UnivApp) -> begin
(

let arg = (let _165_542 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _165_542))
in (aux ((arg)::args) e))
end
| _67_1383 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args))))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _165_545 = (let _165_544 = (let _165_543 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((_165_543), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))
in FStar_Syntax_Syntax.Tm_meta (_165_544))
in (mk _165_545))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let env = (FStar_Parser_Env.push_namespace env lid)
in (desugar_term_maybe_top top_level env e))
end
| FStar_Parser_AST.Let (qual, ((pat, _snd))::_tl, body) -> begin
(

let is_rec = (qual = FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun _67_1405 -> (match (()) with
| () -> begin
(

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _67_1409 -> (match (_67_1409) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _165_549 = (destruct_app_pattern env top_level p)
in ((_165_549), (def)))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _165_550 = (destruct_app_pattern env top_level p)
in ((_165_550), (def)))
end
| _67_1415 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _67_1420); FStar_Parser_AST.prange = _67_1417}, t) -> begin
if top_level then begin
(let _165_553 = (let _165_552 = (let _165_551 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_165_551))
in ((_165_552), ([]), (Some (t))))
in ((_165_553), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end
end
| FStar_Parser_AST.PatVar (id, _67_1429) -> begin
if top_level then begin
(let _165_556 = (let _165_555 = (let _165_554 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_165_554))
in ((_165_555), ([]), (None)))
in ((_165_556), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end
end
| _67_1433 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end
end))))
in (

let _67_1462 = (FStar_List.fold_left (fun _67_1438 _67_1447 -> (match (((_67_1438), (_67_1447))) with
| ((env, fnames, rec_bindings), ((f, _67_1441, _67_1443), _67_1446)) -> begin
(

let _67_1458 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let _67_1452 = (FStar_Parser_Env.push_bv env x)
in (match (_67_1452) with
| (env, xx) -> begin
(let _165_560 = (let _165_559 = (FStar_Syntax_Syntax.mk_binder xx)
in (_165_559)::rec_bindings)
in ((env), (FStar_Util.Inl (xx)), (_165_560)))
end))
end
| FStar_Util.Inr (l) -> begin
(let _165_561 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((_165_561), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (_67_1458) with
| (env, lbname, rec_bindings) -> begin
((env), ((lbname)::fnames), (rec_bindings))
end))
end)) ((env), ([]), ([])) funs)
in (match (_67_1462) with
| (env', fnames, rec_bindings) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let desugar_one_def = (fun env lbname _67_1473 -> (match (_67_1473) with
| ((_67_1468, args, result_t), def) -> begin
(

let args = (FStar_All.pipe_right args (FStar_List.map replace_unit_pattern))
in (

let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(

let _67_1482 = if (is_comp_type env t) then begin
(match ((FStar_All.pipe_right args (FStar_List.tryFind (fun x -> (not ((is_var_pattern x))))))) with
| None -> begin
()
end
| Some (p) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
()
end
in (let _165_569 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) _165_569 FStar_Parser_AST.Expr)))
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| _67_1487 -> begin
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
(let _165_571 = (let _165_570 = (FStar_Syntax_Util.incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _165_570 None))
in FStar_Util.Inr (_165_571))
end)
in (

let body = if is_rec then begin
(FStar_Syntax_Subst.close rec_bindings body)
end else begin
body
end
in (mk_lb ((lbname), (FStar_Syntax_Syntax.tun), (body)))))))))
end))
in (

let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (

let body = (desugar_term env' body)
in (let _165_574 = (let _165_573 = (let _165_572 = (FStar_Syntax_Subst.close rec_bindings body)
in ((((is_rec), (lbs))), (_165_572)))
in FStar_Syntax_Syntax.Tm_let (_165_573))
in (FStar_All.pipe_left mk _165_574))))))
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

let _67_1508 = (desugar_binding_pat_maybe_top top_level env pat is_mutable)
in (match (_67_1508) with
| (env, binder, pat) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body = (desugar_term env t2)
in (

let fv = (let _165_581 = (FStar_Syntax_Util.incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _165_581 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]))), (body)))))))
end
| LocalBinder (x, _67_1517) -> begin
(

let body = (desugar_term env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _165_586 = (let _165_585 = (let _165_584 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _165_583 = (let _165_582 = (FStar_Syntax_Util.branch ((pat), (None), (body)))
in (_165_582)::[])
in ((_165_584), (_165_583))))
in FStar_Syntax_Syntax.Tm_match (_165_585))
in (FStar_Syntax_Syntax.mk _165_586 None body.FStar_Syntax_Syntax.pos))
end)
in (let _165_591 = (let _165_590 = (let _165_589 = (let _165_588 = (let _165_587 = (FStar_Syntax_Syntax.mk_binder x)
in (_165_587)::[])
in (FStar_Syntax_Subst.close _165_588 body))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t1))))::[]))), (_165_589)))
in FStar_Syntax_Syntax.Tm_let (_165_590))
in (FStar_All.pipe_left mk _165_591))))
end)
in if is_mutable then begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc))))))
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
in (let _165_602 = (let _165_601 = (let _165_600 = (desugar_term env t1)
in (let _165_599 = (let _165_598 = (let _165_593 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _165_592 = (desugar_term env t2)
in ((_165_593), (None), (_165_592))))
in (let _165_597 = (let _165_596 = (let _165_595 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _165_594 = (desugar_term env t3)
in ((_165_595), (None), (_165_594))))
in (_165_596)::[])
in (_165_598)::_165_597))
in ((_165_600), (_165_599))))
in FStar_Syntax_Syntax.Tm_match (_165_601))
in (mk _165_602)))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(

let r = top.FStar_Parser_AST.range
in (

let handler = (FStar_Parser_AST.mk_function branches r r)
in (

let body = (FStar_Parser_AST.mk_function (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r)), (None), (e)))::[]) r r)
in (

let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Syntax_Const.try_with_lid)) r top.FStar_Parser_AST.level)), (body), (FStar_Parser_AST.Nothing)))) r top.FStar_Parser_AST.level)
in (

let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((a1), (handler), (FStar_Parser_AST.Nothing)))) r top.FStar_Parser_AST.level)
in (desugar_term env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(

let desugar_branch = (fun _67_1558 -> (match (_67_1558) with
| (pat, wopt, b) -> begin
(

let _67_1561 = (desugar_match_pat env pat)
in (match (_67_1561) with
| (env, pat) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _165_605 = (desugar_term env e)
in Some (_165_605))
end)
in (

let b = (desugar_term env b)
in (FStar_Syntax_Util.branch ((pat), (wopt), (b)))))
end))
end))
in (let _165_609 = (let _165_608 = (let _165_607 = (desugar_term env e)
in (let _165_606 = (FStar_List.map desugar_branch branches)
in ((_165_607), (_165_606))))
in FStar_Syntax_Syntax.Tm_match (_165_608))
in (FStar_All.pipe_left mk _165_609)))
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
in (let _165_612 = (let _165_611 = (let _165_610 = (desugar_term env e)
in ((_165_610), (annot), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_165_611))
in (FStar_All.pipe_left mk _165_612)))))
end
| FStar_Parser_AST.Record (_67_1575, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let _67_1587 = (FStar_List.hd fields)
in (match (_67_1587) with
| (f, _67_1586) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _67_1595 -> (match (_67_1595) with
| (g, _67_1594) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| Some (_67_1599, e) -> begin
((fn), (e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _165_620 = (let _165_619 = (let _165_618 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_Parser_Env.typename.FStar_Ident.str)
in ((_165_618), (top.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_165_619))
in (Prims.raise _165_620))
end
| Some (x) -> begin
((fn), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Project (((x), (fn)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (

let user_constrname = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((record.FStar_Parser_Env.constrname)::[])))
in (

let recterm = (match (eopt) with
| None -> begin
(let _165_625 = (let _165_624 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _67_1612 -> (match (_67_1612) with
| (f, _67_1611) -> begin
(let _165_623 = (let _165_622 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _165_622))
in ((_165_623), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (_165_624)))
in FStar_Parser_AST.Construct (_165_625))
end
| Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (let _165_627 = (let _165_626 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_165_626))
in (FStar_Parser_AST.mk_term _165_627 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = (let _165_630 = (let _165_629 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _67_1620 -> (match (_67_1620) with
| (f, _67_1619) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (_165_629)))
in FStar_Parser_AST.Record (_165_630))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _67_1636; FStar_Syntax_Syntax.pos = _67_1634; FStar_Syntax_Syntax.vars = _67_1632}, args); FStar_Syntax_Syntax.tk = _67_1630; FStar_Syntax_Syntax.pos = _67_1628; FStar_Syntax_Syntax.vars = _67_1626}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e = (let _165_637 = (let _165_636 = (let _165_635 = (let _165_634 = (let _165_633 = (let _165_632 = (let _165_631 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_Env.typename), (_165_631)))
in FStar_Syntax_Syntax.Record_ctor (_165_632))
in Some (_165_633))
in (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant _165_634))
in ((_165_635), (args)))
in FStar_Syntax_Syntax.Tm_app (_165_636))
in (FStar_All.pipe_left mk _165_637))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| _67_1650 -> begin
e
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let _67_1657 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_dc_by_field_name env) f)
in (match (_67_1657) with
| (constrname, is_rec) -> begin
(

let e = (desugar_term env e)
in (

let projname = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname f.FStar_Ident.ident)
in (

let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (((constrname), (f.FStar_Ident.ident))))
end else begin
None
end
in (let _165_642 = (let _165_641 = (let _165_640 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projname (FStar_Ident.range_of_lid f)) FStar_Syntax_Syntax.Delta_equational qual)
in (let _165_639 = (let _165_638 = (FStar_Syntax_Syntax.as_arg e)
in (_165_638)::[])
in ((_165_640), (_165_639))))
in FStar_Syntax_Syntax.Tm_app (_165_641))
in (FStar_All.pipe_left mk _165_642)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _67_1668 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _67_1670 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Let (_67_1672, _67_1674, _67_1676) -> begin
(FStar_All.failwith "Not implemented yet")
end
| FStar_Parser_AST.QForall (_67_1680, _67_1682, _67_1684) -> begin
(FStar_All.failwith "Not implemented yet")
end
| FStar_Parser_AST.QExists (_67_1688, _67_1690, _67_1692) -> begin
(FStar_All.failwith "Not implemented yet")
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _67_1699 -> (match (_67_1699) with
| (a, imp) -> begin
(let _165_646 = (desugar_term env a)
in (arg_withimp_e imp _165_646))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error (((msg), (r))))))
in (

let is_requires = (fun _67_1711 -> (match (_67_1711) with
| (t, _67_1710) -> begin
(match ((let _165_654 = (unparen t)
in _165_654.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_67_1713) -> begin
true
end
| _67_1716 -> begin
false
end)
end))
in (

let is_ensures = (fun _67_1721 -> (match (_67_1721) with
| (t, _67_1720) -> begin
(match ((let _165_657 = (unparen t)
in _165_657.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_67_1723) -> begin
true
end
| _67_1726 -> begin
false
end)
end))
in (

let is_app = (fun head _67_1732 -> (match (_67_1732) with
| (t, _67_1731) -> begin
(match ((let _165_662 = (unparen t)
in _165_662.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _67_1736; FStar_Parser_AST.level = _67_1734}, _67_1741, _67_1743) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _67_1747 -> begin
false
end)
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t -> (

let _67_1753 = (head_and_args t)
in (match (_67_1753) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(

let unit_tm = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type)), (FStar_Parser_AST.Nothing))
in (

let nil_pat = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr)), (FStar_Parser_AST.Nothing))
in (

let req_true = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Requires ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.true_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Formula)), (None)))) t.FStar_Parser_AST.range FStar_Parser_AST.Type)), (FStar_Parser_AST.Nothing))
in (

let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Not enough arguments to \'Lemma\'"), (t.FStar_Parser_AST.range)))))
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

let head_and_attributes = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_name_and_attributes env) lemma)
in ((head_and_attributes), (args)))))))
end
| FStar_Parser_AST.Name (l) when (FStar_Parser_Env.is_effect_name env l) -> begin
(let _165_666 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_name_and_attributes env) l)
in ((_165_666), (args)))
end
| FStar_Parser_AST.Name (l) when ((let _165_667 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _165_667 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((let _165_668 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _165_668 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)), ([]))), ((((t), (FStar_Parser_AST.Nothing)))::[]))
end
| _67_1784 when default_ok -> begin
(((((FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)), ([]))), ((((t), (FStar_Parser_AST.Nothing)))::[]))
end
| _67_1786 -> begin
(let _165_670 = (let _165_669 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _165_669))
in (fail _165_670))
end)
end)))
in (

let _67_1791 = (pre_process_comp_typ t)
in (match (_67_1791) with
| ((eff, cattributes), args) -> begin
(

let _67_1792 = if ((FStar_List.length args) = (Prims.parse_int "0")) then begin
(let _165_672 = (let _165_671 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _165_671))
in (fail _165_672))
end else begin
()
end
in (

let _67_1796 = (let _165_674 = (FStar_List.hd args)
in (let _165_673 = (FStar_List.tl args)
in ((_165_674), (_165_673))))
in (match (_67_1796) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (Prims.fst result_arg))
in (

let rest = (desugar_args env rest)
in (

let _67_1821 = (FStar_All.pipe_right rest (FStar_List.partition (fun _67_1802 -> (match (_67_1802) with
| (t, _67_1801) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _67_1808; FStar_Syntax_Syntax.pos = _67_1806; FStar_Syntax_Syntax.vars = _67_1804}, (_67_1813)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _67_1818 -> begin
false
end)
end))))
in (match (_67_1821) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _67_1825 -> (match (_67_1825) with
| (t, _67_1824) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_67_1827, ((arg, _67_1830))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _67_1836 -> begin
(FStar_All.failwith "impos")
end)
end))))
in (

let no_additional_args = ((((FStar_List.length decreases_clause) = (Prims.parse_int "0")) && ((FStar_List.length rest) = (Prims.parse_int "0"))) && ((FStar_List.length cattributes) = (Prims.parse_int "0")))
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

let flags = (FStar_List.append flags cattributes)
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

let pattern = (let _165_677 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _165_677 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (Some (FStar_Syntax_Syntax.imp_tag))))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _67_1852 -> begin
pat
end)
in (let _165_681 = (let _165_680 = (let _165_679 = (let _165_678 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) None pat.FStar_Syntax_Syntax.pos)
in ((_165_678), (aq)))
in (_165_679)::[])
in (ens)::_165_680)
in (req)::_165_681))
end
| _67_1855 -> begin
rest
end)
end else begin
rest
end
in (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = []; FStar_Syntax_Syntax.effect_name = eff; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = rest; FStar_Syntax_Syntax.flags = (FStar_List.append flags decreases_clause)}))))
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
| _67_1867 -> begin
None
end))
in (

let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _67_1874 = t
in {FStar_Syntax_Syntax.n = _67_1874.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _67_1874.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _67_1874.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let _67_1881 = b
in {FStar_Parser_AST.b = _67_1881.FStar_Parser_AST.b; FStar_Parser_AST.brange = _67_1881.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _67_1881.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _165_716 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _165_716)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(

let _67_1895 = (FStar_Parser_Env.push_bv env a)
in (match (_67_1895) with
| (env, a) -> begin
(

let a = (

let _67_1896 = a
in {FStar_Syntax_Syntax.ppname = _67_1896.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_1896.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats = (desugar_pats env pats)
in (

let body = (desugar_formula env body)
in (

let body = (match (pats) with
| [] -> begin
body
end
| _67_1903 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_pattern (pats))))))
end)
in (

let body = (let _165_719 = (let _165_718 = (let _165_717 = (FStar_Syntax_Syntax.mk_binder a)
in (_165_717)::[])
in (no_annot_abs _165_718 body))
in (FStar_All.pipe_left setpos _165_719))
in (let _165_724 = (let _165_723 = (let _165_722 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (let _165_721 = (let _165_720 = (FStar_Syntax_Syntax.as_arg body)
in (_165_720)::[])
in ((_165_722), (_165_721))))
in FStar_Syntax_Syntax.Tm_app (_165_723))
in (FStar_All.pipe_left mk _165_724)))))))
end))
end
| _67_1907 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (let _165_739 = (q ((rest), (pats), (body)))
in (let _165_738 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _165_739 _165_738 FStar_Parser_AST.Formula)))
in (let _165_740 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term _165_740 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _67_1921 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _165_741 = (unparen f)
in _165_741.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(

let f = (desugar_formula env f)
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((l), (f.FStar_Syntax_Syntax.pos), (p)))))))))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _165_743 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _165_743)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _165_745 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _165_745)))
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
| _67_1979 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let _67_2003 = (FStar_List.fold_left (fun _67_1984 b -> (match (_67_1984) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let _67_1986 = b
in {FStar_Parser_AST.b = _67_1986.FStar_Parser_AST.b; FStar_Parser_AST.brange = _67_1986.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _67_1986.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(

let _67_1995 = (FStar_Parser_Env.push_bv env a)
in (match (_67_1995) with
| (env, a) -> begin
(

let a = (

let _67_1996 = a
in {FStar_Syntax_Syntax.ppname = _67_1996.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_1996.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env), ((((a), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| _67_2000 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (_67_2003) with
| (env, tpars) -> begin
((env), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _165_752 = (desugar_typ env t)
in ((Some (x)), (_165_752)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _165_753 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in ((Some (x)), (_165_753)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _165_754 = (desugar_typ env t)
in ((None), (_165_754)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators = (fun quals env t tps k datas -> (

let quals = (FStar_All.pipe_right quals (FStar_List.filter (fun _67_13 -> (match (_67_13) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| _67_2028 -> begin
false
end))))
in (

let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_Env.iface) || env.FStar_Parser_Env.admitted_iface) then begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _165_766 = (let _165_765 = (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in ((disc_name), ([]), (FStar_Syntax_Syntax.tun), (_165_765), ((FStar_Ident.range_of_lid disc_name))))
in FStar_Syntax_Syntax.Sig_declare_typ (_165_766)))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_Parser_Env.env  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (let _165_794 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _67_2044 -> (match (_67_2044) with
| (x, _67_2043) -> begin
(

let _67_2048 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_67_2048) with
| (field_name, _67_2047) -> begin
(

let only_decl = (((let _165_779 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _165_779)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _165_781 = (let _165_780 = (FStar_Parser_Env.current_module env)
in _165_780.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _165_781)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> if only_decl then begin
(let _165_785 = (FStar_List.filter (fun _67_14 -> (match (_67_14) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| _67_2056 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::_165_785)
end else begin
q
end)
in (

let quals = (

let iquals = (FStar_All.pipe_right iquals (FStar_List.filter (fun _67_15 -> (match (_67_15) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| _67_2061 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun), (quals), ((FStar_Ident.range_of_lid field_name))))
in if only_decl then begin
(decl)::[]
end else begin
(

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end else begin
FStar_Syntax_Syntax.Delta_equational
end
in (

let lb = (let _165_788 = (let _165_787 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_165_787))
in {FStar_Syntax_Syntax.lbname = _165_788; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun})
in (

let impl = (let _165_793 = (let _165_792 = (let _165_791 = (let _165_790 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _165_790 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_165_791)::[])
in ((((false), ((lb)::[]))), (p), (_165_792), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (_165_793))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end)))
end)))))
end))
end))))
in (FStar_All.pipe_right _165_794 FStar_List.flatten))))


let mk_data_projector_names = (fun iquals env _67_2073 -> (match (_67_2073) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _67_2076, t, _67_2079, n, quals, _67_2083, _67_2085) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let _67_2091 = (FStar_Syntax_Util.arrow_formals t)
in (match (_67_2091) with
| (formals, _67_2090) -> begin
(match (formals) with
| [] -> begin
[]
end
| _67_2094 -> begin
(

let filter_records = (fun _67_16 -> (match (_67_16) with
| FStar_Syntax_Syntax.RecordConstructor (_67_2097, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| _67_2102 -> begin
None
end))
in (

let fv_qual = (match ((FStar_Util.find_map quals filter_records)) with
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

let _67_2112 = (FStar_Util.first_N n formals)
in (match (_67_2112) with
| (_67_2110, rest) -> begin
(mk_indexed_projector_names iquals fv_qual env lid rest)
end)))))
end)
end))
end
| _67_2114 -> begin
[]
end)
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _165_816 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (_165_816))
end else begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end
in (

let lb = (let _165_821 = (let _165_817 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (_165_817))
in (let _165_820 = (let _165_818 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _165_818))
in (let _165_819 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _165_821; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _165_820; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _165_819})))
in FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (rng), (lids), (quals), ([]))))))


let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (

let tycon_id = (fun _67_17 -> (match (_67_17) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _165_835 = (let _165_834 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_165_834))
in (FStar_Parser_AST.mk_term _165_835 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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

let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (

let apply_binders = (fun t binders -> (

let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _67_2189 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _165_848 = (let _165_847 = (let _165_846 = (binder_to_term b)
in ((out), (_165_846), ((imp_of_aqual b))))
in FStar_Parser_AST.App (_165_847))
in (FStar_Parser_AST.mk_term _165_848 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun _67_18 -> (match (_67_18) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun _67_2204 -> (match (_67_2204) with
| (x, t, _67_2203) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (let _165_854 = (let _165_853 = (let _165_852 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_165_852))
in (FStar_Parser_AST.mk_term _165_853 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _165_854 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _165_856 = (FStar_All.pipe_right fields (FStar_List.map (fun _67_2213 -> (match (_67_2213) with
| (x, _67_2210, _67_2212) -> begin
(FStar_Syntax_Util.unmangle_field_name x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (_165_856)))))))
end
| _67_2215 -> begin
(FStar_All.failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals _67_19 -> (match (_67_19) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let _67_2229 = (typars_of_binders _env binders)
in (match (_67_2229) with
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

let tconstr = (let _165_867 = (let _165_866 = (let _165_865 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_165_865))
in (FStar_Parser_AST.mk_term _165_866 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _165_867 binders))
in (

let qlid = (FStar_Parser_Env.qualify _env id)
in (

let typars = (FStar_Syntax_Subst.close_binders typars)
in (

let k = (FStar_Syntax_Subst.close typars k)
in (

let se = FStar_Syntax_Syntax.Sig_inductive_typ (((qlid), ([]), (typars), (k), (mutuals), ([]), (quals), (rng)))
in (

let _env = (FStar_Parser_Env.push_top_level_rec_binding _env id FStar_Syntax_Syntax.Delta_constant)
in (

let _env2 = (FStar_Parser_Env.push_top_level_rec_binding _env' id FStar_Syntax_Syntax.Delta_constant)
in ((_env), (_env2), (se), (tconstr))))))))))
end))
end
| _67_2242 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env bs -> (

let _67_2257 = (FStar_List.fold_left (fun _67_2248 _67_2251 -> (match (((_67_2248), (_67_2251))) with
| ((env, tps), (x, imp)) -> begin
(

let _67_2254 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_67_2254) with
| (env, y) -> begin
((env), ((((y), (imp)))::tps))
end))
end)) ((env), ([])) bs)
in (match (_67_2257) with
| (env, bs) -> begin
((env), ((FStar_List.rev bs)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt = (match (kopt) with
| None -> begin
(let _165_874 = (tm_type_z id.FStar_Ident.idRange)
in Some (_165_874))
end
| _67_2266 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt)))
in (

let _67_2276 = (desugar_abstract_tc quals env [] tc)
in (match (_67_2276) with
| (_67_2270, _67_2272, se, _67_2275) -> begin
(

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _67_2279, typars, k, [], [], quals, rng) -> begin
(

let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(

let _67_2288 = (let _165_876 = (FStar_Range.string_of_range rng)
in (let _165_875 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _165_876 _165_875)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (

let t = (match (typars) with
| [] -> begin
k
end
| _67_2293 -> begin
(let _165_879 = (let _165_878 = (let _165_877 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (_165_877)))
in FStar_Syntax_Syntax.Tm_arrow (_165_878))
in (FStar_Syntax_Syntax.mk _165_879 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t), (quals), (rng)))))
end
| _67_2296 -> begin
se
end)
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let _67_2308 = (typars_of_binders env binders)
in (match (_67_2308) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _67_20 -> (match (_67_20) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _67_2313 -> begin
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

let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _67_21 -> (match (_67_21) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _67_2321 -> begin
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

let _67_2346 = (match ((let _165_882 = (unparen t)
in _165_882.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Construct (head, args) -> begin
(

let _67_2341 = (match ((FStar_List.rev args)) with
| ((last_arg, _67_2330))::args_rev -> begin
(match ((let _165_883 = (unparen last_arg)
in _165_883.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| _67_2336 -> begin
(([]), (args))
end)
end
| _67_2338 -> begin
(([]), (args))
end)
in (match (_67_2341) with
| (cattributes, args) -> begin
(let _165_884 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head), (args)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (_165_884)))
end))
end
| _67_2343 -> begin
((t), ([]))
end)
in (match (_67_2346) with
| (t, cattributes) -> begin
(

let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (

let typars = (FStar_Syntax_Subst.close_binders typars)
in (

let c = (FStar_Syntax_Subst.close_comp typars c)
in (let _165_888 = (let _165_887 = (FStar_Parser_Env.qualify env id)
in (let _165_886 = (FStar_All.pipe_right quals (FStar_List.filter (fun _67_22 -> (match (_67_22) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _67_2353 -> begin
true
end))))
in ((_165_887), ([]), (typars), (c), (_165_886), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c))), (rng))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_165_888)))))
end))
end else begin
(

let t = (desugar_typ env' t)
in (

let nm = (FStar_Parser_Env.qualify env id)
in (mk_typ_abbrev nm [] typars k t ((nm)::[]) quals rng)))
end
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[])))))))
end))
end
| (FStar_Parser_AST.TyconRecord (_67_2359))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let _67_2365 = (tycon_record_as_variant trec)
in (match (_67_2365) with
| (t, fs) -> begin
(let _165_893 = (let _165_892 = (let _165_891 = (let _165_890 = (let _165_889 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.ids_of_lid _165_889))
in ((_165_890), (fs)))
in FStar_Syntax_Syntax.RecordType (_165_891))
in (_165_892)::quals)
in (desugar_tycon env rng _165_893 ((t)::[])))
end)))
end
| (_67_2369)::_67_2367 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let _67_2380 = et
in (match (_67_2380) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_67_2382) -> begin
(

let trec = tc
in (

let _67_2387 = (tycon_record_as_variant trec)
in (match (_67_2387) with
| (t, fs) -> begin
(let _165_905 = (let _165_904 = (let _165_903 = (let _165_902 = (let _165_901 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.ids_of_lid _165_901))
in ((_165_902), (fs)))
in FStar_Syntax_Syntax.RecordType (_165_903))
in (_165_904)::quals)
in (collect_tcs _165_905 ((env), (tcs)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let _67_2399 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_67_2399) with
| (env, _67_2396, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let _67_2411 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_67_2411) with
| (env, _67_2408, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (binders), (t), (quals))))::tcs))
end))
end
| _67_2413 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (

let _67_2416 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (_67_2416) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _67_24 -> (match (_67_24) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _67_2424, _67_2426, _67_2428, _67_2430), binders, t, quals) -> begin
(

let t = (

let _67_2440 = (typars_of_binders env binders)
in (match (_67_2440) with
| (env, tpars) -> begin
(

let _67_2443 = (push_tparams env tpars)
in (match (_67_2443) with
| (env_tps, tpars) -> begin
(

let t = (desugar_typ env_tps t)
in (

let tpars = (FStar_Syntax_Subst.close_binders tpars)
in (FStar_Syntax_Subst.close tpars t)))
end))
end))
in (let _165_908 = (let _165_907 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in (([]), (_165_907)))
in (_165_908)::[]))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _67_2453, tags, _67_2456), constrs, tconstr, quals) -> begin
(

let tycon = ((tname), (tpars), (k))
in (

let _67_2467 = (push_tparams env tpars)
in (match (_67_2467) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun _67_2471 -> (match (_67_2471) with
| (x, _67_2470) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let _67_2497 = (let _165_920 = (FStar_All.pipe_right constrs (FStar_List.map (fun _67_2478 -> (match (_67_2478) with
| (id, topt, _67_2476, of_notation) -> begin
(

let t = if of_notation then begin
(match (topt) with
| Some (t) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level None))::[]), (tconstr)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
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

let t = (let _165_912 = (FStar_Parser_Env.default_total env_tps)
in (let _165_911 = (close env_tps t)
in (desugar_term _165_912 _165_911)))
in (

let name = (FStar_Parser_Env.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _67_23 -> (match (_67_23) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _67_2492 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (let _165_919 = (let _165_918 = (let _165_917 = (let _165_916 = (let _165_915 = (let _165_914 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _165_914))
in (FStar_Syntax_Util.arrow data_tpars _165_915))
in ((name), (univs), (_165_916), (tname), (ntps), (quals), (mutuals), (rng)))
in FStar_Syntax_Syntax.Sig_datacon (_165_917))
in ((tps), (_165_918)))
in ((name), (_165_919))))))))
end))))
in (FStar_All.pipe_left FStar_List.split _165_920))
in (match (_67_2497) with
| (constrNames, constrs) -> begin
((([]), (FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))))::constrs
end)))
end)))
end
| _67_2499 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (

let _67_2504 = (let _165_921 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals _165_921 rng))
in (match (_67_2504) with
| (bundle, abbrevs) -> begin
(

let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (

let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env abbrevs)
in (

let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projector_names quals env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _67_25 -> (match (_67_25) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _67_2511, tps, k, _67_2515, constrs, quals, _67_2519) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract quals) then begin
(FStar_Syntax_Syntax.Private)::quals
end else begin
quals
end
in (mk_data_discriminators quals env tname tps k constrs))
end
| _67_2524 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env ops)
in ((env), ((FStar_List.append ((bundle)::[]) (FStar_List.append abbrevs ops))))))))))
end)))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end))))))))))


let desugar_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (

let _67_2548 = (FStar_List.fold_left (fun _67_2533 b -> (match (_67_2533) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(

let _67_2541 = (FStar_Parser_Env.push_bv env a)
in (match (_67_2541) with
| (env, a) -> begin
(let _165_930 = (let _165_929 = (FStar_Syntax_Syntax.mk_binder (

let _67_2542 = a
in {FStar_Syntax_Syntax.ppname = _67_2542.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_2542.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_165_929)::binders)
in ((env), (_165_930)))
end))
end
| _67_2545 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end)
end)) ((env), ([])) binders)
in (match (_67_2548) with
| (env, binders) -> begin
((env), ((FStar_List.rev binders)))
end)))


let rec desugar_effect : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  Prims.bool  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_kind eff_decls actions for_free -> (

let env0 = env
in (

let monad_env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (

let _67_2562 = (desugar_binders monad_env eff_binders)
in (match (_67_2562) with
| (env, binders) -> begin
(

let eff_k = (let _165_968 = (FStar_Parser_Env.default_total env)
in (desugar_term _165_968 eff_kind))
in (

let _67_2573 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _67_2566 decl -> (match (_67_2566) with
| (env, out) -> begin
(

let _67_2570 = (desugar_decl env decl)
in (match (_67_2570) with
| (env, ses) -> begin
(let _165_972 = (let _165_971 = (FStar_List.hd ses)
in (_165_971)::out)
in ((env), (_165_972)))
end))
end)) ((env), ([]))))
in (match (_67_2573) with
| (env, decls) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let actions = (FStar_All.pipe_right actions (FStar_List.map (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_67_2577, ((FStar_Parser_AST.TyconAbbrev (name, _67_2580, _67_2582, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (_67_2588, ((def, _67_2595))::((cps_type, _67_2591))::[]); FStar_Parser_AST.range = _67_2586; FStar_Parser_AST.level = _67_2584}), _67_2604))::[]) when (not (for_free)) -> begin
(let _165_978 = (FStar_Parser_Env.qualify env name)
in (let _165_977 = (let _165_974 = (desugar_term env def)
in (FStar_Syntax_Subst.close binders _165_974))
in (let _165_976 = (let _165_975 = (desugar_typ env cps_type)
in (FStar_Syntax_Subst.close binders _165_975))
in {FStar_Syntax_Syntax.action_name = _165_978; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _165_977; FStar_Syntax_Syntax.action_typ = _165_976})))
end
| FStar_Parser_AST.Tycon (_67_2610, ((FStar_Parser_AST.TyconAbbrev (name, _67_2613, _67_2615, defn), _67_2620))::[]) when for_free -> begin
(let _165_981 = (FStar_Parser_Env.qualify env name)
in (let _165_980 = (let _165_979 = (desugar_term env defn)
in (FStar_Syntax_Subst.close binders _165_979))
in {FStar_Syntax_Syntax.action_name = _165_981; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _165_980; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
end
| _67_2626 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples)."), (d.FStar_Parser_AST.drange)))))
end))))
in (

let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (

let lookup = (fun s -> (

let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange))))
in (let _165_985 = (let _165_984 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _165_984))
in (([]), (_165_985)))))
in (

let mname = (FStar_Parser_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (Some (mname))) quals)
in (

let se = if for_free then begin
(

let dummy_tscheme = (let _165_986 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (([]), (_165_986)))
in (let _165_992 = (let _165_991 = (let _165_990 = (let _165_987 = (lookup "repr")
in (Prims.snd _165_987))
in (let _165_989 = (lookup "return")
in (let _165_988 = (lookup "bind")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = _165_990; FStar_Syntax_Syntax.return_repr = _165_989; FStar_Syntax_Syntax.bind_repr = _165_988; FStar_Syntax_Syntax.actions = actions})))
in ((_165_991), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (_165_992)))
end else begin
(

let rr = ((FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right qualifiers FStar_Syntax_Syntax.contains_reflectable))
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (let _165_1008 = (let _165_1007 = (let _165_1006 = (lookup "return_wp")
in (let _165_1005 = (lookup "bind_wp")
in (let _165_1004 = (lookup "if_then_else")
in (let _165_1003 = (lookup "ite_wp")
in (let _165_1002 = (lookup "stronger")
in (let _165_1001 = (lookup "close_wp")
in (let _165_1000 = (lookup "assert_p")
in (let _165_999 = (lookup "assume_p")
in (let _165_998 = (lookup "null_wp")
in (let _165_997 = (lookup "trivial")
in (let _165_996 = if rr then begin
(let _165_993 = (lookup "repr")
in (FStar_All.pipe_left Prims.snd _165_993))
end else begin
FStar_Syntax_Syntax.tun
end
in (let _165_995 = if rr then begin
(lookup "return")
end else begin
un_ts
end
in (let _165_994 = if rr then begin
(lookup "bind")
end else begin
un_ts
end
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = _165_1006; FStar_Syntax_Syntax.bind_wp = _165_1005; FStar_Syntax_Syntax.if_then_else = _165_1004; FStar_Syntax_Syntax.ite_wp = _165_1003; FStar_Syntax_Syntax.stronger = _165_1002; FStar_Syntax_Syntax.close_wp = _165_1001; FStar_Syntax_Syntax.assert_p = _165_1000; FStar_Syntax_Syntax.assume_p = _165_999; FStar_Syntax_Syntax.null_wp = _165_998; FStar_Syntax_Syntax.trivial = _165_997; FStar_Syntax_Syntax.repr = _165_996; FStar_Syntax_Syntax.return_repr = _165_995; FStar_Syntax_Syntax.bind_repr = _165_994; FStar_Syntax_Syntax.actions = actions})))))))))))))
in ((_165_1007), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect (_165_1008))))
end
in (

let env = (FStar_Parser_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right actions (FStar_List.fold_left (fun env a -> (let _165_1011 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_Parser_Env.push_sigelt env _165_1011))) env))
in (

let env = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable)) then begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_Parser_Env.qualify monad_env))
in (

let refl_decl = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]), (d.FStar_Parser_AST.drange)))
in (FStar_Parser_Env.push_sigelt env refl_decl)))
end else begin
env
end
in ((env), ((se)::[]))))))))))))
end)))
end)))))
and desugar_redefine_effect : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl  ->  (FStar_Ident.lident Prims.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier)  ->  FStar_Parser_AST.qualifier Prims.list  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.eff_decl  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d trans_qual quals eff_name eff_binders defn build_sigelt -> (

let env0 = env
in (

let env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (

let _67_2657 = (desugar_binders env eff_binders)
in (match (_67_2657) with
| (env, binders) -> begin
(

let _67_2684 = (

let _67_2660 = (head_and_args defn)
in (match (_67_2660) with
| (head, args) -> begin
(

let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _67_2664 -> begin
(let _165_1038 = (let _165_1037 = (let _165_1036 = (let _165_1035 = (let _165_1034 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat _165_1034 " not found"))
in (Prims.strcat "Effect " _165_1035))
in ((_165_1036), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_165_1037))
in (Prims.raise _165_1038))
end)
in (

let _67_2680 = (match ((FStar_List.rev args)) with
| ((last_arg, _67_2669))::args_rev -> begin
(match ((let _165_1039 = (unparen last_arg)
in _165_1039.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| _67_2675 -> begin
(([]), (args))
end)
end
| _67_2677 -> begin
(([]), (args))
end)
in (match (_67_2680) with
| (cattributes, args) -> begin
(let _165_1041 = (desugar_args env args)
in (let _165_1040 = (desugar_attributes env cattributes)
in ((ed), (_165_1041), (_165_1040))))
end)))
end))
in (match (_67_2684) with
| (ed, args, cattributes) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let sub = (fun _67_2690 -> (match (_67_2690) with
| (_67_2688, x) -> begin
(

let _67_2693 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_67_2693) with
| (edb, x) -> begin
(

let _67_2694 = if ((FStar_List.length args) <> (FStar_List.length edb)) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end else begin
()
end
in (

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _165_1045 = (let _165_1044 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _165_1044))
in (([]), (_165_1045)))))
end))
end))
in (

let mname = (FStar_Parser_Env.qualify env0 eff_name)
in (

let ed = (let _165_1070 = (let _165_1046 = (trans_qual (Some (mname)))
in (FStar_List.map _165_1046 quals))
in (let _165_1069 = (let _165_1047 = (sub (([]), (ed.FStar_Syntax_Syntax.signature)))
in (Prims.snd _165_1047))
in (let _165_1068 = (sub ed.FStar_Syntax_Syntax.ret_wp)
in (let _165_1067 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _165_1066 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _165_1065 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _165_1064 = (sub ed.FStar_Syntax_Syntax.stronger)
in (let _165_1063 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _165_1062 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _165_1061 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _165_1060 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _165_1059 = (sub ed.FStar_Syntax_Syntax.trivial)
in (let _165_1058 = (let _165_1048 = (sub (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd _165_1048))
in (let _165_1057 = (sub ed.FStar_Syntax_Syntax.return_repr)
in (let _165_1056 = (sub ed.FStar_Syntax_Syntax.bind_repr)
in (let _165_1055 = (FStar_List.map (fun action -> (let _165_1054 = (FStar_Parser_Env.qualify env action.FStar_Syntax_Syntax.action_unqualified_name)
in (let _165_1053 = (let _165_1050 = (sub (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd _165_1050))
in (let _165_1052 = (let _165_1051 = (sub (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd _165_1051))
in {FStar_Syntax_Syntax.action_name = _165_1054; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _165_1053; FStar_Syntax_Syntax.action_typ = _165_1052})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = _165_1070; FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _165_1069; FStar_Syntax_Syntax.ret_wp = _165_1068; FStar_Syntax_Syntax.bind_wp = _165_1067; FStar_Syntax_Syntax.if_then_else = _165_1066; FStar_Syntax_Syntax.ite_wp = _165_1065; FStar_Syntax_Syntax.stronger = _165_1064; FStar_Syntax_Syntax.close_wp = _165_1063; FStar_Syntax_Syntax.assert_p = _165_1062; FStar_Syntax_Syntax.assume_p = _165_1061; FStar_Syntax_Syntax.null_wp = _165_1060; FStar_Syntax_Syntax.trivial = _165_1059; FStar_Syntax_Syntax.repr = _165_1058; FStar_Syntax_Syntax.return_repr = _165_1057; FStar_Syntax_Syntax.bind_repr = _165_1056; FStar_Syntax_Syntax.actions = _165_1055}))))))))))))))))
in (

let se = (build_sigelt ed d.FStar_Parser_AST.drange)
in (

let monad_env = env
in (

let env = (FStar_Parser_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun env a -> (let _165_1073 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_Parser_Env.push_sigelt env _165_1073))) env))
in (

let env = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable)) then begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_Parser_Env.qualify monad_env))
in (

let refl_decl = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]), (d.FStar_Parser_AST.drange)))
in (FStar_Parser_Env.push_sigelt env refl_decl)))
end else begin
env
end
in ((env), ((se)::[])))))))))))
end))
end)))))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let trans_qual = (trans_qual d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(

let se = FStar_Syntax_Syntax.Sig_pragma ((((trans_pragma p)), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end
| FStar_Parser_AST.Fsdoc (_67_2716) -> begin
((env), ([]))
end
| FStar_Parser_AST.TopLevelModule (id) -> begin
((env), ([]))
end
| FStar_Parser_AST.Open (lid) -> begin
(

let env = (FStar_Parser_Env.push_namespace env lid)
in ((env), ([])))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _165_1078 = (FStar_Parser_Env.push_module_abbrev env x l)
in ((_165_1078), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, tcs) -> begin
(

let quals = if is_effect then begin
(FStar_Parser_AST.Effect)::d.FStar_Parser_AST.quals
end else begin
d.FStar_Parser_AST.quals
end
in (

let tcs = (FStar_List.map (fun _67_2735 -> (match (_67_2735) with
| (x, _67_2734) -> begin
x
end)) tcs)
in (let _165_1080 = (FStar_List.map (trans_qual None) quals)
in (desugar_tycon env d.FStar_Parser_AST.drange _165_1080 tcs))))
end
| FStar_Parser_AST.TopLevelLet (isrec, lets) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let attrs = d.FStar_Parser_AST.attrs
in (

let attrs = (FStar_List.map (desugar_term env) attrs)
in (match ((let _165_1082 = (let _165_1081 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _165_1081))
in _165_1082.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _67_2746) -> begin
(

let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals = (match (quals) with
| (_67_2754)::_67_2752 -> begin
(FStar_List.map (trans_qual None) quals)
end
| _67_2757 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _67_26 -> (match (_67_26) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_67_2768); FStar_Syntax_Syntax.lbunivs = _67_2766; FStar_Syntax_Syntax.lbtyp = _67_2764; FStar_Syntax_Syntax.lbeff = _67_2762; FStar_Syntax_Syntax.lbdef = _67_2760} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _67_2778; FStar_Syntax_Syntax.lbtyp = _67_2776; FStar_Syntax_Syntax.lbeff = _67_2774; FStar_Syntax_Syntax.lbdef = _67_2772} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _67_2786 -> (match (_67_2786) with
| (_67_2784, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (

let lbs = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _165_1087 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _67_2790 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let _67_2792 = fv
in {FStar_Syntax_Syntax.fv_name = _67_2792.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = _67_2792.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = _67_2790.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _67_2790.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _67_2790.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _67_2790.FStar_Syntax_Syntax.lbdef})))))
in (((Prims.fst lbs)), (_165_1087)))
end else begin
lbs
end
in (

let s = (let _165_1090 = (let _165_1089 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in ((lbs), (d.FStar_Parser_AST.drange), (_165_1089), (quals), (attrs)))
in FStar_Syntax_Syntax.Sig_let (_165_1090))
in (

let env = (FStar_Parser_Env.push_sigelt env s)
in ((env), ((s)::[]))))))))
end
| _67_2799 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end))))
end
| FStar_Parser_AST.Main (t) -> begin
(

let e = (desugar_term env t)
in (

let se = FStar_Syntax_Syntax.Sig_main (((e), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[]))))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let f = (desugar_formula env t)
in (let _165_1094 = (let _165_1093 = (let _165_1092 = (let _165_1091 = (FStar_Parser_Env.qualify env id)
in ((_165_1091), (f), ((FStar_Syntax_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_assume (_165_1092))
in (_165_1093)::[])
in ((env), (_165_1094))))
end
| FStar_Parser_AST.Val (id, t) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let t = (let _165_1095 = (close_fun env t)
in (desugar_term env _165_1095))
in (

let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (

let se = (let _165_1098 = (let _165_1097 = (FStar_Parser_Env.qualify env id)
in (let _165_1096 = (FStar_List.map (trans_qual None) quals)
in ((_165_1097), ([]), (t), (_165_1096), (d.FStar_Parser_AST.drange))))
in FStar_Syntax_Syntax.Sig_declare_typ (_165_1098))
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[])))))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(

let _67_2825 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (match (_67_2825) with
| (t, _67_2824) -> begin
(

let l = (FStar_Parser_Env.qualify env id)
in (

let se = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Syntax_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((FStar_Syntax_Const.exn_lid)::[]), (d.FStar_Parser_AST.drange)))
in (

let se' = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((l)::[]), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_Env.push_sigelt env se')
in (

let data_ops = (mk_data_projector_names [] env (([]), (se)))
in (

let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (

let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in ((env), ((FStar_List.append ((se')::discs) data_ops))))))))))
end))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(

let t = (desugar_term env term)
in (

let t = (let _165_1103 = (let _165_1099 = (FStar_Syntax_Syntax.null_binder t)
in (_165_1099)::[])
in (let _165_1102 = (let _165_1101 = (let _165_1100 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (Prims.fst _165_1100))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _165_1101))
in (FStar_Syntax_Util.arrow _165_1103 _165_1102)))
in (

let l = (FStar_Parser_Env.qualify env id)
in (

let se = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Syntax_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((FStar_Syntax_Const.exn_lid)::[]), (d.FStar_Parser_AST.drange)))
in (

let se' = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((l)::[]), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_Env.push_sigelt env se')
in (

let data_ops = (mk_data_projector_names [] env (([]), (se)))
in (

let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (

let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in ((env), ((FStar_List.append ((se')::discs) data_ops))))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(

let _67_2854 = (desugar_binders env binders)
in (match (_67_2854) with
| (env_k, binders) -> begin
(

let k = (desugar_term env_k k)
in (

let name = (FStar_Parser_Env.qualify env id)
in (

let se = (mk_typ_abbrev name [] binders FStar_Syntax_Syntax.tun k ((name)::[]) [] d.FStar_Parser_AST.drange)
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))))
end))
end
| FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (desugar_redefine_effect env d trans_qual quals eff_name eff_binders defn (fun ed range -> FStar_Syntax_Syntax.Sig_new_effect (((ed), (range))))))
end
| FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (desugar_redefine_effect env d trans_qual quals eff_name eff_binders defn (fun ed range -> FStar_Syntax_Syntax.Sig_new_effect_for_free (((ed), (range))))))
end
| FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls, actions)) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (desugar_effect env d quals eff_name eff_binders eff_kind eff_decls actions true))
end
| FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls, actions)) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (desugar_effect env d quals eff_name eff_binders eff_kind eff_decls actions false))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(

let lookup = (fun l -> (match ((FStar_Parser_Env.try_lookup_effect_name env l)) with
| None -> begin
(let _165_1114 = (let _165_1113 = (let _165_1112 = (let _165_1111 = (let _165_1110 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat _165_1110 " not found"))
in (Prims.strcat "Effect name " _165_1111))
in ((_165_1112), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_165_1113))
in (Prims.raise _165_1114))
end
| Some (l) -> begin
l
end))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let _67_2914 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(let _165_1117 = (let _165_1116 = (let _165_1115 = (desugar_term env t)
in (([]), (_165_1115)))
in Some (_165_1116))
in ((_165_1117), (None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(let _165_1123 = (let _165_1119 = (let _165_1118 = (desugar_term env wp)
in (([]), (_165_1118)))
in Some (_165_1119))
in (let _165_1122 = (let _165_1121 = (let _165_1120 = (desugar_term env t)
in (([]), (_165_1120)))
in Some (_165_1121))
in ((_165_1123), (_165_1122))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(let _165_1126 = (let _165_1125 = (let _165_1124 = (desugar_term env t)
in (([]), (_165_1124)))
in Some (_165_1125))
in ((None), (_165_1126)))
end)
in (match (_67_2914) with
| (lift_wp, lift) -> begin
(

let se = FStar_Syntax_Syntax.Sig_sub_effect ((({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _67_2920 d -> (match (_67_2920) with
| (env, sigelts) -> begin
(

let _67_2924 = (desugar_decl env d)
in (match (_67_2924) with
| (env, se) -> begin
((env), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))


let open_prims_all : (FStar_Parser_AST.decoration Prims.list  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]


let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_Env.finish_module_or_interface env prev_mod)
end)
in (

let _67_2947 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _165_1144 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in ((_165_1144), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _165_1145 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in ((_165_1145), (mname), (decls), (false)))
end)
in (match (_67_2947) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let _67_2950 = (desugar_decls env decls)
in (match (_67_2950) with
| (env, sigelts) -> begin
(

let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in ((env), (modul), (pop_when_done)))
end))
end))))


let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (

let m = if (FStar_Options.interactive_fsi ()) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface (((mname), (decls), (true)))
end
| FStar_Parser_AST.Interface (mname, _67_2961, _67_2963) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (

let _67_2971 = (desugar_modul_common curmod env m)
in (match (_67_2971) with
| (x, y, _67_2970) -> begin
((x), (y))
end))))


let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (

let _67_2977 = (desugar_modul_common None env m)
in (match (_67_2977) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (

let _67_2979 = if (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _165_1156 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _165_1156))
end else begin
()
end
in (let _165_1157 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in ((_165_1157), (modul)))))
end)))


let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (

let _67_2992 = (FStar_List.fold_left (fun _67_2985 m -> (match (_67_2985) with
| (env, mods) -> begin
(

let _67_2989 = (desugar_modul env m)
in (match (_67_2989) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (_67_2992) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (

let _67_2997 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_67_2997) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (

let _67_2998 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.curmonad = _67_2998.FStar_Parser_Env.curmonad; FStar_Parser_Env.modules = _67_2998.FStar_Parser_Env.modules; FStar_Parser_Env.scope_mods = _67_2998.FStar_Parser_Env.scope_mods; FStar_Parser_Env.sigaccum = _67_2998.FStar_Parser_Env.sigaccum; FStar_Parser_Env.sigmap = _67_2998.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _67_2998.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _67_2998.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _67_2998.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _67_2998.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (

let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




