
open Prims

let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun uu___469 -> (match (uu___469) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| _74_7 -> begin
None
end))


let trans_qual : FStar_Range.range  ->  FStar_Ident.lident Prims.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r maybe_effect_id uu___470 -> (match (uu___470) with
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
| FStar_Parser_AST.Effect_qual -> begin
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

let _74_23 = (FStar_Errors.warn r "The \'opaque\' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given \'opaque val f : t\', the behavior was to exclude the definition of \'f\' to the SMT solver. This corresponds roughly to the new \'irreducible\' qualifier. (2) Given \'opaque type t = t\'\', the behavior was to provide the definition of \'t\' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of \'unfoldable\' (which is currently the default).")
in FStar_Syntax_Syntax.Visible_default)
end
| FStar_Parser_AST.Reflectable -> begin
(match (maybe_effect_id) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((("Qualifier reflect only supported on effects"), (r)))))
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
(Prims.raise (FStar_Errors.Error ((("The \'default\' qualifier on effects is no longer supported"), (r)))))
end
| (FStar_Parser_AST.Inline) | (FStar_Parser_AST.Visible) -> begin
(Prims.raise (FStar_Errors.Error ((("Unsupported qualifier"), (r)))))
end))


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun uu___471 -> (match (uu___471) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun uu___472 -> (match (uu___472) with
| FStar_Parser_AST.Hash -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| _74_43 -> begin
None
end))


let arg_withimp_e = (fun imp t -> ((t), ((as_imp imp))))


let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| _74_50 -> begin
((t), (None))
end))


let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_74_54) -> begin
true
end
| _74_57 -> begin
false
end)))))


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _74_62 -> begin
t
end))


let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _175_25 = (let _175_24 = (FStar_Ident.lid_of_path (("Type0")::[]) r)
in FStar_Parser_AST.Name (_175_24))
in (FStar_Parser_AST.mk_term _175_25 r FStar_Parser_AST.Kind)))


let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _175_29 = (let _175_28 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_175_28))
in (FStar_Parser_AST.mk_term _175_29 r FStar_Parser_AST.Kind)))


let rec is_comp_type : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> (match (t.FStar_Parser_AST.tm) with
| (FStar_Parser_AST.Name (l)) | (FStar_Parser_AST.Construct (l, _)) -> begin
(let _175_34 = (FStar_ToSyntax_Env.try_lookup_effect_name env l)
in (FStar_All.pipe_right _175_34 FStar_Option.isSome))
end
| FStar_Parser_AST.App (head, _74_75, _74_77) -> begin
(is_comp_type env head)
end
| (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) | (FStar_Parser_AST.LetOpen (_, t)) -> begin
(is_comp_type env t)
end
| _74_91 -> begin
false
end))


let unit_ty : FStar_Parser_AST.term = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) FStar_Range.dummyRange FStar_Parser_AST.Type_level)


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _175_44 = (let _175_43 = (let _175_42 = (let _175_41 = (FStar_Parser_AST.compile_op n s)
in ((_175_41), (r)))
in (FStar_Ident.mk_ident _175_42))
in (_175_43)::[])
in (FStar_All.pipe_right _175_44 FStar_Ident.lid_of_ids)))


let op_as_term : FStar_ToSyntax_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (

let r = (fun l dd -> (let _175_58 = (let _175_57 = (FStar_Syntax_Syntax.lid_as_fv (FStar_Ident.set_lid_range l rng) dd None)
in (FStar_All.pipe_right _175_57 FStar_Syntax_Syntax.fv_to_tm))
in Some (_175_58)))
in (

let fallback = (fun _74_103 -> (match (()) with
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
if (FStar_Options.ml_ish ()) then begin
(r FStar_Syntax_Const.list_append_lid FStar_Syntax_Syntax.Delta_equational)
end else begin
(r FStar_Syntax_Const.list_tot_append_lid FStar_Syntax_Syntax.Delta_equational)
end
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
| _74_131 -> begin
None
end)
end))
in (match ((let _175_61 = (compile_op_lid arity s rng)
in (FStar_ToSyntax_Env.try_lookup_lid env _175_61))) with
| Some (t) -> begin
Some ((Prims.fst t))
end
| _74_135 -> begin
(fallback ())
end))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _175_68 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _175_68)))


let rec free_type_vars_b : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_ToSyntax_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_74_144) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let _74_151 = (FStar_ToSyntax_Env.push_bv env x)
in (match (_74_151) with
| (env, _74_150) -> begin
((env), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (_74_153, term) -> begin
(let _175_75 = (free_type_vars env term)
in ((env), (_175_75)))
end
| FStar_Parser_AST.TAnnotated (id, _74_159) -> begin
(

let _74_165 = (FStar_ToSyntax_Env.push_bv env id)
in (match (_74_165) with
| (env, _74_164) -> begin
((env), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _175_76 = (free_type_vars env t)
in ((env), (_175_76)))
end))
and free_type_vars : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _175_79 = (unparen t)
in _175_79.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_74_171) -> begin
(failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_ToSyntax_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _74_177 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Projector (_)) | (FStar_Parser_AST.Discrim (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Assign (_, t)) | (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_74_220, ts) -> begin
(FStar_List.collect (fun _74_227 -> (match (_74_227) with
| (t, _74_226) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_74_229, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _74_236) -> begin
(let _175_82 = (free_type_vars env t1)
in (let _175_81 = (free_type_vars env t2)
in (FStar_List.append _175_82 _175_81)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(

let _74_245 = (free_type_vars_b env b)
in (match (_74_245) with
| (env, f) -> begin
(let _175_83 = (free_type_vars env t)
in (FStar_List.append f _175_83))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(

let _74_261 = (FStar_List.fold_left (fun _74_254 binder -> (match (_74_254) with
| (env, free) -> begin
(

let _74_258 = (free_type_vars_b env binder)
in (match (_74_258) with
| (env, f) -> begin
((env), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (_74_261) with
| (env, free) -> begin
(let _175_86 = (free_type_vars env body)
in (FStar_List.append free _175_86))
end))
end
| FStar_Parser_AST.Project (t, _74_264) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.collect (free_type_vars env) cattributes)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t -> (match ((let _175_93 = (unparen t)
in _175_93.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _74_313 -> begin
((t), (args))
end))
in (aux [] t)))


let close : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _175_98 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _175_98))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _175_102 = (let _175_101 = (let _175_100 = (tm_type x.FStar_Ident.idRange)
in ((x), (_175_100)))
in FStar_Parser_AST.TAnnotated (_175_101))
in (FStar_Parser_AST.mk_binder _175_102 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))


let close_fun : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _175_107 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _175_107))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _175_111 = (let _175_110 = (let _175_109 = (tm_type x.FStar_Ident.idRange)
in ((x), (_175_109)))
in FStar_Parser_AST.TAnnotated (_175_110))
in (FStar_Parser_AST.mk_binder _175_111 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (Some (FStar_Parser_AST.Implicit)))))))
in (

let t = (match ((let _175_112 = (unparen t)
in _175_112.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_74_326) -> begin
t
end
| _74_329 -> begin
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
| _74_339 -> begin
((bs), (t))
end))


let rec is_var_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatTvar (_, _)) | (FStar_Parser_AST.PatVar (_, _)) -> begin
true
end
| FStar_Parser_AST.PatAscribed (p, _74_356) -> begin
(is_var_pattern p)
end
| _74_360 -> begin
false
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _74_364) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_74_370); FStar_Parser_AST.prange = _74_368}, _74_374) -> begin
true
end
| _74_378 -> begin
false
end))


let replace_unit_pattern : FStar_Parser_AST.pattern  ->  FStar_Parser_AST.pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatConst (FStar_Const.Const_unit) -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatAscribed ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)), (unit_ty)))) p.FStar_Parser_AST.prange)
end
| _74_383 -> begin
p
end))


let rec destruct_app_pattern : FStar_ToSyntax_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _74_395 = (destruct_app_pattern env is_top_level p)
in (match (_74_395) with
| (name, args, _74_394) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _74_400); FStar_Parser_AST.prange = _74_397}, args) when is_top_level -> begin
(let _175_130 = (let _175_129 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (_175_129))
in ((_175_130), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _74_411); FStar_Parser_AST.prange = _74_408}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| _74_419 -> begin
(failwith "Not an app pattern")
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
| LocalBinder (_74_422) -> begin
_74_422
end))


let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_74_425) -> begin
_74_425
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun uu___473 -> (match (uu___473) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| _74_432 -> begin
(failwith "Impossible")
end))


let as_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_ToSyntax_Env.env) = (fun env imp uu___474 -> (match (uu___474) with
| (None, k) -> begin
(let _175_167 = (FStar_Syntax_Syntax.null_binder k)
in ((_175_167), (env)))
end
| (Some (a), k) -> begin
(

let _74_445 = (FStar_ToSyntax_Env.push_bv env a)
in (match (_74_445) with
| (env, a) -> begin
(((((

let _74_446 = a
in {FStar_Syntax_Syntax.ppname = _74_446.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _74_446.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env))
end))
end))


type env_t =
FStar_ToSyntax_Env.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _74_451 -> (match (_74_451) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))


let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))


let mk_ref_read = (fun tm -> (

let tm' = (let _175_180 = (let _175_179 = (let _175_175 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _175_175))
in (let _175_178 = (let _175_177 = (let _175_176 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_175_176)))
in (_175_177)::[])
in ((_175_179), (_175_178))))
in FStar_Syntax_Syntax.Tm_app (_175_180))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc = (fun tm -> (

let tm' = (let _175_187 = (let _175_186 = (let _175_182 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _175_182))
in (let _175_185 = (let _175_184 = (let _175_183 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_175_183)))
in (_175_184)::[])
in ((_175_186), (_175_185))))
in FStar_Syntax_Syntax.Tm_app (_175_187))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign = (fun t1 t2 pos -> (

let tm = (let _175_199 = (let _175_198 = (let _175_191 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _175_191))
in (let _175_197 = (let _175_196 = (let _175_192 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (_175_192)))
in (let _175_195 = (let _175_194 = (let _175_193 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (_175_193)))
in (_175_194)::[])
in (_175_196)::_175_195))
in ((_175_198), (_175_197))))
in FStar_Syntax_Syntax.Tm_app (_175_199))
in (FStar_Syntax_Syntax.mk tm None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun uu___475 -> (match (uu___475) with
| ("repr") | ("post") | ("pre") | ("wp") -> begin
true
end
| _74_468 -> begin
false
end))


let rec sum_to_universe : FStar_Syntax_Syntax.universe  ->  Prims.int  ->  FStar_Syntax_Syntax.universe = (fun u n -> if (n = (Prims.parse_int "0")) then begin
u
end else begin
(let _175_206 = (sum_to_universe u (n - (Prims.parse_int "1")))
in FStar_Syntax_Syntax.U_succ (_175_206))
end)


let int_to_universe : Prims.int  ->  FStar_Syntax_Syntax.universe = (fun n -> (sum_to_universe FStar_Syntax_Syntax.U_zero n))


let rec desugar_maybe_non_constant_universe : FStar_Parser_AST.term  ->  (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun t -> (match ((let _175_211 = (unparen t)
in _175_211.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(let _175_213 = (let _175_212 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_175_212))
in FStar_Util.Inr (_175_213))
end
| FStar_Parser_AST.Uvar (u) -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_name (u))
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (repr, _74_478)) -> begin
(

let n = (FStar_Util.int_of_string repr)
in (

let _74_483 = if (n < (Prims.parse_int "0")) then begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Negative universe constant  are not supported : " repr)), (t.FStar_Parser_AST.range)))))
end else begin
()
end
in FStar_Util.Inl (n)))
end
| FStar_Parser_AST.Op (op_plus, (t1)::(t2)::[]) -> begin
(

let _74_491 = ()
in (

let u1 = (desugar_maybe_non_constant_universe t1)
in (

let u2 = (desugar_maybe_non_constant_universe t2)
in (match (((u1), (u2))) with
| (FStar_Util.Inl (n1), FStar_Util.Inl (n2)) -> begin
FStar_Util.Inl ((n1 + n2))
end
| ((FStar_Util.Inl (n), FStar_Util.Inr (u))) | ((FStar_Util.Inr (u), FStar_Util.Inl (n))) -> begin
(let _175_214 = (sum_to_universe u n)
in FStar_Util.Inr (_175_214))
end
| (FStar_Util.Inr (u1), FStar_Util.Inr (u2)) -> begin
(let _175_218 = (let _175_217 = (let _175_216 = (let _175_215 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "This universe might contain a sum of two universe variables " _175_215))
in ((_175_216), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (_175_217))
in (Prims.raise _175_218))
end))))
end
| FStar_Parser_AST.App (_74_514) -> begin
(

let rec aux = (fun t univargs -> (match ((let _175_223 = (unparen t)
in _175_223.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, targ, _74_522) -> begin
(

let uarg = (desugar_maybe_non_constant_universe targ)
in (aux t ((uarg)::univargs)))
end
| FStar_Parser_AST.Var (max_lid) -> begin
(

let _74_528 = ()
in if (FStar_List.existsb (fun uu___476 -> (match (uu___476) with
| FStar_Util.Inr (_74_532) -> begin
true
end
| _74_535 -> begin
false
end)) univargs) then begin
(let _175_227 = (let _175_226 = (FStar_List.map (fun uu___477 -> (match (uu___477) with
| FStar_Util.Inl (n) -> begin
(int_to_universe n)
end
| FStar_Util.Inr (u) -> begin
u
end)) univargs)
in FStar_Syntax_Syntax.U_max (_175_226))
in FStar_Util.Inr (_175_227))
end else begin
(

let nargs = (FStar_List.map (fun uu___478 -> (match (uu___478) with
| FStar_Util.Inl (n) -> begin
n
end
| FStar_Util.Inr (_74_545) -> begin
(failwith "impossible")
end)) univargs)
in (let _175_231 = (FStar_List.fold_left (fun m n -> if (m > n) then begin
m
end else begin
n
end) (Prims.parse_int "0") nargs)
in FStar_Util.Inl (_175_231)))
end)
end
| _74_551 -> begin
(let _175_236 = (let _175_235 = (let _175_234 = (let _175_233 = (let _175_232 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat _175_232 " in universe context"))
in (Prims.strcat "Unexpected term " _175_233))
in ((_175_234), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (_175_235))
in (Prims.raise _175_236))
end))
in (aux t []))
end
| _74_553 -> begin
(let _175_241 = (let _175_240 = (let _175_239 = (let _175_238 = (let _175_237 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat _175_237 " in universe context"))
in (Prims.strcat "Unexpected term " _175_238))
in ((_175_239), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (_175_240))
in (Prims.raise _175_241))
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

let _74_566 = (FStar_List.hd fields)
in (match (_74_566) with
| (f, _74_565) -> begin
(

let record = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f)
in (

let check_field = (fun _74_572 -> (match (_74_572) with
| (f', _74_571) -> begin
if (FStar_ToSyntax_Env.belongs_to_record env f' record) then begin
()
end else begin
(

let msg = (FStar_Util.format3 "Field %s belongs to record type %s, whereas field %s does not" f.FStar_Ident.str record.FStar_ToSyntax_Env.typename.FStar_Ident.str f'.FStar_Ident.str)
in (Prims.raise (FStar_Errors.Error (((msg), (rg))))))
end
end))
in (

let _74_574 = (let _175_249 = (FStar_List.tl fields)
in (FStar_List.iter check_field _175_249))
in (match (()) with
| () -> begin
record
end))))
end)))


let rec desugar_data_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat) = (fun env p is_mut -> (

let check_linear_pattern_variables = (fun p -> (

let rec pat_vars = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_dot_term (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_constant (_)) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (_74_594, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _74_602 -> (match (_74_602) with
| (p, _74_601) -> begin
(let _175_306 = (pat_vars p)
in (FStar_Util.set_union out _175_306))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let xs = (pat_vars hd)
in if (not ((FStar_Util.for_all (fun p -> (

let ys = (pat_vars p)
in ((FStar_Util.set_is_subset_of xs ys) && (FStar_Util.set_is_subset_of ys xs)))) tl))) then begin
(Prims.raise (FStar_Errors.Error ((("Disjunctive pattern binds different variables in each case"), (p.FStar_Syntax_Syntax.p)))))
end else begin
xs
end)
end))
in (pat_vars p)))
in (

let _74_625 = (match (((is_mut), (p.FStar_Parser_AST.pat))) with
| ((false, _)) | ((true, FStar_Parser_AST.PatVar (_))) -> begin
()
end
| (true, _74_623) -> begin
(Prims.raise (FStar_Errors.Error ((("let-mutable is for variables only"), (p.FStar_Parser_AST.prange)))))
end)
in (

let push_bv_maybe_mut = if is_mut then begin
FStar_ToSyntax_Env.push_bv_mutable
end else begin
FStar_ToSyntax_Env.push_bv
end
in (

let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))) with
| Some (y) -> begin
((l), (e), (y))
end
| _74_636 -> begin
(

let _74_639 = (push_bv_maybe_mut e x)
in (match (_74_639) with
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
(let _175_335 = (let _175_334 = (let _175_333 = (let _175_332 = (let _175_331 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") op)
in (FStar_Ident.id_of_text _175_331))
in ((_175_332), (None)))
in FStar_Parser_AST.PatVar (_175_333))
in {FStar_Parser_AST.pat = _175_334; FStar_Parser_AST.prange = p.FStar_Parser_AST.prange})
in (aux loc env _175_335))
end
| FStar_Parser_AST.PatOr ([]) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(

let _74_663 = (aux loc env p)
in (match (_74_663) with
| (loc, env, var, p, _74_662) -> begin
(

let _74_680 = (FStar_List.fold_left (fun _74_667 p -> (match (_74_667) with
| (loc, env, ps) -> begin
(

let _74_676 = (aux loc env p)
in (match (_74_676) with
| (loc, env, _74_672, p, _74_675) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (_74_680) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in ((loc), (env), (var), (pat), (false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _74_691 = (aux loc env p)
in (match (_74_691) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (_74_693) -> begin
(failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t = (let _175_338 = (close_fun env t)
in (desugar_term env _175_338))
in LocalBinder ((((

let _74_700 = x
in {FStar_Syntax_Syntax.ppname = _74_700.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _74_700.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (aq))))
end)
in ((loc), (env'), (binder), (p), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _175_339 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_175_339), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _175_340 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_175_340), (false))))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let _74_719 = (resolvex loc env x)
in (match (_74_719) with
| (loc, env, xbv) -> begin
(let _175_341 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc), (env), (LocalBinder (((xbv), (aq)))), (_175_341), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _175_342 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), ([])))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_175_342), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _74_725}, args) -> begin
(

let _74_747 = (FStar_List.fold_right (fun arg _74_736 -> (match (_74_736) with
| (loc, env, args) -> begin
(

let _74_743 = (aux loc env arg)
in (match (_74_743) with
| (loc, env, _74_740, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (_74_747) with
| (loc, env, args) -> begin
(

let l = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _175_345 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_175_345), (false)))))
end))
end
| FStar_Parser_AST.PatApp (_74_751) -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let _74_771 = (FStar_List.fold_right (fun pat _74_759 -> (match (_74_759) with
| (loc, env, pats) -> begin
(

let _74_767 = (aux loc env pat)
in (match (_74_767) with
| (loc, env, _74_763, pat, _74_766) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (_74_771) with
| (loc, env, pats) -> begin
(

let pat = (let _175_358 = (let _175_357 = (let _175_353 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _175_353))
in (let _175_356 = (let _175_355 = (let _175_354 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_175_354), ([])))
in FStar_Syntax_Syntax.Pat_cons (_175_355))
in (FStar_All.pipe_left _175_357 _175_356)))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _175_352 = (let _175_351 = (let _175_350 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_175_350), ((((hd), (false)))::(((tl), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (_175_351))
in (FStar_All.pipe_left (pos_r r) _175_352)))) pats _175_358))
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc), (env), (LocalBinder (((x), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let _74_797 = (FStar_List.fold_left (fun _74_784 p -> (match (_74_784) with
| (loc, env, pats) -> begin
(

let _74_793 = (aux loc env p)
in (match (_74_793) with
| (loc, env, _74_789, pat, _74_792) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (_74_797) with
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

let _74_803 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) l)
in (match (_74_803) with
| (constr, _74_802) -> begin
(

let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| _74_807 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _175_361 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_175_361), (false)))))
end))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let record = (check_fields env fields p.FStar_Parser_AST.prange)
in (

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _74_817 -> (match (_74_817) with
| (f, p) -> begin
((f.FStar_Ident.ident), (p))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun _74_822 -> (match (_74_822) with
| (f, _74_821) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _74_826 -> (match (_74_826) with
| (g, _74_825) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.idText)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_74_829, p) -> begin
p
end)
end))))
in (

let app = (let _175_369 = (let _175_368 = (let _175_367 = (let _175_366 = (let _175_365 = (FStar_Ident.lid_of_ids (FStar_List.append record.FStar_ToSyntax_Env.typename.FStar_Ident.ns ((record.FStar_ToSyntax_Env.constrname)::[])))
in FStar_Parser_AST.PatName (_175_365))
in (FStar_Parser_AST.mk_pattern _175_366 p.FStar_Parser_AST.prange))
in ((_175_367), (args)))
in FStar_Parser_AST.PatApp (_175_368))
in (FStar_Parser_AST.mk_pattern _175_369 p.FStar_Parser_AST.prange))
in (

let _74_841 = (aux loc env app)
in (match (_74_841) with
| (env, e, b, p, _74_840) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _175_376 = (let _175_375 = (let _175_374 = (

let _74_846 = fv
in (let _175_373 = (let _175_372 = (let _175_371 = (let _175_370 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_ToSyntax_Env.typename), (_175_370)))
in FStar_Syntax_Syntax.Record_ctor (_175_371))
in Some (_175_372))
in {FStar_Syntax_Syntax.fv_name = _74_846.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _74_846.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _175_373}))
in ((_175_374), (args)))
in FStar_Syntax_Syntax.Pat_cons (_175_375))
in (FStar_All.pipe_left pos _175_376))
end
| _74_849 -> begin
p
end)
in ((env), (e), (b), (p), (false)))
end))))))
end))))
in (

let _74_858 = (aux [] env p)
in (match (_74_858) with
| (_74_852, env, b, p, _74_857) -> begin
(

let _74_859 = (let _175_377 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _175_377))
in ((env), (b), (p)))
end))))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p is_mut -> (

let mklet = (fun x -> (let _175_386 = (let _175_385 = (let _175_384 = (FStar_ToSyntax_Env.qualify env x)
in ((_175_384), (FStar_Syntax_Syntax.tun)))
in LetBinder (_175_385))
in ((env), (_175_386), (None))))
in if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(let _175_388 = (let _175_387 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") x)
in (FStar_Ident.id_of_text _175_387))
in (mklet _175_388))
end
| FStar_Parser_AST.PatVar (x, _74_871) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _74_878); FStar_Parser_AST.prange = _74_875}, t) -> begin
(let _175_392 = (let _175_391 = (let _175_390 = (FStar_ToSyntax_Env.qualify env x)
in (let _175_389 = (desugar_term env t)
in ((_175_390), (_175_389))))
in LetBinder (_175_391))
in ((env), (_175_392), (None)))
end
| _74_886 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
(

let _74_890 = (desugar_data_pat env p is_mut)
in (match (_74_890) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _74_898 -> begin
Some (p)
end)
in ((env), (binder), (p)))
end))
end))
and desugar_binding_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _74_902 env pat -> (

let _74_910 = (desugar_data_pat env pat false)
in (match (_74_910) with
| (env, _74_908, pat) -> begin
((env), (pat))
end)))
and desugar_match_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _74_915 = env
in {FStar_ToSyntax_Env.curmodule = _74_915.FStar_ToSyntax_Env.curmodule; FStar_ToSyntax_Env.curmonad = _74_915.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = _74_915.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = _74_915.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = _74_915.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = _74_915.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = _74_915.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = _74_915.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = _74_915.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.default_result_effect = _74_915.FStar_ToSyntax_Env.default_result_effect; FStar_ToSyntax_Env.iface = _74_915.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = _74_915.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _74_920 = env
in {FStar_ToSyntax_Env.curmodule = _74_920.FStar_ToSyntax_Env.curmodule; FStar_ToSyntax_Env.curmonad = _74_920.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = _74_920.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = _74_920.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = _74_920.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = _74_920.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = _74_920.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = _74_920.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = _74_920.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.default_result_effect = _74_920.FStar_ToSyntax_Env.default_result_effect; FStar_ToSyntax_Env.iface = _74_920.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = _74_920.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_machine_integer : FStar_ToSyntax_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env repr _74_927 range -> (match (_74_927) with
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

let lid = (match ((FStar_ToSyntax_Env.try_lookup_lid env lid)) with
| Some (lid) -> begin
(Prims.fst lid)
end
| None -> begin
(let _175_408 = (FStar_Util.format1 "%s not in scope\n" (FStar_Ident.text_of_lid lid))
in (failwith _175_408))
end)
in (

let repr = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (None))))) None range)
in (let _175_413 = (let _175_412 = (let _175_411 = (let _175_410 = (let _175_409 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr), (_175_409)))
in (_175_410)::[])
in ((lid), (_175_411)))
in FStar_Syntax_Syntax.Tm_app (_175_412))
in (FStar_Syntax_Syntax.mk _175_413 None range))))))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env_t  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk setpos env l -> (

let _74_950 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) l)
in (match (_74_950) with
| (tm, mut) -> begin
(

let tm = (setpos tm)
in if mut then begin
(let _175_426 = (let _175_425 = (let _175_424 = (mk_ref_read tm)
in ((_175_424), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (_175_425))
in (FStar_All.pipe_left mk _175_426))
end else begin
tm
end)
end)))
and desugar_attributes : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (match ((let _175_431 = (unparen t)
in _175_431.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = _74_962; FStar_Ident.ident = _74_960; FStar_Ident.nsstr = _74_958; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| _74_966 -> begin
(let _175_435 = (let _175_434 = (let _175_433 = (let _175_432 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " _175_432))
in ((_175_433), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (_175_434))
in (Prims.raise _175_435))
end))
in (FStar_List.map desugar_attribute cattributes)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let _74_974 = e
in {FStar_Syntax_Syntax.n = _74_974.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _74_974.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _74_974.FStar_Syntax_Syntax.vars}))
in (match ((let _175_443 = (unparen top)
in _175_443.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_74_978) -> begin
(desugar_formula env top)
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(desugar_formula env t)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(desugar_formula env t)
end
| FStar_Parser_AST.Attributes (ts) -> begin
(failwith "Attributes should not be desugared by desugar_term_maybe_top")
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
| FStar_Parser_AST.Op ("*", (_74_1006)::(_74_1004)::[]) when (let _175_444 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _175_444 FStar_Option.isNone)) -> begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(let _175_447 = (flatten t1)
in (FStar_List.append _175_447 ((t2)::[])))
end
| _74_1019 -> begin
(t)::[]
end))
in (

let targs = (let _175_451 = (let _175_448 = (unparen top)
in (flatten _175_448))
in (FStar_All.pipe_right _175_451 (FStar_List.map (fun t -> (let _175_450 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _175_450))))))
in (

let _74_1025 = (let _175_452 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) _175_452))
in (match (_74_1025) with
| (tup, _74_1024) -> begin
(mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _175_454 = (let _175_453 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) a)
in (Prims.fst _175_453))
in (FStar_All.pipe_left setpos _175_454))
end
| FStar_Parser_AST.Uvar (u) -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected universe variable " (Prims.strcat (FStar_Ident.text_of_id u) " in non-universe context"))), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected or unbound operator: " s)), (top.FStar_Parser_AST.range)))))
end
| Some (op) -> begin
if ((FStar_List.length args) > (Prims.parse_int "0")) then begin
(

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _175_456 = (desugar_term env t)
in ((_175_456), (None))))))
in (mk (FStar_Syntax_Syntax.Tm_app (((op), (args))))))
end else begin
op
end
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _74_1045; FStar_Ident.ident = _74_1043; FStar_Ident.nsstr = _74_1041; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _74_1054; FStar_Ident.ident = _74_1052; FStar_Ident.nsstr = _74_1050; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = _74_1063; FStar_Ident.ident = _74_1061; FStar_Ident.nsstr = _74_1059; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(let _175_458 = (let _175_457 = (desugar_universe t)
in FStar_Syntax_Syntax.Tm_type (_175_457))
in (mk _175_458))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _74_1077; FStar_Ident.ident = _74_1075; FStar_Ident.nsstr = _74_1073; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _74_1086; FStar_Ident.ident = _74_1084; FStar_Ident.nsstr = _74_1082; FStar_Ident.str = "True"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _74_1095; FStar_Ident.ident = _74_1093; FStar_Ident.nsstr = _74_1091; FStar_Ident.str = "False"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = _74_1100}) when ((is_special_effect_combinator txt) && (FStar_ToSyntax_Env.is_effect_name env eff_name)) -> begin
(match ((FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name)) with
| Some (ed) -> begin
(let _175_459 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" txt))) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.fvar _175_459 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
end
| None -> begin
(failwith "immpossible special_effect_combinator")
end)
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t2 = (desugar_term env t2)
in (

let _74_1115 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) ident)
in (match (_74_1115) with
| (t1, mut) -> begin
(

let _74_1116 = if (not (mut)) then begin
(Prims.raise (FStar_Errors.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
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

let found = ((let _175_460 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (FStar_Option.isSome _175_460)) || (let _175_461 = (FStar_ToSyntax_Env.try_lookup_effect_defn env l)
in (FStar_Option.isSome _175_461)))
in if found then begin
(let _175_462 = (FStar_Syntax_Util.mk_field_projector_name_from_ident l i)
in (desugar_name mk setpos env _175_462))
end else begin
(let _175_465 = (let _175_464 = (let _175_463 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((_175_463), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (_175_464))
in (Prims.raise _175_465))
end)
end
| FStar_Parser_AST.Discrim (lid) -> begin
(match ((FStar_ToSyntax_Env.try_lookup_datacon env lid)) with
| None -> begin
(let _175_468 = (let _175_467 = (let _175_466 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((_175_466), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (_175_467))
in (Prims.raise _175_468))
end
| _74_1130 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (desugar_name mk setpos env lid'))
end)
end
| FStar_Parser_AST.Construct (l, args) -> begin
(match ((FStar_ToSyntax_Env.try_lookup_datacon env l)) with
| Some (head) -> begin
(

let _74_1140 = (let _175_469 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in ((_175_469), (true)))
in (match (_74_1140) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _74_1143 -> begin
(

let args = (FStar_List.map (fun _74_1146 -> (match (_74_1146) with
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
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Constructor " (Prims.strcat l.FStar_Ident.str " not found"))), (top.FStar_Parser_AST.range)))))
end)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let _74_1175 = (FStar_List.fold_left (fun _74_1158 b -> (match (_74_1158) with
| (env, tparams, typs) -> begin
(

let _74_1162 = (desugar_binder env b)
in (match (_74_1162) with
| (xopt, t) -> begin
(

let _74_1168 = (match (xopt) with
| None -> begin
(let _175_473 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env), (_175_473)))
end
| Some (x) -> begin
(FStar_ToSyntax_Env.push_bv env x)
end)
in (match (_74_1168) with
| (env, x) -> begin
(let _175_477 = (let _175_476 = (let _175_475 = (let _175_474 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _175_474))
in (_175_475)::[])
in (FStar_List.append typs _175_476))
in ((env), ((FStar_List.append tparams (((((

let _74_1169 = x
in {FStar_Syntax_Syntax.ppname = _74_1169.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _74_1169.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (None)))::[]))), (_175_477)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level None))::[])))
in (match (_74_1175) with
| (env, _74_1173, targs) -> begin
(

let _74_1179 = (let _175_478 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) _175_478))
in (match (_74_1179) with
| (tup, _74_1178) -> begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let _74_1186 = (uncurry binders t)
in (match (_74_1186) with
| (bs, t) -> begin
(

let rec aux = (fun env bs uu___479 -> (match (uu___479) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _175_485 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _175_485)))
end
| (hd)::tl -> begin
(

let mlenv = (FStar_ToSyntax_Env.default_ml env)
in (

let bb = (desugar_binder mlenv hd)
in (

let _74_1200 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_74_1200) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _74_1207) -> begin
(failwith "Missing binder in refinement")
end
| b -> begin
(

let _74_1215 = (as_binder env None b)
in (match (_74_1215) with
| ((x, _74_1212), env) -> begin
(

let f = (desugar_formula env f)
in (let _175_486 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _175_486)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let _74_1236 = (FStar_List.fold_left (fun _74_1224 pat -> (match (_74_1224) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_74_1227, t) -> begin
(let _175_490 = (let _175_489 = (free_type_vars env t)
in (FStar_List.append _175_489 ftvs))
in ((env), (_175_490)))
end
| _74_1232 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (_74_1236) with
| (_74_1234, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (let _175_492 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append _175_492 binders))
in (

let rec aux = (fun env bs sc_pat_opt uu___480 -> (match (uu___480) with
| [] -> begin
(

let body = (desugar_term env body)
in (

let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(

let body = (let _175_502 = (let _175_501 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _175_501 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _175_502 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (None), (body)))::[])))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _175_503 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _175_503))))
end
| (p)::rest -> begin
(

let _74_1260 = (desugar_binding_pat env p)
in (match (_74_1260) with
| (env, b, pat) -> begin
(

let _74_1311 = (match (b) with
| LetBinder (_74_1262) -> begin
(failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, _74_1270) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _175_505 = (let _175_504 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_175_504), (p)))
in Some (_175_505))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (_74_1284), _74_1287) -> begin
(

let tup2 = (let _175_506 = (FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _175_506 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _175_514 = (let _175_513 = (let _175_512 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _175_511 = (let _175_510 = (FStar_Syntax_Syntax.as_arg sc)
in (let _175_509 = (let _175_508 = (let _175_507 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _175_507))
in (_175_508)::[])
in (_175_510)::_175_509))
in ((_175_512), (_175_511))))
in FStar_Syntax_Syntax.Tm_app (_175_513))
in (FStar_Syntax_Syntax.mk _175_514 None top.FStar_Parser_AST.range))
in (

let p = (let _175_515 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p), (false)))::[])))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _175_515))
in Some (((sc), (p))))))
end
| (FStar_Syntax_Syntax.Tm_app (_74_1293, args), FStar_Syntax_Syntax.Pat_cons (_74_1298, pats)) -> begin
(

let tupn = (let _175_516 = (FStar_Syntax_Util.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _175_516 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _175_523 = (let _175_522 = (let _175_521 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _175_520 = (let _175_519 = (let _175_518 = (let _175_517 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _175_517))
in (_175_518)::[])
in (FStar_List.append args _175_519))
in ((_175_521), (_175_520))))
in FStar_Syntax_Syntax.Tm_app (_175_522))
in (mk _175_523))
in (

let p = (let _175_524 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p), (false)))::[])))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _175_524))
in Some (((sc), (p))))))
end
| _74_1307 -> begin
(failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt)))
end)
in (match (_74_1311) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end)))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = rng; FStar_Parser_AST.level = _74_1313}, phi, _74_1320) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env phi)
in (

let a = (FStar_Ident.set_lid_range a rng)
in (let _175_532 = (let _175_531 = (let _175_530 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _175_529 = (let _175_528 = (FStar_Syntax_Syntax.as_arg phi)
in (let _175_527 = (let _175_526 = (let _175_525 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _175_525))
in (_175_526)::[])
in (_175_528)::_175_527))
in ((_175_530), (_175_529))))
in FStar_Syntax_Syntax.Tm_app (_175_531))
in (mk _175_532))))
end
| FStar_Parser_AST.App (_74_1326, _74_1328, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (match ((let _175_537 = (unparen e)
in _175_537.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e))
end
| _74_1342 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_uinst (((head), (universes))))))
end))
in (aux [] top))
end
| FStar_Parser_AST.App (_74_1345) -> begin
(

let rec aux = (fun args e -> (match ((let _175_542 = (unparen e)
in _175_542.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) when (imp <> FStar_Parser_AST.UnivApp) -> begin
(

let arg = (let _175_543 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _175_543))
in (aux ((arg)::args) e))
end
| _74_1357 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args))))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _175_546 = (let _175_545 = (let _175_544 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((_175_544), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))
in FStar_Syntax_Syntax.Tm_meta (_175_545))
in (mk _175_546))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let env = (FStar_ToSyntax_Env.push_namespace env lid)
in (desugar_term_maybe_top top_level env e))
end
| FStar_Parser_AST.Let (qual, ((pat, _snd))::_tl, body) -> begin
(

let is_rec = (qual = FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun _74_1379 -> (match (()) with
| () -> begin
(

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _74_1383 -> (match (_74_1383) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _175_550 = (destruct_app_pattern env top_level p)
in ((_175_550), (def)))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _175_551 = (destruct_app_pattern env top_level p)
in ((_175_551), (def)))
end
| _74_1389 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _74_1394); FStar_Parser_AST.prange = _74_1391}, t) -> begin
if top_level then begin
(let _175_554 = (let _175_553 = (let _175_552 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (_175_552))
in ((_175_553), ([]), (Some (t))))
in ((_175_554), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end
end
| FStar_Parser_AST.PatVar (id, _74_1403) -> begin
if top_level then begin
(let _175_557 = (let _175_556 = (let _175_555 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (_175_555))
in ((_175_556), ([]), (None)))
in ((_175_557), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end
end
| _74_1407 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end
end))))
in (

let _74_1436 = (FStar_List.fold_left (fun _74_1412 _74_1421 -> (match (((_74_1412), (_74_1421))) with
| ((env, fnames, rec_bindings), ((f, _74_1415, _74_1417), _74_1420)) -> begin
(

let _74_1432 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let _74_1426 = (FStar_ToSyntax_Env.push_bv env x)
in (match (_74_1426) with
| (env, xx) -> begin
(let _175_561 = (let _175_560 = (FStar_Syntax_Syntax.mk_binder xx)
in (_175_560)::rec_bindings)
in ((env), (FStar_Util.Inl (xx)), (_175_561)))
end))
end
| FStar_Util.Inr (l) -> begin
(let _175_562 = (FStar_ToSyntax_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((_175_562), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (_74_1432) with
| (env, lbname, rec_bindings) -> begin
((env), ((lbname)::fnames), (rec_bindings))
end))
end)) ((env), ([]), ([])) funs)
in (match (_74_1436) with
| (env', fnames, rec_bindings) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let rec_bindings = (FStar_List.rev rec_bindings)
in (

let desugar_one_def = (fun env lbname _74_1448 -> (match (_74_1448) with
| ((_74_1443, args, result_t), def) -> begin
(

let args = (FStar_All.pipe_right args (FStar_List.map replace_unit_pattern))
in (

let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(

let _74_1457 = if (is_comp_type env t) then begin
(match ((FStar_All.pipe_right args (FStar_List.tryFind (fun x -> (not ((is_var_pattern x))))))) with
| None -> begin
()
end
| Some (p) -> begin
(Prims.raise (FStar_Errors.Error ((("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
()
end
in (let _175_570 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) _175_570 FStar_Parser_AST.Expr)))
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| _74_1462 -> begin
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
(let _175_572 = (let _175_571 = (FStar_Syntax_Util.incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _175_571 None))
in FStar_Util.Inr (_175_572))
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
in (let _175_575 = (let _175_574 = (let _175_573 = (FStar_Syntax_Subst.close rec_bindings body)
in ((((is_rec), (lbs))), (_175_573)))
in FStar_Syntax_Syntax.Tm_let (_175_574))
in (FStar_All.pipe_left mk _175_575)))))))
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

let _74_1483 = (desugar_binding_pat_maybe_top top_level env pat is_mutable)
in (match (_74_1483) with
| (env, binder, pat) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body = (desugar_term env t2)
in (

let fv = (let _175_582 = (FStar_Syntax_Util.incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _175_582 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]))), (body)))))))
end
| LocalBinder (x, _74_1492) -> begin
(

let body = (desugar_term env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _175_587 = (let _175_586 = (let _175_585 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _175_584 = (let _175_583 = (FStar_Syntax_Util.branch ((pat), (None), (body)))
in (_175_583)::[])
in ((_175_585), (_175_584))))
in FStar_Syntax_Syntax.Tm_match (_175_586))
in (FStar_Syntax_Syntax.mk _175_587 None body.FStar_Syntax_Syntax.pos))
end)
in (let _175_592 = (let _175_591 = (let _175_590 = (let _175_589 = (let _175_588 = (FStar_Syntax_Syntax.mk_binder x)
in (_175_588)::[])
in (FStar_Syntax_Subst.close _175_589 body))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t1))))::[]))), (_175_590)))
in FStar_Syntax_Syntax.Tm_let (_175_591))
in (FStar_All.pipe_left mk _175_592))))
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
in (let _175_603 = (let _175_602 = (let _175_601 = (desugar_term env t1)
in (let _175_600 = (let _175_599 = (let _175_594 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _175_593 = (desugar_term env t2)
in ((_175_594), (None), (_175_593))))
in (let _175_598 = (let _175_597 = (let _175_596 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _175_595 = (desugar_term env t3)
in ((_175_596), (None), (_175_595))))
in (_175_597)::[])
in (_175_599)::_175_598))
in ((_175_601), (_175_600))))
in FStar_Syntax_Syntax.Tm_match (_175_602))
in (mk _175_603)))
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

let desugar_branch = (fun _74_1533 -> (match (_74_1533) with
| (pat, wopt, b) -> begin
(

let _74_1536 = (desugar_match_pat env pat)
in (match (_74_1536) with
| (env, pat) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _175_606 = (desugar_term env e)
in Some (_175_606))
end)
in (

let b = (desugar_term env b)
in (FStar_Syntax_Util.branch ((pat), (wopt), (b)))))
end))
end))
in (let _175_610 = (let _175_609 = (let _175_608 = (desugar_term env e)
in (let _175_607 = (FStar_List.map desugar_branch branches)
in ((_175_608), (_175_607))))
in FStar_Syntax_Syntax.Tm_match (_175_609))
in (FStar_All.pipe_left mk _175_610)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(

let env = (FStar_ToSyntax_Env.default_ml env)
in (

let c = (desugar_comp t.FStar_Parser_AST.range true env t)
in (

let annot = if (FStar_Syntax_Util.is_ml_comp c) then begin
FStar_Util.Inl ((FStar_Syntax_Util.comp_result c))
end else begin
FStar_Util.Inr (c)
end
in (let _175_613 = (let _175_612 = (let _175_611 = (desugar_term env e)
in ((_175_611), (annot), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_175_612))
in (FStar_All.pipe_left mk _175_613)))))
end
| FStar_Parser_AST.Record (_74_1550, []) -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let _74_1562 = (FStar_List.hd fields)
in (match (_74_1562) with
| (f, _74_1561) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _74_1570 -> (match (_74_1570) with
| (g, _74_1569) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| Some (_74_1574, e) -> begin
((fn), (e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _175_621 = (let _175_620 = (let _175_619 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_ToSyntax_Env.typename.FStar_Ident.str)
in ((_175_619), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (_175_620))
in (Prims.raise _175_621))
end
| Some (x) -> begin
((fn), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Project (((x), (fn)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (

let user_constrname = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((record.FStar_ToSyntax_Env.constrname)::[])))
in (

let recterm = (match (eopt) with
| None -> begin
(let _175_626 = (let _175_625 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun _74_1587 -> (match (_74_1587) with
| (f, _74_1586) -> begin
(let _175_624 = (let _175_623 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _175_623))
in ((_175_624), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (_175_625)))
in FStar_Parser_AST.Construct (_175_626))
end
| Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (let _175_628 = (let _175_627 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_175_627))
in (FStar_Parser_AST.mk_term _175_628 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = (let _175_631 = (let _175_630 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun _74_1595 -> (match (_74_1595) with
| (f, _74_1594) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (_175_630)))
in FStar_Parser_AST.Record (_175_631))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _74_1611; FStar_Syntax_Syntax.pos = _74_1609; FStar_Syntax_Syntax.vars = _74_1607}, args); FStar_Syntax_Syntax.tk = _74_1605; FStar_Syntax_Syntax.pos = _74_1603; FStar_Syntax_Syntax.vars = _74_1601}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e = (let _175_638 = (let _175_637 = (let _175_636 = (let _175_635 = (let _175_634 = (let _175_633 = (let _175_632 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_ToSyntax_Env.typename), (_175_632)))
in FStar_Syntax_Syntax.Record_ctor (_175_633))
in Some (_175_634))
in (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant _175_635))
in ((_175_636), (args)))
in FStar_Syntax_Syntax.Tm_app (_175_637))
in (FStar_All.pipe_left mk _175_638))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| _74_1625 -> begin
e
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let _74_1632 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f)
in (match (_74_1632) with
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
in (let _175_643 = (let _175_642 = (let _175_641 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projname (FStar_Ident.range_of_lid f)) FStar_Syntax_Syntax.Delta_equational qual)
in (let _175_640 = (let _175_639 = (FStar_Syntax_Syntax.as_arg e)
in (_175_639)::[])
in ((_175_641), (_175_640))))
in FStar_Syntax_Syntax.Tm_app (_175_642))
in (FStar_All.pipe_left mk _175_643)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _74_1643 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _74_1645 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Let (_74_1647, _74_1649, _74_1651) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QForall (_74_1655, _74_1657, _74_1659) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QExists (_74_1663, _74_1665, _74_1667) -> begin
(failwith "Not implemented yet")
end))))
and desugar_args : FStar_ToSyntax_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _74_1674 -> (match (_74_1674) with
| (a, imp) -> begin
(let _175_647 = (desugar_term env a)
in (arg_withimp_e imp _175_647))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Errors.Error (((msg), (r))))))
in (

let is_requires = (fun _74_1686 -> (match (_74_1686) with
| (t, _74_1685) -> begin
(match ((let _175_655 = (unparen t)
in _175_655.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_74_1688) -> begin
true
end
| _74_1691 -> begin
false
end)
end))
in (

let is_ensures = (fun _74_1696 -> (match (_74_1696) with
| (t, _74_1695) -> begin
(match ((let _175_658 = (unparen t)
in _175_658.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_74_1698) -> begin
true
end
| _74_1701 -> begin
false
end)
end))
in (

let is_app = (fun head _74_1707 -> (match (_74_1707) with
| (t, _74_1706) -> begin
(match ((let _175_663 = (unparen t)
in _175_663.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _74_1711; FStar_Parser_AST.level = _74_1709}, _74_1716, _74_1718) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _74_1722 -> begin
false
end)
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t -> (

let _74_1728 = (head_and_args t)
in (match (_74_1728) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(

let unit_tm = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level)), (FStar_Parser_AST.Nothing))
in (

let nil_pat = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr)), (FStar_Parser_AST.Nothing))
in (

let req_true = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Requires ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.true_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Formula)), (None)))) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level)), (FStar_Parser_AST.Nothing))
in (

let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Errors.Error ((("Not enough arguments to \'Lemma\'"), (t.FStar_Parser_AST.range)))))
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

let head_and_attributes = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes env) lemma)
in ((head_and_attributes), (args)))))))
end
| FStar_Parser_AST.Name (l) when (FStar_ToSyntax_Env.is_effect_name env l) -> begin
(let _175_667 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes env) l)
in ((_175_667), (args)))
end
| FStar_Parser_AST.Name (l) when ((let _175_668 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals _175_668 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((let _175_669 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals _175_669 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)), ([]))), ((((t), (FStar_Parser_AST.Nothing)))::[]))
end
| _74_1759 when default_ok -> begin
(((((FStar_Ident.set_lid_range env.FStar_ToSyntax_Env.default_result_effect head.FStar_Parser_AST.range)), ([]))), ((((t), (FStar_Parser_AST.Nothing)))::[]))
end
| _74_1761 -> begin
(let _175_671 = (let _175_670 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _175_670))
in (fail _175_671))
end)
end)))
in (

let _74_1766 = (pre_process_comp_typ t)
in (match (_74_1766) with
| ((eff, cattributes), args) -> begin
(

let _74_1767 = if ((FStar_List.length args) = (Prims.parse_int "0")) then begin
(let _175_673 = (let _175_672 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _175_672))
in (fail _175_673))
end else begin
()
end
in (

let _74_1771 = (let _175_675 = (FStar_List.hd args)
in (let _175_674 = (FStar_List.tl args)
in ((_175_675), (_175_674))))
in (match (_74_1771) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (Prims.fst result_arg))
in (

let rest = (desugar_args env rest)
in (

let _74_1796 = (FStar_All.pipe_right rest (FStar_List.partition (fun _74_1777 -> (match (_74_1777) with
| (t, _74_1776) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _74_1783; FStar_Syntax_Syntax.pos = _74_1781; FStar_Syntax_Syntax.vars = _74_1779}, (_74_1788)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _74_1793 -> begin
false
end)
end))))
in (match (_74_1796) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _74_1800 -> (match (_74_1800) with
| (t, _74_1799) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_74_1802, ((arg, _74_1805))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _74_1811 -> begin
(failwith "impos")
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

let pattern = (let _175_678 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _175_678 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (Some (FStar_Syntax_Syntax.imp_tag))))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _74_1827 -> begin
pat
end)
in (let _175_682 = (let _175_681 = (let _175_680 = (let _175_679 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) None pat.FStar_Syntax_Syntax.pos)
in ((_175_679), (aq)))
in (_175_680)::[])
in (ens)::_175_681)
in (req)::_175_682))
end
| _74_1830 -> begin
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
| _74_1842 -> begin
None
end))
in (

let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _74_1849 = t
in {FStar_Syntax_Syntax.n = _74_1849.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _74_1849.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _74_1849.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let _74_1856 = b
in {FStar_Parser_AST.b = _74_1856.FStar_Parser_AST.b; FStar_Parser_AST.brange = _74_1856.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _74_1856.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _175_717 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _175_717)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(

let _74_1870 = (FStar_ToSyntax_Env.push_bv env a)
in (match (_74_1870) with
| (env, a) -> begin
(

let a = (

let _74_1871 = a
in {FStar_Syntax_Syntax.ppname = _74_1871.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _74_1871.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats = (desugar_pats env pats)
in (

let body = (desugar_formula env body)
in (

let body = (match (pats) with
| [] -> begin
body
end
| _74_1878 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_pattern (pats))))))
end)
in (

let body = (let _175_720 = (let _175_719 = (let _175_718 = (FStar_Syntax_Syntax.mk_binder a)
in (_175_718)::[])
in (no_annot_abs _175_719 body))
in (FStar_All.pipe_left setpos _175_720))
in (let _175_725 = (let _175_724 = (let _175_723 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (let _175_722 = (let _175_721 = (FStar_Syntax_Syntax.as_arg body)
in (_175_721)::[])
in ((_175_723), (_175_722))))
in FStar_Syntax_Syntax.Tm_app (_175_724))
in (FStar_All.pipe_left mk _175_725)))))))
end))
end
| _74_1882 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (let _175_740 = (q ((rest), (pats), (body)))
in (let _175_739 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _175_740 _175_739 FStar_Parser_AST.Formula)))
in (let _175_741 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term _175_741 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _74_1896 -> begin
(failwith "impossible")
end))
in (match ((let _175_742 = (unparen f)
in _175_742.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(

let f = (desugar_formula env f)
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((l), (f.FStar_Syntax_Syntax.pos), (p)))))))))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _175_744 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _175_744)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _175_746 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _175_746)))
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
| _74_1954 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let _74_1978 = (FStar_List.fold_left (fun _74_1959 b -> (match (_74_1959) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let _74_1961 = b
in {FStar_Parser_AST.b = _74_1961.FStar_Parser_AST.b; FStar_Parser_AST.brange = _74_1961.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _74_1961.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(

let _74_1970 = (FStar_ToSyntax_Env.push_bv env a)
in (match (_74_1970) with
| (env, a) -> begin
(

let a = (

let _74_1971 = a
in {FStar_Syntax_Syntax.ppname = _74_1971.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _74_1971.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env), ((((a), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| _74_1975 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (_74_1978) with
| (env, tpars) -> begin
((env), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _175_753 = (desugar_typ env t)
in ((Some (x)), (_175_753)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _175_754 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in ((Some (x)), (_175_754)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _175_755 = (desugar_typ env t)
in ((None), (_175_755)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators = (fun quals env t tps k datas -> (

let quals = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___481 -> (match (uu___481) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| _74_2003 -> begin
false
end))))
in (

let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_ToSyntax_Env.iface) || env.FStar_ToSyntax_Env.admitted_iface) then begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _175_767 = (let _175_766 = (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in ((disc_name), ([]), (FStar_Syntax_Syntax.tun), (_175_766), ((FStar_Ident.range_of_lid disc_name))))
in FStar_Syntax_Syntax.Sig_declare_typ (_175_767)))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_ToSyntax_Env.env  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (let _175_795 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _74_2019 -> (match (_74_2019) with
| (x, _74_2018) -> begin
(

let _74_2023 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_74_2023) with
| (field_name, _74_2022) -> begin
(

let only_decl = (((let _175_780 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _175_780)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _175_782 = (let _175_781 = (FStar_ToSyntax_Env.current_module env)
in _175_781.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _175_782)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> if only_decl then begin
(let _175_786 = (FStar_List.filter (fun uu___482 -> (match (uu___482) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| _74_2031 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::_175_786)
end else begin
q
end)
in (

let quals = (

let iquals = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___483 -> (match (uu___483) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| _74_2036 -> begin
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

let lb = (let _175_789 = (let _175_788 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_175_788))
in {FStar_Syntax_Syntax.lbname = _175_789; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun})
in (

let impl = (let _175_794 = (let _175_793 = (let _175_792 = (let _175_791 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _175_791 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_175_792)::[])
in ((((false), ((lb)::[]))), (p), (_175_793), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (_175_794))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end)))
end)))))
end))
end))))
in (FStar_All.pipe_right _175_795 FStar_List.flatten))))


let mk_data_projector_names = (fun iquals env _74_2048 -> (match (_74_2048) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _74_2051, t, _74_2054, n, quals, _74_2058, _74_2060) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let _74_2066 = (FStar_Syntax_Util.arrow_formals t)
in (match (_74_2066) with
| (formals, _74_2065) -> begin
(match (formals) with
| [] -> begin
[]
end
| _74_2069 -> begin
(

let filter_records = (fun uu___484 -> (match (uu___484) with
| FStar_Syntax_Syntax.RecordConstructor (_74_2072, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| _74_2077 -> begin
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

let _74_2087 = (FStar_Util.first_N n formals)
in (match (_74_2087) with
| (_74_2085, rest) -> begin
(mk_indexed_projector_names iquals fv_qual env lid rest)
end)))))
end)
end))
end
| _74_2089 -> begin
[]
end)
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _175_817 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (_175_817))
end else begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end
in (

let lb = (let _175_822 = (let _175_818 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (_175_818))
in (let _175_821 = (let _175_819 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _175_819))
in (let _175_820 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _175_822; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _175_821; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _175_820})))
in FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (rng), (lids), (quals), ([]))))))


let rec desugar_tycon : FStar_ToSyntax_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (

let tycon_id = (fun uu___485 -> (match (uu___485) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _175_836 = (let _175_835 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_175_835))
in (FStar_Parser_AST.mk_term _175_836 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type_level)
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
| _74_2164 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _175_849 = (let _175_848 = (let _175_847 = (binder_to_term b)
in ((out), (_175_847), ((imp_of_aqual b))))
in FStar_Parser_AST.App (_175_848))
in (FStar_Parser_AST.mk_term _175_849 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun uu___486 -> (match (uu___486) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun _74_2179 -> (match (_74_2179) with
| (x, t, _74_2178) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (let _175_855 = (let _175_854 = (let _175_853 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_175_853))
in (FStar_Parser_AST.mk_term _175_854 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders _175_855 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type_level)
in (let _175_857 = (FStar_All.pipe_right fields (FStar_List.map (fun _74_2188 -> (match (_74_2188) with
| (x, _74_2185, _74_2187) -> begin
(FStar_Syntax_Util.unmangle_field_name x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (_175_857)))))))
end
| _74_2190 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals uu___487 -> (match (uu___487) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let _74_2204 = (typars_of_binders _env binders)
in (match (_74_2204) with
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

let tconstr = (let _175_868 = (let _175_867 = (let _175_866 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_175_866))
in (FStar_Parser_AST.mk_term _175_867 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders _175_868 binders))
in (

let qlid = (FStar_ToSyntax_Env.qualify _env id)
in (

let typars = (FStar_Syntax_Subst.close_binders typars)
in (

let k = (FStar_Syntax_Subst.close typars k)
in (

let se = FStar_Syntax_Syntax.Sig_inductive_typ (((qlid), ([]), (typars), (k), (mutuals), ([]), (quals), (rng)))
in (

let _env = (FStar_ToSyntax_Env.push_top_level_rec_binding _env id FStar_Syntax_Syntax.Delta_constant)
in (

let _env2 = (FStar_ToSyntax_Env.push_top_level_rec_binding _env' id FStar_Syntax_Syntax.Delta_constant)
in ((_env), (_env2), (se), (tconstr))))))))))
end))
end
| _74_2217 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env bs -> (

let _74_2232 = (FStar_List.fold_left (fun _74_2223 _74_2226 -> (match (((_74_2223), (_74_2226))) with
| ((env, tps), (x, imp)) -> begin
(

let _74_2229 = (FStar_ToSyntax_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_74_2229) with
| (env, y) -> begin
((env), ((((y), (imp)))::tps))
end))
end)) ((env), ([])) bs)
in (match (_74_2232) with
| (env, bs) -> begin
((env), ((FStar_List.rev bs)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt = (match (kopt) with
| None -> begin
(let _175_875 = (tm_type_z id.FStar_Ident.idRange)
in Some (_175_875))
end
| _74_2241 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt)))
in (

let _74_2251 = (desugar_abstract_tc quals env [] tc)
in (match (_74_2251) with
| (_74_2245, _74_2247, se, _74_2250) -> begin
(

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _74_2254, typars, k, [], [], quals, rng) -> begin
(

let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(

let _74_2263 = (let _175_877 = (FStar_Range.string_of_range rng)
in (let _175_876 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _175_877 _175_876)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (

let t = (match (typars) with
| [] -> begin
k
end
| _74_2268 -> begin
(let _175_880 = (let _175_879 = (let _175_878 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (_175_878)))
in FStar_Syntax_Syntax.Tm_arrow (_175_879))
in (FStar_Syntax_Syntax.mk _175_880 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t), (quals), (rng)))))
end
| _74_2271 -> begin
se
end)
in (

let env = (FStar_ToSyntax_Env.push_sigelt env se)
in ((env), ((se)::[]))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let _74_2283 = (typars_of_binders env binders)
in (match (_74_2283) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun uu___488 -> (match (uu___488) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _74_2288 -> begin
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

let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___489 -> (match (uu___489) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _74_2296 -> begin
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

let _74_2321 = (match ((let _175_883 = (unparen t)
in _175_883.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Construct (head, args) -> begin
(

let _74_2316 = (match ((FStar_List.rev args)) with
| ((last_arg, _74_2305))::args_rev -> begin
(match ((let _175_884 = (unparen last_arg)
in _175_884.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| _74_2311 -> begin
(([]), (args))
end)
end
| _74_2313 -> begin
(([]), (args))
end)
in (match (_74_2316) with
| (cattributes, args) -> begin
(let _175_885 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head), (args)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (_175_885)))
end))
end
| _74_2318 -> begin
((t), ([]))
end)
in (match (_74_2321) with
| (t, cattributes) -> begin
(

let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (

let typars = (FStar_Syntax_Subst.close_binders typars)
in (

let c = (FStar_Syntax_Subst.close_comp typars c)
in (let _175_889 = (let _175_888 = (FStar_ToSyntax_Env.qualify env id)
in (let _175_887 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___490 -> (match (uu___490) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _74_2328 -> begin
true
end))))
in ((_175_888), ([]), (typars), (c), (_175_887), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c))), (rng))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_175_889)))))
end))
end else begin
(

let t = (desugar_typ env' t)
in (

let nm = (FStar_ToSyntax_Env.qualify env id)
in (mk_typ_abbrev nm [] typars k t ((nm)::[]) quals rng)))
end
in (

let env = (FStar_ToSyntax_Env.push_sigelt env se)
in ((env), ((se)::[])))))))
end))
end
| (FStar_Parser_AST.TyconRecord (_74_2334))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let _74_2340 = (tycon_record_as_variant trec)
in (match (_74_2340) with
| (t, fs) -> begin
(let _175_894 = (let _175_893 = (let _175_892 = (let _175_891 = (let _175_890 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.ids_of_lid _175_890))
in ((_175_891), (fs)))
in FStar_Syntax_Syntax.RecordType (_175_892))
in (_175_893)::quals)
in (desugar_tycon env rng _175_894 ((t)::[])))
end)))
end
| (_74_2344)::_74_2342 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let _74_2355 = et
in (match (_74_2355) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_74_2357) -> begin
(

let trec = tc
in (

let _74_2362 = (tycon_record_as_variant trec)
in (match (_74_2362) with
| (t, fs) -> begin
(let _175_906 = (let _175_905 = (let _175_904 = (let _175_903 = (let _175_902 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.ids_of_lid _175_902))
in ((_175_903), (fs)))
in FStar_Syntax_Syntax.RecordType (_175_904))
in (_175_905)::quals)
in (collect_tcs _175_906 ((env), (tcs)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let _74_2374 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_74_2374) with
| (env, _74_2371, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let _74_2386 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_74_2386) with
| (env, _74_2383, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (binders), (t), (quals))))::tcs))
end))
end
| _74_2388 -> begin
(failwith "Unrecognized mutual type definition")
end)
end)))
in (

let _74_2391 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (_74_2391) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun uu___492 -> (match (uu___492) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _74_2399, _74_2401, _74_2403, _74_2405), binders, t, quals) -> begin
(

let t = (

let _74_2415 = (typars_of_binders env binders)
in (match (_74_2415) with
| (env, tpars) -> begin
(

let _74_2418 = (push_tparams env tpars)
in (match (_74_2418) with
| (env_tps, tpars) -> begin
(

let t = (desugar_typ env_tps t)
in (

let tpars = (FStar_Syntax_Subst.close_binders tpars)
in (FStar_Syntax_Subst.close tpars t)))
end))
end))
in (let _175_909 = (let _175_908 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in (([]), (_175_908)))
in (_175_909)::[]))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _74_2428, tags, _74_2431), constrs, tconstr, quals) -> begin
(

let tycon = ((tname), (tpars), (k))
in (

let _74_2442 = (push_tparams env tpars)
in (match (_74_2442) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun _74_2446 -> (match (_74_2446) with
| (x, _74_2445) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let _74_2472 = (let _175_921 = (FStar_All.pipe_right constrs (FStar_List.map (fun _74_2453 -> (match (_74_2453) with
| (id, topt, _74_2451, of_notation) -> begin
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
(failwith "Impossible")
end
| Some (t) -> begin
t
end)
end
in (

let t = (let _175_913 = (FStar_ToSyntax_Env.default_total env_tps)
in (let _175_912 = (close env_tps t)
in (desugar_term _175_913 _175_912)))
in (

let name = (FStar_ToSyntax_Env.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun uu___491 -> (match (uu___491) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _74_2467 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (let _175_920 = (let _175_919 = (let _175_918 = (let _175_917 = (let _175_916 = (let _175_915 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _175_915))
in (FStar_Syntax_Util.arrow data_tpars _175_916))
in ((name), (univs), (_175_917), (tname), (ntps), (quals), (mutuals), (rng)))
in FStar_Syntax_Syntax.Sig_datacon (_175_918))
in ((tps), (_175_919)))
in ((name), (_175_920))))))))
end))))
in (FStar_All.pipe_left FStar_List.split _175_921))
in (match (_74_2472) with
| (constrNames, constrs) -> begin
((([]), (FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))))::constrs
end)))
end)))
end
| _74_2474 -> begin
(failwith "impossible")
end))))
in (

let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (

let _74_2479 = (let _175_922 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals _175_922 rng))
in (match (_74_2479) with
| (bundle, abbrevs) -> begin
(

let env = (FStar_ToSyntax_Env.push_sigelt env0 bundle)
in (

let env = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env abbrevs)
in (

let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projector_names quals env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun uu___493 -> (match (uu___493) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _74_2486, tps, k, _74_2490, constrs, quals, _74_2494) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract quals) then begin
(FStar_Syntax_Syntax.Private)::quals
end else begin
quals
end
in (mk_data_discriminators quals env tname tps k constrs))
end
| _74_2499 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env ops)
in ((env), ((FStar_List.append ((bundle)::[]) (FStar_List.append abbrevs ops))))))))))
end)))))
end)))))
end
| [] -> begin
(failwith "impossible")
end))))))))))


let desugar_binders : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (

let _74_2523 = (FStar_List.fold_left (fun _74_2508 b -> (match (_74_2508) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(

let _74_2516 = (FStar_ToSyntax_Env.push_bv env a)
in (match (_74_2516) with
| (env, a) -> begin
(let _175_931 = (let _175_930 = (FStar_Syntax_Syntax.mk_binder (

let _74_2517 = a
in {FStar_Syntax_Syntax.ppname = _74_2517.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _74_2517.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_175_930)::binders)
in ((env), (_175_931)))
end))
end
| _74_2520 -> begin
(Prims.raise (FStar_Errors.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end)
end)) ((env), ([])) binders)
in (match (_74_2523) with
| (env, binders) -> begin
((env), ((FStar_List.rev binders)))
end)))


let rec desugar_effect : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  Prims.bool  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_kind eff_decls actions for_free -> (

let env0 = env
in (

let monad_env = (FStar_ToSyntax_Env.enter_monad_scope env eff_name)
in (

let _74_2537 = (desugar_binders monad_env eff_binders)
in (match (_74_2537) with
| (env, binders) -> begin
(

let eff_k = (let _175_969 = (FStar_ToSyntax_Env.default_total env)
in (desugar_term _175_969 eff_kind))
in (

let _74_2548 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _74_2541 decl -> (match (_74_2541) with
| (env, out) -> begin
(

let _74_2545 = (desugar_decl env decl)
in (match (_74_2545) with
| (env, ses) -> begin
(let _175_973 = (let _175_972 = (FStar_List.hd ses)
in (_175_972)::out)
in ((env), (_175_973)))
end))
end)) ((env), ([]))))
in (match (_74_2548) with
| (env, decls) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let actions = (FStar_All.pipe_right actions (FStar_List.map (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_74_2552, ((FStar_Parser_AST.TyconAbbrev (name, _74_2555, _74_2557, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (_74_2563, ((def, _74_2570))::((cps_type, _74_2566))::[]); FStar_Parser_AST.range = _74_2561; FStar_Parser_AST.level = _74_2559}), _74_2579))::[]) when (not (for_free)) -> begin
(let _175_979 = (FStar_ToSyntax_Env.qualify env name)
in (let _175_978 = (let _175_975 = (desugar_term env def)
in (FStar_Syntax_Subst.close binders _175_975))
in (let _175_977 = (let _175_976 = (desugar_typ env cps_type)
in (FStar_Syntax_Subst.close binders _175_976))
in {FStar_Syntax_Syntax.action_name = _175_979; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _175_978; FStar_Syntax_Syntax.action_typ = _175_977})))
end
| FStar_Parser_AST.Tycon (_74_2585, ((FStar_Parser_AST.TyconAbbrev (name, _74_2588, _74_2590, defn), _74_2595))::[]) when for_free -> begin
(let _175_982 = (FStar_ToSyntax_Env.qualify env name)
in (let _175_981 = (let _175_980 = (desugar_term env defn)
in (FStar_Syntax_Subst.close binders _175_980))
in {FStar_Syntax_Syntax.action_name = _175_982; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _175_981; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
end
| _74_2601 -> begin
(Prims.raise (FStar_Errors.Error ((("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples)."), (d.FStar_Parser_AST.drange)))))
end))))
in (

let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (

let lookup = (fun s -> (

let l = (FStar_ToSyntax_Env.qualify env (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange))))
in (let _175_986 = (let _175_985 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _175_985))
in (([]), (_175_986)))))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (Some (mname))) quals)
in (

let se = if for_free then begin
(

let dummy_tscheme = (let _175_987 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (([]), (_175_987)))
in (let _175_993 = (let _175_992 = (let _175_991 = (let _175_988 = (lookup "repr")
in (Prims.snd _175_988))
in (let _175_990 = (lookup "return")
in (let _175_989 = (lookup "bind")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = _175_991; FStar_Syntax_Syntax.return_repr = _175_990; FStar_Syntax_Syntax.bind_repr = _175_989; FStar_Syntax_Syntax.actions = actions})))
in ((_175_992), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (_175_993)))
end else begin
(

let rr = ((FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right qualifiers FStar_Syntax_Syntax.contains_reflectable))
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (let _175_1009 = (let _175_1008 = (let _175_1007 = (lookup "return_wp")
in (let _175_1006 = (lookup "bind_wp")
in (let _175_1005 = (lookup "if_then_else")
in (let _175_1004 = (lookup "ite_wp")
in (let _175_1003 = (lookup "stronger")
in (let _175_1002 = (lookup "close_wp")
in (let _175_1001 = (lookup "assert_p")
in (let _175_1000 = (lookup "assume_p")
in (let _175_999 = (lookup "null_wp")
in (let _175_998 = (lookup "trivial")
in (let _175_997 = if rr then begin
(let _175_994 = (lookup "repr")
in (FStar_All.pipe_left Prims.snd _175_994))
end else begin
FStar_Syntax_Syntax.tun
end
in (let _175_996 = if rr then begin
(lookup "return")
end else begin
un_ts
end
in (let _175_995 = if rr then begin
(lookup "bind")
end else begin
un_ts
end
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = _175_1007; FStar_Syntax_Syntax.bind_wp = _175_1006; FStar_Syntax_Syntax.if_then_else = _175_1005; FStar_Syntax_Syntax.ite_wp = _175_1004; FStar_Syntax_Syntax.stronger = _175_1003; FStar_Syntax_Syntax.close_wp = _175_1002; FStar_Syntax_Syntax.assert_p = _175_1001; FStar_Syntax_Syntax.assume_p = _175_1000; FStar_Syntax_Syntax.null_wp = _175_999; FStar_Syntax_Syntax.trivial = _175_998; FStar_Syntax_Syntax.repr = _175_997; FStar_Syntax_Syntax.return_repr = _175_996; FStar_Syntax_Syntax.bind_repr = _175_995; FStar_Syntax_Syntax.actions = actions})))))))))))))
in ((_175_1008), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect (_175_1009))))
end
in (

let env = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right actions (FStar_List.fold_left (fun env a -> (let _175_1012 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env _175_1012))) env))
in (

let env = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable)) then begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let refl_decl = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]), (d.FStar_Parser_AST.drange)))
in (FStar_ToSyntax_Env.push_sigelt env refl_decl)))
end else begin
env
end
in ((env), ((se)::[]))))))))))))
end)))
end)))))
and desugar_redefine_effect : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  (FStar_Ident.lident Prims.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier)  ->  FStar_Parser_AST.qualifier Prims.list  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.eff_decl  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d trans_qual quals eff_name eff_binders defn build_sigelt -> (

let env0 = env
in (

let env = (FStar_ToSyntax_Env.enter_monad_scope env eff_name)
in (

let _74_2632 = (desugar_binders env eff_binders)
in (match (_74_2632) with
| (env, binders) -> begin
(

let _74_2659 = (

let _74_2635 = (head_and_args defn)
in (match (_74_2635) with
| (head, args) -> begin
(

let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_defn env) l)
end
| _74_2639 -> begin
(let _175_1039 = (let _175_1038 = (let _175_1037 = (let _175_1036 = (let _175_1035 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat _175_1035 " not found"))
in (Prims.strcat "Effect " _175_1036))
in ((_175_1037), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (_175_1038))
in (Prims.raise _175_1039))
end)
in (

let _74_2655 = (match ((FStar_List.rev args)) with
| ((last_arg, _74_2644))::args_rev -> begin
(match ((let _175_1040 = (unparen last_arg)
in _175_1040.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| _74_2650 -> begin
(([]), (args))
end)
end
| _74_2652 -> begin
(([]), (args))
end)
in (match (_74_2655) with
| (cattributes, args) -> begin
(let _175_1042 = (desugar_args env args)
in (let _175_1041 = (desugar_attributes env cattributes)
in ((ed), (_175_1042), (_175_1041))))
end)))
end))
in (match (_74_2659) with
| (ed, args, cattributes) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let sub = (fun _74_2665 -> (match (_74_2665) with
| (_74_2663, x) -> begin
(

let _74_2668 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_74_2668) with
| (edb, x) -> begin
(

let _74_2669 = if ((FStar_List.length args) <> (FStar_List.length edb)) then begin
(Prims.raise (FStar_Errors.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end else begin
()
end
in (

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _175_1046 = (let _175_1045 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _175_1045))
in (([]), (_175_1046)))))
end))
end))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let ed = (let _175_1071 = (let _175_1047 = (trans_qual (Some (mname)))
in (FStar_List.map _175_1047 quals))
in (let _175_1070 = (let _175_1048 = (sub (([]), (ed.FStar_Syntax_Syntax.signature)))
in (Prims.snd _175_1048))
in (let _175_1069 = (sub ed.FStar_Syntax_Syntax.ret_wp)
in (let _175_1068 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _175_1067 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _175_1066 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _175_1065 = (sub ed.FStar_Syntax_Syntax.stronger)
in (let _175_1064 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _175_1063 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _175_1062 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _175_1061 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _175_1060 = (sub ed.FStar_Syntax_Syntax.trivial)
in (let _175_1059 = (let _175_1049 = (sub (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd _175_1049))
in (let _175_1058 = (sub ed.FStar_Syntax_Syntax.return_repr)
in (let _175_1057 = (sub ed.FStar_Syntax_Syntax.bind_repr)
in (let _175_1056 = (FStar_List.map (fun action -> (let _175_1055 = (FStar_ToSyntax_Env.qualify env action.FStar_Syntax_Syntax.action_unqualified_name)
in (let _175_1054 = (let _175_1051 = (sub (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd _175_1051))
in (let _175_1053 = (let _175_1052 = (sub (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd _175_1052))
in {FStar_Syntax_Syntax.action_name = _175_1055; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _175_1054; FStar_Syntax_Syntax.action_typ = _175_1053})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = _175_1071; FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _175_1070; FStar_Syntax_Syntax.ret_wp = _175_1069; FStar_Syntax_Syntax.bind_wp = _175_1068; FStar_Syntax_Syntax.if_then_else = _175_1067; FStar_Syntax_Syntax.ite_wp = _175_1066; FStar_Syntax_Syntax.stronger = _175_1065; FStar_Syntax_Syntax.close_wp = _175_1064; FStar_Syntax_Syntax.assert_p = _175_1063; FStar_Syntax_Syntax.assume_p = _175_1062; FStar_Syntax_Syntax.null_wp = _175_1061; FStar_Syntax_Syntax.trivial = _175_1060; FStar_Syntax_Syntax.repr = _175_1059; FStar_Syntax_Syntax.return_repr = _175_1058; FStar_Syntax_Syntax.bind_repr = _175_1057; FStar_Syntax_Syntax.actions = _175_1056}))))))))))))))))
in (

let se = (build_sigelt ed d.FStar_Parser_AST.drange)
in (

let monad_env = env
in (

let env = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun env a -> (let _175_1074 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env _175_1074))) env))
in (

let env = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable)) then begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let refl_decl = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]), (d.FStar_Parser_AST.drange)))
in (FStar_ToSyntax_Env.push_sigelt env refl_decl)))
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
| FStar_Parser_AST.Fsdoc (_74_2691) -> begin
((env), ([]))
end
| FStar_Parser_AST.TopLevelModule (id) -> begin
((env), ([]))
end
| FStar_Parser_AST.Open (lid) -> begin
(

let env = (FStar_ToSyntax_Env.push_namespace env lid)
in ((env), ([])))
end
| FStar_Parser_AST.Include (lid) -> begin
(

let env = (FStar_ToSyntax_Env.push_include env lid)
in ((env), ([])))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _175_1079 = (FStar_ToSyntax_Env.push_module_abbrev env x l)
in ((_175_1079), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, tcs) -> begin
(

let quals = if is_effect then begin
(FStar_Parser_AST.Effect_qual)::d.FStar_Parser_AST.quals
end else begin
d.FStar_Parser_AST.quals
end
in (

let tcs = (FStar_List.map (fun _74_2713 -> (match (_74_2713) with
| (x, _74_2712) -> begin
x
end)) tcs)
in (let _175_1081 = (FStar_List.map (trans_qual None) quals)
in (desugar_tycon env d.FStar_Parser_AST.drange _175_1081 tcs))))
end
| FStar_Parser_AST.TopLevelLet (isrec, lets) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let attrs = d.FStar_Parser_AST.attrs
in (

let attrs = (FStar_List.map (desugar_term env) attrs)
in (match ((let _175_1083 = (let _175_1082 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _175_1082))
in _175_1083.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _74_2724) -> begin
(

let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals = (match (quals) with
| (_74_2732)::_74_2730 -> begin
(FStar_List.map (trans_qual None) quals)
end
| _74_2735 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun uu___494 -> (match (uu___494) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_74_2746); FStar_Syntax_Syntax.lbunivs = _74_2744; FStar_Syntax_Syntax.lbtyp = _74_2742; FStar_Syntax_Syntax.lbeff = _74_2740; FStar_Syntax_Syntax.lbdef = _74_2738} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _74_2756; FStar_Syntax_Syntax.lbtyp = _74_2754; FStar_Syntax_Syntax.lbeff = _74_2752; FStar_Syntax_Syntax.lbdef = _74_2750} -> begin
(FStar_ToSyntax_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _74_2764 -> (match (_74_2764) with
| (_74_2762, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (

let lbs = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _175_1088 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _74_2768 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let _74_2770 = fv
in {FStar_Syntax_Syntax.fv_name = _74_2770.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = _74_2770.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = _74_2768.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _74_2768.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _74_2768.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _74_2768.FStar_Syntax_Syntax.lbdef})))))
in (((Prims.fst lbs)), (_175_1088)))
end else begin
lbs
end
in (

let s = (let _175_1091 = (let _175_1090 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in ((lbs), (d.FStar_Parser_AST.drange), (_175_1090), (quals), (attrs)))
in FStar_Syntax_Syntax.Sig_let (_175_1091))
in (

let env = (FStar_ToSyntax_Env.push_sigelt env s)
in ((env), ((s)::[]))))))))
end
| _74_2777 -> begin
(failwith "Desugaring a let did not produce a let")
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
in (let _175_1095 = (let _175_1094 = (let _175_1093 = (let _175_1092 = (FStar_ToSyntax_Env.qualify env id)
in ((_175_1092), (f), ((FStar_Syntax_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_assume (_175_1093))
in (_175_1094)::[])
in ((env), (_175_1095))))
end
| FStar_Parser_AST.Val (id, t) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let t = (let _175_1096 = (close_fun env t)
in (desugar_term env _175_1096))
in (

let quals = if (env.FStar_ToSyntax_Env.iface && env.FStar_ToSyntax_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (

let se = (let _175_1099 = (let _175_1098 = (FStar_ToSyntax_Env.qualify env id)
in (let _175_1097 = (FStar_List.map (trans_qual None) quals)
in ((_175_1098), ([]), (t), (_175_1097), (d.FStar_Parser_AST.drange))))
in FStar_Syntax_Syntax.Sig_declare_typ (_175_1099))
in (

let env = (FStar_ToSyntax_Env.push_sigelt env se)
in ((env), ((se)::[])))))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(

let _74_2803 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (match (_74_2803) with
| (t, _74_2802) -> begin
(

let l = (FStar_ToSyntax_Env.qualify env id)
in (

let se = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Syntax_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((FStar_Syntax_Const.exn_lid)::[]), (d.FStar_Parser_AST.drange)))
in (

let se' = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((l)::[]), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_ToSyntax_Env.push_sigelt env se')
in (

let data_ops = (mk_data_projector_names [] env (([]), (se)))
in (

let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (

let env = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env (FStar_List.append discs data_ops))
in ((env), ((FStar_List.append ((se')::discs) data_ops))))))))))
end))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(

let t = (desugar_term env term)
in (

let t = (let _175_1104 = (let _175_1100 = (FStar_Syntax_Syntax.null_binder t)
in (_175_1100)::[])
in (let _175_1103 = (let _175_1102 = (let _175_1101 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (Prims.fst _175_1101))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _175_1102))
in (FStar_Syntax_Util.arrow _175_1104 _175_1103)))
in (

let l = (FStar_ToSyntax_Env.qualify env id)
in (

let se = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Syntax_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((FStar_Syntax_Const.exn_lid)::[]), (d.FStar_Parser_AST.drange)))
in (

let se' = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((l)::[]), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_ToSyntax_Env.push_sigelt env se')
in (

let data_ops = (mk_data_projector_names [] env (([]), (se)))
in (

let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (

let env = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env (FStar_List.append discs data_ops))
in ((env), ((FStar_List.append ((se')::discs) data_ops))))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(

let _74_2832 = (desugar_binders env binders)
in (match (_74_2832) with
| (env_k, binders) -> begin
(

let k = (desugar_term env_k k)
in (

let name = (FStar_ToSyntax_Env.qualify env id)
in (

let se = (mk_typ_abbrev name [] binders FStar_Syntax_Syntax.tun k ((name)::[]) [] d.FStar_Parser_AST.drange)
in (

let env = (FStar_ToSyntax_Env.push_sigelt env se)
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

let lookup = (fun l -> (match ((FStar_ToSyntax_Env.try_lookup_effect_name env l)) with
| None -> begin
(let _175_1115 = (let _175_1114 = (let _175_1113 = (let _175_1112 = (let _175_1111 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat _175_1111 " not found"))
in (Prims.strcat "Effect name " _175_1112))
in ((_175_1113), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (_175_1114))
in (Prims.raise _175_1115))
end
| Some (l) -> begin
l
end))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let _74_2892 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(let _175_1118 = (let _175_1117 = (let _175_1116 = (desugar_term env t)
in (([]), (_175_1116)))
in Some (_175_1117))
in ((_175_1118), (None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(let _175_1124 = (let _175_1120 = (let _175_1119 = (desugar_term env wp)
in (([]), (_175_1119)))
in Some (_175_1120))
in (let _175_1123 = (let _175_1122 = (let _175_1121 = (desugar_term env t)
in (([]), (_175_1121)))
in Some (_175_1122))
in ((_175_1124), (_175_1123))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(let _175_1127 = (let _175_1126 = (let _175_1125 = (desugar_term env t)
in (([]), (_175_1125)))
in Some (_175_1126))
in ((None), (_175_1127)))
end)
in (match (_74_2892) with
| (lift_wp, lift) -> begin
(

let se = FStar_Syntax_Syntax.Sig_sub_effect ((({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _74_2898 d -> (match (_74_2898) with
| (env, sigelts) -> begin
(

let _74_2902 = (desugar_decl env d)
in (match (_74_2902) with
| (env, se) -> begin
((env), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))


let open_prims_all : (FStar_Parser_AST.decoration Prims.list  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]


let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_ToSyntax_Env.finish_module_or_interface env prev_mod)
end)
in (

let _74_2925 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _175_1145 = (FStar_ToSyntax_Env.prepare_module_or_interface true admitted env mname)
in ((_175_1145), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _175_1146 = (FStar_ToSyntax_Env.prepare_module_or_interface false false env mname)
in ((_175_1146), (mname), (decls), (false)))
end)
in (match (_74_2925) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let _74_2928 = (desugar_decls env decls)
in (match (_74_2928) with
| (env, sigelts) -> begin
(

let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in ((env), (modul), (pop_when_done)))
end))
end))))


let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (

let m = if ((FStar_Options.interactive ()) && ((let _175_1154 = (let _175_1153 = (FStar_Options.file_list ())
in (FStar_List.hd _175_1153))
in (FStar_Util.get_file_extension _175_1154)) = "fsti")) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface (((mname), (decls), (true)))
end
| FStar_Parser_AST.Interface (mname, _74_2939, _74_2941) -> begin
(failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (

let _74_2949 = (desugar_modul_common curmod env m)
in (match (_74_2949) with
| (x, y, _74_2948) -> begin
((x), (y))
end))))


let desugar_modul : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (

let _74_2955 = (desugar_modul_common None env m)
in (match (_74_2955) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_ToSyntax_Env.finish_module_or_interface env modul)
in (

let _74_2957 = if (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _175_1159 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _175_1159))
end else begin
()
end
in (let _175_1160 = if pop_when_done then begin
(FStar_ToSyntax_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in ((_175_1160), (modul)))))
end)))


let desugar_file : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (

let _74_2970 = (FStar_List.fold_left (fun _74_2963 m -> (match (_74_2963) with
| (env, mods) -> begin
(

let _74_2967 = (desugar_modul env m)
in (match (_74_2967) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (_74_2970) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_ToSyntax_Env.env  ->  FStar_ToSyntax_Env.env = (fun m en -> (

let _74_2975 = (FStar_ToSyntax_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_74_2975) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt (

let _74_2976 = en
in {FStar_ToSyntax_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_ToSyntax_Env.curmonad = _74_2976.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = _74_2976.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = _74_2976.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = _74_2976.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = _74_2976.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = _74_2976.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = _74_2976.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = _74_2976.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.default_result_effect = _74_2976.FStar_ToSyntax_Env.default_result_effect; FStar_ToSyntax_Env.iface = _74_2976.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = _74_2976.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = _74_2976.FStar_ToSyntax_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (

let env = (FStar_ToSyntax_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




