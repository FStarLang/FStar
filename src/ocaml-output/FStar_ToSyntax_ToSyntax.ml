
open Prims

let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun uu___184_5 -> (match (uu___184_5) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| uu____8 -> begin
None
end))


let trans_qual : FStar_Range.range  ->  FStar_Ident.lident Prims.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r maybe_effect_id uu___185_19 -> (match (uu___185_19) with
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
((FStar_Errors.warn r "The \'opaque\' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given \'opaque val f : t\', the behavior was to exclude the definition of \'f\' to the SMT solver. This corresponds roughly to the new \'irreducible\' qualifier. (2) Given \'opaque type t = t\'\', the behavior was to provide the definition of \'t\' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of \'unfoldable\' (which is currently the default).");
FStar_Syntax_Syntax.Visible_default;
)
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


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun uu___186_25 -> (match (uu___186_25) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun uu___187_32 -> (match (uu___187_32) with
| FStar_Parser_AST.Hash -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| uu____34 -> begin
None
end))


let arg_withimp_e = (fun imp t -> ((t), ((as_imp imp))))


let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| uu____67 -> begin
((t), (None))
end))


let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (uu____76) -> begin
true
end
| uu____79 -> begin
false
end)))))


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| uu____84 -> begin
t
end))


let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _0_370 = FStar_Parser_AST.Name ((FStar_Ident.lid_of_path (("Type0")::[]) r))
in (FStar_Parser_AST.mk_term _0_370 r FStar_Parser_AST.Kind)))


let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _0_371 = FStar_Parser_AST.Name ((FStar_Ident.lid_of_path (("Type")::[]) r))
in (FStar_Parser_AST.mk_term _0_371 r FStar_Parser_AST.Kind)))


let rec is_comp_type : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> (match (t.FStar_Parser_AST.tm) with
| (FStar_Parser_AST.Name (l)) | (FStar_Parser_AST.Construct (l, _)) -> begin
(let _0_372 = (FStar_ToSyntax_Env.try_lookup_effect_name env l)
in (FStar_All.pipe_right _0_372 FStar_Option.isSome))
end
| FStar_Parser_AST.App (head, uu____104, uu____105) -> begin
(is_comp_type env head)
end
| (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) | (FStar_Parser_AST.LetOpen (_, t)) -> begin
(is_comp_type env t)
end
| uu____109 -> begin
false
end))


let unit_ty : FStar_Parser_AST.term = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) FStar_Range.dummyRange FStar_Parser_AST.Type_level)


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _0_375 = (let _0_374 = (FStar_Ident.mk_ident (let _0_373 = (FStar_Parser_AST.compile_op n s)
in ((_0_373), (r))))
in (_0_374)::[])
in (FStar_All.pipe_right _0_375 FStar_Ident.lid_of_ids)))


let op_as_term : FStar_ToSyntax_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (

let r = (fun l dd -> Some ((let _0_376 = (FStar_Syntax_Syntax.lid_as_fv (FStar_Ident.set_lid_range l rng) dd None)
in (FStar_All.pipe_right _0_376 FStar_Syntax_Syntax.fv_to_tm))))
in (

let fallback = (fun uu____146 -> (match (s) with
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
(

let uu____148 = (FStar_Options.ml_ish ())
in (match (uu____148) with
| true -> begin
(r FStar_Syntax_Const.list_append_lid FStar_Syntax_Syntax.Delta_equational)
end
| uu____150 -> begin
(r FStar_Syntax_Const.list_tot_append_lid FStar_Syntax_Syntax.Delta_equational)
end))
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
| uu____151 -> begin
None
end))
in (

let uu____152 = (let _0_377 = (compile_op_lid arity s rng)
in (FStar_ToSyntax_Env.try_lookup_lid env _0_377))
in (match (uu____152) with
| Some (t) -> begin
Some ((Prims.fst t))
end
| uu____162 -> begin
(fallback ())
end)))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _0_378 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _0_378)))


let rec free_type_vars_b : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_ToSyntax_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (uu____195) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____198 = (FStar_ToSyntax_Env.push_bv env x)
in (match (uu____198) with
| (env, uu____205) -> begin
((env), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (uu____207, term) -> begin
(let _0_379 = (free_type_vars env term)
in ((env), (_0_379)))
end
| FStar_Parser_AST.TAnnotated (id, uu____211) -> begin
(

let uu____212 = (FStar_ToSyntax_Env.push_bv env id)
in (match (uu____212) with
| (env, uu____219) -> begin
((env), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _0_380 = (free_type_vars env t)
in ((env), (_0_380)))
end))
and free_type_vars : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (

let uu____225 = (unparen t).FStar_Parser_AST.tm
in (match (uu____225) with
| FStar_Parser_AST.Labeled (uu____227) -> begin
(failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____233 = (FStar_ToSyntax_Env.try_lookup_id env a)
in (match (uu____233) with
| None -> begin
(a)::[]
end
| uu____240 -> begin
[]
end))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Projector (_)) | (FStar_Parser_AST.Discrim (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Assign (_, t)) | (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (uu____258, ts) -> begin
(FStar_List.collect (fun uu____268 -> (match (uu____268) with
| (t, uu____273) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (uu____274, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, uu____280) -> begin
(let _0_382 = (free_type_vars env t1)
in (let _0_381 = (free_type_vars env t2)
in (FStar_List.append _0_382 _0_381)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(

let uu____283 = (free_type_vars_b env b)
in (match (uu____283) with
| (env, f) -> begin
(let _0_383 = (free_type_vars env t)
in (FStar_List.append f _0_383))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(

let uu____298 = (FStar_List.fold_left (fun uu____305 binder -> (match (uu____305) with
| (env, free) -> begin
(

let uu____317 = (free_type_vars_b env binder)
in (match (uu____317) with
| (env, f) -> begin
((env), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (uu____298) with
| (env, free) -> begin
(let _0_384 = (free_type_vars env body)
in (FStar_List.append free _0_384))
end))
end
| FStar_Parser_AST.Project (t, uu____336) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.collect (free_type_vars env) cattributes)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end)))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t -> (

let uu____375 = (unparen t).FStar_Parser_AST.tm
in (match (uu____375) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| uu____399 -> begin
((t), (args))
end)))
in (aux [] t)))


let close : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _0_385 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _0_385))
in (match (((FStar_List.length ftv) = (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____417 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _0_387 = FStar_Parser_AST.TAnnotated ((let _0_386 = (tm_type x.FStar_Ident.idRange)
in ((x), (_0_386))))
in (FStar_Parser_AST.mk_binder _0_387 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end)))


let close_fun : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _0_388 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _0_388))
in (match (((FStar_List.length ftv) = (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____437 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _0_390 = FStar_Parser_AST.TAnnotated ((let _0_389 = (tm_type x.FStar_Ident.idRange)
in ((x), (_0_389))))
in (FStar_Parser_AST.mk_binder _0_390 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (Some (FStar_Parser_AST.Implicit)))))))
in (

let t = (

let uu____444 = (unparen t).FStar_Parser_AST.tm
in (match (uu____444) with
| FStar_Parser_AST.Product (uu____445) -> begin
t
end
| uu____449 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end)))


let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| uu____470 -> begin
((bs), (t))
end))


let rec is_var_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatTvar (_, _)) | (FStar_Parser_AST.PatVar (_, _)) -> begin
true
end
| FStar_Parser_AST.PatAscribed (p, uu____482) -> begin
(is_var_pattern p)
end
| uu____483 -> begin
false
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, uu____488) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____489); FStar_Parser_AST.prange = uu____490}, uu____491) -> begin
true
end
| uu____497 -> begin
false
end))


let replace_unit_pattern : FStar_Parser_AST.pattern  ->  FStar_Parser_AST.pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatConst (FStar_Const.Const_unit) -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatAscribed ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)), (unit_ty)))) p.FStar_Parser_AST.prange)
end
| uu____501 -> begin
p
end))


let rec destruct_app_pattern : FStar_ToSyntax_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let uu____527 = (destruct_app_pattern env is_top_level p)
in (match (uu____527) with
| (name, args, uu____544) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____558); FStar_Parser_AST.prange = uu____559}, args) when is_top_level -> begin
(let _0_391 = FStar_Util.Inr ((FStar_ToSyntax_Env.qualify env id))
in ((_0_391), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____570); FStar_Parser_AST.prange = uu____571}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| uu____581 -> begin
(failwith "Not an app pattern")
end))


let rec gather_pattern_bound_vars_maybe_top : FStar_Ident.ident FStar_Util.set  ->  FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (fun acc p -> (

let gather_pattern_bound_vars_from_list = (FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc)
in (match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatConst (_)) | (FStar_Parser_AST.PatVar (_, Some (FStar_Parser_AST.Implicit))) | (FStar_Parser_AST.PatName (_)) | (FStar_Parser_AST.PatTvar (_)) | (FStar_Parser_AST.PatOp (_)) -> begin
acc
end
| FStar_Parser_AST.PatApp (phead, pats) -> begin
(gather_pattern_bound_vars_from_list ((phead)::pats))
end
| FStar_Parser_AST.PatVar (x, uu____616) -> begin
(FStar_Util.set_add x acc)
end
| (FStar_Parser_AST.PatList (pats)) | (FStar_Parser_AST.PatTuple (pats, _)) | (FStar_Parser_AST.PatOr (pats)) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatRecord (guarded_pats) -> begin
(gather_pattern_bound_vars_from_list (FStar_List.map Prims.snd guarded_pats))
end
| FStar_Parser_AST.PatAscribed (pat, uu____632) -> begin
(gather_pattern_bound_vars_maybe_top acc pat)
end)))


let gather_pattern_bound_vars : FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (

let acc = (FStar_Util.new_set (fun id1 id2 -> (match ((id1.FStar_Ident.idText = id2.FStar_Ident.idText)) with
| true -> begin
(Prims.parse_int "0")
end
| uu____640 -> begin
(Prims.parse_int "1")
end)) (fun uu____641 -> (Prims.parse_int "0")))
in (fun p -> (gather_pattern_bound_vars_maybe_top acc p)))

type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term)


let uu___is_LocalBinder : bnd  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LocalBinder (_0) -> begin
true
end
| uu____659 -> begin
false
end))


let __proj__LocalBinder__item___0 : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun projectee -> (match (projectee) with
| LocalBinder (_0) -> begin
_0
end))


let uu___is_LetBinder : bnd  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LetBinder (_0) -> begin
true
end
| uu____679 -> begin
false
end))


let __proj__LetBinder__item___0 : bnd  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| LetBinder (_0) -> begin
_0
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun uu___188_697 -> (match (uu___188_697) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| uu____702 -> begin
(failwith "Impossible")
end))


let as_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_ToSyntax_Env.env) = (fun env imp uu___189_719 -> (match (uu___189_719) with
| (None, k) -> begin
(let _0_392 = (FStar_Syntax_Syntax.null_binder k)
in ((_0_392), (env)))
end
| (Some (a), k) -> begin
(

let uu____731 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____731) with
| (env, a) -> begin
(((((

let uu___210_742 = a
in {FStar_Syntax_Syntax.ppname = uu___210_742.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___210_742.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env))
end))
end))


type env_t =
FStar_ToSyntax_Env.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : ((FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.letbinding = (fun uu____755 -> (match (uu____755) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))


let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))


let mk_ref_read = (fun tm -> (

let tm' = FStar_Syntax_Syntax.Tm_app ((let _0_396 = (FStar_Syntax_Syntax.fv_to_tm (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid FStar_Syntax_Syntax.Delta_constant None))
in (let _0_395 = (let _0_394 = (let _0_393 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_0_393)))
in (_0_394)::[])
in ((_0_396), (_0_395)))))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc = (fun tm -> (

let tm' = FStar_Syntax_Syntax.Tm_app ((let _0_400 = (FStar_Syntax_Syntax.fv_to_tm (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant None))
in (let _0_399 = (let _0_398 = (let _0_397 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_0_397)))
in (_0_398)::[])
in ((_0_400), (_0_399)))))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign = (fun t1 t2 pos -> (

let tm = FStar_Syntax_Syntax.Tm_app ((let _0_407 = (FStar_Syntax_Syntax.fv_to_tm (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant None))
in (let _0_406 = (let _0_405 = (let _0_401 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (_0_401)))
in (let _0_404 = (let _0_403 = (let _0_402 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (_0_402)))
in (_0_403)::[])
in (_0_405)::_0_404))
in ((_0_407), (_0_406)))))
in (FStar_Syntax_Syntax.mk tm None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun uu___190_918 -> (match (uu___190_918) with
| ("repr") | ("post") | ("pre") | ("wp") -> begin
true
end
| uu____919 -> begin
false
end))


let rec sum_to_universe : FStar_Syntax_Syntax.universe  ->  Prims.int  ->  FStar_Syntax_Syntax.universe = (fun u n -> (match ((n = (Prims.parse_int "0"))) with
| true -> begin
u
end
| uu____926 -> begin
FStar_Syntax_Syntax.U_succ ((sum_to_universe u (n - (Prims.parse_int "1"))))
end))


let int_to_universe : Prims.int  ->  FStar_Syntax_Syntax.universe = (fun n -> (sum_to_universe FStar_Syntax_Syntax.U_zero n))


let rec desugar_maybe_non_constant_universe : FStar_Parser_AST.term  ->  (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun t -> (

let uu____937 = (unparen t).FStar_Parser_AST.tm
in (match (uu____937) with
| FStar_Parser_AST.Wild -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_unif ((FStar_Unionfind.fresh None)))
end
| FStar_Parser_AST.Uvar (u) -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_name (u))
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____943)) -> begin
(

let n = (FStar_Util.int_of_string repr)
in ((match ((n < (Prims.parse_int "0"))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Negative universe constant  are not supported : " repr)), (t.FStar_Parser_AST.range)))))
end
| uu____952 -> begin
()
end);
FStar_Util.Inl (n);
))
end
| FStar_Parser_AST.Op (op_plus, (t1)::(t2)::[]) -> begin
(

let u1 = (desugar_maybe_non_constant_universe t1)
in (

let u2 = (desugar_maybe_non_constant_universe t2)
in (match (((u1), (u2))) with
| (FStar_Util.Inl (n1), FStar_Util.Inl (n2)) -> begin
FStar_Util.Inl ((n1 + n2))
end
| ((FStar_Util.Inl (n), FStar_Util.Inr (u))) | ((FStar_Util.Inr (u), FStar_Util.Inl (n))) -> begin
FStar_Util.Inr ((sum_to_universe u n))
end
| (FStar_Util.Inr (u1), FStar_Util.Inr (u2)) -> begin
(Prims.raise (FStar_Errors.Error ((let _0_409 = (let _0_408 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "This universe might contain a sum of two universe variables " _0_408))
in ((_0_409), (t.FStar_Parser_AST.range))))))
end)))
end
| FStar_Parser_AST.App (uu____994) -> begin
(

let rec aux = (fun t univargs -> (

let uu____1013 = (unparen t).FStar_Parser_AST.tm
in (match (uu____1013) with
| FStar_Parser_AST.App (t, targ, uu____1018) -> begin
(

let uarg = (desugar_maybe_non_constant_universe targ)
in (aux t ((uarg)::univargs)))
end
| FStar_Parser_AST.Var (max_lid) -> begin
(match ((FStar_List.existsb (fun uu___191_1030 -> (match (uu___191_1030) with
| FStar_Util.Inr (uu____1033) -> begin
true
end
| uu____1034 -> begin
false
end)) univargs)) with
| true -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_max ((FStar_List.map (fun uu___192_1039 -> (match (uu___192_1039) with
| FStar_Util.Inl (n) -> begin
(int_to_universe n)
end
| FStar_Util.Inr (u) -> begin
u
end)) univargs)))
end
| uu____1044 -> begin
(

let nargs = (FStar_List.map (fun uu___193_1049 -> (match (uu___193_1049) with
| FStar_Util.Inl (n) -> begin
n
end
| FStar_Util.Inr (uu____1053) -> begin
(failwith "impossible")
end)) univargs)
in FStar_Util.Inl ((FStar_List.fold_left (fun m n -> (match ((m > n)) with
| true -> begin
m
end
| uu____1056 -> begin
n
end)) (Prims.parse_int "0") nargs)))
end)
end
| uu____1057 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_412 = (let _0_411 = (let _0_410 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat _0_410 " in universe context"))
in (Prims.strcat "Unexpected term " _0_411))
in ((_0_412), (t.FStar_Parser_AST.range))))))
end)))
in (aux t []))
end
| uu____1062 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_415 = (let _0_414 = (let _0_413 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat _0_413 " in universe context"))
in (Prims.strcat "Unexpected term " _0_414))
in ((_0_415), (t.FStar_Parser_AST.range))))))
end)))


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

let uu____1096 = (FStar_List.hd fields)
in (match (uu____1096) with
| (f, uu____1102) -> begin
(

let record = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f)
in (

let check_field = (fun uu____1109 -> (match (uu____1109) with
| (f', uu____1113) -> begin
(

let uu____1114 = (FStar_ToSyntax_Env.belongs_to_record env f' record)
in (match (uu____1114) with
| true -> begin
()
end
| uu____1115 -> begin
(

let msg = (FStar_Util.format3 "Field %s belongs to record type %s, whereas field %s does not" f.FStar_Ident.str record.FStar_ToSyntax_Env.typename.FStar_Ident.str f'.FStar_Ident.str)
in (Prims.raise (FStar_Errors.Error (((msg), (rg))))))
end))
end))
in ((let _0_416 = (FStar_List.tl fields)
in (FStar_List.iter check_field _0_416));
(match (()) with
| () -> begin
record
end);
)))
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
| FStar_Syntax_Syntax.Pat_cons (uu____1274, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out uu____1296 -> (match (uu____1296) with
| (p, uu____1302) -> begin
(let _0_417 = (pat_vars p)
in (FStar_Util.set_union out _0_417))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let xs = (pat_vars hd)
in (

let uu____1315 = (not ((FStar_Util.for_all (fun p -> (

let ys = (pat_vars p)
in ((FStar_Util.set_is_subset_of xs ys) && (FStar_Util.set_is_subset_of ys xs)))) tl)))
in (match (uu____1315) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Disjunctive pattern binds different variables in each case"), (p.FStar_Syntax_Syntax.p)))))
end
| uu____1318 -> begin
xs
end)))
end))
in (pat_vars p)))
in ((match (((is_mut), (p.FStar_Parser_AST.pat))) with
| ((false, _)) | ((true, FStar_Parser_AST.PatVar (_))) -> begin
()
end
| (true, uu____1322) -> begin
(Prims.raise (FStar_Errors.Error ((("let-mutable is for variables only"), (p.FStar_Parser_AST.prange)))))
end);
(

let push_bv_maybe_mut = (match (is_mut) with
| true -> begin
FStar_ToSyntax_Env.push_bv_mutable
end
| uu____1336 -> begin
FStar_ToSyntax_Env.push_bv
end)
in (

let resolvex = (fun l e x -> (

let uu____1350 = (FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))
in (match (uu____1350) with
| Some (y) -> begin
((l), (e), (y))
end
| uu____1358 -> begin
(

let uu____1360 = (push_bv_maybe_mut e x)
in (match (uu____1360) with
| (e, x) -> begin
(((x)::l), (e), (x))
end))
end)))
in (

let rec aux = (fun loc env p -> (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Parser_AST.prange))
in (

let pos_r = (fun r q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (op) -> begin
(let _0_420 = (let _0_419 = FStar_Parser_AST.PatVar ((let _0_418 = (FStar_Ident.id_of_text (FStar_Parser_AST.compile_op (Prims.parse_int "0") op))
in ((_0_418), (None))))
in {FStar_Parser_AST.pat = _0_419; FStar_Parser_AST.prange = p.FStar_Parser_AST.prange})
in (aux loc env _0_420))
end
| FStar_Parser_AST.PatOr ([]) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(

let uu____1420 = (aux loc env p)
in (match (uu____1420) with
| (loc, env, var, p, uu____1439) -> begin
(

let uu____1444 = (FStar_List.fold_left (fun uu____1457 p -> (match (uu____1457) with
| (loc, env, ps) -> begin
(

let uu____1480 = (aux loc env p)
in (match (uu____1480) with
| (loc, env, uu____1496, p, uu____1498) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (uu____1444) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in ((loc), (env), (var), (pat), (false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let uu____1542 = (aux loc env p)
in (match (uu____1542) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (uu____1567) -> begin
(failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t = (let _0_421 = (close_fun env t)
in (desugar_term env _0_421))
in ((match ((match (x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| uu____1574 -> begin
true
end)) with
| true -> begin
(let _0_424 = (FStar_Syntax_Print.bv_to_string x)
in (let _0_423 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _0_422 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3_warning "Multiple ascriptions for %s in pattern, type %s was shadowed by %s" _0_424 _0_423 _0_422))))
end
| uu____1575 -> begin
()
end);
LocalBinder ((((

let uu___211_1576 = x
in {FStar_Syntax_Syntax.ppname = uu___211_1576.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___211_1576.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (aq)));
))
end)
in ((loc), (env'), (binder), (p), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _0_425 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_0_425), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _0_426 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_0_426), (false))))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let uu____1602 = (resolvex loc env x)
in (match (uu____1602) with
| (loc, env, xbv) -> begin
(let _0_427 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc), (env), (LocalBinder (((xbv), (aq)))), (_0_427), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _0_428 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), ([])))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_0_428), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = uu____1639}, args) -> begin
(

let uu____1643 = (FStar_List.fold_right (fun arg uu____1661 -> (match (uu____1661) with
| (loc, env, args) -> begin
(

let uu____1691 = (aux loc env arg)
in (match (uu____1691) with
| (loc, env, uu____1709, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (uu____1643) with
| (loc, env, args) -> begin
(

let l = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _0_429 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_0_429), (false)))))
end))
end
| FStar_Parser_AST.PatApp (uu____1768) -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____1781 = (FStar_List.fold_right (fun pat uu____1795 -> (match (uu____1795) with
| (loc, env, pats) -> begin
(

let uu____1817 = (aux loc env pat)
in (match (uu____1817) with
| (loc, env, uu____1833, pat, uu____1835) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (uu____1781) with
| (loc, env, pats) -> begin
(

let pat = (let _0_435 = (let _0_434 = (pos_r (FStar_Range.end_range p.FStar_Parser_AST.prange))
in (let _0_433 = FStar_Syntax_Syntax.Pat_cons ((let _0_432 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_0_432), ([]))))
in (FStar_All.pipe_left _0_434 _0_433)))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _0_431 = FStar_Syntax_Syntax.Pat_cons ((let _0_430 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_0_430), ((((hd), (false)))::(((tl), (false)))::[]))))
in (FStar_All.pipe_left (pos_r r) _0_431)))) pats _0_435))
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc), (env), (LocalBinder (((x), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let uu____1922 = (FStar_List.fold_left (fun uu____1939 p -> (match (uu____1939) with
| (loc, env, pats) -> begin
(

let uu____1970 = (aux loc env p)
in (match (uu____1970) with
| (loc, env, uu____1988, pat, uu____1990) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (uu____1922) with
| (loc, env, args) -> begin
(

let args = (FStar_List.rev args)
in (

let l = (match (dep) with
| true -> begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
| uu____2053 -> begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end)
in (

let uu____2061 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) l)
in (match (uu____2061) with
| (constr, uu____2074) -> begin
(

let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____2077 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _0_436 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_0_436), (false)))))
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

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun uu____2117 -> (match (uu____2117) with
| (f, p) -> begin
((f.FStar_Ident.ident), (p))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____2132 -> (match (uu____2132) with
| (f, uu____2136) -> begin
(

let uu____2137 = (FStar_All.pipe_right fields (FStar_List.tryFind (fun uu____2149 -> (match (uu____2149) with
| (g, uu____2153) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.idText)
end))))
in (match (uu____2137) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (uu____2156, p) -> begin
p
end))
end))))
in (

let app = (let _0_439 = FStar_Parser_AST.PatApp ((let _0_438 = (let _0_437 = FStar_Parser_AST.PatName ((FStar_Ident.lid_of_ids (FStar_List.append record.FStar_ToSyntax_Env.typename.FStar_Ident.ns ((record.FStar_ToSyntax_Env.constrname)::[]))))
in (FStar_Parser_AST.mk_pattern _0_437 p.FStar_Parser_AST.prange))
in ((_0_438), (args))))
in (FStar_Parser_AST.mk_pattern _0_439 p.FStar_Parser_AST.prange))
in (

let uu____2162 = (aux loc env app)
in (match (uu____2162) with
| (env, e, b, p, uu____2181) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _0_443 = FStar_Syntax_Syntax.Pat_cons ((let _0_442 = (

let uu___212_2210 = fv
in (let _0_441 = Some (FStar_Syntax_Syntax.Record_ctor ((let _0_440 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_ToSyntax_Env.typename), (_0_440)))))
in {FStar_Syntax_Syntax.fv_name = uu___212_2210.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = uu___212_2210.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _0_441}))
in ((_0_442), (args))))
in (FStar_All.pipe_left pos _0_443))
end
| uu____2221 -> begin
p
end)
in ((env), (e), (b), (p), (false)))
end))))))
end))))
in (

let uu____2224 = (aux [] env p)
in (match (uu____2224) with
| (uu____2235, env, b, p, uu____2239) -> begin
((let _0_444 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _0_444));
((env), (b), (p));
)
end)))));
)))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p is_mut -> (

let mklet = (fun x -> (let _0_446 = LetBinder ((let _0_445 = (FStar_ToSyntax_Env.qualify env x)
in ((_0_445), (FStar_Syntax_Syntax.tun))))
in ((env), (_0_446), (None))))
in (match (top) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(mklet (FStar_Ident.id_of_text (FStar_Parser_AST.compile_op (Prims.parse_int "0") x)))
end
| FStar_Parser_AST.PatVar (x, uu____2274) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2278); FStar_Parser_AST.prange = uu____2279}, t) -> begin
(let _0_449 = LetBinder ((let _0_448 = (FStar_ToSyntax_Env.qualify env x)
in (let _0_447 = (desugar_term env t)
in ((_0_448), (_0_447)))))
in ((env), (_0_449), (None)))
end
| uu____2284 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end
| uu____2289 -> begin
(

let uu____2290 = (desugar_data_pat env p is_mut)
in (match (uu____2290) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| uu____2306 -> begin
Some (p)
end)
in ((env), (binder), (p)))
end))
end)))
and desugar_binding_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun uu____2310 env pat -> (

let uu____2313 = (desugar_data_pat env pat false)
in (match (uu____2313) with
| (env, uu____2320, pat) -> begin
((env), (pat))
end)))
and desugar_match_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let uu___213_2327 = env
in {FStar_ToSyntax_Env.curmodule = uu___213_2327.FStar_ToSyntax_Env.curmodule; FStar_ToSyntax_Env.curmonad = uu___213_2327.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = uu___213_2327.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = uu___213_2327.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = uu___213_2327.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = uu___213_2327.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = uu___213_2327.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = uu___213_2327.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = uu___213_2327.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.default_result_effect = uu___213_2327.FStar_ToSyntax_Env.default_result_effect; FStar_ToSyntax_Env.iface = uu___213_2327.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = uu___213_2327.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let uu___214_2331 = env
in {FStar_ToSyntax_Env.curmodule = uu___214_2331.FStar_ToSyntax_Env.curmodule; FStar_ToSyntax_Env.curmonad = uu___214_2331.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = uu___214_2331.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = uu___214_2331.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = uu___214_2331.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = uu___214_2331.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = uu___214_2331.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = uu___214_2331.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = uu___214_2331.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.default_result_effect = uu___214_2331.FStar_ToSyntax_Env.default_result_effect; FStar_ToSyntax_Env.iface = uu___214_2331.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = uu___214_2331.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_machine_integer : FStar_ToSyntax_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env repr uu____2334 range -> (match (uu____2334) with
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

let lid = (

let uu____2345 = (FStar_ToSyntax_Env.try_lookup_lid env lid)
in (match (uu____2345) with
| Some (lid) -> begin
(Prims.fst lid)
end
| None -> begin
(failwith (FStar_Util.format1 "%s not in scope\n" (FStar_Ident.text_of_lid lid)))
end))
in (

let repr = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (None)))))) None range)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_452 = (let _0_451 = (let _0_450 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr), (_0_450)))
in (_0_451)::[])
in ((lid), (_0_452)))))) None range)))))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env_t  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk setpos env l -> (

let uu____2405 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) l)
in (match (uu____2405) with
| (tm, mut) -> begin
(

let tm = (setpos tm)
in (match (mut) with
| true -> begin
(let _0_454 = FStar_Syntax_Syntax.Tm_meta ((let _0_453 = (mk_ref_read tm)
in ((_0_453), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval)))))
in (FStar_All.pipe_left mk _0_454))
end
| uu____2417 -> begin
tm
end))
end)))
and desugar_attributes : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (

let uu____2426 = (unparen t).FStar_Parser_AST.tm
in (match (uu____2426) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = uu____2427; FStar_Ident.ident = uu____2428; FStar_Ident.nsstr = uu____2429; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| uu____2431 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_456 = (let _0_455 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " _0_455))
in ((_0_456), (t.FStar_Parser_AST.range))))))
end)))
in (FStar_List.map desugar_attribute cattributes)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk = (fun e -> ((FStar_Syntax_Syntax.mk e) None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let uu___215_2459 = e
in {FStar_Syntax_Syntax.n = uu___215_2459.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___215_2459.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___215_2459.FStar_Syntax_Syntax.vars}))
in (

let uu____2466 = (unparen top).FStar_Parser_AST.tm
in (match (uu____2466) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (uu____2467) -> begin
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
| FStar_Parser_AST.Op ("*", (uu____2496)::(uu____2497)::[]) when (let _0_457 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _0_457 FStar_Option.isNone)) -> begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(let _0_458 = (flatten t1)
in (FStar_List.append _0_458 ((t2)::[])))
end
| uu____2509 -> begin
(t)::[]
end))
in (

let targs = (let _0_459 = (flatten (unparen top))
in (FStar_All.pipe_right _0_459 (FStar_List.map (fun t -> (FStar_Syntax_Syntax.as_arg (desugar_typ env t))))))
in (

let uu____2515 = (let _0_460 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) _0_460))
in (match (uu____2515) with
| (tup, uu____2524) -> begin
(mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _0_461 = (Prims.fst (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) a))
in (FStar_All.pipe_left setpos _0_461))
end
| FStar_Parser_AST.Uvar (u) -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected universe variable " (Prims.strcat (FStar_Ident.text_of_id u) " in non-universe context"))), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(

let uu____2538 = (op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)
in (match (uu____2538) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected or unbound operator: " s)), (top.FStar_Parser_AST.range)))))
end
| Some (op) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _0_462 = (desugar_term env t)
in ((_0_462), (None))))))
in (mk (FStar_Syntax_Syntax.Tm_app (((op), (args))))))
end
| uu____2565 -> begin
op
end)
end))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2566; FStar_Ident.ident = uu____2567; FStar_Ident.nsstr = uu____2568; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2570; FStar_Ident.ident = uu____2571; FStar_Ident.nsstr = uu____2572; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = uu____2574; FStar_Ident.ident = uu____2575; FStar_Ident.nsstr = uu____2576; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(mk (FStar_Syntax_Syntax.Tm_type ((desugar_universe t))))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2586; FStar_Ident.ident = uu____2587; FStar_Ident.nsstr = uu____2588; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2590; FStar_Ident.ident = uu____2591; FStar_Ident.nsstr = uu____2592; FStar_Ident.str = "True"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2594; FStar_Ident.ident = uu____2595; FStar_Ident.nsstr = uu____2596; FStar_Ident.str = "False"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = uu____2600}) when ((is_special_effect_combinator txt) && (FStar_ToSyntax_Env.is_effect_name env eff_name)) -> begin
(

let uu____2601 = (FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name)
in (match (uu____2601) with
| Some (ed) -> begin
(let _0_463 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" txt))) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.fvar _0_463 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
end
| None -> begin
(failwith "immpossible special_effect_combinator")
end))
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t2 = (desugar_term env t2)
in (

let uu____2607 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) ident)
in (match (uu____2607) with
| (t1, mut) -> begin
((match ((not (mut))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
end
| uu____2615 -> begin
()
end);
(mk_ref_assign t1 t2 top.FStar_Parser_AST.range);
)
end)))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(desugar_name mk setpos env l)
end
| FStar_Parser_AST.Projector (l, i) -> begin
(

let found = ((FStar_Option.isSome (FStar_ToSyntax_Env.try_lookup_datacon env l)) || (FStar_Option.isSome (FStar_ToSyntax_Env.try_lookup_effect_defn env l)))
in (match (found) with
| true -> begin
(let _0_464 = (FStar_Syntax_Util.mk_field_projector_name_from_ident l i)
in (desugar_name mk setpos env _0_464))
end
| uu____2620 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_465 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((_0_465), (top.FStar_Parser_AST.range))))))
end))
end
| FStar_Parser_AST.Discrim (lid) -> begin
(

let uu____2622 = (FStar_ToSyntax_Env.try_lookup_datacon env lid)
in (match (uu____2622) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_466 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((_0_466), (top.FStar_Parser_AST.range))))))
end
| uu____2624 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (desugar_name mk setpos env lid'))
end))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(

let uu____2635 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____2635) with
| Some (head) -> begin
(

let uu____2638 = (let _0_467 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in ((_0_467), (true)))
in (match (uu____2638) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| uu____2653 -> begin
(

let uu____2657 = (FStar_Util.take (fun uu____2668 -> (match (uu____2668) with
| (uu____2671, imp) -> begin
(imp = FStar_Parser_AST.UnivApp)
end)) args)
in (match (uu____2657) with
| (universes, args) -> begin
(

let universes = (FStar_List.map (fun x -> (desugar_universe (Prims.fst x))) universes)
in (

let args = (FStar_List.map (fun uu____2704 -> (match (uu____2704) with
| (t, imp) -> begin
(

let te = (desugar_term env t)
in (arg_withimp_e imp te))
end)) args)
in (

let head = (match ((universes = [])) with
| true -> begin
head
end
| uu____2719 -> begin
(mk (FStar_Syntax_Syntax.Tm_uinst (((head), (universes)))))
end)
in (

let app = (mk (FStar_Syntax_Syntax.Tm_app (((head), (args)))))
in (match (is_data) with
| true -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((app), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| uu____2734 -> begin
app
end)))))
end))
end)
end))
end
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Constructor " (Prims.strcat l.FStar_Ident.str " not found"))), (top.FStar_Parser_AST.range)))))
end))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let uu____2739 = (FStar_List.fold_left (fun uu____2756 b -> (match (uu____2756) with
| (env, tparams, typs) -> begin
(

let uu____2787 = (desugar_binder env b)
in (match (uu____2787) with
| (xopt, t) -> begin
(

let uu____2803 = (match (xopt) with
| None -> begin
(let _0_468 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env), (_0_468)))
end
| Some (x) -> begin
(FStar_ToSyntax_Env.push_bv env x)
end)
in (match (uu____2803) with
| (env, x) -> begin
(let _0_472 = (let _0_471 = (let _0_470 = (let _0_469 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_469))
in (_0_470)::[])
in (FStar_List.append typs _0_471))
in ((env), ((FStar_List.append tparams (((((

let uu___216_2831 = x
in {FStar_Syntax_Syntax.ppname = uu___216_2831.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___216_2831.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (None)))::[]))), (_0_472)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level None))::[])))
in (match (uu____2739) with
| (env, uu____2844, targs) -> begin
(

let uu____2856 = (let _0_473 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) _0_473))
in (match (uu____2856) with
| (tup, uu____2865) -> begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let uu____2873 = (uncurry binders t)
in (match (uu____2873) with
| (bs, t) -> begin
(

let rec aux = (fun env bs uu___194_2896 -> (match (uu___194_2896) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _0_474 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _0_474)))
end
| (hd)::tl -> begin
(

let mlenv = (FStar_ToSyntax_Env.default_ml env)
in (

let bb = (desugar_binder mlenv hd)
in (

let uu____2920 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (uu____2920) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(

let uu____2931 = (desugar_binder env b)
in (match (uu____2931) with
| (None, uu____2935) -> begin
(failwith "Missing binder in refinement")
end
| b -> begin
(

let uu____2941 = (as_binder env None b)
in (match (uu____2941) with
| ((x, uu____2945), env) -> begin
(

let f = (desugar_formula env f)
in (let _0_475 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _0_475)))
end))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let uu____2962 = (FStar_List.fold_left (fun uu____2969 pat -> (match (uu____2969) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (uu____2984, t) -> begin
(let _0_477 = (let _0_476 = (free_type_vars env t)
in (FStar_List.append _0_476 ftvs))
in ((env), (_0_477)))
end
| uu____2987 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (uu____2962) with
| (uu____2990, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (let _0_478 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append _0_478 binders))
in (

let rec aux = (fun env bs sc_pat_opt uu___195_3025 -> (match (uu___195_3025) with
| [] -> begin
(

let body = (desugar_term env body)
in (

let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(

let body = (let _0_480 = (let _0_479 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _0_479 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _0_480 body))
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (None), (body)))::[]))))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (setpos (no_annot_abs (FStar_List.rev bs) body))))
end
| (p)::rest -> begin
(

let uu____3099 = (desugar_binding_pat env p)
in (match (uu____3099) with
| (env, b, pat) -> begin
(

let uu____3111 = (match (b) with
| LetBinder (uu____3130) -> begin
(failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, uu____3161) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
Some ((let _0_481 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_0_481), (p))))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (uu____3208), uu____3209) -> begin
(

let tup2 = (let _0_482 = (FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _0_482 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_488 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _0_487 = (let _0_486 = (FStar_Syntax_Syntax.as_arg sc)
in (let _0_485 = (let _0_484 = (let _0_483 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_483))
in (_0_484)::[])
in (_0_486)::_0_485))
in ((_0_488), (_0_487))))))) None top.FStar_Parser_AST.range)
in (

let p = (let _0_489 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p), (false)))::[])))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _0_489))
in Some (((sc), (p))))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____3247, args), FStar_Syntax_Syntax.Pat_cons (uu____3249, pats)) -> begin
(

let tupn = (let _0_490 = (FStar_Syntax_Util.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _0_490 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_495 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _0_494 = (let _0_493 = (let _0_492 = (let _0_491 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_491))
in (_0_492)::[])
in (FStar_List.append args _0_493))
in ((_0_495), (_0_494)))))))
in (

let p = (let _0_496 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p), (false)))::[])))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _0_496))
in Some (((sc), (p))))))
end
| uu____3322 -> begin
(failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt)))
end)
in (match (uu____3111) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end)))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = rng; FStar_Parser_AST.level = uu____3365}, phi, uu____3367) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env phi)
in (

let a = (FStar_Ident.set_lid_range a rng)
in (mk (FStar_Syntax_Syntax.Tm_app ((let _0_502 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _0_501 = (let _0_500 = (FStar_Syntax_Syntax.as_arg phi)
in (let _0_499 = (let _0_498 = (let _0_497 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_497))
in (_0_498)::[])
in (_0_500)::_0_499))
in ((_0_502), (_0_501)))))))))
end
| FStar_Parser_AST.App (uu____3371, uu____3372, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (

let uu____3384 = (unparen e).FStar_Parser_AST.tm
in (match (uu____3384) with
| FStar_Parser_AST.App (e, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e))
end
| uu____3390 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_uinst (((head), (universes))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.App (uu____3393) -> begin
(

let rec aux = (fun args e -> (

let uu____3414 = (unparen e).FStar_Parser_AST.tm
in (match (uu____3414) with
| FStar_Parser_AST.App (e, t, imp) when (imp <> FStar_Parser_AST.UnivApp) -> begin
(

let arg = (let _0_503 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _0_503))
in (aux ((arg)::args) e))
end
| uu____3430 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((let _0_504 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((_0_504), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))))))
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

let ds_let_rec_or_app = (fun uu____3470 -> (

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun uu____3512 -> (match (uu____3512) with
| (p, def) -> begin
(

let uu____3526 = (is_app_pattern p)
in (match (uu____3526) with
| true -> begin
(let _0_505 = (destruct_app_pattern env top_level p)
in ((_0_505), (def)))
end
| uu____3543 -> begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _0_506 = (destruct_app_pattern env top_level p)
in ((_0_506), (def)))
end
| uu____3564 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____3578); FStar_Parser_AST.prange = uu____3579}, t) -> begin
(match (top_level) with
| true -> begin
(let _0_508 = (let _0_507 = FStar_Util.Inr ((FStar_ToSyntax_Env.qualify env id))
in ((_0_507), ([]), (Some (t))))
in ((_0_508), (def)))
end
| uu____3603 -> begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end)
end
| FStar_Parser_AST.PatVar (id, uu____3616) -> begin
(match (top_level) with
| true -> begin
(let _0_510 = (let _0_509 = FStar_Util.Inr ((FStar_ToSyntax_Env.qualify env id))
in ((_0_509), ([]), (None)))
in ((_0_510), (def)))
end
| uu____3639 -> begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end)
end
| uu____3651 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end))
end))))
in (

let uu____3661 = (FStar_List.fold_left (fun uu____3685 uu____3686 -> (match (((uu____3685), (uu____3686))) with
| ((env, fnames, rec_bindings), ((f, uu____3730, uu____3731), uu____3732)) -> begin
(

let uu____3772 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let uu____3786 = (FStar_ToSyntax_Env.push_bv env x)
in (match (uu____3786) with
| (env, xx) -> begin
(let _0_512 = (let _0_511 = (FStar_Syntax_Syntax.mk_binder xx)
in (_0_511)::rec_bindings)
in ((env), (FStar_Util.Inl (xx)), (_0_512)))
end))
end
| FStar_Util.Inr (l) -> begin
(let _0_513 = (FStar_ToSyntax_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((_0_513), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (uu____3772) with
| (env, lbname, rec_bindings) -> begin
((env), ((lbname)::fnames), (rec_bindings))
end))
end)) ((env), ([]), ([])) funs)
in (match (uu____3661) with
| (env', fnames, rec_bindings) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let rec_bindings = (FStar_List.rev rec_bindings)
in (

let desugar_one_def = (fun env lbname uu____3873 -> (match (uu____3873) with
| ((uu____3885, args, result_t), def) -> begin
(

let args = (FStar_All.pipe_right args (FStar_List.map replace_unit_pattern))
in (

let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
((

let uu____3911 = (is_comp_type env t)
in (match (uu____3911) with
| true -> begin
(

let uu____3912 = (FStar_All.pipe_right args (FStar_List.tryFind (fun x -> (not ((is_var_pattern x))))))
in (match (uu____3912) with
| None -> begin
()
end
| Some (p) -> begin
(Prims.raise (FStar_Errors.Error ((("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable"), (p.FStar_Parser_AST.prange)))))
end))
end
| uu____3918 -> begin
()
end));
(let _0_514 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) _0_514 FStar_Parser_AST.Expr));
)
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| uu____3920 -> begin
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
FStar_Util.Inr ((let _0_515 = (FStar_Syntax_Util.incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _0_515 None)))
end)
in (

let body = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.close rec_bindings body)
end
| uu____3931 -> begin
body
end)
in (mk_lb ((lbname), (FStar_Syntax_Syntax.tun), (body)))))))))
end))
in (

let lbs = (FStar_List.map2 (desugar_one_def (match (is_rec) with
| true -> begin
env'
end
| uu____3947 -> begin
env
end)) fnames funs)
in (

let body = (desugar_term env' body)
in (let _0_517 = FStar_Syntax_Syntax.Tm_let ((let _0_516 = (FStar_Syntax_Subst.close rec_bindings body)
in ((((is_rec), (lbs))), (_0_516))))
in (FStar_All.pipe_left mk _0_517)))))))
end)))))
in (

let ds_non_rec = (fun pat t1 t2 -> (

let t1 = (desugar_term env t1)
in (

let is_mutable = (qual = FStar_Parser_AST.Mutable)
in (

let t1 = (match (is_mutable) with
| true -> begin
(mk_ref_alloc t1)
end
| uu____3974 -> begin
t1
end)
in (

let uu____3975 = (desugar_binding_pat_maybe_top top_level env pat is_mutable)
in (match (uu____3975) with
| (env, binder, pat) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body = (desugar_term env t2)
in (

let fv = (let _0_518 = (FStar_Syntax_Util.incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _0_518 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]))), (body)))))))
end
| LocalBinder (x, uu____4003) -> begin
(

let body = (desugar_term env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((let _0_521 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _0_520 = (let _0_519 = (FStar_Syntax_Util.branch ((pat), (None), (body)))
in (_0_519)::[])
in ((_0_521), (_0_520))))))) None body.FStar_Syntax_Syntax.pos)
end)
in (let _0_525 = FStar_Syntax_Syntax.Tm_let ((let _0_524 = (let _0_523 = (let _0_522 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_522)::[])
in (FStar_Syntax_Subst.close _0_523 body))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t1))))::[]))), (_0_524))))
in (FStar_All.pipe_left mk _0_525))))
end)
in (match (is_mutable) with
| true -> begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc))))))
end
| uu____4044 -> begin
tm
end))
end))))))
in (

let uu____4045 = (is_rec || (is_app_pattern pat))
in (match (uu____4045) with
| true -> begin
(ds_let_rec_or_app ())
end
| uu____4046 -> begin
(ds_non_rec pat _snd body)
end)))))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (mk (FStar_Syntax_Syntax.Tm_match ((let _0_534 = (desugar_term env t1)
in (let _0_533 = (let _0_532 = (let _0_527 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _0_526 = (desugar_term env t2)
in ((_0_527), (None), (_0_526))))
in (let _0_531 = (let _0_530 = (let _0_529 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _0_528 = (desugar_term env t3)
in ((_0_529), (None), (_0_528))))
in (_0_530)::[])
in (_0_532)::_0_531))
in ((_0_534), (_0_533))))))))
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

let desugar_branch = (fun uu____4143 -> (match (uu____4143) with
| (pat, wopt, b) -> begin
(

let uu____4153 = (desugar_match_pat env pat)
in (match (uu____4153) with
| (env, pat) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
Some ((desugar_term env e))
end)
in (

let b = (desugar_term env b)
in (FStar_Syntax_Util.branch ((pat), (wopt), (b)))))
end))
end))
in (let _0_537 = FStar_Syntax_Syntax.Tm_match ((let _0_536 = (desugar_term env e)
in (let _0_535 = (FStar_List.map desugar_branch branches)
in ((_0_536), (_0_535)))))
in (FStar_All.pipe_left mk _0_537)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(

let env = (FStar_ToSyntax_Env.default_ml env)
in (

let c = (desugar_comp t.FStar_Parser_AST.range true env t)
in (

let annot = (

let uu____4184 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____4184) with
| true -> begin
FStar_Util.Inl ((FStar_Syntax_Util.comp_result c))
end
| uu____4195 -> begin
FStar_Util.Inr (c)
end))
in (let _0_539 = FStar_Syntax_Syntax.Tm_ascribed ((let _0_538 = (desugar_term env e)
in ((_0_538), (annot), (None))))
in (FStar_All.pipe_left mk _0_539)))))
end
| FStar_Parser_AST.Record (uu____4209, []) -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let uu____4230 = (FStar_List.hd fields)
in (match (uu____4230) with
| (f, uu____4237) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun uu____4261 -> (match (uu____4261) with
| (g, uu____4265) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| Some (uu____4269, e) -> begin
((fn), (e))
end
| None -> begin
(match (xopt) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_540 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_ToSyntax_Env.typename.FStar_Ident.str)
in ((_0_540), (top.FStar_Parser_AST.range))))))
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
FStar_Parser_AST.Construct ((let _0_543 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____4295 -> (match (uu____4295) with
| (f, uu____4301) -> begin
(let _0_542 = (let _0_541 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _0_541))
in ((_0_542), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (_0_543))))
end
| Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (let _0_544 = FStar_Parser_AST.Var ((FStar_Ident.lid_of_ids ((x)::[])))
in (FStar_Parser_AST.mk_term _0_544 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = FStar_Parser_AST.Record ((let _0_545 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____4322 -> (match (uu____4322) with
| (f, uu____4328) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (_0_545))))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____4340; FStar_Syntax_Syntax.pos = uu____4341; FStar_Syntax_Syntax.vars = uu____4342}, args); FStar_Syntax_Syntax.tk = uu____4344; FStar_Syntax_Syntax.pos = uu____4345; FStar_Syntax_Syntax.vars = uu____4346}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e = (let _0_549 = FStar_Syntax_Syntax.Tm_app ((let _0_548 = (let _0_547 = Some (FStar_Syntax_Syntax.Record_ctor ((let _0_546 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_ToSyntax_Env.typename), (_0_546)))))
in (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant _0_547))
in ((_0_548), (args))))
in (FStar_All.pipe_left mk _0_549))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| uu____4390 -> begin
e
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let uu____4393 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f)
in (match (uu____4393) with
| (constrname, is_rec) -> begin
(

let e = (desugar_term env e)
in (

let projname = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname f.FStar_Ident.ident)
in (

let qual = (match (is_rec) with
| true -> begin
Some (FStar_Syntax_Syntax.Record_projector (((constrname), (f.FStar_Ident.ident))))
end
| uu____4405 -> begin
None
end)
in (let _0_553 = FStar_Syntax_Syntax.Tm_app ((let _0_552 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projname (FStar_Ident.range_of_lid f)) FStar_Syntax_Syntax.Delta_equational qual)
in (let _0_551 = (let _0_550 = (FStar_Syntax_Syntax.as_arg e)
in (_0_550)::[])
in ((_0_552), (_0_551)))))
in (FStar_All.pipe_left mk _0_553)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| uu____4411 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| uu____4412 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Let (uu____4413, uu____4414, uu____4415) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QForall (uu____4422, uu____4423, uu____4424) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QExists (uu____4431, uu____4432, uu____4433) -> begin
(failwith "Not implemented yet")
end)))))
and desugar_args : FStar_ToSyntax_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____4457 -> (match (uu____4457) with
| (a, imp) -> begin
(let _0_554 = (desugar_term env a)
in (arg_withimp_e imp _0_554))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Errors.Error (((msg), (r))))))
in (

let is_requires = (fun uu____4482 -> (match (uu____4482) with
| (t, uu____4486) -> begin
(

let uu____4487 = (unparen t).FStar_Parser_AST.tm
in (match (uu____4487) with
| FStar_Parser_AST.Requires (uu____4488) -> begin
true
end
| uu____4492 -> begin
false
end))
end))
in (

let is_ensures = (fun uu____4498 -> (match (uu____4498) with
| (t, uu____4502) -> begin
(

let uu____4503 = (unparen t).FStar_Parser_AST.tm
in (match (uu____4503) with
| FStar_Parser_AST.Ensures (uu____4504) -> begin
true
end
| uu____4508 -> begin
false
end))
end))
in (

let is_app = (fun head uu____4517 -> (match (uu____4517) with
| (t, uu____4521) -> begin
(

let uu____4522 = (unparen t).FStar_Parser_AST.tm
in (match (uu____4522) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = uu____4524; FStar_Parser_AST.level = uu____4525}, uu____4526, uu____4527) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| uu____4528 -> begin
false
end))
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t -> (

let uu____4546 = (head_and_args t)
in (match (uu____4546) with
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
(let _0_555 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes env) l)
in ((_0_555), (args)))
end
| FStar_Parser_AST.Name (l) when ((let _0_556 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals _0_556 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((let _0_557 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals _0_557 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)), ([]))), ((((t), (FStar_Parser_AST.Nothing)))::[]))
end
| uu____4748 when default_ok -> begin
(((((FStar_Ident.set_lid_range env.FStar_ToSyntax_Env.default_result_effect head.FStar_Parser_AST.range)), ([]))), ((((t), (FStar_Parser_AST.Nothing)))::[]))
end
| uu____4760 -> begin
(fail (let _0_558 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _0_558)))
end)
end)))
in (

let uu____4769 = (pre_process_comp_typ t)
in (match (uu____4769) with
| ((eff, cattributes), args) -> begin
((match (((FStar_List.length args) = (Prims.parse_int "0"))) with
| true -> begin
(fail (let _0_559 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _0_559)))
end
| uu____4799 -> begin
()
end);
(

let is_universe = (fun uu____4805 -> (match (uu____4805) with
| (uu____4808, imp) -> begin
(imp = FStar_Parser_AST.UnivApp)
end))
in (

let uu____4810 = (FStar_Util.take is_universe args)
in (match (uu____4810) with
| (universes, args) -> begin
(

let universes = (FStar_List.map (fun uu____4841 -> (match (uu____4841) with
| (u, imp) -> begin
(desugar_universe u)
end)) universes)
in (

let uu____4846 = (let _0_561 = (FStar_List.hd args)
in (let _0_560 = (FStar_List.tl args)
in ((_0_561), (_0_560))))
in (match (uu____4846) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (Prims.fst result_arg))
in (

let rest = (desugar_args env rest)
in (

let uu____4883 = (FStar_All.pipe_right rest (FStar_List.partition (fun uu____4921 -> (match (uu____4921) with
| (t, uu____4928) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____4936; FStar_Syntax_Syntax.pos = uu____4937; FStar_Syntax_Syntax.vars = uu____4938}, (uu____4939)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| uu____4961 -> begin
false
end)
end))))
in (match (uu____4883) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun uu____5004 -> (match (uu____5004) with
| (t, uu____5011) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____5018, ((arg, uu____5020))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| uu____5042 -> begin
(failwith "impos")
end)
end))))
in (

let no_additional_args = (

let is_empty = (fun l -> (match (l) with
| [] -> begin
true
end
| uu____5054 -> begin
false
end))
in ((((is_empty decreases_clause) && (is_empty rest)) && (is_empty cattributes)) && (is_empty universes)))
in (match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end
| uu____5063 -> begin
(match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end
| uu____5066 -> begin
(

let flags = (match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid)) with
| true -> begin
(FStar_Syntax_Syntax.LEMMA)::[]
end
| uu____5070 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____5072 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_ML_lid)) with
| true -> begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end
| uu____5074 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____5076 -> begin
[]
end)
end)
end)
end)
in (

let flags = (FStar_List.append flags cattributes)
in (

let rest = (match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid)) with
| true -> begin
(match (rest) with
| (req)::(ens)::((pat, aq))::[] -> begin
(

let pat = (match (pat.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
(

let nil = (FStar_Syntax_Syntax.mk_Tm_uinst pat ((FStar_Syntax_Syntax.U_succ (FStar_Syntax_Syntax.U_zero))::[]))
in (

let pattern = (let _0_562 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_562 ((FStar_Syntax_Syntax.U_zero)::[])))
in ((FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (Some (FStar_Syntax_Syntax.imp_tag))))::[])) None pat.FStar_Syntax_Syntax.pos)))
end
| uu____5157 -> begin
pat
end)
in (let _0_566 = (let _0_565 = (let _0_564 = (let _0_563 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))))) None pat.FStar_Syntax_Syntax.pos)
in ((_0_563), (aq)))
in (_0_564)::[])
in (ens)::_0_565)
in (req)::_0_566))
end
| uu____5195 -> begin
rest
end)
end
| uu____5202 -> begin
rest
end)
in (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = universes; FStar_Syntax_Syntax.effect_name = eff; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = rest; FStar_Syntax_Syntax.flags = (FStar_List.append flags decreases_clause)}))))
end)
end)))
end))))
end)))
end)));
)
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
| uu____5211 -> begin
None
end))
in (

let mk = (fun t -> ((FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let uu___217_5252 = t
in {FStar_Syntax_Syntax.n = uu___217_5252.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___217_5252.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___217_5252.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let uu___218_5282 = b
in {FStar_Parser_AST.b = uu___218_5282.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___218_5282.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___218_5282.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _0_567 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _0_567)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(

let uu____5323 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____5323) with
| (env, a) -> begin
(

let a = (

let uu___219_5331 = a
in {FStar_Syntax_Syntax.ppname = uu___219_5331.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___219_5331.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats = (desugar_pats env pats)
in (

let body = (desugar_formula env body)
in (

let body = (match (pats) with
| [] -> begin
body
end
| uu____5344 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_pattern (pats))))))
end)
in (

let body = (let _0_570 = (let _0_569 = (let _0_568 = (FStar_Syntax_Syntax.mk_binder a)
in (_0_568)::[])
in (no_annot_abs _0_569 body))
in (FStar_All.pipe_left setpos _0_570))
in (let _0_574 = FStar_Syntax_Syntax.Tm_app ((let _0_573 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (let _0_572 = (let _0_571 = (FStar_Syntax_Syntax.as_arg body)
in (_0_571)::[])
in ((_0_573), (_0_572)))))
in (FStar_All.pipe_left mk _0_574)))))))
end))
end
| uu____5360 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (let _0_576 = (q ((rest), (pats), (body)))
in (let _0_575 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _0_576 _0_575 FStar_Parser_AST.Formula)))
in (let _0_577 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term _0_577 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| uu____5416 -> begin
(failwith "impossible")
end))
in (

let uu____5418 = (unparen f).FStar_Parser_AST.tm
in (match (uu____5418) with
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
in (let _0_578 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _0_578)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _0_579 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _0_579)))
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
| uu____5492 -> begin
(desugar_term env f)
end)))))))))
and typars_of_binders : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let uu____5496 = (FStar_List.fold_left (fun uu____5509 b -> (match (uu____5509) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let uu___220_5537 = b
in {FStar_Parser_AST.b = uu___220_5537.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___220_5537.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___220_5537.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(

let uu____5547 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____5547) with
| (env, a) -> begin
(

let a = (

let uu___221_5559 = a
in {FStar_Syntax_Syntax.ppname = uu___221_5559.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___221_5559.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env), ((((a), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| uu____5568 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (uu____5496) with
| (env, tpars) -> begin
((env), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _0_580 = (desugar_typ env t)
in ((Some (x)), (_0_580)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _0_581 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown))) None x.FStar_Ident.idRange)
in ((Some (x)), (_0_581)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _0_582 = (desugar_typ env t)
in ((None), (_0_582)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators = (fun quals env t tps k datas -> (

let quals = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___196_5684 -> (match (uu___196_5684) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| uu____5685 -> begin
false
end))))
in (

let quals = (fun q -> (

let uu____5693 = ((FStar_All.pipe_left Prims.op_Negation env.FStar_ToSyntax_Env.iface) || env.FStar_ToSyntax_Env.admitted_iface)
in (match (uu____5693) with
| true -> begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end
| uu____5695 -> begin
(FStar_List.append q quals)
end)))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in FStar_Syntax_Syntax.Sig_declare_typ ((let _0_583 = (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in ((disc_name), ([]), (FStar_Syntax_Syntax.tun), (_0_583), ((FStar_Ident.range_of_lid disc_name))))))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_ToSyntax_Env.env  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (let _0_590 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____5733 -> (match (uu____5733) with
| (x, uu____5738) -> begin
(

let uu____5739 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____5739) with
| (field_name, uu____5744) -> begin
(

let only_decl = (((let _0_584 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _0_584)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (FStar_Options.dont_gen_projectors (FStar_ToSyntax_Env.current_module env).FStar_Ident.str))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(let _0_585 = (FStar_List.filter (fun uu___197_5755 -> (match (uu___197_5755) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____5756 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::_0_585)
end
| uu____5757 -> begin
q
end))
in (

let quals = (

let iquals = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___198_5764 -> (match (uu___198_5764) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| uu____5765 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun), (quals), ((FStar_Ident.range_of_lid field_name))))
in (match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____5770 -> begin
(

let dd = (

let uu____5772 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____5772) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____5774 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lb = (let _0_586 = FStar_Util.Inr ((FStar_Syntax_Syntax.lid_as_fv field_name dd None))
in {FStar_Syntax_Syntax.lbname = _0_586; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun})
in (

let impl = FStar_Syntax_Syntax.Sig_let ((let _0_589 = (let _0_588 = (let _0_587 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _0_587 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_0_588)::[])
in ((((false), ((lb)::[]))), (p), (_0_589), (quals), ([]))))
in (match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____5792 -> begin
(decl)::(impl)::[]
end))))
end))))))
end))
end))))
in (FStar_All.pipe_right _0_590 FStar_List.flatten))))


let mk_data_projector_names = (fun iquals env uu____5813 -> (match (uu____5813) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____5821, t, uu____5823, n, quals, uu____5826, uu____5827) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let uu____5832 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____5832) with
| (formals, uu____5842) -> begin
(match (formals) with
| [] -> begin
[]
end
| uu____5856 -> begin
(

let filter_records = (fun uu___199_5864 -> (match (uu___199_5864) with
| FStar_Syntax_Syntax.RecordConstructor (uu____5866, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| uu____5873 -> begin
None
end))
in (

let fv_qual = (

let uu____5875 = (FStar_Util.find_map quals filter_records)
in (match (uu____5875) with
| None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| Some (q) -> begin
q
end))
in (

let iquals = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract iquals)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::iquals
end
| uu____5881 -> begin
iquals
end)
in (

let uu____5882 = (FStar_Util.first_N n formals)
in (match (uu____5882) with
| (uu____5894, rest) -> begin
(mk_indexed_projector_names iquals fv_qual env lid rest)
end)))))
end)
end))
end
| uu____5908 -> begin
[]
end)
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = (

let uu____5946 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____5946) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract ((FStar_Syntax_Util.incr_delta_qualifier t))
end
| uu____5948 -> begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end))
in (

let lb = (let _0_594 = FStar_Util.Inr ((FStar_Syntax_Syntax.lid_as_fv lid dd None))
in (let _0_593 = (let _0_591 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _0_591))
in (let _0_592 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _0_594; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _0_593; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _0_592})))
in FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (rng), (lids), (quals), ([]))))))


let rec desugar_tycon : FStar_ToSyntax_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (

let tycon_id = (fun uu___200_5980 -> (match (uu___200_5980) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _0_595 = FStar_Parser_AST.Var ((FStar_Ident.lid_of_ids ((x)::[])))
in (FStar_Parser_AST.mk_term _0_595 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| uu____6040 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _0_597 = FStar_Parser_AST.App ((let _0_596 = (binder_to_term b)
in ((out), (_0_596), ((imp_of_aqual b)))))
in (FStar_Parser_AST.mk_term _0_597 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun uu___201_6049 -> (match (uu___201_6049) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun uu____6078 -> (match (uu____6078) with
| (x, t, uu____6085) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (let _0_599 = (let _0_598 = FStar_Parser_AST.Var ((FStar_Ident.lid_of_ids ((id)::[])))
in (FStar_Parser_AST.mk_term _0_598 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders _0_599 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type_level)
in (let _0_600 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____6125 -> (match (uu____6125) with
| (x, uu____6131, uu____6132) -> begin
(FStar_Syntax_Util.unmangle_field_name x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (_0_600)))))))
end
| uu____6135 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals uu___202_6157 -> (match (uu___202_6157) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let uu____6171 = (typars_of_binders _env binders)
in (match (uu____6171) with
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

let tconstr = (let _0_602 = (let _0_601 = FStar_Parser_AST.Var ((FStar_Ident.lid_of_ids ((id)::[])))
in (FStar_Parser_AST.mk_term _0_601 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders _0_602 binders))
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
| uu____6209 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env bs -> (

let uu____6235 = (FStar_List.fold_left (fun uu____6251 uu____6252 -> (match (((uu____6251), (uu____6252))) with
| ((env, tps), (x, imp)) -> begin
(

let uu____6300 = (FStar_ToSyntax_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (uu____6300) with
| (env, y) -> begin
((env), ((((y), (imp)))::tps))
end))
end)) ((env), ([])) bs)
in (match (uu____6235) with
| (env, bs) -> begin
((env), ((FStar_List.rev bs)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt = (match (kopt) with
| None -> begin
Some ((tm_type_z id.FStar_Ident.idRange))
end
| uu____6361 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt)))
in (

let uu____6366 = (desugar_abstract_tc quals env [] tc)
in (match (uu____6366) with
| (uu____6373, uu____6374, se, uu____6376) -> begin
(

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, uu____6379, typars, k, [], [], quals, rng) -> begin
(

let quals = (

let uu____6390 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (match (uu____6390) with
| true -> begin
quals
end
| uu____6393 -> begin
((let _0_604 = (FStar_Range.string_of_range rng)
in (let _0_603 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _0_604 _0_603)));
(FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals;
)
end))
in (

let t = (match (typars) with
| [] -> begin
k
end
| uu____6398 -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((let _0_605 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (_0_605)))))) None rng)
end)
in FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t), (quals), (rng)))))
end
| uu____6409 -> begin
se
end)
in (

let env = (FStar_ToSyntax_Env.push_sigelt env se)
in ((env), ((se)::[]))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let uu____6420 = (typars_of_binders env binders)
in (match (uu____6420) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
(

let uu____6440 = (FStar_Util.for_some (fun uu___203_6441 -> (match (uu___203_6441) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| uu____6442 -> begin
false
end)) quals)
in (match (uu____6440) with
| true -> begin
FStar_Syntax_Syntax.teff
end
| uu____6443 -> begin
FStar_Syntax_Syntax.tun
end))
end
| Some (k) -> begin
(desugar_term env' k)
end)
in (

let t0 = t
in (

let quals = (

let uu____6448 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___204_6450 -> (match (uu___204_6450) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| uu____6451 -> begin
false
end))))
in (match (uu____6448) with
| true -> begin
quals
end
| uu____6453 -> begin
(match ((t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula)) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____6455 -> begin
quals
end)
end))
in (

let se = (

let uu____6457 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Effect))
in (match (uu____6457) with
| true -> begin
(

let uu____6459 = (

let uu____6463 = (unparen t).FStar_Parser_AST.tm
in (match (uu____6463) with
| FStar_Parser_AST.Construct (head, args) -> begin
(

let uu____6475 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____6491))::args_rev -> begin
(

let uu____6498 = (unparen last_arg).FStar_Parser_AST.tm
in (match (uu____6498) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____6513 -> begin
(([]), (args))
end))
end
| uu____6518 -> begin
(([]), (args))
end)
in (match (uu____6475) with
| (cattributes, args) -> begin
(let _0_606 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head), (args)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (_0_606)))
end))
end
| uu____6543 -> begin
((t), ([]))
end))
in (match (uu____6459) with
| (t, cattributes) -> begin
(

let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (

let typars = (FStar_Syntax_Subst.close_binders typars)
in (

let c = (FStar_Syntax_Subst.close_comp typars c)
in FStar_Syntax_Syntax.Sig_effect_abbrev ((let _0_608 = (FStar_ToSyntax_Env.qualify env id)
in (let _0_607 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___205_6559 -> (match (uu___205_6559) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| uu____6560 -> begin
true
end))))
in ((_0_608), ([]), (typars), (c), (_0_607), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c))), (rng))))))))
end))
end
| uu____6561 -> begin
(

let t = (desugar_typ env' t)
in (

let nm = (FStar_ToSyntax_Env.qualify env id)
in (mk_typ_abbrev nm [] typars k t ((nm)::[]) quals rng)))
end))
in (

let env = (FStar_ToSyntax_Env.push_sigelt env se)
in ((env), ((se)::[])))))))
end))
end
| (FStar_Parser_AST.TyconRecord (uu____6566))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let uu____6579 = (tycon_record_as_variant trec)
in (match (uu____6579) with
| (t, fs) -> begin
(let _0_611 = (let _0_610 = FStar_Syntax_Syntax.RecordType ((let _0_609 = (FStar_Ident.ids_of_lid (FStar_ToSyntax_Env.current_module env))
in ((_0_609), (fs))))
in (_0_610)::quals)
in (desugar_tycon env rng _0_611 ((t)::[])))
end)))
end
| (uu____6591)::uu____6592 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let uu____6679 = et
in (match (uu____6679) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (uu____6793) -> begin
(

let trec = tc
in (

let uu____6806 = (tycon_record_as_variant trec)
in (match (uu____6806) with
| (t, fs) -> begin
(let _0_614 = (let _0_613 = FStar_Syntax_Syntax.RecordType ((let _0_612 = (FStar_Ident.ids_of_lid (FStar_ToSyntax_Env.current_module env))
in ((_0_612), (fs))))
in (_0_613)::quals)
in (collect_tcs _0_614 ((env), (tcs)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let uu____6882 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____6882) with
| (env, uu____6913, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let uu____6991 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____6991) with
| (env, uu____7022, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (binders), (t), (quals))))::tcs))
end))
end
| uu____7086 -> begin
(failwith "Unrecognized mutual type definition")
end)
end)))
in (

let uu____7110 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (uu____7110) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun uu___207_7348 -> (match (uu___207_7348) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, uu____7380, uu____7381, uu____7382, uu____7383), binders, t, quals) -> begin
(

let t = (

let uu____7416 = (typars_of_binders env binders)
in (match (uu____7416) with
| (env, tpars) -> begin
(

let uu____7433 = (push_tparams env tpars)
in (match (uu____7433) with
| (env_tps, tpars) -> begin
(

let t = (desugar_typ env_tps t)
in (

let tpars = (FStar_Syntax_Subst.close_binders tpars)
in (FStar_Syntax_Subst.close tpars t)))
end))
end))
in (let _0_616 = (let _0_615 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in (([]), (_0_615)))
in (_0_616)::[]))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, uu____7476, tags, uu____7478), constrs, tconstr, quals) -> begin
(

let tycon = ((tname), (tpars), (k))
in (

let uu____7526 = (push_tparams env tpars)
in (match (uu____7526) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun uu____7561 -> (match (uu____7561) with
| (x, uu____7569) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let uu____7573 = (let _0_623 = (FStar_All.pipe_right constrs (FStar_List.map (fun uu____7639 -> (match (uu____7639) with
| (id, topt, uu____7656, of_notation) -> begin
(

let t = (match (of_notation) with
| true -> begin
(match (topt) with
| Some (t) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level None))::[]), (tconstr)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end
| None -> begin
tconstr
end)
end
| uu____7665 -> begin
(match (topt) with
| None -> begin
(failwith "Impossible")
end
| Some (t) -> begin
t
end)
end)
in (

let t = (let _0_618 = (FStar_ToSyntax_Env.default_total env_tps)
in (let _0_617 = (close env_tps t)
in (desugar_term _0_618 _0_617)))
in (

let name = (FStar_ToSyntax_Env.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun uu___206_7673 -> (match (uu___206_7673) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| uu____7680 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (let _0_622 = (let _0_621 = FStar_Syntax_Syntax.Sig_datacon ((let _0_620 = (let _0_619 = (FStar_Syntax_Syntax.mk_Total (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders))
in (FStar_Syntax_Util.arrow data_tpars _0_619))
in ((name), (univs), (_0_620), (tname), (ntps), (quals), (mutuals), (rng))))
in ((tps), (_0_621)))
in ((name), (_0_622))))))))
end))))
in (FStar_All.pipe_left FStar_List.split _0_623))
in (match (uu____7573) with
| (constrNames, constrs) -> begin
((([]), (FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))))::constrs
end)))
end)))
end
| uu____7745 -> begin
(failwith "impossible")
end))))
in (

let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (

let uu____7793 = (let _0_624 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals _0_624 rng))
in (match (uu____7793) with
| (bundle, abbrevs) -> begin
(

let env = (FStar_ToSyntax_Env.push_sigelt env0 bundle)
in (

let env = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env abbrevs)
in (

let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projector_names quals env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun uu___208_7829 -> (match (uu___208_7829) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, uu____7832, tps, k, uu____7835, constrs, quals, uu____7838) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::quals
end
| uu____7851 -> begin
quals
end)
in (mk_data_discriminators quals env tname tps k constrs))
end
| uu____7852 -> begin
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

let uu____7870 = (FStar_List.fold_left (fun uu____7877 b -> (match (uu____7877) with
| (env, binders) -> begin
(

let uu____7889 = (desugar_binder env b)
in (match (uu____7889) with
| (Some (a), k) -> begin
(

let uu____7899 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____7899) with
| (env, a) -> begin
(let _0_626 = (let _0_625 = (FStar_Syntax_Syntax.mk_binder (

let uu___222_7908 = a
in {FStar_Syntax_Syntax.ppname = uu___222_7908.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___222_7908.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_0_625)::binders)
in ((env), (_0_626)))
end))
end
| uu____7909 -> begin
(Prims.raise (FStar_Errors.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) binders)
in (match (uu____7870) with
| (env, binders) -> begin
((env), ((FStar_List.rev binders)))
end)))


let rec desugar_effect : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  Prims.bool  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_kind eff_decls actions for_free -> (

let env0 = env
in (

let monad_env = (FStar_ToSyntax_Env.enter_monad_scope env eff_name)
in (

let uu____8003 = (desugar_binders monad_env eff_binders)
in (match (uu____8003) with
| (env, binders) -> begin
(

let eff_k = (let _0_627 = (FStar_ToSyntax_Env.default_total env)
in (desugar_term _0_627 eff_kind))
in (

let uu____8015 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun uu____8026 decl -> (match (uu____8026) with
| (env, out) -> begin
(

let uu____8038 = (desugar_decl env decl)
in (match (uu____8038) with
| (env, ses) -> begin
(let _0_629 = (let _0_628 = (FStar_List.hd ses)
in (_0_628)::out)
in ((env), (_0_629)))
end))
end)) ((env), ([]))))
in (match (uu____8015) with
| (env, decls) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let actions = (FStar_All.pipe_right actions (FStar_List.map (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____8061, ((FStar_Parser_AST.TyconAbbrev (name, uu____8063, uu____8064, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (uu____8065, ((def, uu____8067))::((cps_type, uu____8069))::[]); FStar_Parser_AST.range = uu____8070; FStar_Parser_AST.level = uu____8071}), uu____8072))::[]) when (not (for_free)) -> begin
(let _0_634 = (FStar_ToSyntax_Env.qualify env name)
in (let _0_633 = (let _0_630 = (desugar_term env def)
in (FStar_Syntax_Subst.close binders _0_630))
in (let _0_632 = (let _0_631 = (desugar_typ env cps_type)
in (FStar_Syntax_Subst.close binders _0_631))
in {FStar_Syntax_Syntax.action_name = _0_634; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _0_633; FStar_Syntax_Syntax.action_typ = _0_632})))
end
| FStar_Parser_AST.Tycon (uu____8098, ((FStar_Parser_AST.TyconAbbrev (name, uu____8100, uu____8101, defn), uu____8103))::[]) when for_free -> begin
(let _0_637 = (FStar_ToSyntax_Env.qualify env name)
in (let _0_636 = (let _0_635 = (desugar_term env defn)
in (FStar_Syntax_Subst.close binders _0_635))
in {FStar_Syntax_Syntax.action_name = _0_637; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _0_636; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
end
| uu____8120 -> begin
(Prims.raise (FStar_Errors.Error ((("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples)."), (d.FStar_Parser_AST.drange)))))
end))))
in (

let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (

let lookup = (fun s -> (

let l = (FStar_ToSyntax_Env.qualify env (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange))))
in (let _0_639 = (let _0_638 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _0_638))
in (([]), (_0_639)))))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (Some (mname))) quals)
in (

let se = (match (for_free) with
| true -> begin
(

let dummy_tscheme = (let _0_640 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (([]), (_0_640)))
in FStar_Syntax_Syntax.Sig_new_effect_for_free ((let _0_644 = (let _0_643 = (Prims.snd (lookup "repr"))
in (let _0_642 = (lookup "return")
in (let _0_641 = (lookup "bind")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = _0_643; FStar_Syntax_Syntax.return_repr = _0_642; FStar_Syntax_Syntax.bind_repr = _0_641; FStar_Syntax_Syntax.actions = actions})))
in ((_0_644), (d.FStar_Parser_AST.drange)))))
end
| uu____8153 -> begin
(

let rr = ((FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right qualifiers FStar_Syntax_Syntax.contains_reflectable))
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in FStar_Syntax_Syntax.Sig_new_effect ((let _0_659 = (let _0_658 = (lookup "return_wp")
in (let _0_657 = (lookup "bind_wp")
in (let _0_656 = (lookup "if_then_else")
in (let _0_655 = (lookup "ite_wp")
in (let _0_654 = (lookup "stronger")
in (let _0_653 = (lookup "close_wp")
in (let _0_652 = (lookup "assert_p")
in (let _0_651 = (lookup "assume_p")
in (let _0_650 = (lookup "null_wp")
in (let _0_649 = (lookup "trivial")
in (let _0_648 = (match (rr) with
| true -> begin
(let _0_645 = (lookup "repr")
in (FStar_All.pipe_left Prims.snd _0_645))
end
| uu____8166 -> begin
FStar_Syntax_Syntax.tun
end)
in (let _0_647 = (match (rr) with
| true -> begin
(lookup "return")
end
| uu____8167 -> begin
un_ts
end)
in (let _0_646 = (match (rr) with
| true -> begin
(lookup "bind")
end
| uu____8168 -> begin
un_ts
end)
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = _0_658; FStar_Syntax_Syntax.bind_wp = _0_657; FStar_Syntax_Syntax.if_then_else = _0_656; FStar_Syntax_Syntax.ite_wp = _0_655; FStar_Syntax_Syntax.stronger = _0_654; FStar_Syntax_Syntax.close_wp = _0_653; FStar_Syntax_Syntax.assert_p = _0_652; FStar_Syntax_Syntax.assume_p = _0_651; FStar_Syntax_Syntax.null_wp = _0_650; FStar_Syntax_Syntax.trivial = _0_649; FStar_Syntax_Syntax.repr = _0_648; FStar_Syntax_Syntax.return_repr = _0_647; FStar_Syntax_Syntax.bind_repr = _0_646; FStar_Syntax_Syntax.actions = actions})))))))))))))
in ((_0_659), (d.FStar_Parser_AST.drange))))))
end)
in (

let env = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right actions (FStar_List.fold_left (fun env a -> (let _0_660 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env _0_660))) env))
in (

let env = (

let uu____8175 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____8175) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let refl_decl = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]), (d.FStar_Parser_AST.drange)))
in (FStar_ToSyntax_Env.push_sigelt env refl_decl)))
end
| uu____8180 -> begin
env
end))
in ((env), ((se)::[]))))))))))))
end)))
end)))))
and desugar_redefine_effect : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  (FStar_Ident.lident Prims.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier)  ->  FStar_Parser_AST.qualifier Prims.list  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.eff_decl  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d trans_qual quals eff_name eff_binders defn build_sigelt -> (

let env0 = env
in (

let env = (FStar_ToSyntax_Env.enter_monad_scope env eff_name)
in (

let uu____8203 = (desugar_binders env eff_binders)
in (match (uu____8203) with
| (env, binders) -> begin
(

let uu____8214 = (

let uu____8223 = (head_and_args defn)
in (match (uu____8223) with
| (head, args) -> begin
(

let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_defn env) l)
end
| uu____8247 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_663 = (let _0_662 = (let _0_661 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat _0_661 " not found"))
in (Prims.strcat "Effect " _0_662))
in ((_0_663), (d.FStar_Parser_AST.drange))))))
end)
in (

let uu____8248 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____8264))::args_rev -> begin
(

let uu____8271 = (unparen last_arg).FStar_Parser_AST.tm
in (match (uu____8271) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____8286 -> begin
(([]), (args))
end))
end
| uu____8291 -> begin
(([]), (args))
end)
in (match (uu____8248) with
| (cattributes, args) -> begin
(let _0_665 = (desugar_args env args)
in (let _0_664 = (desugar_attributes env cattributes)
in ((ed), (_0_665), (_0_664))))
end)))
end))
in (match (uu____8214) with
| (ed, args, cattributes) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let sub = (fun uu____8348 -> (match (uu____8348) with
| (uu____8355, x) -> begin
(

let uu____8359 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (uu____8359) with
| (edb, x) -> begin
((match (((FStar_List.length args) <> (FStar_List.length edb))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end
| uu____8377 -> begin
()
end);
(

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _0_667 = (let _0_666 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _0_666))
in (([]), (_0_667))));
)
end))
end))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let ed = (let _0_687 = (let _0_668 = (trans_qual (Some (mname)))
in (FStar_List.map _0_668 quals))
in (let _0_686 = (Prims.snd (sub (([]), (ed.FStar_Syntax_Syntax.signature))))
in (let _0_685 = (sub ed.FStar_Syntax_Syntax.ret_wp)
in (let _0_684 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _0_683 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _0_682 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _0_681 = (sub ed.FStar_Syntax_Syntax.stronger)
in (let _0_680 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _0_679 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _0_678 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _0_677 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _0_676 = (sub ed.FStar_Syntax_Syntax.trivial)
in (let _0_675 = (Prims.snd (sub (([]), (ed.FStar_Syntax_Syntax.repr))))
in (let _0_674 = (sub ed.FStar_Syntax_Syntax.return_repr)
in (let _0_673 = (sub ed.FStar_Syntax_Syntax.bind_repr)
in (let _0_672 = (FStar_List.map (fun action -> (let _0_671 = (FStar_ToSyntax_Env.qualify env action.FStar_Syntax_Syntax.action_unqualified_name)
in (let _0_670 = (Prims.snd (sub (([]), (action.FStar_Syntax_Syntax.action_defn))))
in (let _0_669 = (Prims.snd (sub (([]), (action.FStar_Syntax_Syntax.action_typ))))
in {FStar_Syntax_Syntax.action_name = _0_671; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _0_670; FStar_Syntax_Syntax.action_typ = _0_669})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = _0_687; FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _0_686; FStar_Syntax_Syntax.ret_wp = _0_685; FStar_Syntax_Syntax.bind_wp = _0_684; FStar_Syntax_Syntax.if_then_else = _0_683; FStar_Syntax_Syntax.ite_wp = _0_682; FStar_Syntax_Syntax.stronger = _0_681; FStar_Syntax_Syntax.close_wp = _0_680; FStar_Syntax_Syntax.assert_p = _0_679; FStar_Syntax_Syntax.assume_p = _0_678; FStar_Syntax_Syntax.null_wp = _0_677; FStar_Syntax_Syntax.trivial = _0_676; FStar_Syntax_Syntax.repr = _0_675; FStar_Syntax_Syntax.return_repr = _0_674; FStar_Syntax_Syntax.bind_repr = _0_673; FStar_Syntax_Syntax.actions = _0_672}))))))))))))))))
in (

let se = (build_sigelt ed d.FStar_Parser_AST.drange)
in (

let monad_env = env
in (

let env = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun env a -> (let _0_688 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env _0_688))) env))
in (

let env = (

let uu____8399 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____8399) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let refl_decl = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]), (d.FStar_Parser_AST.drange)))
in (FStar_ToSyntax_Env.push_sigelt env refl_decl)))
end
| uu____8405 -> begin
env
end))
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
| FStar_Parser_AST.Fsdoc (uu____8422) -> begin
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
(let _0_689 = (FStar_ToSyntax_Env.push_module_abbrev env x l)
in ((_0_689), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, tcs) -> begin
(

let quals = (match (is_effect) with
| true -> begin
(FStar_Parser_AST.Effect_qual)::d.FStar_Parser_AST.quals
end
| uu____8448 -> begin
d.FStar_Parser_AST.quals
end)
in (

let tcs = (FStar_List.map (fun uu____8454 -> (match (uu____8454) with
| (x, uu____8459) -> begin
x
end)) tcs)
in (let _0_690 = (FStar_List.map (trans_qual None) quals)
in (desugar_tycon env d.FStar_Parser_AST.drange _0_690 tcs))))
end
| FStar_Parser_AST.TopLevelLet (isrec, lets) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let attrs = d.FStar_Parser_AST.attrs
in (

let attrs = (FStar_List.map (desugar_term env) attrs)
in (

let expand_toplevel_pattern = ((isrec = FStar_Parser_AST.NoLetQualifier) && (match (lets) with
| ((({FStar_Parser_AST.pat = FStar_Parser_AST.PatOp (_); FStar_Parser_AST.prange = _}, _))::[]) | ((({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_); FStar_Parser_AST.prange = _}, _))::[]) | ((({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_); FStar_Parser_AST.prange = _}, _); FStar_Parser_AST.prange = _}, _))::[]) -> begin
false
end
| ((p, uu____8499))::[] -> begin
(not ((is_app_pattern p)))
end
| uu____8504 -> begin
false
end))
in (match ((not (expand_toplevel_pattern))) with
| true -> begin
(

let as_inner_let = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let ds_lets = (desugar_term_maybe_top true env as_inner_let)
in (

let uu____8515 = (FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets).FStar_Syntax_Syntax.n
in (match (uu____8515) with
| FStar_Syntax_Syntax.Tm_let (lbs, uu____8519) -> begin
(

let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals = (match (quals) with
| (uu____8539)::uu____8540 -> begin
(FStar_List.map (trans_qual None) quals)
end
| uu____8542 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun uu___209_8546 -> (match (uu___209_8546) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (uu____8548); FStar_Syntax_Syntax.lbunivs = uu____8549; FStar_Syntax_Syntax.lbtyp = uu____8550; FStar_Syntax_Syntax.lbeff = uu____8551; FStar_Syntax_Syntax.lbdef = uu____8552} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____8559; FStar_Syntax_Syntax.lbtyp = uu____8560; FStar_Syntax_Syntax.lbeff = uu____8561; FStar_Syntax_Syntax.lbdef = uu____8562} -> begin
(FStar_ToSyntax_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals = (

let uu____8574 = (FStar_All.pipe_right lets (FStar_Util.for_some (fun uu____8580 -> (match (uu____8580) with
| (uu____8583, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end))))
in (match (uu____8574) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____8586 -> begin
quals
end))
in (

let lbs = (

let uu____8591 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____8591) with
| true -> begin
(let _0_691 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu___223_8603 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let uu___224_8604 = fv
in {FStar_Syntax_Syntax.fv_name = uu___224_8604.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = uu___224_8604.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = uu___223_8603.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___223_8603.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___223_8603.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___223_8603.FStar_Syntax_Syntax.lbdef})))))
in (((Prims.fst lbs)), (_0_691)))
end
| uu____8608 -> begin
lbs
end))
in (

let s = FStar_Syntax_Syntax.Sig_let ((let _0_692 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in ((lbs), (d.FStar_Parser_AST.drange), (_0_692), (quals), (attrs))))
in (

let env = (FStar_ToSyntax_Env.push_sigelt env s)
in ((env), ((s)::[]))))))))
end
| uu____8625 -> begin
(failwith "Desugaring a let did not produce a let")
end))))
end
| uu____8628 -> begin
(

let uu____8629 = (match (lets) with
| ((pat, body))::[] -> begin
((pat), (body))
end
| uu____8640 -> begin
(failwith "expand_toplevel_pattern should only allow single definition lets")
end)
in (match (uu____8629) with
| (pat, body) -> begin
(

let fresh_toplevel_name = (FStar_Ident.gen FStar_Range.dummyRange)
in (

let fresh_pat = (

let var_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((fresh_toplevel_name), (None)))) FStar_Range.dummyRange)
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, ty) -> begin
(

let uu___225_8656 = pat
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed (((var_pat), (ty))); FStar_Parser_AST.prange = uu___225_8656.FStar_Parser_AST.prange})
end
| uu____8657 -> begin
var_pat
end))
in (

let main_let = (desugar_decl env (

let uu___226_8661 = d
in {FStar_Parser_AST.d = FStar_Parser_AST.TopLevelLet (((isrec), ((((fresh_pat), (body)))::[]))); FStar_Parser_AST.drange = uu___226_8661.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___226_8661.FStar_Parser_AST.doc; FStar_Parser_AST.quals = (FStar_Parser_AST.Private)::d.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = uu___226_8661.FStar_Parser_AST.attrs}))
in (

let build_projection = (fun uu____8680 id -> (match (uu____8680) with
| (env, ses) -> begin
(

let main = (let _0_693 = FStar_Parser_AST.Var ((FStar_Ident.lid_of_ids ((fresh_toplevel_name)::[])))
in (FStar_Parser_AST.mk_term _0_693 FStar_Range.dummyRange FStar_Parser_AST.Expr))
in (

let lid = (FStar_Ident.lid_of_ids ((id)::[]))
in (

let projectee = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (lid)) FStar_Range.dummyRange FStar_Parser_AST.Expr)
in (

let body = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Match (((main), ((((pat), (None), (projectee)))::[])))) FStar_Range.dummyRange FStar_Parser_AST.Expr)
in (

let bv_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((id), (None)))) FStar_Range.dummyRange)
in (

let id_decl = (FStar_Parser_AST.mk_decl (FStar_Parser_AST.TopLevelLet (((FStar_Parser_AST.NoLetQualifier), ((((bv_pat), (body)))::[])))) FStar_Range.dummyRange [])
in (

let uu____8720 = (desugar_decl env id_decl)
in (match (uu____8720) with
| (env, ses') -> begin
((env), ((FStar_List.append ses ses')))
end))))))))
end))
in (

let bvs = (let _0_694 = (gather_pattern_bound_vars pat)
in (FStar_All.pipe_right _0_694 FStar_Util.set_elements))
in (FStar_List.fold_left build_projection main_let bvs))))))
end))
end)))))
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
in (let _0_697 = (let _0_696 = FStar_Syntax_Syntax.Sig_assume ((let _0_695 = (FStar_ToSyntax_Env.qualify env id)
in ((_0_695), (f), ((FStar_Syntax_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange))))
in (_0_696)::[])
in ((env), (_0_697))))
end
| FStar_Parser_AST.Val (id, t) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let t = (let _0_698 = (close_fun env t)
in (desugar_term env _0_698))
in (

let quals = (match ((env.FStar_ToSyntax_Env.iface && env.FStar_ToSyntax_Env.admitted_iface)) with
| true -> begin
(FStar_Parser_AST.Assumption)::quals
end
| uu____8752 -> begin
quals
end)
in (

let se = FStar_Syntax_Syntax.Sig_declare_typ ((let _0_700 = (FStar_ToSyntax_Env.qualify env id)
in (let _0_699 = (FStar_List.map (trans_qual None) quals)
in ((_0_700), ([]), (t), (_0_699), (d.FStar_Parser_AST.drange)))))
in (

let env = (FStar_ToSyntax_Env.push_sigelt env se)
in ((env), ((se)::[])))))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(

let uu____8760 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (match (uu____8760) with
| (t, uu____8768) -> begin
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

let t = (let _0_704 = (let _0_701 = (FStar_Syntax_Syntax.null_binder t)
in (_0_701)::[])
in (let _0_703 = (let _0_702 = (Prims.fst (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _0_702))
in (FStar_Syntax_Util.arrow _0_704 _0_703)))
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

let uu____8823 = (desugar_binders env binders)
in (match (uu____8823) with
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

let lookup = (fun l -> (

let uu____8883 = (FStar_ToSyntax_Env.try_lookup_effect_name env l)
in (match (uu____8883) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_707 = (let _0_706 = (let _0_705 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat _0_705 " not found"))
in (Prims.strcat "Effect name " _0_706))
in ((_0_707), (d.FStar_Parser_AST.drange))))))
end
| Some (l) -> begin
l
end)))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let uu____8888 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(let _0_709 = Some ((let _0_708 = (desugar_term env t)
in (([]), (_0_708))))
in ((_0_709), (None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(let _0_713 = Some ((let _0_710 = (desugar_term env wp)
in (([]), (_0_710))))
in (let _0_712 = Some ((let _0_711 = (desugar_term env t)
in (([]), (_0_711))))
in ((_0_713), (_0_712))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(let _0_715 = Some ((let _0_714 = (desugar_term env t)
in (([]), (_0_714))))
in ((None), (_0_715)))
end)
in (match (uu____8888) with
| (lift_wp, lift) -> begin
(

let se = FStar_Syntax_Syntax.Sig_sub_effect ((({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun uu____8994 d -> (match (uu____8994) with
| (env, sigelts) -> begin
(

let uu____9006 = (desugar_decl env d)
in (match (uu____9006) with
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

let uu____9048 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _0_716 = (FStar_ToSyntax_Env.prepare_module_or_interface true admitted env mname)
in ((_0_716), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _0_717 = (FStar_ToSyntax_Env.prepare_module_or_interface false false env mname)
in ((_0_717), (mname), (decls), (false)))
end)
in (match (uu____9048) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let uu____9090 = (desugar_decls env decls)
in (match (uu____9090) with
| (env, sigelts) -> begin
(

let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in ((env), (modul), (pop_when_done)))
end))
end))))


let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (

let m = (

let uu____9115 = ((FStar_Options.interactive ()) && (let _0_718 = (FStar_Util.get_file_extension (FStar_List.hd (FStar_Options.file_list ())))
in (_0_718 = "fsti")))
in (match (uu____9115) with
| true -> begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface (((mname), (decls), (true)))
end
| FStar_Parser_AST.Interface (mname, uu____9122, uu____9123) -> begin
(failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end
| uu____9126 -> begin
m
end))
in (

let uu____9127 = (desugar_modul_common curmod env m)
in (match (uu____9127) with
| (x, y, uu____9135) -> begin
((x), (y))
end))))


let desugar_modul : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun env m -> (

let uu____9146 = (desugar_modul_common None env m)
in (match (uu____9146) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_ToSyntax_Env.finish_module_or_interface env modul)
in ((

let uu____9157 = (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____9157) with
| true -> begin
(let _0_719 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _0_719))
end
| uu____9158 -> begin
()
end));
(let _0_720 = (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end
| uu____9159 -> begin
env
end)
in ((_0_720), (modul)));
))
end)))


let desugar_file : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (

let uu____9169 = (FStar_List.fold_left (fun uu____9176 m -> (match (uu____9176) with
| (env, mods) -> begin
(

let uu____9188 = (desugar_modul env m)
in (match (uu____9188) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (uu____9169) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_ToSyntax_Env.env  ->  FStar_ToSyntax_Env.env = (fun m en -> (

let uu____9212 = (FStar_ToSyntax_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (uu____9212) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt (

let uu___227_9218 = en
in {FStar_ToSyntax_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_ToSyntax_Env.curmonad = uu___227_9218.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = uu___227_9218.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = uu___227_9218.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = uu___227_9218.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = uu___227_9218.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = uu___227_9218.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = uu___227_9218.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = uu___227_9218.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.default_result_effect = uu___227_9218.FStar_ToSyntax_Env.default_result_effect; FStar_ToSyntax_Env.iface = uu___227_9218.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = uu___227_9218.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = uu___227_9218.FStar_ToSyntax_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (

let env = (FStar_ToSyntax_Env.finish_module_or_interface en m)
in (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name env)
end
| uu____9220 -> begin
env
end)))
end)))




