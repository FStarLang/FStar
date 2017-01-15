
open Prims

let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun uu___198_5 -> (match (uu___198_5) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| uu____8 -> begin
None
end))


let trans_qual : FStar_Range.range  ->  FStar_Ident.lident Prims.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r maybe_effect_id uu___199_19 -> (match (uu___199_19) with
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


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun uu___200_25 -> (match (uu___200_25) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun uu___201_32 -> (match (uu___201_32) with
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


let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _0_455 = FStar_Parser_AST.Name ((FStar_Ident.lid_of_path (("Type0")::[]) r))
in (FStar_Parser_AST.mk_term _0_455 r FStar_Parser_AST.Kind)))


let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _0_456 = FStar_Parser_AST.Name ((FStar_Ident.lid_of_path (("Type")::[]) r))
in (FStar_Parser_AST.mk_term _0_456 r FStar_Parser_AST.Kind)))


let rec is_comp_type : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> (match (t.FStar_Parser_AST.tm) with
| (FStar_Parser_AST.Name (l)) | (FStar_Parser_AST.Construct (l, _)) -> begin
(let _0_457 = (FStar_ToSyntax_Env.try_lookup_effect_name env l)
in (FStar_All.pipe_right _0_457 FStar_Option.isSome))
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


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _0_460 = (let _0_459 = (FStar_Ident.mk_ident (let _0_458 = (FStar_Parser_AST.compile_op n s)
in ((_0_458), (r))))
in (_0_459)::[])
in (FStar_All.pipe_right _0_460 FStar_Ident.lid_of_ids)))


let op_as_term : FStar_ToSyntax_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (

let r = (fun l dd -> Some ((let _0_461 = (FStar_Syntax_Syntax.lid_as_fv (FStar_Ident.set_lid_range l rng) dd None)
in (FStar_All.pipe_right _0_461 FStar_Syntax_Syntax.fv_to_tm))))
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

let uu____152 = (let _0_462 = (compile_op_lid arity s rng)
in (FStar_ToSyntax_Env.try_lookup_lid env _0_462))
in (match (uu____152) with
| Some (t) -> begin
Some ((Prims.fst t))
end
| uu____162 -> begin
(fallback ())
end)))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _0_463 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _0_463)))


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
(let _0_464 = (free_type_vars env term)
in ((env), (_0_464)))
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
(let _0_465 = (free_type_vars env t)
in ((env), (_0_465)))
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
(let _0_467 = (free_type_vars env t1)
in (let _0_466 = (free_type_vars env t2)
in (FStar_List.append _0_467 _0_466)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(

let uu____283 = (free_type_vars_b env b)
in (match (uu____283) with
| (env, f) -> begin
(let _0_468 = (free_type_vars env t)
in (FStar_List.append f _0_468))
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
(let _0_469 = (free_type_vars env body)
in (FStar_List.append free _0_469))
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

let ftv = (let _0_470 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _0_470))
in (match (((FStar_List.length ftv) = (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____417 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _0_472 = FStar_Parser_AST.TAnnotated ((let _0_471 = (tm_type x.FStar_Ident.idRange)
in ((x), (_0_471))))
in (FStar_Parser_AST.mk_binder _0_472 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end)))


let close_fun : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _0_473 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _0_473))
in (match (((FStar_List.length ftv) = (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____437 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _0_475 = FStar_Parser_AST.TAnnotated ((let _0_474 = (tm_type x.FStar_Ident.idRange)
in ((x), (_0_474))))
in (FStar_Parser_AST.mk_binder _0_475 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (Some (FStar_Parser_AST.Implicit)))))))
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
(let _0_476 = FStar_Util.Inr ((FStar_ToSyntax_Env.qualify env id))
in ((_0_476), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____570); FStar_Parser_AST.prange = uu____571}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| uu____581 -> begin
(failwith "Not an app pattern")
end))

type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term)


let uu___is_LocalBinder : bnd  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LocalBinder (_0) -> begin
true
end
| uu____605 -> begin
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
| uu____625 -> begin
false
end))


let __proj__LetBinder__item___0 : bnd  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| LetBinder (_0) -> begin
_0
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun uu___202_643 -> (match (uu___202_643) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| uu____648 -> begin
(failwith "Impossible")
end))


let as_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_ToSyntax_Env.env) = (fun env imp uu___203_665 -> (match (uu___203_665) with
| (None, k) -> begin
(let _0_477 = (FStar_Syntax_Syntax.null_binder k)
in ((_0_477), (env)))
end
| (Some (a), k) -> begin
(

let uu____677 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____677) with
| (env, a) -> begin
(((((

let uu___224_688 = a
in {FStar_Syntax_Syntax.ppname = uu___224_688.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___224_688.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env))
end))
end))


type env_t =
FStar_ToSyntax_Env.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : ((FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.letbinding = (fun uu____701 -> (match (uu____701) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))


let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))


let mk_ref_read = (fun tm -> (

let tm' = FStar_Syntax_Syntax.Tm_app ((let _0_481 = (FStar_Syntax_Syntax.fv_to_tm (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid FStar_Syntax_Syntax.Delta_constant None))
in (let _0_480 = (let _0_479 = (let _0_478 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_0_478)))
in (_0_479)::[])
in ((_0_481), (_0_480)))))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc = (fun tm -> (

let tm' = FStar_Syntax_Syntax.Tm_app ((let _0_485 = (FStar_Syntax_Syntax.fv_to_tm (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant None))
in (let _0_484 = (let _0_483 = (let _0_482 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_0_482)))
in (_0_483)::[])
in ((_0_485), (_0_484)))))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign = (fun t1 t2 pos -> (

let tm = FStar_Syntax_Syntax.Tm_app ((let _0_492 = (FStar_Syntax_Syntax.fv_to_tm (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant None))
in (let _0_491 = (let _0_490 = (let _0_486 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (_0_486)))
in (let _0_489 = (let _0_488 = (let _0_487 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (_0_487)))
in (_0_488)::[])
in (_0_490)::_0_489))
in ((_0_492), (_0_491)))))
in (FStar_Syntax_Syntax.mk tm None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun uu___204_864 -> (match (uu___204_864) with
| ("repr") | ("post") | ("pre") | ("wp") -> begin
true
end
| uu____865 -> begin
false
end))


let rec sum_to_universe : FStar_Syntax_Syntax.universe  ->  Prims.int  ->  FStar_Syntax_Syntax.universe = (fun u n -> (match ((n = (Prims.parse_int "0"))) with
| true -> begin
u
end
| uu____872 -> begin
FStar_Syntax_Syntax.U_succ ((sum_to_universe u (n - (Prims.parse_int "1"))))
end))


let int_to_universe : Prims.int  ->  FStar_Syntax_Syntax.universe = (fun n -> (sum_to_universe FStar_Syntax_Syntax.U_zero n))


let rec desugar_maybe_non_constant_universe : FStar_Parser_AST.term  ->  (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun t -> (

let uu____883 = (unparen t).FStar_Parser_AST.tm
in (match (uu____883) with
| FStar_Parser_AST.Wild -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_unif ((FStar_Unionfind.fresh None)))
end
| FStar_Parser_AST.Uvar (u) -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_name (u))
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____889)) -> begin
(

let n = (FStar_Util.int_of_string repr)
in ((match ((n < (Prims.parse_int "0"))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Negative universe constant  are not supported : " repr)), (t.FStar_Parser_AST.range)))))
end
| uu____898 -> begin
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
(Prims.raise (FStar_Errors.Error ((let _0_494 = (let _0_493 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "This universe might contain a sum of two universe variables " _0_493))
in ((_0_494), (t.FStar_Parser_AST.range))))))
end)))
end
| FStar_Parser_AST.App (uu____940) -> begin
(

let rec aux = (fun t univargs -> (

let uu____959 = (unparen t).FStar_Parser_AST.tm
in (match (uu____959) with
| FStar_Parser_AST.App (t, targ, uu____964) -> begin
(

let uarg = (desugar_maybe_non_constant_universe targ)
in (aux t ((uarg)::univargs)))
end
| FStar_Parser_AST.Var (max_lid) -> begin
(match ((FStar_List.existsb (fun uu___205_976 -> (match (uu___205_976) with
| FStar_Util.Inr (uu____979) -> begin
true
end
| uu____980 -> begin
false
end)) univargs)) with
| true -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_max ((FStar_List.map (fun uu___206_985 -> (match (uu___206_985) with
| FStar_Util.Inl (n) -> begin
(int_to_universe n)
end
| FStar_Util.Inr (u) -> begin
u
end)) univargs)))
end
| uu____990 -> begin
(

let nargs = (FStar_List.map (fun uu___207_995 -> (match (uu___207_995) with
| FStar_Util.Inl (n) -> begin
n
end
| FStar_Util.Inr (uu____999) -> begin
(failwith "impossible")
end)) univargs)
in FStar_Util.Inl ((FStar_List.fold_left (fun m n -> (match ((m > n)) with
| true -> begin
m
end
| uu____1002 -> begin
n
end)) (Prims.parse_int "0") nargs)))
end)
end
| uu____1003 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_497 = (let _0_496 = (let _0_495 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat _0_495 " in universe context"))
in (Prims.strcat "Unexpected term " _0_496))
in ((_0_497), (t.FStar_Parser_AST.range))))))
end)))
in (aux t []))
end
| uu____1008 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_500 = (let _0_499 = (let _0_498 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat _0_498 " in universe context"))
in (Prims.strcat "Unexpected term " _0_499))
in ((_0_500), (t.FStar_Parser_AST.range))))))
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

let uu____1042 = (FStar_List.hd fields)
in (match (uu____1042) with
| (f, uu____1048) -> begin
(

let record = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f)
in (

let check_field = (fun uu____1055 -> (match (uu____1055) with
| (f', uu____1059) -> begin
(

let uu____1060 = (FStar_ToSyntax_Env.belongs_to_record env f' record)
in (match (uu____1060) with
| true -> begin
()
end
| uu____1061 -> begin
(

let msg = (FStar_Util.format3 "Field %s belongs to record type %s, whereas field %s does not" f.FStar_Ident.str record.FStar_ToSyntax_Env.typename.FStar_Ident.str f'.FStar_Ident.str)
in (Prims.raise (FStar_Errors.Error (((msg), (rg))))))
end))
end))
in ((let _0_501 = (FStar_List.tl fields)
in (FStar_List.iter check_field _0_501));
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
| FStar_Syntax_Syntax.Pat_cons (uu____1220, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out uu____1242 -> (match (uu____1242) with
| (p, uu____1248) -> begin
(let _0_502 = (pat_vars p)
in (FStar_Util.set_union out _0_502))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let xs = (pat_vars hd)
in (

let uu____1261 = (not ((FStar_Util.for_all (fun p -> (

let ys = (pat_vars p)
in ((FStar_Util.set_is_subset_of xs ys) && (FStar_Util.set_is_subset_of ys xs)))) tl)))
in (match (uu____1261) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Disjunctive pattern binds different variables in each case"), (p.FStar_Syntax_Syntax.p)))))
end
| uu____1264 -> begin
xs
end)))
end))
in (pat_vars p)))
in ((match (((is_mut), (p.FStar_Parser_AST.pat))) with
| ((false, _)) | ((true, FStar_Parser_AST.PatVar (_))) -> begin
()
end
| (true, uu____1268) -> begin
(Prims.raise (FStar_Errors.Error ((("let-mutable is for variables only"), (p.FStar_Parser_AST.prange)))))
end);
(

let push_bv_maybe_mut = (match (is_mut) with
| true -> begin
FStar_ToSyntax_Env.push_bv_mutable
end
| uu____1282 -> begin
FStar_ToSyntax_Env.push_bv
end)
in (

let resolvex = (fun l e x -> (

let uu____1296 = (FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))
in (match (uu____1296) with
| Some (y) -> begin
((l), (e), (y))
end
| uu____1304 -> begin
(

let uu____1306 = (push_bv_maybe_mut e x)
in (match (uu____1306) with
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
(let _0_505 = (let _0_504 = FStar_Parser_AST.PatVar ((let _0_503 = (FStar_Ident.id_of_text (FStar_Parser_AST.compile_op (Prims.parse_int "0") op))
in ((_0_503), (None))))
in {FStar_Parser_AST.pat = _0_504; FStar_Parser_AST.prange = p.FStar_Parser_AST.prange})
in (aux loc env _0_505))
end
| FStar_Parser_AST.PatOr ([]) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(

let uu____1366 = (aux loc env p)
in (match (uu____1366) with
| (loc, env, var, p, uu____1385) -> begin
(

let uu____1390 = (FStar_List.fold_left (fun uu____1403 p -> (match (uu____1403) with
| (loc, env, ps) -> begin
(

let uu____1426 = (aux loc env p)
in (match (uu____1426) with
| (loc, env, uu____1442, p, uu____1444) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (uu____1390) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in ((loc), (env), (var), (pat), (false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let uu____1488 = (aux loc env p)
in (match (uu____1488) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (uu____1513) -> begin
(failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t = (let _0_506 = (close_fun env t)
in (desugar_term env _0_506))
in LocalBinder ((((

let uu___225_1519 = x
in {FStar_Syntax_Syntax.ppname = uu___225_1519.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___225_1519.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (aq))))
end)
in ((loc), (env'), (binder), (p), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _0_507 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_0_507), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _0_508 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_0_508), (false))))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let uu____1545 = (resolvex loc env x)
in (match (uu____1545) with
| (loc, env, xbv) -> begin
(let _0_509 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc), (env), (LocalBinder (((xbv), (aq)))), (_0_509), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _0_510 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), ([])))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_0_510), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = uu____1582}, args) -> begin
(

let uu____1586 = (FStar_List.fold_right (fun arg uu____1604 -> (match (uu____1604) with
| (loc, env, args) -> begin
(

let uu____1634 = (aux loc env arg)
in (match (uu____1634) with
| (loc, env, uu____1652, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (uu____1586) with
| (loc, env, args) -> begin
(

let l = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _0_511 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_0_511), (false)))))
end))
end
| FStar_Parser_AST.PatApp (uu____1711) -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____1724 = (FStar_List.fold_right (fun pat uu____1738 -> (match (uu____1738) with
| (loc, env, pats) -> begin
(

let uu____1760 = (aux loc env pat)
in (match (uu____1760) with
| (loc, env, uu____1776, pat, uu____1778) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (uu____1724) with
| (loc, env, pats) -> begin
(

let pat = (let _0_517 = (let _0_516 = (pos_r (FStar_Range.end_range p.FStar_Parser_AST.prange))
in (let _0_515 = FStar_Syntax_Syntax.Pat_cons ((let _0_514 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_0_514), ([]))))
in (FStar_All.pipe_left _0_516 _0_515)))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _0_513 = FStar_Syntax_Syntax.Pat_cons ((let _0_512 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_0_512), ((((hd), (false)))::(((tl), (false)))::[]))))
in (FStar_All.pipe_left (pos_r r) _0_513)))) pats _0_517))
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc), (env), (LocalBinder (((x), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let uu____1865 = (FStar_List.fold_left (fun uu____1882 p -> (match (uu____1882) with
| (loc, env, pats) -> begin
(

let uu____1913 = (aux loc env p)
in (match (uu____1913) with
| (loc, env, uu____1931, pat, uu____1933) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (uu____1865) with
| (loc, env, args) -> begin
(

let args = (FStar_List.rev args)
in (

let l = (match (dep) with
| true -> begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
| uu____1996 -> begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end)
in (

let uu____2004 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) l)
in (match (uu____2004) with
| (constr, uu____2017) -> begin
(

let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____2020 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _0_518 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_0_518), (false)))))
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

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun uu____2060 -> (match (uu____2060) with
| (f, p) -> begin
((f.FStar_Ident.ident), (p))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____2075 -> (match (uu____2075) with
| (f, uu____2079) -> begin
(

let uu____2080 = (FStar_All.pipe_right fields (FStar_List.tryFind (fun uu____2092 -> (match (uu____2092) with
| (g, uu____2096) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.idText)
end))))
in (match (uu____2080) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (uu____2099, p) -> begin
p
end))
end))))
in (

let app = (let _0_521 = FStar_Parser_AST.PatApp ((let _0_520 = (let _0_519 = FStar_Parser_AST.PatName ((FStar_Ident.lid_of_ids (FStar_List.append record.FStar_ToSyntax_Env.typename.FStar_Ident.ns ((record.FStar_ToSyntax_Env.constrname)::[]))))
in (FStar_Parser_AST.mk_pattern _0_519 p.FStar_Parser_AST.prange))
in ((_0_520), (args))))
in (FStar_Parser_AST.mk_pattern _0_521 p.FStar_Parser_AST.prange))
in (

let uu____2105 = (aux loc env app)
in (match (uu____2105) with
| (env, e, b, p, uu____2124) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _0_525 = FStar_Syntax_Syntax.Pat_cons ((let _0_524 = (

let uu___226_2153 = fv
in (let _0_523 = Some (FStar_Syntax_Syntax.Record_ctor ((let _0_522 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_ToSyntax_Env.typename), (_0_522)))))
in {FStar_Syntax_Syntax.fv_name = uu___226_2153.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = uu___226_2153.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _0_523}))
in ((_0_524), (args))))
in (FStar_All.pipe_left pos _0_525))
end
| uu____2164 -> begin
p
end)
in ((env), (e), (b), (p), (false)))
end))))))
end))))
in (

let uu____2167 = (aux [] env p)
in (match (uu____2167) with
| (uu____2178, env, b, p, uu____2182) -> begin
((let _0_526 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _0_526));
((env), (b), (p));
)
end)))));
)))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p is_mut -> (

let mklet = (fun x -> (let _0_528 = LetBinder ((let _0_527 = (FStar_ToSyntax_Env.qualify env x)
in ((_0_527), (FStar_Syntax_Syntax.tun))))
in ((env), (_0_528), (None))))
in (match (top) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(mklet (FStar_Ident.id_of_text (FStar_Parser_AST.compile_op (Prims.parse_int "0") x)))
end
| FStar_Parser_AST.PatVar (x, uu____2217) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2221); FStar_Parser_AST.prange = uu____2222}, t) -> begin
(let _0_531 = LetBinder ((let _0_530 = (FStar_ToSyntax_Env.qualify env x)
in (let _0_529 = (desugar_term env t)
in ((_0_530), (_0_529)))))
in ((env), (_0_531), (None)))
end
| uu____2227 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end
| uu____2232 -> begin
(

let uu____2233 = (desugar_data_pat env p is_mut)
in (match (uu____2233) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| uu____2249 -> begin
Some (p)
end)
in ((env), (binder), (p)))
end))
end)))
and desugar_binding_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun uu____2253 env pat -> (

let uu____2256 = (desugar_data_pat env pat false)
in (match (uu____2256) with
| (env, uu____2263, pat) -> begin
((env), (pat))
end)))
and desugar_match_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let uu___227_2270 = env
in {FStar_ToSyntax_Env.curmodule = uu___227_2270.FStar_ToSyntax_Env.curmodule; FStar_ToSyntax_Env.curmonad = uu___227_2270.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = uu___227_2270.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = uu___227_2270.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = uu___227_2270.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = uu___227_2270.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = uu___227_2270.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = uu___227_2270.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = uu___227_2270.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.default_result_effect = uu___227_2270.FStar_ToSyntax_Env.default_result_effect; FStar_ToSyntax_Env.iface = uu___227_2270.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = uu___227_2270.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let uu___228_2274 = env
in {FStar_ToSyntax_Env.curmodule = uu___228_2274.FStar_ToSyntax_Env.curmodule; FStar_ToSyntax_Env.curmonad = uu___228_2274.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = uu___228_2274.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = uu___228_2274.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = uu___228_2274.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = uu___228_2274.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = uu___228_2274.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = uu___228_2274.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = uu___228_2274.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.default_result_effect = uu___228_2274.FStar_ToSyntax_Env.default_result_effect; FStar_ToSyntax_Env.iface = uu___228_2274.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = uu___228_2274.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_machine_integer : FStar_ToSyntax_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env repr uu____2277 range -> (match (uu____2277) with
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

let uu____2288 = (FStar_ToSyntax_Env.try_lookup_lid env lid)
in (match (uu____2288) with
| Some (lid) -> begin
(Prims.fst lid)
end
| None -> begin
(failwith (FStar_Util.format1 "%s not in scope\n" (FStar_Ident.text_of_lid lid)))
end))
in (

let repr = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (None)))))) None range)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_534 = (let _0_533 = (let _0_532 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr), (_0_532)))
in (_0_533)::[])
in ((lid), (_0_534)))))) None range)))))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env_t  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk setpos env l -> (

let uu____2348 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) l)
in (match (uu____2348) with
| (tm, mut) -> begin
(

let tm = (setpos tm)
in (match (mut) with
| true -> begin
(let _0_536 = FStar_Syntax_Syntax.Tm_meta ((let _0_535 = (mk_ref_read tm)
in ((_0_535), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval)))))
in (FStar_All.pipe_left mk _0_536))
end
| uu____2360 -> begin
tm
end))
end)))
and desugar_attributes : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (

let uu____2369 = (unparen t).FStar_Parser_AST.tm
in (match (uu____2369) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = uu____2370; FStar_Ident.ident = uu____2371; FStar_Ident.nsstr = uu____2372; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| uu____2374 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_538 = (let _0_537 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " _0_537))
in ((_0_538), (t.FStar_Parser_AST.range))))))
end)))
in (FStar_List.map desugar_attribute cattributes)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk = (fun e -> ((FStar_Syntax_Syntax.mk e) None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let uu___229_2402 = e
in {FStar_Syntax_Syntax.n = uu___229_2402.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___229_2402.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___229_2402.FStar_Syntax_Syntax.vars}))
in (

let uu____2409 = (unparen top).FStar_Parser_AST.tm
in (match (uu____2409) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (uu____2410) -> begin
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
| FStar_Parser_AST.Op ("*", (uu____2439)::(uu____2440)::[]) when (let _0_539 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _0_539 FStar_Option.isNone)) -> begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(let _0_540 = (flatten t1)
in (FStar_List.append _0_540 ((t2)::[])))
end
| uu____2452 -> begin
(t)::[]
end))
in (

let targs = (let _0_541 = (flatten (unparen top))
in (FStar_All.pipe_right _0_541 (FStar_List.map (fun t -> (FStar_Syntax_Syntax.as_arg (desugar_typ env t))))))
in (

let uu____2458 = (let _0_542 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) _0_542))
in (match (uu____2458) with
| (tup, uu____2467) -> begin
(mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _0_543 = (Prims.fst (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) a))
in (FStar_All.pipe_left setpos _0_543))
end
| FStar_Parser_AST.Uvar (u) -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected universe variable " (Prims.strcat (FStar_Ident.text_of_id u) " in non-universe context"))), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(

let uu____2481 = (op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)
in (match (uu____2481) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected or unbound operator: " s)), (top.FStar_Parser_AST.range)))))
end
| Some (op) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _0_544 = (desugar_term env t)
in ((_0_544), (None))))))
in (mk (FStar_Syntax_Syntax.Tm_app (((op), (args))))))
end
| uu____2508 -> begin
op
end)
end))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2509; FStar_Ident.ident = uu____2510; FStar_Ident.nsstr = uu____2511; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2513; FStar_Ident.ident = uu____2514; FStar_Ident.nsstr = uu____2515; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = uu____2517; FStar_Ident.ident = uu____2518; FStar_Ident.nsstr = uu____2519; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(mk (FStar_Syntax_Syntax.Tm_type ((desugar_universe t))))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2529; FStar_Ident.ident = uu____2530; FStar_Ident.nsstr = uu____2531; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2533; FStar_Ident.ident = uu____2534; FStar_Ident.nsstr = uu____2535; FStar_Ident.str = "True"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2537; FStar_Ident.ident = uu____2538; FStar_Ident.nsstr = uu____2539; FStar_Ident.str = "False"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = uu____2543}) when ((is_special_effect_combinator txt) && (FStar_ToSyntax_Env.is_effect_name env eff_name)) -> begin
(

let uu____2544 = (FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name)
in (match (uu____2544) with
| Some (ed) -> begin
(let _0_545 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" txt))) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.fvar _0_545 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
end
| None -> begin
(failwith "immpossible special_effect_combinator")
end))
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t2 = (desugar_term env t2)
in (

let uu____2550 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) ident)
in (match (uu____2550) with
| (t1, mut) -> begin
((match ((not (mut))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
end
| uu____2558 -> begin
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
(let _0_546 = (FStar_Syntax_Util.mk_field_projector_name_from_ident l i)
in (desugar_name mk setpos env _0_546))
end
| uu____2563 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_547 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((_0_547), (top.FStar_Parser_AST.range))))))
end))
end
| FStar_Parser_AST.Discrim (lid) -> begin
(

let uu____2565 = (FStar_ToSyntax_Env.try_lookup_datacon env lid)
in (match (uu____2565) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_548 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((_0_548), (top.FStar_Parser_AST.range))))))
end
| uu____2567 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (desugar_name mk setpos env lid'))
end))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(

let uu____2578 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____2578) with
| Some (head) -> begin
(

let uu____2581 = (let _0_549 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in ((_0_549), (true)))
in (match (uu____2581) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| uu____2596 -> begin
(

let args = (FStar_List.map (fun uu____2610 -> (match (uu____2610) with
| (t, imp) -> begin
(

let te = (desugar_term env t)
in (arg_withimp_e imp te))
end)) args)
in (

let app = (mk (FStar_Syntax_Syntax.Tm_app (((head), (args)))))
in (match (is_data) with
| true -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((app), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| uu____2630 -> begin
app
end)))
end)
end))
end
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Constructor " (Prims.strcat l.FStar_Ident.str " not found"))), (top.FStar_Parser_AST.range)))))
end))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let uu____2635 = (FStar_List.fold_left (fun uu____2652 b -> (match (uu____2652) with
| (env, tparams, typs) -> begin
(

let uu____2683 = (desugar_binder env b)
in (match (uu____2683) with
| (xopt, t) -> begin
(

let uu____2699 = (match (xopt) with
| None -> begin
(let _0_550 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env), (_0_550)))
end
| Some (x) -> begin
(FStar_ToSyntax_Env.push_bv env x)
end)
in (match (uu____2699) with
| (env, x) -> begin
(let _0_554 = (let _0_553 = (let _0_552 = (let _0_551 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_551))
in (_0_552)::[])
in (FStar_List.append typs _0_553))
in ((env), ((FStar_List.append tparams (((((

let uu___230_2727 = x
in {FStar_Syntax_Syntax.ppname = uu___230_2727.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___230_2727.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (None)))::[]))), (_0_554)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level None))::[])))
in (match (uu____2635) with
| (env, uu____2740, targs) -> begin
(

let uu____2752 = (let _0_555 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) _0_555))
in (match (uu____2752) with
| (tup, uu____2761) -> begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let uu____2769 = (uncurry binders t)
in (match (uu____2769) with
| (bs, t) -> begin
(

let rec aux = (fun env bs uu___208_2792 -> (match (uu___208_2792) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _0_556 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _0_556)))
end
| (hd)::tl -> begin
(

let mlenv = (FStar_ToSyntax_Env.default_ml env)
in (

let bb = (desugar_binder mlenv hd)
in (

let uu____2816 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (uu____2816) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(

let uu____2827 = (desugar_binder env b)
in (match (uu____2827) with
| (None, uu____2831) -> begin
(failwith "Missing binder in refinement")
end
| b -> begin
(

let uu____2837 = (as_binder env None b)
in (match (uu____2837) with
| ((x, uu____2841), env) -> begin
(

let f = (desugar_formula env f)
in (let _0_557 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _0_557)))
end))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let uu____2858 = (FStar_List.fold_left (fun uu____2865 pat -> (match (uu____2865) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (uu____2880, t) -> begin
(let _0_559 = (let _0_558 = (free_type_vars env t)
in (FStar_List.append _0_558 ftvs))
in ((env), (_0_559)))
end
| uu____2883 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (uu____2858) with
| (uu____2886, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (let _0_560 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append _0_560 binders))
in (

let rec aux = (fun env bs sc_pat_opt uu___209_2921 -> (match (uu___209_2921) with
| [] -> begin
(

let body = (desugar_term env body)
in (

let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(

let body = (let _0_562 = (let _0_561 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _0_561 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _0_562 body))
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (None), (body)))::[]))))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (setpos (no_annot_abs (FStar_List.rev bs) body))))
end
| (p)::rest -> begin
(

let uu____2995 = (desugar_binding_pat env p)
in (match (uu____2995) with
| (env, b, pat) -> begin
(

let uu____3007 = (match (b) with
| LetBinder (uu____3026) -> begin
(failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, uu____3057) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
Some ((let _0_563 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_0_563), (p))))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (uu____3104), uu____3105) -> begin
(

let tup2 = (let _0_564 = (FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _0_564 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_570 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _0_569 = (let _0_568 = (FStar_Syntax_Syntax.as_arg sc)
in (let _0_567 = (let _0_566 = (let _0_565 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_565))
in (_0_566)::[])
in (_0_568)::_0_567))
in ((_0_570), (_0_569))))))) None top.FStar_Parser_AST.range)
in (

let p = (let _0_571 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p), (false)))::[])))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _0_571))
in Some (((sc), (p))))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____3143, args), FStar_Syntax_Syntax.Pat_cons (uu____3145, pats)) -> begin
(

let tupn = (let _0_572 = (FStar_Syntax_Util.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _0_572 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_577 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _0_576 = (let _0_575 = (let _0_574 = (let _0_573 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_573))
in (_0_574)::[])
in (FStar_List.append args _0_575))
in ((_0_577), (_0_576)))))))
in (

let p = (let _0_578 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p), (false)))::[])))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _0_578))
in Some (((sc), (p))))))
end
| uu____3218 -> begin
(failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt)))
end)
in (match (uu____3007) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end)))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = rng; FStar_Parser_AST.level = uu____3261}, phi, uu____3263) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env phi)
in (

let a = (FStar_Ident.set_lid_range a rng)
in (mk (FStar_Syntax_Syntax.Tm_app ((let _0_584 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _0_583 = (let _0_582 = (FStar_Syntax_Syntax.as_arg phi)
in (let _0_581 = (let _0_580 = (let _0_579 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_579))
in (_0_580)::[])
in (_0_582)::_0_581))
in ((_0_584), (_0_583)))))))))
end
| FStar_Parser_AST.App (uu____3267, uu____3268, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (

let uu____3280 = (unparen e).FStar_Parser_AST.tm
in (match (uu____3280) with
| FStar_Parser_AST.App (e, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e))
end
| uu____3286 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_uinst (((head), (universes))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.App (uu____3289) -> begin
(

let rec aux = (fun args e -> (

let uu____3310 = (unparen e).FStar_Parser_AST.tm
in (match (uu____3310) with
| FStar_Parser_AST.App (e, t, imp) when (imp <> FStar_Parser_AST.UnivApp) -> begin
(

let arg = (let _0_585 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _0_585))
in (aux ((arg)::args) e))
end
| uu____3326 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((let _0_586 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((_0_586), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))))))
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

let ds_let_rec_or_app = (fun uu____3366 -> (

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun uu____3408 -> (match (uu____3408) with
| (p, def) -> begin
(

let uu____3422 = (is_app_pattern p)
in (match (uu____3422) with
| true -> begin
(let _0_587 = (destruct_app_pattern env top_level p)
in ((_0_587), (def)))
end
| uu____3439 -> begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _0_588 = (destruct_app_pattern env top_level p)
in ((_0_588), (def)))
end
| uu____3460 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____3474); FStar_Parser_AST.prange = uu____3475}, t) -> begin
(match (top_level) with
| true -> begin
(let _0_590 = (let _0_589 = FStar_Util.Inr ((FStar_ToSyntax_Env.qualify env id))
in ((_0_589), ([]), (Some (t))))
in ((_0_590), (def)))
end
| uu____3499 -> begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end)
end
| FStar_Parser_AST.PatVar (id, uu____3512) -> begin
(match (top_level) with
| true -> begin
(let _0_592 = (let _0_591 = FStar_Util.Inr ((FStar_ToSyntax_Env.qualify env id))
in ((_0_591), ([]), (None)))
in ((_0_592), (def)))
end
| uu____3535 -> begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end)
end
| uu____3547 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end))
end))))
in (

let uu____3557 = (FStar_List.fold_left (fun uu____3581 uu____3582 -> (match (((uu____3581), (uu____3582))) with
| ((env, fnames, rec_bindings), ((f, uu____3626, uu____3627), uu____3628)) -> begin
(

let uu____3668 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let uu____3682 = (FStar_ToSyntax_Env.push_bv env x)
in (match (uu____3682) with
| (env, xx) -> begin
(let _0_594 = (let _0_593 = (FStar_Syntax_Syntax.mk_binder xx)
in (_0_593)::rec_bindings)
in ((env), (FStar_Util.Inl (xx)), (_0_594)))
end))
end
| FStar_Util.Inr (l) -> begin
(let _0_595 = (FStar_ToSyntax_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((_0_595), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (uu____3668) with
| (env, lbname, rec_bindings) -> begin
((env), ((lbname)::fnames), (rec_bindings))
end))
end)) ((env), ([]), ([])) funs)
in (match (uu____3557) with
| (env', fnames, rec_bindings) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let rec_bindings = (FStar_List.rev rec_bindings)
in (

let desugar_one_def = (fun env lbname uu____3769 -> (match (uu____3769) with
| ((uu____3781, args, result_t), def) -> begin
(

let args = (FStar_All.pipe_right args (FStar_List.map replace_unit_pattern))
in (

let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
((

let uu____3807 = (is_comp_type env t)
in (match (uu____3807) with
| true -> begin
(

let uu____3808 = (FStar_All.pipe_right args (FStar_List.tryFind (fun x -> (not ((is_var_pattern x))))))
in (match (uu____3808) with
| None -> begin
()
end
| Some (p) -> begin
(Prims.raise (FStar_Errors.Error ((("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable"), (p.FStar_Parser_AST.prange)))))
end))
end
| uu____3814 -> begin
()
end));
(let _0_596 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) _0_596 FStar_Parser_AST.Expr));
)
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| uu____3816 -> begin
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
FStar_Util.Inr ((let _0_597 = (FStar_Syntax_Util.incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _0_597 None)))
end)
in (

let body = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.close rec_bindings body)
end
| uu____3827 -> begin
body
end)
in (mk_lb ((lbname), (FStar_Syntax_Syntax.tun), (body)))))))))
end))
in (

let lbs = (FStar_List.map2 (desugar_one_def (match (is_rec) with
| true -> begin
env'
end
| uu____3843 -> begin
env
end)) fnames funs)
in (

let body = (desugar_term env' body)
in (let _0_599 = FStar_Syntax_Syntax.Tm_let ((let _0_598 = (FStar_Syntax_Subst.close rec_bindings body)
in ((((is_rec), (lbs))), (_0_598))))
in (FStar_All.pipe_left mk _0_599)))))))
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
| uu____3870 -> begin
t1
end)
in (

let uu____3871 = (desugar_binding_pat_maybe_top top_level env pat is_mutable)
in (match (uu____3871) with
| (env, binder, pat) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body = (desugar_term env t2)
in (

let fv = (let _0_600 = (FStar_Syntax_Util.incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _0_600 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]))), (body)))))))
end
| LocalBinder (x, uu____3899) -> begin
(

let body = (desugar_term env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((let _0_603 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _0_602 = (let _0_601 = (FStar_Syntax_Util.branch ((pat), (None), (body)))
in (_0_601)::[])
in ((_0_603), (_0_602))))))) None body.FStar_Syntax_Syntax.pos)
end)
in (let _0_607 = FStar_Syntax_Syntax.Tm_let ((let _0_606 = (let _0_605 = (let _0_604 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_604)::[])
in (FStar_Syntax_Subst.close _0_605 body))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t1))))::[]))), (_0_606))))
in (FStar_All.pipe_left mk _0_607))))
end)
in (match (is_mutable) with
| true -> begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc))))))
end
| uu____3940 -> begin
tm
end))
end))))))
in (

let uu____3941 = (is_rec || (is_app_pattern pat))
in (match (uu____3941) with
| true -> begin
(ds_let_rec_or_app ())
end
| uu____3942 -> begin
(ds_non_rec pat _snd body)
end)))))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (mk (FStar_Syntax_Syntax.Tm_match ((let _0_616 = (desugar_term env t1)
in (let _0_615 = (let _0_614 = (let _0_609 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _0_608 = (desugar_term env t2)
in ((_0_609), (None), (_0_608))))
in (let _0_613 = (let _0_612 = (let _0_611 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _0_610 = (desugar_term env t3)
in ((_0_611), (None), (_0_610))))
in (_0_612)::[])
in (_0_614)::_0_613))
in ((_0_616), (_0_615))))))))
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

let desugar_branch = (fun uu____4039 -> (match (uu____4039) with
| (pat, wopt, b) -> begin
(

let uu____4049 = (desugar_match_pat env pat)
in (match (uu____4049) with
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
in (let _0_619 = FStar_Syntax_Syntax.Tm_match ((let _0_618 = (desugar_term env e)
in (let _0_617 = (FStar_List.map desugar_branch branches)
in ((_0_618), (_0_617)))))
in (FStar_All.pipe_left mk _0_619)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(

let env = (FStar_ToSyntax_Env.default_ml env)
in (

let c = (desugar_comp t.FStar_Parser_AST.range true env t)
in (

let annot = (

let uu____4080 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____4080) with
| true -> begin
FStar_Util.Inl ((FStar_Syntax_Util.comp_result c))
end
| uu____4091 -> begin
FStar_Util.Inr (c)
end))
in (let _0_621 = FStar_Syntax_Syntax.Tm_ascribed ((let _0_620 = (desugar_term env e)
in ((_0_620), (annot), (None))))
in (FStar_All.pipe_left mk _0_621)))))
end
| FStar_Parser_AST.Record (uu____4105, []) -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let uu____4126 = (FStar_List.hd fields)
in (match (uu____4126) with
| (f, uu____4133) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun uu____4157 -> (match (uu____4157) with
| (g, uu____4161) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| Some (uu____4165, e) -> begin
((fn), (e))
end
| None -> begin
(match (xopt) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_622 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_ToSyntax_Env.typename.FStar_Ident.str)
in ((_0_622), (top.FStar_Parser_AST.range))))))
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
FStar_Parser_AST.Construct ((let _0_625 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____4191 -> (match (uu____4191) with
| (f, uu____4197) -> begin
(let _0_624 = (let _0_623 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _0_623))
in ((_0_624), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (_0_625))))
end
| Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (let _0_626 = FStar_Parser_AST.Var ((FStar_Ident.lid_of_ids ((x)::[])))
in (FStar_Parser_AST.mk_term _0_626 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = FStar_Parser_AST.Record ((let _0_627 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____4218 -> (match (uu____4218) with
| (f, uu____4224) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (_0_627))))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____4236; FStar_Syntax_Syntax.pos = uu____4237; FStar_Syntax_Syntax.vars = uu____4238}, args); FStar_Syntax_Syntax.tk = uu____4240; FStar_Syntax_Syntax.pos = uu____4241; FStar_Syntax_Syntax.vars = uu____4242}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e = (let _0_631 = FStar_Syntax_Syntax.Tm_app ((let _0_630 = (let _0_629 = Some (FStar_Syntax_Syntax.Record_ctor ((let _0_628 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_ToSyntax_Env.typename), (_0_628)))))
in (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant _0_629))
in ((_0_630), (args))))
in (FStar_All.pipe_left mk _0_631))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| uu____4286 -> begin
e
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let uu____4289 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f)
in (match (uu____4289) with
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
| uu____4301 -> begin
None
end)
in (let _0_635 = FStar_Syntax_Syntax.Tm_app ((let _0_634 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projname (FStar_Ident.range_of_lid f)) FStar_Syntax_Syntax.Delta_equational qual)
in (let _0_633 = (let _0_632 = (FStar_Syntax_Syntax.as_arg e)
in (_0_632)::[])
in ((_0_634), (_0_633)))))
in (FStar_All.pipe_left mk _0_635)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| uu____4307 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| uu____4308 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Let (uu____4309, uu____4310, uu____4311) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QForall (uu____4318, uu____4319, uu____4320) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QExists (uu____4327, uu____4328, uu____4329) -> begin
(failwith "Not implemented yet")
end)))))
and desugar_args : FStar_ToSyntax_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____4353 -> (match (uu____4353) with
| (a, imp) -> begin
(let _0_636 = (desugar_term env a)
in (arg_withimp_e imp _0_636))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Errors.Error (((msg), (r))))))
in (

let is_requires = (fun uu____4378 -> (match (uu____4378) with
| (t, uu____4382) -> begin
(

let uu____4383 = (unparen t).FStar_Parser_AST.tm
in (match (uu____4383) with
| FStar_Parser_AST.Requires (uu____4384) -> begin
true
end
| uu____4388 -> begin
false
end))
end))
in (

let is_ensures = (fun uu____4394 -> (match (uu____4394) with
| (t, uu____4398) -> begin
(

let uu____4399 = (unparen t).FStar_Parser_AST.tm
in (match (uu____4399) with
| FStar_Parser_AST.Ensures (uu____4400) -> begin
true
end
| uu____4404 -> begin
false
end))
end))
in (

let is_app = (fun head uu____4413 -> (match (uu____4413) with
| (t, uu____4417) -> begin
(

let uu____4418 = (unparen t).FStar_Parser_AST.tm
in (match (uu____4418) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = uu____4420; FStar_Parser_AST.level = uu____4421}, uu____4422, uu____4423) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| uu____4424 -> begin
false
end))
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t -> (

let uu____4442 = (head_and_args t)
in (match (uu____4442) with
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
(let _0_637 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes env) l)
in ((_0_637), (args)))
end
| FStar_Parser_AST.Name (l) when ((let _0_638 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals _0_638 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((let _0_639 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals _0_639 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)), ([]))), ((((t), (FStar_Parser_AST.Nothing)))::[]))
end
| uu____4644 when default_ok -> begin
(((((FStar_Ident.set_lid_range env.FStar_ToSyntax_Env.default_result_effect head.FStar_Parser_AST.range)), ([]))), ((((t), (FStar_Parser_AST.Nothing)))::[]))
end
| uu____4656 -> begin
(fail (let _0_640 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _0_640)))
end)
end)))
in (

let uu____4665 = (pre_process_comp_typ t)
in (match (uu____4665) with
| ((eff, cattributes), args) -> begin
((match (((FStar_List.length args) = (Prims.parse_int "0"))) with
| true -> begin
(fail (let _0_641 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _0_641)))
end
| uu____4695 -> begin
()
end);
(

let uu____4696 = (let _0_643 = (FStar_List.hd args)
in (let _0_642 = (FStar_List.tl args)
in ((_0_643), (_0_642))))
in (match (uu____4696) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (Prims.fst result_arg))
in (

let rest = (desugar_args env rest)
in (

let uu____4733 = (FStar_All.pipe_right rest (FStar_List.partition (fun uu____4771 -> (match (uu____4771) with
| (t, uu____4778) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____4786; FStar_Syntax_Syntax.pos = uu____4787; FStar_Syntax_Syntax.vars = uu____4788}, (uu____4789)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| uu____4811 -> begin
false
end)
end))))
in (match (uu____4733) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun uu____4854 -> (match (uu____4854) with
| (t, uu____4861) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____4868, ((arg, uu____4870))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| uu____4892 -> begin
(failwith "impos")
end)
end))))
in (

let no_additional_args = ((((FStar_List.length decreases_clause) = (Prims.parse_int "0")) && ((FStar_List.length rest) = (Prims.parse_int "0"))) && ((FStar_List.length cattributes) = (Prims.parse_int "0")))
in (match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end
| uu____4907 -> begin
(match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end
| uu____4910 -> begin
(

let flags = (match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid)) with
| true -> begin
(FStar_Syntax_Syntax.LEMMA)::[]
end
| uu____4914 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____4916 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_ML_lid)) with
| true -> begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end
| uu____4918 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____4920 -> begin
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

let pattern = (let _0_644 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_644 ((FStar_Syntax_Syntax.U_zero)::[])))
in ((FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (Some (FStar_Syntax_Syntax.imp_tag))))::[])) None pat.FStar_Syntax_Syntax.pos)))
end
| uu____5001 -> begin
pat
end)
in (let _0_648 = (let _0_647 = (let _0_646 = (let _0_645 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))))) None pat.FStar_Syntax_Syntax.pos)
in ((_0_645), (aq)))
in (_0_646)::[])
in (ens)::_0_647)
in (req)::_0_648))
end
| uu____5039 -> begin
rest
end)
end
| uu____5046 -> begin
rest
end)
in (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = []; FStar_Syntax_Syntax.effect_name = eff; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = rest; FStar_Syntax_Syntax.flags = (FStar_List.append flags decreases_clause)}))))
end)
end)))
end))))
end));
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
| uu____5055 -> begin
None
end))
in (

let mk = (fun t -> ((FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let uu___231_5096 = t
in {FStar_Syntax_Syntax.n = uu___231_5096.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___231_5096.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___231_5096.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let uu___232_5126 = b
in {FStar_Parser_AST.b = uu___232_5126.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___232_5126.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___232_5126.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _0_649 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _0_649)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(

let uu____5167 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____5167) with
| (env, a) -> begin
(

let a = (

let uu___233_5175 = a
in {FStar_Syntax_Syntax.ppname = uu___233_5175.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___233_5175.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats = (desugar_pats env pats)
in (

let body = (desugar_formula env body)
in (

let body = (match (pats) with
| [] -> begin
body
end
| uu____5188 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_pattern (pats))))))
end)
in (

let body = (let _0_652 = (let _0_651 = (let _0_650 = (FStar_Syntax_Syntax.mk_binder a)
in (_0_650)::[])
in (no_annot_abs _0_651 body))
in (FStar_All.pipe_left setpos _0_652))
in (let _0_656 = FStar_Syntax_Syntax.Tm_app ((let _0_655 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (let _0_654 = (let _0_653 = (FStar_Syntax_Syntax.as_arg body)
in (_0_653)::[])
in ((_0_655), (_0_654)))))
in (FStar_All.pipe_left mk _0_656)))))))
end))
end
| uu____5204 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (let _0_658 = (q ((rest), (pats), (body)))
in (let _0_657 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _0_658 _0_657 FStar_Parser_AST.Formula)))
in (let _0_659 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term _0_659 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| uu____5260 -> begin
(failwith "impossible")
end))
in (

let uu____5262 = (unparen f).FStar_Parser_AST.tm
in (match (uu____5262) with
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
in (let _0_660 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _0_660)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _0_661 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _0_661)))
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
| uu____5336 -> begin
(desugar_term env f)
end)))))))))
and typars_of_binders : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let uu____5340 = (FStar_List.fold_left (fun uu____5353 b -> (match (uu____5353) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let uu___234_5381 = b
in {FStar_Parser_AST.b = uu___234_5381.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___234_5381.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___234_5381.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(

let uu____5391 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____5391) with
| (env, a) -> begin
(

let a = (

let uu___235_5403 = a
in {FStar_Syntax_Syntax.ppname = uu___235_5403.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___235_5403.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env), ((((a), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| uu____5412 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (uu____5340) with
| (env, tpars) -> begin
((env), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _0_662 = (desugar_typ env t)
in ((Some (x)), (_0_662)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _0_663 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown))) None x.FStar_Ident.idRange)
in ((Some (x)), (_0_663)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _0_664 = (desugar_typ env t)
in ((None), (_0_664)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators = (fun quals env t tps k datas -> (

let quals = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___210_5528 -> (match (uu___210_5528) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| uu____5529 -> begin
false
end))))
in (

let quals = (fun q -> (

let uu____5537 = ((FStar_All.pipe_left Prims.op_Negation env.FStar_ToSyntax_Env.iface) || env.FStar_ToSyntax_Env.admitted_iface)
in (match (uu____5537) with
| true -> begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end
| uu____5539 -> begin
(FStar_List.append q quals)
end)))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in FStar_Syntax_Syntax.Sig_declare_typ ((let _0_665 = (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in ((disc_name), ([]), (FStar_Syntax_Syntax.tun), (_0_665), ((FStar_Ident.range_of_lid disc_name))))))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_ToSyntax_Env.env  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (let _0_672 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____5577 -> (match (uu____5577) with
| (x, uu____5582) -> begin
(

let uu____5583 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____5583) with
| (field_name, uu____5588) -> begin
(

let only_decl = (((let _0_666 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _0_666)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (FStar_Options.dont_gen_projectors (FStar_ToSyntax_Env.current_module env).FStar_Ident.str))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(let _0_667 = (FStar_List.filter (fun uu___211_5599 -> (match (uu___211_5599) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____5600 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::_0_667)
end
| uu____5601 -> begin
q
end))
in (

let quals = (

let iquals = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___212_5608 -> (match (uu___212_5608) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| uu____5609 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun), (quals), ((FStar_Ident.range_of_lid field_name))))
in (match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____5614 -> begin
(

let dd = (

let uu____5616 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____5616) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____5618 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lb = (let _0_668 = FStar_Util.Inr ((FStar_Syntax_Syntax.lid_as_fv field_name dd None))
in {FStar_Syntax_Syntax.lbname = _0_668; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun})
in (

let impl = FStar_Syntax_Syntax.Sig_let ((let _0_671 = (let _0_670 = (let _0_669 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _0_669 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_0_670)::[])
in ((((false), ((lb)::[]))), (p), (_0_671), (quals), ([]))))
in (match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____5636 -> begin
(decl)::(impl)::[]
end))))
end))))))
end))
end))))
in (FStar_All.pipe_right _0_672 FStar_List.flatten))))


let mk_data_projector_names = (fun iquals env uu____5657 -> (match (uu____5657) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____5665, t, uu____5667, n, quals, uu____5670, uu____5671) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let uu____5676 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____5676) with
| (formals, uu____5686) -> begin
(match (formals) with
| [] -> begin
[]
end
| uu____5700 -> begin
(

let filter_records = (fun uu___213_5708 -> (match (uu___213_5708) with
| FStar_Syntax_Syntax.RecordConstructor (uu____5710, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| uu____5717 -> begin
None
end))
in (

let fv_qual = (

let uu____5719 = (FStar_Util.find_map quals filter_records)
in (match (uu____5719) with
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
| uu____5725 -> begin
iquals
end)
in (

let uu____5726 = (FStar_Util.first_N n formals)
in (match (uu____5726) with
| (uu____5738, rest) -> begin
(mk_indexed_projector_names iquals fv_qual env lid rest)
end)))))
end)
end))
end
| uu____5752 -> begin
[]
end)
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = (

let uu____5790 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____5790) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract ((FStar_Syntax_Util.incr_delta_qualifier t))
end
| uu____5792 -> begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end))
in (

let lb = (let _0_676 = FStar_Util.Inr ((FStar_Syntax_Syntax.lid_as_fv lid dd None))
in (let _0_675 = (let _0_673 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _0_673))
in (let _0_674 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _0_676; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _0_675; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _0_674})))
in FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (rng), (lids), (quals), ([]))))))


let rec desugar_tycon : FStar_ToSyntax_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (

let tycon_id = (fun uu___214_5824 -> (match (uu___214_5824) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _0_677 = FStar_Parser_AST.Var ((FStar_Ident.lid_of_ids ((x)::[])))
in (FStar_Parser_AST.mk_term _0_677 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| uu____5884 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _0_679 = FStar_Parser_AST.App ((let _0_678 = (binder_to_term b)
in ((out), (_0_678), ((imp_of_aqual b)))))
in (FStar_Parser_AST.mk_term _0_679 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun uu___215_5893 -> (match (uu___215_5893) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun uu____5922 -> (match (uu____5922) with
| (x, t, uu____5929) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (let _0_681 = (let _0_680 = FStar_Parser_AST.Var ((FStar_Ident.lid_of_ids ((id)::[])))
in (FStar_Parser_AST.mk_term _0_680 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders _0_681 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type_level)
in (let _0_682 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____5969 -> (match (uu____5969) with
| (x, uu____5975, uu____5976) -> begin
(FStar_Syntax_Util.unmangle_field_name x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (_0_682)))))))
end
| uu____5979 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals uu___216_6001 -> (match (uu___216_6001) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let uu____6015 = (typars_of_binders _env binders)
in (match (uu____6015) with
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

let tconstr = (let _0_684 = (let _0_683 = FStar_Parser_AST.Var ((FStar_Ident.lid_of_ids ((id)::[])))
in (FStar_Parser_AST.mk_term _0_683 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders _0_684 binders))
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
| uu____6053 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env bs -> (

let uu____6079 = (FStar_List.fold_left (fun uu____6095 uu____6096 -> (match (((uu____6095), (uu____6096))) with
| ((env, tps), (x, imp)) -> begin
(

let uu____6144 = (FStar_ToSyntax_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (uu____6144) with
| (env, y) -> begin
((env), ((((y), (imp)))::tps))
end))
end)) ((env), ([])) bs)
in (match (uu____6079) with
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
| uu____6205 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt)))
in (

let uu____6210 = (desugar_abstract_tc quals env [] tc)
in (match (uu____6210) with
| (uu____6217, uu____6218, se, uu____6220) -> begin
(

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, uu____6223, typars, k, [], [], quals, rng) -> begin
(

let quals = (

let uu____6234 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (match (uu____6234) with
| true -> begin
quals
end
| uu____6237 -> begin
((let _0_686 = (FStar_Range.string_of_range rng)
in (let _0_685 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _0_686 _0_685)));
(FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals;
)
end))
in (

let t = (match (typars) with
| [] -> begin
k
end
| uu____6242 -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((let _0_687 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (_0_687)))))) None rng)
end)
in FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t), (quals), (rng)))))
end
| uu____6253 -> begin
se
end)
in (

let env = (FStar_ToSyntax_Env.push_sigelt env se)
in ((env), ((se)::[]))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let uu____6264 = (typars_of_binders env binders)
in (match (uu____6264) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
(

let uu____6284 = (FStar_Util.for_some (fun uu___217_6285 -> (match (uu___217_6285) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| uu____6286 -> begin
false
end)) quals)
in (match (uu____6284) with
| true -> begin
FStar_Syntax_Syntax.teff
end
| uu____6287 -> begin
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

let uu____6292 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___218_6294 -> (match (uu___218_6294) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| uu____6295 -> begin
false
end))))
in (match (uu____6292) with
| true -> begin
quals
end
| uu____6297 -> begin
(match ((t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula)) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____6299 -> begin
quals
end)
end))
in (

let se = (

let uu____6301 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Effect))
in (match (uu____6301) with
| true -> begin
(

let uu____6303 = (

let uu____6307 = (unparen t).FStar_Parser_AST.tm
in (match (uu____6307) with
| FStar_Parser_AST.Construct (head, args) -> begin
(

let uu____6319 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____6335))::args_rev -> begin
(

let uu____6342 = (unparen last_arg).FStar_Parser_AST.tm
in (match (uu____6342) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____6357 -> begin
(([]), (args))
end))
end
| uu____6362 -> begin
(([]), (args))
end)
in (match (uu____6319) with
| (cattributes, args) -> begin
(let _0_688 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head), (args)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (_0_688)))
end))
end
| uu____6387 -> begin
((t), ([]))
end))
in (match (uu____6303) with
| (t, cattributes) -> begin
(

let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (

let typars = (FStar_Syntax_Subst.close_binders typars)
in (

let c = (FStar_Syntax_Subst.close_comp typars c)
in FStar_Syntax_Syntax.Sig_effect_abbrev ((let _0_690 = (FStar_ToSyntax_Env.qualify env id)
in (let _0_689 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___219_6403 -> (match (uu___219_6403) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| uu____6404 -> begin
true
end))))
in ((_0_690), ([]), (typars), (c), (_0_689), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c))), (rng))))))))
end))
end
| uu____6405 -> begin
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
| (FStar_Parser_AST.TyconRecord (uu____6410))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let uu____6423 = (tycon_record_as_variant trec)
in (match (uu____6423) with
| (t, fs) -> begin
(let _0_693 = (let _0_692 = FStar_Syntax_Syntax.RecordType ((let _0_691 = (FStar_Ident.ids_of_lid (FStar_ToSyntax_Env.current_module env))
in ((_0_691), (fs))))
in (_0_692)::quals)
in (desugar_tycon env rng _0_693 ((t)::[])))
end)))
end
| (uu____6435)::uu____6436 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let uu____6523 = et
in (match (uu____6523) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (uu____6637) -> begin
(

let trec = tc
in (

let uu____6650 = (tycon_record_as_variant trec)
in (match (uu____6650) with
| (t, fs) -> begin
(let _0_696 = (let _0_695 = FStar_Syntax_Syntax.RecordType ((let _0_694 = (FStar_Ident.ids_of_lid (FStar_ToSyntax_Env.current_module env))
in ((_0_694), (fs))))
in (_0_695)::quals)
in (collect_tcs _0_696 ((env), (tcs)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let uu____6726 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____6726) with
| (env, uu____6757, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let uu____6835 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____6835) with
| (env, uu____6866, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (binders), (t), (quals))))::tcs))
end))
end
| uu____6930 -> begin
(failwith "Unrecognized mutual type definition")
end)
end)))
in (

let uu____6954 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (uu____6954) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun uu___221_7192 -> (match (uu___221_7192) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, uu____7224, uu____7225, uu____7226, uu____7227), binders, t, quals) -> begin
(

let t = (

let uu____7260 = (typars_of_binders env binders)
in (match (uu____7260) with
| (env, tpars) -> begin
(

let uu____7277 = (push_tparams env tpars)
in (match (uu____7277) with
| (env_tps, tpars) -> begin
(

let t = (desugar_typ env_tps t)
in (

let tpars = (FStar_Syntax_Subst.close_binders tpars)
in (FStar_Syntax_Subst.close tpars t)))
end))
end))
in (let _0_698 = (let _0_697 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in (([]), (_0_697)))
in (_0_698)::[]))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, uu____7320, tags, uu____7322), constrs, tconstr, quals) -> begin
(

let tycon = ((tname), (tpars), (k))
in (

let uu____7370 = (push_tparams env tpars)
in (match (uu____7370) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun uu____7405 -> (match (uu____7405) with
| (x, uu____7413) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let uu____7417 = (let _0_705 = (FStar_All.pipe_right constrs (FStar_List.map (fun uu____7483 -> (match (uu____7483) with
| (id, topt, uu____7500, of_notation) -> begin
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
| uu____7509 -> begin
(match (topt) with
| None -> begin
(failwith "Impossible")
end
| Some (t) -> begin
t
end)
end)
in (

let t = (let _0_700 = (FStar_ToSyntax_Env.default_total env_tps)
in (let _0_699 = (close env_tps t)
in (desugar_term _0_700 _0_699)))
in (

let name = (FStar_ToSyntax_Env.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun uu___220_7517 -> (match (uu___220_7517) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| uu____7524 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (let _0_704 = (let _0_703 = FStar_Syntax_Syntax.Sig_datacon ((let _0_702 = (let _0_701 = (FStar_Syntax_Syntax.mk_Total (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders))
in (FStar_Syntax_Util.arrow data_tpars _0_701))
in ((name), (univs), (_0_702), (tname), (ntps), (quals), (mutuals), (rng))))
in ((tps), (_0_703)))
in ((name), (_0_704))))))))
end))))
in (FStar_All.pipe_left FStar_List.split _0_705))
in (match (uu____7417) with
| (constrNames, constrs) -> begin
((([]), (FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))))::constrs
end)))
end)))
end
| uu____7589 -> begin
(failwith "impossible")
end))))
in (

let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (

let uu____7637 = (let _0_706 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals _0_706 rng))
in (match (uu____7637) with
| (bundle, abbrevs) -> begin
(

let env = (FStar_ToSyntax_Env.push_sigelt env0 bundle)
in (

let env = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env abbrevs)
in (

let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projector_names quals env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun uu___222_7673 -> (match (uu___222_7673) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, uu____7676, tps, k, uu____7679, constrs, quals, uu____7682) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::quals
end
| uu____7695 -> begin
quals
end)
in (mk_data_discriminators quals env tname tps k constrs))
end
| uu____7696 -> begin
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

let uu____7714 = (FStar_List.fold_left (fun uu____7721 b -> (match (uu____7721) with
| (env, binders) -> begin
(

let uu____7733 = (desugar_binder env b)
in (match (uu____7733) with
| (Some (a), k) -> begin
(

let uu____7743 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____7743) with
| (env, a) -> begin
(let _0_708 = (let _0_707 = (FStar_Syntax_Syntax.mk_binder (

let uu___236_7752 = a
in {FStar_Syntax_Syntax.ppname = uu___236_7752.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___236_7752.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_0_707)::binders)
in ((env), (_0_708)))
end))
end
| uu____7753 -> begin
(Prims.raise (FStar_Errors.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) binders)
in (match (uu____7714) with
| (env, binders) -> begin
((env), ((FStar_List.rev binders)))
end)))


let rec desugar_effect : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  Prims.bool  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_kind eff_decls actions for_free -> (

let env0 = env
in (

let monad_env = (FStar_ToSyntax_Env.enter_monad_scope env eff_name)
in (

let uu____7847 = (desugar_binders monad_env eff_binders)
in (match (uu____7847) with
| (env, binders) -> begin
(

let eff_k = (let _0_709 = (FStar_ToSyntax_Env.default_total env)
in (desugar_term _0_709 eff_kind))
in (

let uu____7859 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun uu____7870 decl -> (match (uu____7870) with
| (env, out) -> begin
(

let uu____7882 = (desugar_decl env decl)
in (match (uu____7882) with
| (env, ses) -> begin
(let _0_711 = (let _0_710 = (FStar_List.hd ses)
in (_0_710)::out)
in ((env), (_0_711)))
end))
end)) ((env), ([]))))
in (match (uu____7859) with
| (env, decls) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let actions = (FStar_All.pipe_right actions (FStar_List.map (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____7905, ((FStar_Parser_AST.TyconAbbrev (name, uu____7907, uu____7908, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (uu____7909, ((def, uu____7911))::((cps_type, uu____7913))::[]); FStar_Parser_AST.range = uu____7914; FStar_Parser_AST.level = uu____7915}), uu____7916))::[]) when (not (for_free)) -> begin
(let _0_716 = (FStar_ToSyntax_Env.qualify env name)
in (let _0_715 = (let _0_712 = (desugar_term env def)
in (FStar_Syntax_Subst.close binders _0_712))
in (let _0_714 = (let _0_713 = (desugar_typ env cps_type)
in (FStar_Syntax_Subst.close binders _0_713))
in {FStar_Syntax_Syntax.action_name = _0_716; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _0_715; FStar_Syntax_Syntax.action_typ = _0_714})))
end
| FStar_Parser_AST.Tycon (uu____7942, ((FStar_Parser_AST.TyconAbbrev (name, uu____7944, uu____7945, defn), uu____7947))::[]) when for_free -> begin
(let _0_719 = (FStar_ToSyntax_Env.qualify env name)
in (let _0_718 = (let _0_717 = (desugar_term env defn)
in (FStar_Syntax_Subst.close binders _0_717))
in {FStar_Syntax_Syntax.action_name = _0_719; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _0_718; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
end
| uu____7964 -> begin
(Prims.raise (FStar_Errors.Error ((("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples)."), (d.FStar_Parser_AST.drange)))))
end))))
in (

let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (

let lookup = (fun s -> (

let l = (FStar_ToSyntax_Env.qualify env (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange))))
in (let _0_721 = (let _0_720 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _0_720))
in (([]), (_0_721)))))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (Some (mname))) quals)
in (

let se = (match (for_free) with
| true -> begin
(

let dummy_tscheme = (let _0_722 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (([]), (_0_722)))
in FStar_Syntax_Syntax.Sig_new_effect_for_free ((let _0_726 = (let _0_725 = (Prims.snd (lookup "repr"))
in (let _0_724 = (lookup "return")
in (let _0_723 = (lookup "bind")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = _0_725; FStar_Syntax_Syntax.return_repr = _0_724; FStar_Syntax_Syntax.bind_repr = _0_723; FStar_Syntax_Syntax.actions = actions})))
in ((_0_726), (d.FStar_Parser_AST.drange)))))
end
| uu____7997 -> begin
(

let rr = ((FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right qualifiers FStar_Syntax_Syntax.contains_reflectable))
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in FStar_Syntax_Syntax.Sig_new_effect ((let _0_741 = (let _0_740 = (lookup "return_wp")
in (let _0_739 = (lookup "bind_wp")
in (let _0_738 = (lookup "if_then_else")
in (let _0_737 = (lookup "ite_wp")
in (let _0_736 = (lookup "stronger")
in (let _0_735 = (lookup "close_wp")
in (let _0_734 = (lookup "assert_p")
in (let _0_733 = (lookup "assume_p")
in (let _0_732 = (lookup "null_wp")
in (let _0_731 = (lookup "trivial")
in (let _0_730 = (match (rr) with
| true -> begin
(let _0_727 = (lookup "repr")
in (FStar_All.pipe_left Prims.snd _0_727))
end
| uu____8010 -> begin
FStar_Syntax_Syntax.tun
end)
in (let _0_729 = (match (rr) with
| true -> begin
(lookup "return")
end
| uu____8011 -> begin
un_ts
end)
in (let _0_728 = (match (rr) with
| true -> begin
(lookup "bind")
end
| uu____8012 -> begin
un_ts
end)
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = _0_740; FStar_Syntax_Syntax.bind_wp = _0_739; FStar_Syntax_Syntax.if_then_else = _0_738; FStar_Syntax_Syntax.ite_wp = _0_737; FStar_Syntax_Syntax.stronger = _0_736; FStar_Syntax_Syntax.close_wp = _0_735; FStar_Syntax_Syntax.assert_p = _0_734; FStar_Syntax_Syntax.assume_p = _0_733; FStar_Syntax_Syntax.null_wp = _0_732; FStar_Syntax_Syntax.trivial = _0_731; FStar_Syntax_Syntax.repr = _0_730; FStar_Syntax_Syntax.return_repr = _0_729; FStar_Syntax_Syntax.bind_repr = _0_728; FStar_Syntax_Syntax.actions = actions})))))))))))))
in ((_0_741), (d.FStar_Parser_AST.drange))))))
end)
in (

let env = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right actions (FStar_List.fold_left (fun env a -> (let _0_742 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env _0_742))) env))
in (

let env = (

let uu____8019 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____8019) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let refl_decl = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]), (d.FStar_Parser_AST.drange)))
in (FStar_ToSyntax_Env.push_sigelt env refl_decl)))
end
| uu____8024 -> begin
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

let uu____8047 = (desugar_binders env eff_binders)
in (match (uu____8047) with
| (env, binders) -> begin
(

let uu____8058 = (

let uu____8067 = (head_and_args defn)
in (match (uu____8067) with
| (head, args) -> begin
(

let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_defn env) l)
end
| uu____8091 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_745 = (let _0_744 = (let _0_743 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat _0_743 " not found"))
in (Prims.strcat "Effect " _0_744))
in ((_0_745), (d.FStar_Parser_AST.drange))))))
end)
in (

let uu____8092 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____8108))::args_rev -> begin
(

let uu____8115 = (unparen last_arg).FStar_Parser_AST.tm
in (match (uu____8115) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____8130 -> begin
(([]), (args))
end))
end
| uu____8135 -> begin
(([]), (args))
end)
in (match (uu____8092) with
| (cattributes, args) -> begin
(let _0_747 = (desugar_args env args)
in (let _0_746 = (desugar_attributes env cattributes)
in ((ed), (_0_747), (_0_746))))
end)))
end))
in (match (uu____8058) with
| (ed, args, cattributes) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let sub = (fun uu____8192 -> (match (uu____8192) with
| (uu____8199, x) -> begin
(

let uu____8203 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (uu____8203) with
| (edb, x) -> begin
((match (((FStar_List.length args) <> (FStar_List.length edb))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end
| uu____8221 -> begin
()
end);
(

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _0_749 = (let _0_748 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _0_748))
in (([]), (_0_749))));
)
end))
end))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let ed = (let _0_769 = (let _0_750 = (trans_qual (Some (mname)))
in (FStar_List.map _0_750 quals))
in (let _0_768 = (Prims.snd (sub (([]), (ed.FStar_Syntax_Syntax.signature))))
in (let _0_767 = (sub ed.FStar_Syntax_Syntax.ret_wp)
in (let _0_766 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _0_765 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _0_764 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _0_763 = (sub ed.FStar_Syntax_Syntax.stronger)
in (let _0_762 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _0_761 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _0_760 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _0_759 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _0_758 = (sub ed.FStar_Syntax_Syntax.trivial)
in (let _0_757 = (Prims.snd (sub (([]), (ed.FStar_Syntax_Syntax.repr))))
in (let _0_756 = (sub ed.FStar_Syntax_Syntax.return_repr)
in (let _0_755 = (sub ed.FStar_Syntax_Syntax.bind_repr)
in (let _0_754 = (FStar_List.map (fun action -> (let _0_753 = (FStar_ToSyntax_Env.qualify env action.FStar_Syntax_Syntax.action_unqualified_name)
in (let _0_752 = (Prims.snd (sub (([]), (action.FStar_Syntax_Syntax.action_defn))))
in (let _0_751 = (Prims.snd (sub (([]), (action.FStar_Syntax_Syntax.action_typ))))
in {FStar_Syntax_Syntax.action_name = _0_753; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _0_752; FStar_Syntax_Syntax.action_typ = _0_751})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = _0_769; FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _0_768; FStar_Syntax_Syntax.ret_wp = _0_767; FStar_Syntax_Syntax.bind_wp = _0_766; FStar_Syntax_Syntax.if_then_else = _0_765; FStar_Syntax_Syntax.ite_wp = _0_764; FStar_Syntax_Syntax.stronger = _0_763; FStar_Syntax_Syntax.close_wp = _0_762; FStar_Syntax_Syntax.assert_p = _0_761; FStar_Syntax_Syntax.assume_p = _0_760; FStar_Syntax_Syntax.null_wp = _0_759; FStar_Syntax_Syntax.trivial = _0_758; FStar_Syntax_Syntax.repr = _0_757; FStar_Syntax_Syntax.return_repr = _0_756; FStar_Syntax_Syntax.bind_repr = _0_755; FStar_Syntax_Syntax.actions = _0_754}))))))))))))))))
in (

let se = (build_sigelt ed d.FStar_Parser_AST.drange)
in (

let monad_env = env
in (

let env = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun env a -> (let _0_770 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env _0_770))) env))
in (

let env = (

let uu____8243 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____8243) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let refl_decl = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]), (d.FStar_Parser_AST.drange)))
in (FStar_ToSyntax_Env.push_sigelt env refl_decl)))
end
| uu____8249 -> begin
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
| FStar_Parser_AST.Fsdoc (uu____8266) -> begin
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
(let _0_771 = (FStar_ToSyntax_Env.push_module_abbrev env x l)
in ((_0_771), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, tcs) -> begin
(

let quals = (match (is_effect) with
| true -> begin
(FStar_Parser_AST.Effect_qual)::d.FStar_Parser_AST.quals
end
| uu____8292 -> begin
d.FStar_Parser_AST.quals
end)
in (

let tcs = (FStar_List.map (fun uu____8298 -> (match (uu____8298) with
| (x, uu____8303) -> begin
x
end)) tcs)
in (let _0_772 = (FStar_List.map (trans_qual None) quals)
in (desugar_tycon env d.FStar_Parser_AST.drange _0_772 tcs))))
end
| FStar_Parser_AST.TopLevelLet (isrec, lets) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let attrs = d.FStar_Parser_AST.attrs
in (

let attrs = (FStar_List.map (desugar_term env) attrs)
in (

let uu____8318 = (let _0_773 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _0_773)).FStar_Syntax_Syntax.n
in (match (uu____8318) with
| FStar_Syntax_Syntax.Tm_let (lbs, uu____8325) -> begin
(

let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals = (match (quals) with
| (uu____8345)::uu____8346 -> begin
(FStar_List.map (trans_qual None) quals)
end
| uu____8348 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun uu___223_8352 -> (match (uu___223_8352) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (uu____8354); FStar_Syntax_Syntax.lbunivs = uu____8355; FStar_Syntax_Syntax.lbtyp = uu____8356; FStar_Syntax_Syntax.lbeff = uu____8357; FStar_Syntax_Syntax.lbdef = uu____8358} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____8365; FStar_Syntax_Syntax.lbtyp = uu____8366; FStar_Syntax_Syntax.lbeff = uu____8367; FStar_Syntax_Syntax.lbdef = uu____8368} -> begin
(FStar_ToSyntax_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals = (

let uu____8380 = (FStar_All.pipe_right lets (FStar_Util.for_some (fun uu____8386 -> (match (uu____8386) with
| (uu____8389, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end))))
in (match (uu____8380) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____8392 -> begin
quals
end))
in (

let lbs = (

let uu____8397 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____8397) with
| true -> begin
(let _0_774 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu___237_8409 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let uu___238_8410 = fv
in {FStar_Syntax_Syntax.fv_name = uu___238_8410.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = uu___238_8410.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = uu___237_8409.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___237_8409.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___237_8409.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___237_8409.FStar_Syntax_Syntax.lbdef})))))
in (((Prims.fst lbs)), (_0_774)))
end
| uu____8414 -> begin
lbs
end))
in (

let s = FStar_Syntax_Syntax.Sig_let ((let _0_775 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in ((lbs), (d.FStar_Parser_AST.drange), (_0_775), (quals), (attrs))))
in (

let env = (FStar_ToSyntax_Env.push_sigelt env s)
in ((env), ((s)::[]))))))))
end
| uu____8431 -> begin
(failwith "Desugaring a let did not produce a let")
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
in (let _0_778 = (let _0_777 = FStar_Syntax_Syntax.Sig_assume ((let _0_776 = (FStar_ToSyntax_Env.qualify env id)
in ((_0_776), (f), ((FStar_Syntax_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange))))
in (_0_777)::[])
in ((env), (_0_778))))
end
| FStar_Parser_AST.Val (id, t) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let t = (let _0_779 = (close_fun env t)
in (desugar_term env _0_779))
in (

let quals = (match ((env.FStar_ToSyntax_Env.iface && env.FStar_ToSyntax_Env.admitted_iface)) with
| true -> begin
(FStar_Parser_AST.Assumption)::quals
end
| uu____8450 -> begin
quals
end)
in (

let se = FStar_Syntax_Syntax.Sig_declare_typ ((let _0_781 = (FStar_ToSyntax_Env.qualify env id)
in (let _0_780 = (FStar_List.map (trans_qual None) quals)
in ((_0_781), ([]), (t), (_0_780), (d.FStar_Parser_AST.drange)))))
in (

let env = (FStar_ToSyntax_Env.push_sigelt env se)
in ((env), ((se)::[])))))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(

let uu____8458 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (match (uu____8458) with
| (t, uu____8466) -> begin
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

let t = (let _0_785 = (let _0_782 = (FStar_Syntax_Syntax.null_binder t)
in (_0_782)::[])
in (let _0_784 = (let _0_783 = (Prims.fst (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _0_783))
in (FStar_Syntax_Util.arrow _0_785 _0_784)))
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

let uu____8521 = (desugar_binders env binders)
in (match (uu____8521) with
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

let uu____8581 = (FStar_ToSyntax_Env.try_lookup_effect_name env l)
in (match (uu____8581) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_788 = (let _0_787 = (let _0_786 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat _0_786 " not found"))
in (Prims.strcat "Effect name " _0_787))
in ((_0_788), (d.FStar_Parser_AST.drange))))))
end
| Some (l) -> begin
l
end)))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let uu____8586 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(let _0_790 = Some ((let _0_789 = (desugar_term env t)
in (([]), (_0_789))))
in ((_0_790), (None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(let _0_794 = Some ((let _0_791 = (desugar_term env wp)
in (([]), (_0_791))))
in (let _0_793 = Some ((let _0_792 = (desugar_term env t)
in (([]), (_0_792))))
in ((_0_794), (_0_793))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(let _0_796 = Some ((let _0_795 = (desugar_term env t)
in (([]), (_0_795))))
in ((None), (_0_796)))
end)
in (match (uu____8586) with
| (lift_wp, lift) -> begin
(

let se = FStar_Syntax_Syntax.Sig_sub_effect ((({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun uu____8692 d -> (match (uu____8692) with
| (env, sigelts) -> begin
(

let uu____8704 = (desugar_decl env d)
in (match (uu____8704) with
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

let uu____8746 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _0_797 = (FStar_ToSyntax_Env.prepare_module_or_interface true admitted env mname)
in ((_0_797), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _0_798 = (FStar_ToSyntax_Env.prepare_module_or_interface false false env mname)
in ((_0_798), (mname), (decls), (false)))
end)
in (match (uu____8746) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let uu____8788 = (desugar_decls env decls)
in (match (uu____8788) with
| (env, sigelts) -> begin
(

let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in ((env), (modul), (pop_when_done)))
end))
end))))


let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (

let m = (

let uu____8813 = ((FStar_Options.interactive ()) && (let _0_799 = (FStar_Util.get_file_extension (FStar_List.hd (FStar_Options.file_list ())))
in (_0_799 = "fsti")))
in (match (uu____8813) with
| true -> begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface (((mname), (decls), (true)))
end
| FStar_Parser_AST.Interface (mname, uu____8820, uu____8821) -> begin
(failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end
| uu____8824 -> begin
m
end))
in (

let uu____8825 = (desugar_modul_common curmod env m)
in (match (uu____8825) with
| (x, y, uu____8833) -> begin
((x), (y))
end))))


let desugar_modul : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun env m -> (

let uu____8844 = (desugar_modul_common None env m)
in (match (uu____8844) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_ToSyntax_Env.finish_module_or_interface env modul)
in ((

let uu____8855 = (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____8855) with
| true -> begin
(let _0_800 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _0_800))
end
| uu____8856 -> begin
()
end));
(let _0_801 = (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end
| uu____8857 -> begin
env
end)
in ((_0_801), (modul)));
))
end)))


let desugar_file : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (

let uu____8867 = (FStar_List.fold_left (fun uu____8874 m -> (match (uu____8874) with
| (env, mods) -> begin
(

let uu____8886 = (desugar_modul env m)
in (match (uu____8886) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (uu____8867) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_ToSyntax_Env.env  ->  FStar_ToSyntax_Env.env = (fun m en -> (

let uu____8910 = (FStar_ToSyntax_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (uu____8910) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt (

let uu___239_8916 = en
in {FStar_ToSyntax_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_ToSyntax_Env.curmonad = uu___239_8916.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = uu___239_8916.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = uu___239_8916.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = uu___239_8916.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = uu___239_8916.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = uu___239_8916.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = uu___239_8916.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = uu___239_8916.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.default_result_effect = uu___239_8916.FStar_ToSyntax_Env.default_result_effect; FStar_ToSyntax_Env.iface = uu___239_8916.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = uu___239_8916.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = uu___239_8916.FStar_ToSyntax_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (

let env = (FStar_ToSyntax_Env.finish_module_or_interface en m)
in (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name env)
end
| uu____8918 -> begin
env
end)))
end)))




