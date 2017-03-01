
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
end
| FStar_Parser_AST.LightOff -> begin
FStar_Syntax_Syntax.LightOff
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


let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (

let uu____88 = (

let uu____89 = (FStar_Ident.lid_of_path (("Type0")::[]) r)
in FStar_Parser_AST.Name (uu____89))
in (FStar_Parser_AST.mk_term uu____88 r FStar_Parser_AST.Kind)))


let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (

let uu____93 = (

let uu____94 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (uu____94))
in (FStar_Parser_AST.mk_term uu____93 r FStar_Parser_AST.Kind)))


let rec is_comp_type : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> (match (t.FStar_Parser_AST.tm) with
| (FStar_Parser_AST.Name (l)) | (FStar_Parser_AST.Construct (l, _)) -> begin
(

let uu____106 = (FStar_ToSyntax_Env.try_lookup_effect_name env l)
in (FStar_All.pipe_right uu____106 FStar_Option.isSome))
end
| FStar_Parser_AST.App (head, uu____110, uu____111) -> begin
(is_comp_type env head)
end
| (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) | (FStar_Parser_AST.LetOpen (_, t)) -> begin
(is_comp_type env t)
end
| uu____115 -> begin
false
end))


let unit_ty : FStar_Parser_AST.term = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) FStar_Range.dummyRange FStar_Parser_AST.Type_level)


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (

let uu____125 = (

let uu____127 = (

let uu____128 = (

let uu____131 = (FStar_Parser_AST.compile_op n s)
in ((uu____131), (r)))
in (FStar_Ident.mk_ident uu____128))
in (uu____127)::[])
in (FStar_All.pipe_right uu____125 FStar_Ident.lid_of_ids)))


let op_as_term : FStar_ToSyntax_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (

let r = (fun l dd -> (

let uu____155 = (

let uu____156 = (FStar_Syntax_Syntax.lid_as_fv (FStar_Ident.set_lid_range l rng) dd None)
in (FStar_All.pipe_right uu____156 FStar_Syntax_Syntax.fv_to_tm))
in Some (uu____155)))
in (

let fallback = (fun uu____161 -> (match (s) with
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

let uu____163 = (FStar_Options.ml_ish ())
in (match (uu____163) with
| true -> begin
(r FStar_Syntax_Const.list_append_lid FStar_Syntax_Syntax.Delta_equational)
end
| uu____165 -> begin
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
| uu____166 -> begin
None
end))
in (

let uu____167 = (

let uu____171 = (compile_op_lid arity s rng)
in (FStar_ToSyntax_Env.try_lookup_lid env uu____171))
in (match (uu____167) with
| Some (t) -> begin
Some ((Prims.fst t))
end
| uu____178 -> begin
(fallback ())
end)))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (

let uu____188 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) uu____188)))


let rec free_type_vars_b : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_ToSyntax_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (uu____213) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____216 = (FStar_ToSyntax_Env.push_bv env x)
in (match (uu____216) with
| (env, uu____223) -> begin
((env), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (uu____225, term) -> begin
(

let uu____227 = (free_type_vars env term)
in ((env), (uu____227)))
end
| FStar_Parser_AST.TAnnotated (id, uu____231) -> begin
(

let uu____232 = (FStar_ToSyntax_Env.push_bv env id)
in (match (uu____232) with
| (env, uu____239) -> begin
((env), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____242 = (free_type_vars env t)
in ((env), (uu____242)))
end))
and free_type_vars : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (

let uu____247 = (

let uu____248 = (unparen t)
in uu____248.FStar_Parser_AST.tm)
in (match (uu____247) with
| FStar_Parser_AST.Labeled (uu____250) -> begin
(failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____256 = (FStar_ToSyntax_Env.try_lookup_id env a)
in (match (uu____256) with
| None -> begin
(a)::[]
end
| uu____263 -> begin
[]
end))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Projector (_)) | (FStar_Parser_AST.Discrim (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Assign (_, t)) | (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (uu____281, ts) -> begin
(FStar_List.collect (fun uu____291 -> (match (uu____291) with
| (t, uu____296) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (uu____297, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, uu____303) -> begin
(

let uu____304 = (free_type_vars env t1)
in (

let uu____306 = (free_type_vars env t2)
in (FStar_List.append uu____304 uu____306)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(

let uu____310 = (free_type_vars_b env b)
in (match (uu____310) with
| (env, f) -> begin
(

let uu____319 = (free_type_vars env t)
in (FStar_List.append f uu____319))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(

let uu____327 = (FStar_List.fold_left (fun uu____334 binder -> (match (uu____334) with
| (env, free) -> begin
(

let uu____346 = (free_type_vars_b env binder)
in (match (uu____346) with
| (env, f) -> begin
((env), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (uu____327) with
| (env, free) -> begin
(

let uu____364 = (free_type_vars env body)
in (FStar_List.append free uu____364))
end))
end
| FStar_Parser_AST.Project (t, uu____367) -> begin
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

let uu____406 = (

let uu____407 = (unparen t)
in uu____407.FStar_Parser_AST.tm)
in (match (uu____406) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| uu____431 -> begin
((t), (args))
end)))
in (aux [] t)))


let close : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____445 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____445))
in (match (((FStar_List.length ftv) = (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____451 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____457 = (

let uu____458 = (

let uu____461 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____461)))
in FStar_Parser_AST.TAnnotated (uu____458))
in (FStar_Parser_AST.mk_binder uu____457 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end)))


let close_fun : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____472 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____472))
in (match (((FStar_List.length ftv) = (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____478 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____484 = (

let uu____485 = (

let uu____488 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____488)))
in FStar_Parser_AST.TAnnotated (uu____485))
in (FStar_Parser_AST.mk_binder uu____484 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (Some (FStar_Parser_AST.Implicit)))))))
in (

let t = (

let uu____490 = (

let uu____491 = (unparen t)
in uu____491.FStar_Parser_AST.tm)
in (match (uu____490) with
| FStar_Parser_AST.Product (uu____492) -> begin
t
end
| uu____496 -> begin
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
| uu____517 -> begin
((bs), (t))
end))


let rec is_var_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatTvar (_, _)) | (FStar_Parser_AST.PatVar (_, _)) -> begin
true
end
| FStar_Parser_AST.PatAscribed (p, uu____529) -> begin
(is_var_pattern p)
end
| uu____530 -> begin
false
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, uu____535) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____536); FStar_Parser_AST.prange = uu____537}, uu____538) -> begin
true
end
| uu____544 -> begin
false
end))


let replace_unit_pattern : FStar_Parser_AST.pattern  ->  FStar_Parser_AST.pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatConst (FStar_Const.Const_unit) -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatAscribed ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)), (unit_ty)))) p.FStar_Parser_AST.prange)
end
| uu____548 -> begin
p
end))


let rec destruct_app_pattern : FStar_ToSyntax_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let uu____574 = (destruct_app_pattern env is_top_level p)
in (match (uu____574) with
| (name, args, uu____591) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____605); FStar_Parser_AST.prange = uu____606}, args) when is_top_level -> begin
(

let uu____612 = (

let uu____615 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____615))
in ((uu____612), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____621); FStar_Parser_AST.prange = uu____622}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| uu____632 -> begin
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
| FStar_Parser_AST.PatVar (x, uu____667) -> begin
(FStar_Util.set_add x acc)
end
| (FStar_Parser_AST.PatList (pats)) | (FStar_Parser_AST.PatTuple (pats, _)) | (FStar_Parser_AST.PatOr (pats)) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatRecord (guarded_pats) -> begin
(

let uu____680 = (FStar_List.map Prims.snd guarded_pats)
in (gather_pattern_bound_vars_from_list uu____680))
end
| FStar_Parser_AST.PatAscribed (pat, uu____685) -> begin
(gather_pattern_bound_vars_maybe_top acc pat)
end)))


let gather_pattern_bound_vars : FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (

let acc = (FStar_Util.new_set (fun id1 id2 -> (match ((id1.FStar_Ident.idText = id2.FStar_Ident.idText)) with
| true -> begin
(Prims.parse_int "0")
end
| uu____693 -> begin
(Prims.parse_int "1")
end)) (fun uu____694 -> (Prims.parse_int "0")))
in (fun p -> (gather_pattern_bound_vars_maybe_top acc p)))

type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term)


let uu___is_LocalBinder : bnd  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LocalBinder (_0) -> begin
true
end
| uu____712 -> begin
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
| uu____732 -> begin
false
end))


let __proj__LetBinder__item___0 : bnd  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| LetBinder (_0) -> begin
_0
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun uu___188_750 -> (match (uu___188_750) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| uu____755 -> begin
(failwith "Impossible")
end))


let as_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_ToSyntax_Env.env) = (fun env imp uu___189_772 -> (match (uu___189_772) with
| (None, k) -> begin
(

let uu____781 = (FStar_Syntax_Syntax.null_binder k)
in ((uu____781), (env)))
end
| (Some (a), k) -> begin
(

let uu____785 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____785) with
| (env, a) -> begin
(((((

let uu___210_796 = a
in {FStar_Syntax_Syntax.ppname = uu___210_796.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___210_796.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env))
end))
end))


type env_t =
FStar_ToSyntax_Env.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : ((FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.letbinding = (fun uu____809 -> (match (uu____809) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))


let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))


let mk_ref_read = (fun tm -> (

let tm' = (

let uu____865 = (

let uu____875 = (

let uu____876 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm uu____876))
in (

let uu____877 = (

let uu____883 = (

let uu____888 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____888)))
in (uu____883)::[])
in ((uu____875), (uu____877))))
in FStar_Syntax_Syntax.Tm_app (uu____865))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc = (fun tm -> (

let tm' = (

let uu____922 = (

let uu____932 = (

let uu____933 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm uu____933))
in (

let uu____934 = (

let uu____940 = (

let uu____945 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____945)))
in (uu____940)::[])
in ((uu____932), (uu____934))))
in FStar_Syntax_Syntax.Tm_app (uu____922))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign = (fun t1 t2 pos -> (

let tm = (

let uu____993 = (

let uu____1003 = (

let uu____1004 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1004))
in (

let uu____1005 = (

let uu____1011 = (

let uu____1016 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (uu____1016)))
in (

let uu____1019 = (

let uu____1025 = (

let uu____1030 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (uu____1030)))
in (uu____1025)::[])
in (uu____1011)::uu____1019))
in ((uu____1003), (uu____1005))))
in FStar_Syntax_Syntax.Tm_app (uu____993))
in (FStar_Syntax_Syntax.mk tm None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun uu___190_1056 -> (match (uu___190_1056) with
| ("repr") | ("post") | ("pre") | ("wp") -> begin
true
end
| uu____1057 -> begin
false
end))


let rec sum_to_universe : FStar_Syntax_Syntax.universe  ->  Prims.int  ->  FStar_Syntax_Syntax.universe = (fun u n -> (match ((n = (Prims.parse_int "0"))) with
| true -> begin
u
end
| uu____1064 -> begin
(

let uu____1065 = (sum_to_universe u (n - (Prims.parse_int "1")))
in FStar_Syntax_Syntax.U_succ (uu____1065))
end))


let int_to_universe : Prims.int  ->  FStar_Syntax_Syntax.universe = (fun n -> (sum_to_universe FStar_Syntax_Syntax.U_zero n))


let rec desugar_maybe_non_constant_universe : FStar_Parser_AST.term  ->  (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun t -> (

let uu____1076 = (

let uu____1077 = (unparen t)
in uu____1077.FStar_Parser_AST.tm)
in (match (uu____1076) with
| FStar_Parser_AST.Wild -> begin
(

let uu____1080 = (

let uu____1081 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (uu____1081))
in FStar_Util.Inr (uu____1080))
end
| FStar_Parser_AST.Uvar (u) -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_name (u))
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____1087)) -> begin
(

let n = (FStar_Util.int_of_string repr)
in ((match ((n < (Prims.parse_int "0"))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Negative universe constant  are not supported : " repr)), (t.FStar_Parser_AST.range)))))
end
| uu____1096 -> begin
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
(

let uu____1130 = (sum_to_universe u n)
in FStar_Util.Inr (uu____1130))
end
| (FStar_Util.Inr (u1), FStar_Util.Inr (u2)) -> begin
(

let uu____1137 = (

let uu____1138 = (

let uu____1141 = (

let uu____1142 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "This universe might contain a sum of two universe variables " uu____1142))
in ((uu____1141), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____1138))
in (Prims.raise uu____1137))
end)))
end
| FStar_Parser_AST.App (uu____1145) -> begin
(

let rec aux = (fun t univargs -> (

let uu____1164 = (

let uu____1165 = (unparen t)
in uu____1165.FStar_Parser_AST.tm)
in (match (uu____1164) with
| FStar_Parser_AST.App (t, targ, uu____1170) -> begin
(

let uarg = (desugar_maybe_non_constant_universe targ)
in (aux t ((uarg)::univargs)))
end
| FStar_Parser_AST.Var (max_lid) -> begin
(match ((FStar_List.existsb (fun uu___191_1182 -> (match (uu___191_1182) with
| FStar_Util.Inr (uu____1185) -> begin
true
end
| uu____1186 -> begin
false
end)) univargs)) with
| true -> begin
(

let uu____1189 = (

let uu____1190 = (FStar_List.map (fun uu___192_1194 -> (match (uu___192_1194) with
| FStar_Util.Inl (n) -> begin
(int_to_universe n)
end
| FStar_Util.Inr (u) -> begin
u
end)) univargs)
in FStar_Syntax_Syntax.U_max (uu____1190))
in FStar_Util.Inr (uu____1189))
end
| uu____1199 -> begin
(

let nargs = (FStar_List.map (fun uu___193_1204 -> (match (uu___193_1204) with
| FStar_Util.Inl (n) -> begin
n
end
| FStar_Util.Inr (uu____1208) -> begin
(failwith "impossible")
end)) univargs)
in (

let uu____1209 = (FStar_List.fold_left (fun m n -> (match ((m > n)) with
| true -> begin
m
end
| uu____1212 -> begin
n
end)) (Prims.parse_int "0") nargs)
in FStar_Util.Inl (uu____1209)))
end)
end
| uu____1213 -> begin
(

let uu____1214 = (

let uu____1215 = (

let uu____1218 = (

let uu____1219 = (

let uu____1220 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat uu____1220 " in universe context"))
in (Prims.strcat "Unexpected term " uu____1219))
in ((uu____1218), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____1215))
in (Prims.raise uu____1214))
end)))
in (aux t []))
end
| uu____1225 -> begin
(

let uu____1226 = (

let uu____1227 = (

let uu____1230 = (

let uu____1231 = (

let uu____1232 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat uu____1232 " in universe context"))
in (Prims.strcat "Unexpected term " uu____1231))
in ((uu____1230), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____1227))
in (Prims.raise uu____1226))
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

let uu____1266 = (FStar_List.hd fields)
in (match (uu____1266) with
| (f, uu____1272) -> begin
(

let record = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f)
in (

let check_field = (fun uu____1279 -> (match (uu____1279) with
| (f', uu____1283) -> begin
(

let uu____1284 = (FStar_ToSyntax_Env.belongs_to_record env f' record)
in (match (uu____1284) with
| true -> begin
()
end
| uu____1285 -> begin
(

let msg = (FStar_Util.format3 "Field %s belongs to record type %s, whereas field %s does not" f.FStar_Ident.str record.FStar_ToSyntax_Env.typename.FStar_Ident.str f'.FStar_Ident.str)
in (Prims.raise (FStar_Errors.Error (((msg), (rg))))))
end))
end))
in ((

let uu____1288 = (FStar_List.tl fields)
in (FStar_List.iter check_field uu____1288));
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
| FStar_Syntax_Syntax.Pat_cons (uu____1448, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out uu____1470 -> (match (uu____1470) with
| (p, uu____1476) -> begin
(

let uu____1477 = (pat_vars p)
in (FStar_Util.set_union out uu____1477))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let xs = (pat_vars hd)
in (

let uu____1491 = (

let uu____1492 = (FStar_Util.for_all (fun p -> (

let ys = (pat_vars p)
in ((FStar_Util.set_is_subset_of xs ys) && (FStar_Util.set_is_subset_of ys xs)))) tl)
in (not (uu____1492)))
in (match (uu____1491) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Disjunctive pattern binds different variables in each case"), (p.FStar_Syntax_Syntax.p)))))
end
| uu____1495 -> begin
xs
end)))
end))
in (pat_vars p)))
in ((match (((is_mut), (p.FStar_Parser_AST.pat))) with
| ((false, _)) | ((true, FStar_Parser_AST.PatVar (_))) -> begin
()
end
| (true, uu____1499) -> begin
(Prims.raise (FStar_Errors.Error ((("let-mutable is for variables only"), (p.FStar_Parser_AST.prange)))))
end);
(

let push_bv_maybe_mut = (match (is_mut) with
| true -> begin
FStar_ToSyntax_Env.push_bv_mutable
end
| uu____1513 -> begin
FStar_ToSyntax_Env.push_bv
end)
in (

let resolvex = (fun l e x -> (

let uu____1527 = (FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))
in (match (uu____1527) with
| Some (y) -> begin
((l), (e), (y))
end
| uu____1535 -> begin
(

let uu____1537 = (push_bv_maybe_mut e x)
in (match (uu____1537) with
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
(

let uu____1586 = (

let uu____1587 = (

let uu____1588 = (

let uu____1592 = (

let uu____1593 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") op)
in (FStar_Ident.id_of_text uu____1593))
in ((uu____1592), (None)))
in FStar_Parser_AST.PatVar (uu____1588))
in {FStar_Parser_AST.pat = uu____1587; FStar_Parser_AST.prange = p.FStar_Parser_AST.prange})
in (aux loc env uu____1586))
end
| FStar_Parser_AST.PatOr ([]) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(

let uu____1605 = (aux loc env p)
in (match (uu____1605) with
| (loc, env, var, p, uu____1624) -> begin
(

let uu____1629 = (FStar_List.fold_left (fun uu____1642 p -> (match (uu____1642) with
| (loc, env, ps) -> begin
(

let uu____1665 = (aux loc env p)
in (match (uu____1665) with
| (loc, env, uu____1681, p, uu____1683) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (uu____1629) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in ((loc), (env), (var), (pat), (false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let uu____1727 = (aux loc env p)
in (match (uu____1727) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (uu____1752) -> begin
(failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t = (

let uu____1758 = (close_fun env t)
in (desugar_term env uu____1758))
in ((match ((match (x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| uu____1760 -> begin
true
end)) with
| true -> begin
(

let uu____1761 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____1762 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____1763 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3_warning "Multiple ascriptions for %s in pattern, type %s was shadowed by %s" uu____1761 uu____1762 uu____1763))))
end
| uu____1764 -> begin
()
end);
LocalBinder ((((

let uu___211_1765 = x
in {FStar_Syntax_Syntax.ppname = uu___211_1765.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___211_1765.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (aq)));
))
end)
in ((loc), (env'), (binder), (p), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1769 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env), (LocalBinder (((x), (None)))), (uu____1769), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1779 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env), (LocalBinder (((x), (None)))), (uu____1779), (false))))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let uu____1797 = (resolvex loc env x)
in (match (uu____1797) with
| (loc, env, xbv) -> begin
(

let uu____1811 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc), (env), (LocalBinder (((xbv), (aq)))), (uu____1811), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1822 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), ([])))))
in ((loc), (env), (LocalBinder (((x), (None)))), (uu____1822), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = uu____1840}, args) -> begin
(

let uu____1844 = (FStar_List.fold_right (fun arg uu____1862 -> (match (uu____1862) with
| (loc, env, args) -> begin
(

let uu____1892 = (aux loc env arg)
in (match (uu____1892) with
| (loc, env, uu____1910, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (uu____1844) with
| (loc, env, args) -> begin
(

let l = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1959 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (uu____1959), (false)))))
end))
end
| FStar_Parser_AST.PatApp (uu____1972) -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____1985 = (FStar_List.fold_right (fun pat uu____1999 -> (match (uu____1999) with
| (loc, env, pats) -> begin
(

let uu____2021 = (aux loc env pat)
in (match (uu____2021) with
| (loc, env, uu____2037, pat, uu____2039) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (uu____1985) with
| (loc, env, pats) -> begin
(

let pat = (

let uu____2073 = (

let uu____2076 = (

let uu____2081 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r uu____2081))
in (

let uu____2082 = (

let uu____2083 = (

let uu____2091 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____2091), ([])))
in FStar_Syntax_Syntax.Pat_cons (uu____2083))
in (FStar_All.pipe_left uu____2076 uu____2082)))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (

let uu____2114 = (

let uu____2115 = (

let uu____2123 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____2123), ((((hd), (false)))::(((tl), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (uu____2115))
in (FStar_All.pipe_left (pos_r r) uu____2114)))) pats uu____2073))
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc), (env), (LocalBinder (((x), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let uu____2155 = (FStar_List.fold_left (fun uu____2172 p -> (match (uu____2172) with
| (loc, env, pats) -> begin
(

let uu____2203 = (aux loc env p)
in (match (uu____2203) with
| (loc, env, uu____2221, pat, uu____2223) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (uu____2155) with
| (loc, env, args) -> begin
(

let args = (FStar_List.rev args)
in (

let l = (match (dep) with
| true -> begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
| uu____2286 -> begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end)
in (

let uu____2294 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) l)
in (match (uu____2294) with
| (constr, uu____2307) -> begin
(

let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____2310 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____2312 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (uu____2312), (false)))))
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

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun uu____2353 -> (match (uu____2353) with
| (f, p) -> begin
((f.FStar_Ident.ident), (p))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____2368 -> (match (uu____2368) with
| (f, uu____2372) -> begin
(

let uu____2373 = (FStar_All.pipe_right fields (FStar_List.tryFind (fun uu____2385 -> (match (uu____2385) with
| (g, uu____2389) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.idText)
end))))
in (match (uu____2373) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (uu____2392, p) -> begin
p
end))
end))))
in (

let app = (

let uu____2397 = (

let uu____2398 = (

let uu____2402 = (

let uu____2403 = (

let uu____2404 = (FStar_Ident.lid_of_ids (FStar_List.append record.FStar_ToSyntax_Env.typename.FStar_Ident.ns ((record.FStar_ToSyntax_Env.constrname)::[])))
in FStar_Parser_AST.PatName (uu____2404))
in (FStar_Parser_AST.mk_pattern uu____2403 p.FStar_Parser_AST.prange))
in ((uu____2402), (args)))
in FStar_Parser_AST.PatApp (uu____2398))
in (FStar_Parser_AST.mk_pattern uu____2397 p.FStar_Parser_AST.prange))
in (

let uu____2406 = (aux loc env app)
in (match (uu____2406) with
| (env, e, b, p, uu____2425) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(

let uu____2447 = (

let uu____2448 = (

let uu____2456 = (

let uu___212_2457 = fv
in (

let uu____2458 = (

let uu____2460 = (

let uu____2461 = (

let uu____2465 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_ToSyntax_Env.typename), (uu____2465)))
in FStar_Syntax_Syntax.Record_ctor (uu____2461))
in Some (uu____2460))
in {FStar_Syntax_Syntax.fv_name = uu___212_2457.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = uu___212_2457.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu____2458}))
in ((uu____2456), (args)))
in FStar_Syntax_Syntax.Pat_cons (uu____2448))
in (FStar_All.pipe_left pos uu____2447))
end
| uu____2484 -> begin
p
end)
in ((env), (e), (b), (p), (false)))
end))))))
end))))
in (

let uu____2487 = (aux [] env p)
in (match (uu____2487) with
| (uu____2498, env, b, p, uu____2502) -> begin
((

let uu____2508 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore uu____2508));
((env), (b), (p));
)
end)))));
)))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p is_mut -> (

let mklet = (fun x -> (

let uu____2527 = (

let uu____2528 = (

let uu____2531 = (FStar_ToSyntax_Env.qualify env x)
in ((uu____2531), (FStar_Syntax_Syntax.tun)))
in LetBinder (uu____2528))
in ((env), (uu____2527), (None))))
in (match (top) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(

let uu____2542 = (

let uu____2543 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") x)
in (FStar_Ident.id_of_text uu____2543))
in (mklet uu____2542))
end
| FStar_Parser_AST.PatVar (x, uu____2545) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2549); FStar_Parser_AST.prange = uu____2550}, t) -> begin
(

let uu____2554 = (

let uu____2555 = (

let uu____2558 = (FStar_ToSyntax_Env.qualify env x)
in (

let uu____2559 = (desugar_term env t)
in ((uu____2558), (uu____2559))))
in LetBinder (uu____2555))
in ((env), (uu____2554), (None)))
end
| uu____2561 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end
| uu____2566 -> begin
(

let uu____2567 = (desugar_data_pat env p is_mut)
in (match (uu____2567) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| uu____2583 -> begin
Some (p)
end)
in ((env), (binder), (p)))
end))
end)))
and desugar_binding_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun uu____2587 env pat -> (

let uu____2590 = (desugar_data_pat env pat false)
in (match (uu____2590) with
| (env, uu____2597, pat) -> begin
((env), (pat))
end)))
and desugar_match_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let uu___213_2604 = env
in {FStar_ToSyntax_Env.curmodule = uu___213_2604.FStar_ToSyntax_Env.curmodule; FStar_ToSyntax_Env.curmonad = uu___213_2604.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = uu___213_2604.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = uu___213_2604.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = uu___213_2604.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = uu___213_2604.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = uu___213_2604.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = uu___213_2604.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = uu___213_2604.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.iface = uu___213_2604.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = uu___213_2604.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let uu___214_2608 = env
in {FStar_ToSyntax_Env.curmodule = uu___214_2608.FStar_ToSyntax_Env.curmodule; FStar_ToSyntax_Env.curmonad = uu___214_2608.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = uu___214_2608.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = uu___214_2608.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = uu___214_2608.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = uu___214_2608.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = uu___214_2608.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = uu___214_2608.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = uu___214_2608.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.iface = uu___214_2608.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = uu___214_2608.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_machine_integer : FStar_ToSyntax_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env repr uu____2611 range -> (match (uu____2611) with
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

let uu____2622 = (FStar_ToSyntax_Env.try_lookup_lid env lid)
in (match (uu____2622) with
| Some (lid) -> begin
(Prims.fst lid)
end
| None -> begin
(

let uu____2633 = (FStar_Util.format1 "%s not in scope\n" (FStar_Ident.text_of_lid lid))
in (failwith uu____2633))
end))
in (

let repr = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (None)))))) None range)
in (

let uu____2650 = (

let uu____2653 = (

let uu____2654 = (

let uu____2664 = (

let uu____2670 = (

let uu____2675 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr), (uu____2675)))
in (uu____2670)::[])
in ((lid), (uu____2664)))
in FStar_Syntax_Syntax.Tm_app (uu____2654))
in (FStar_Syntax_Syntax.mk uu____2653))
in (uu____2650 None range))))))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env_t  ->  Prims.bool  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk setpos env resolve l -> (

let uu____2710 = (FStar_ToSyntax_Env.fail_or env ((match (resolve) with
| true -> begin
FStar_ToSyntax_Env.try_lookup_lid
end
| uu____2722 -> begin
FStar_ToSyntax_Env.try_lookup_lid_no_resolve
end) env) l)
in (match (uu____2710) with
| (tm, mut) -> begin
(

let tm = (setpos tm)
in (match (mut) with
| true -> begin
(

let uu____2728 = (

let uu____2729 = (

let uu____2734 = (mk_ref_read tm)
in ((uu____2734), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (uu____2729))
in (FStar_All.pipe_left mk uu____2728))
end
| uu____2739 -> begin
tm
end))
end)))
and desugar_attributes : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (

let uu____2748 = (

let uu____2749 = (unparen t)
in uu____2749.FStar_Parser_AST.tm)
in (match (uu____2748) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = uu____2750; FStar_Ident.ident = uu____2751; FStar_Ident.nsstr = uu____2752; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| uu____2754 -> begin
(

let uu____2755 = (

let uu____2756 = (

let uu____2759 = (

let uu____2760 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " uu____2760))
in ((uu____2759), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____2756))
in (Prims.raise uu____2755))
end)))
in (FStar_List.map desugar_attribute cattributes)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk = (fun e -> ((FStar_Syntax_Syntax.mk e) None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let uu___215_2788 = e
in {FStar_Syntax_Syntax.n = uu___215_2788.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___215_2788.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___215_2788.FStar_Syntax_Syntax.vars}))
in (

let uu____2795 = (

let uu____2796 = (unparen top)
in uu____2796.FStar_Parser_AST.tm)
in (match (uu____2795) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (uu____2797) -> begin
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
| FStar_Parser_AST.Op ("*", (uu____2826)::(uu____2827)::[]) when (

let uu____2829 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right uu____2829 FStar_Option.isNone)) -> begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(

let uu____2841 = (flatten t1)
in (FStar_List.append uu____2841 ((t2)::[])))
end
| uu____2843 -> begin
(t)::[]
end))
in (

let targs = (

let uu____2846 = (

let uu____2848 = (unparen top)
in (flatten uu____2848))
in (FStar_All.pipe_right uu____2846 (FStar_List.map (fun t -> (

let uu____2852 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg uu____2852))))))
in (

let uu____2853 = (

let uu____2856 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) uu____2856))
in (match (uu____2853) with
| (tup, uu____2863) -> begin
(mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____2866 = (

let uu____2869 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) a)
in (Prims.fst uu____2869))
in (FStar_All.pipe_left setpos uu____2866))
end
| FStar_Parser_AST.Uvar (u) -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected universe variable " (Prims.strcat (FStar_Ident.text_of_id u) " in non-universe context"))), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(

let uu____2883 = (op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)
in (match (uu____2883) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected or unbound operator: " s)), (top.FStar_Parser_AST.range)))))
end
| Some (op) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (

let uu____2905 = (desugar_term env t)
in ((uu____2905), (None))))))
in (mk (FStar_Syntax_Syntax.Tm_app (((op), (args))))))
end
| uu____2911 -> begin
op
end)
end))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2912; FStar_Ident.ident = uu____2913; FStar_Ident.nsstr = uu____2914; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2916; FStar_Ident.ident = uu____2917; FStar_Ident.nsstr = uu____2918; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = uu____2920; FStar_Ident.ident = uu____2921; FStar_Ident.nsstr = uu____2922; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(

let uu____2932 = (

let uu____2933 = (desugar_universe t)
in FStar_Syntax_Syntax.Tm_type (uu____2933))
in (mk uu____2932))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2934; FStar_Ident.ident = uu____2935; FStar_Ident.nsstr = uu____2936; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2938; FStar_Ident.ident = uu____2939; FStar_Ident.nsstr = uu____2940; FStar_Ident.str = "True"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2942; FStar_Ident.ident = uu____2943; FStar_Ident.nsstr = uu____2944; FStar_Ident.str = "False"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = uu____2948}) when ((is_special_effect_combinator txt) && (FStar_ToSyntax_Env.is_effect_name env eff_name)) -> begin
(

let uu____2949 = (FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name)
in (match (uu____2949) with
| Some (ed) -> begin
(

let uu____2952 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" txt))) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.fvar uu____2952 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
end
| None -> begin
(

let uu____2953 = (FStar_Util.format2 "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)" (FStar_Ident.text_of_lid eff_name) txt)
in (failwith uu____2953))
end))
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t2 = (desugar_term env t2)
in (

let uu____2957 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) ident)
in (match (uu____2957) with
| (t1, mut) -> begin
((match ((not (mut))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
end
| uu____2965 -> begin
()
end);
(mk_ref_assign t1 t2 top.FStar_Parser_AST.range);
)
end)))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(desugar_name mk setpos env true l)
end
| FStar_Parser_AST.Projector (l, i) -> begin
(

let name = (

let uu____2973 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____2973) with
| Some (uu____2978) -> begin
Some (((true), (l)))
end
| None -> begin
(

let uu____2981 = (FStar_ToSyntax_Env.try_lookup_root_effect_name env l)
in (match (uu____2981) with
| Some (new_name) -> begin
Some (((false), (new_name)))
end
| uu____2989 -> begin
None
end))
end))
in (match (name) with
| Some (resolve, new_name) -> begin
(

let uu____2997 = (FStar_Syntax_Util.mk_field_projector_name_from_ident new_name i)
in (desugar_name mk setpos env resolve uu____2997))
end
| uu____2998 -> begin
(

let uu____3002 = (

let uu____3003 = (

let uu____3006 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((uu____3006), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____3003))
in (Prims.raise uu____3002))
end))
end
| FStar_Parser_AST.Discrim (lid) -> begin
(

let uu____3008 = (FStar_ToSyntax_Env.try_lookup_datacon env lid)
in (match (uu____3008) with
| None -> begin
(

let uu____3010 = (

let uu____3011 = (

let uu____3014 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((uu____3014), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____3011))
in (Prims.raise uu____3010))
end
| uu____3015 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (desugar_name mk setpos env true lid'))
end))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(

let uu____3026 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____3026) with
| Some (head) -> begin
(

let uu____3029 = (

let uu____3034 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in ((uu____3034), (true)))
in (match (uu____3029) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| uu____3047 -> begin
(

let uu____3051 = (FStar_Util.take (fun uu____3062 -> (match (uu____3062) with
| (uu____3065, imp) -> begin
(imp = FStar_Parser_AST.UnivApp)
end)) args)
in (match (uu____3051) with
| (universes, args) -> begin
(

let universes = (FStar_List.map (fun x -> (desugar_universe (Prims.fst x))) universes)
in (

let args = (FStar_List.map (fun uu____3098 -> (match (uu____3098) with
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
| uu____3113 -> begin
(mk (FStar_Syntax_Syntax.Tm_uinst (((head), (universes)))))
end)
in (

let app = (mk (FStar_Syntax_Syntax.Tm_app (((head), (args)))))
in (match (is_data) with
| true -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((app), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| uu____3128 -> begin
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

let uu____3133 = (FStar_List.fold_left (fun uu____3150 b -> (match (uu____3150) with
| (env, tparams, typs) -> begin
(

let uu____3181 = (desugar_binder env b)
in (match (uu____3181) with
| (xopt, t) -> begin
(

let uu____3197 = (match (xopt) with
| None -> begin
(

let uu____3202 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env), (uu____3202)))
end
| Some (x) -> begin
(FStar_ToSyntax_Env.push_bv env x)
end)
in (match (uu____3197) with
| (env, x) -> begin
(

let uu____3214 = (

let uu____3216 = (

let uu____3218 = (

let uu____3219 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3219))
in (uu____3218)::[])
in (FStar_List.append typs uu____3216))
in ((env), ((FStar_List.append tparams (((((

let uu___216_3232 = x
in {FStar_Syntax_Syntax.ppname = uu___216_3232.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___216_3232.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (None)))::[]))), (uu____3214)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level None))::[])))
in (match (uu____3133) with
| (env, uu____3245, targs) -> begin
(

let uu____3257 = (

let uu____3260 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) uu____3260))
in (match (uu____3257) with
| (tup, uu____3267) -> begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let uu____3275 = (uncurry binders t)
in (match (uu____3275) with
| (bs, t) -> begin
(

let rec aux = (fun env bs uu___194_3298 -> (match (uu___194_3298) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range env t)
in (

let uu____3308 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos uu____3308)))
end
| (hd)::tl -> begin
(

let bb = (desugar_binder env hd)
in (

let uu____3324 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (uu____3324) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end)))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(

let uu____3335 = (desugar_binder env b)
in (match (uu____3335) with
| (None, uu____3339) -> begin
(failwith "Missing binder in refinement")
end
| b -> begin
(

let uu____3345 = (as_binder env None b)
in (match (uu____3345) with
| ((x, uu____3349), env) -> begin
(

let f = (desugar_formula env f)
in (

let uu____3354 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos uu____3354)))
end))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let uu____3369 = (FStar_List.fold_left (fun uu____3376 pat -> (match (uu____3376) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (uu____3391, t) -> begin
(

let uu____3393 = (

let uu____3395 = (free_type_vars env t)
in (FStar_List.append uu____3395 ftvs))
in ((env), (uu____3393)))
end
| uu____3398 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (uu____3369) with
| (uu____3401, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (

let uu____3409 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append uu____3409 binders))
in (

let rec aux = (fun env bs sc_pat_opt uu___195_3438 -> (match (uu___195_3438) with
| [] -> begin
(

let body = (desugar_term env body)
in (

let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(

let body = (

let uu____3467 = (

let uu____3468 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right uu____3468 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close uu____3467 body))
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (None), (body)))::[]))))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (

let uu____3510 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos uu____3510))))
end
| (p)::rest -> begin
(

let uu____3518 = (desugar_binding_pat env p)
in (match (uu____3518) with
| (env, b, pat) -> begin
(

let uu____3530 = (match (b) with
| LetBinder (uu____3549) -> begin
(failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, uu____3580) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(

let uu____3603 = (

let uu____3606 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____3606), (p)))
in Some (uu____3603))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (uu____3631), uu____3632) -> begin
(

let tup2 = (

let uu____3634 = (FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____3634 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (

let uu____3638 = (

let uu____3641 = (

let uu____3642 = (

let uu____3652 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (

let uu____3655 = (

let uu____3657 = (FStar_Syntax_Syntax.as_arg sc)
in (

let uu____3658 = (

let uu____3660 = (

let uu____3661 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3661))
in (uu____3660)::[])
in (uu____3657)::uu____3658))
in ((uu____3652), (uu____3655))))
in FStar_Syntax_Syntax.Tm_app (uu____3642))
in (FStar_Syntax_Syntax.mk uu____3641))
in (uu____3638 None top.FStar_Parser_AST.range))
in (

let p = (

let uu____3676 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p), (false)))::[])))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n uu____3676))
in Some (((sc), (p))))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____3696, args), FStar_Syntax_Syntax.Pat_cons (uu____3698, pats)) -> begin
(

let tupn = (

let uu____3725 = (FStar_Syntax_Util.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____3725 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (

let uu____3735 = (

let uu____3736 = (

let uu____3746 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (

let uu____3749 = (

let uu____3755 = (

let uu____3761 = (

let uu____3762 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3762))
in (uu____3761)::[])
in (FStar_List.append args uu____3755))
in ((uu____3746), (uu____3749))))
in FStar_Syntax_Syntax.Tm_app (uu____3736))
in (mk uu____3735))
in (

let p = (

let uu____3777 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p), (false)))::[])))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n uu____3777))
in Some (((sc), (p))))))
end
| uu____3801 -> begin
(failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt)))
end)
in (match (uu____3530) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end)))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = rng; FStar_Parser_AST.level = uu____3844}, phi, uu____3846) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env phi)
in (

let a = (FStar_Ident.set_lid_range a rng)
in (

let uu____3849 = (

let uu____3850 = (

let uu____3860 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (

let uu____3861 = (

let uu____3863 = (FStar_Syntax_Syntax.as_arg phi)
in (

let uu____3864 = (

let uu____3866 = (

let uu____3867 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3867))
in (uu____3866)::[])
in (uu____3863)::uu____3864))
in ((uu____3860), (uu____3861))))
in FStar_Syntax_Syntax.Tm_app (uu____3850))
in (mk uu____3849))))
end
| FStar_Parser_AST.App (uu____3869, uu____3870, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (

let uu____3882 = (

let uu____3883 = (unparen e)
in uu____3883.FStar_Parser_AST.tm)
in (match (uu____3882) with
| FStar_Parser_AST.App (e, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e))
end
| uu____3889 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_uinst (((head), (universes))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.App (uu____3892) -> begin
(

let rec aux = (fun args e -> (

let uu____3913 = (

let uu____3914 = (unparen e)
in uu____3914.FStar_Parser_AST.tm)
in (match (uu____3913) with
| FStar_Parser_AST.App (e, t, imp) when (imp <> FStar_Parser_AST.UnivApp) -> begin
(

let arg = (

let uu____3924 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) uu____3924))
in (aux ((arg)::args) e))
end
| uu____3931 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let uu____3942 = (

let uu____3943 = (

let uu____3948 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((uu____3948), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))
in FStar_Syntax_Syntax.Tm_meta (uu____3943))
in (mk uu____3942))
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

let ds_let_rec_or_app = (fun uu____3978 -> (

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun uu____4020 -> (match (uu____4020) with
| (p, def) -> begin
(

let uu____4034 = (is_app_pattern p)
in (match (uu____4034) with
| true -> begin
(

let uu____4044 = (destruct_app_pattern env top_level p)
in ((uu____4044), (def)))
end
| uu____4059 -> begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(

let uu____4073 = (destruct_app_pattern env top_level p)
in ((uu____4073), (def)))
end
| uu____4088 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____4102); FStar_Parser_AST.prange = uu____4103}, t) -> begin
(match (top_level) with
| true -> begin
(

let uu____4116 = (

let uu____4124 = (

let uu____4127 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____4127))
in ((uu____4124), ([]), (Some (t))))
in ((uu____4116), (def)))
end
| uu____4139 -> begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end)
end
| FStar_Parser_AST.PatVar (id, uu____4152) -> begin
(match (top_level) with
| true -> begin
(

let uu____4164 = (

let uu____4172 = (

let uu____4175 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____4175))
in ((uu____4172), ([]), (None)))
in ((uu____4164), (def)))
end
| uu____4187 -> begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end)
end
| uu____4199 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end))
end))))
in (

let uu____4209 = (FStar_List.fold_left (fun uu____4233 uu____4234 -> (match (((uu____4233), (uu____4234))) with
| ((env, fnames, rec_bindings), ((f, uu____4278, uu____4279), uu____4280)) -> begin
(

let uu____4320 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let uu____4334 = (FStar_ToSyntax_Env.push_bv env x)
in (match (uu____4334) with
| (env, xx) -> begin
(

let uu____4345 = (

let uu____4347 = (FStar_Syntax_Syntax.mk_binder xx)
in (uu____4347)::rec_bindings)
in ((env), (FStar_Util.Inl (xx)), (uu____4345)))
end))
end
| FStar_Util.Inr (l) -> begin
(

let uu____4352 = (FStar_ToSyntax_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((uu____4352), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (uu____4320) with
| (env, lbname, rec_bindings) -> begin
((env), ((lbname)::fnames), (rec_bindings))
end))
end)) ((env), ([]), ([])) funs)
in (match (uu____4209) with
| (env', fnames, rec_bindings) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let rec_bindings = (FStar_List.rev rec_bindings)
in (

let desugar_one_def = (fun env lbname uu____4425 -> (match (uu____4425) with
| ((uu____4437, args, result_t), def) -> begin
(

let args = (FStar_All.pipe_right args (FStar_List.map replace_unit_pattern))
in (

let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(

let t = (

let uu____4463 = (is_comp_type env t)
in (match (uu____4463) with
| true -> begin
((

let uu____4465 = (FStar_All.pipe_right args (FStar_List.tryFind (fun x -> (

let uu____4470 = (is_var_pattern x)
in (not (uu____4470))))))
in (match (uu____4465) with
| None -> begin
()
end
| Some (p) -> begin
(Prims.raise (FStar_Errors.Error ((("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable"), (p.FStar_Parser_AST.prange)))))
end));
t;
)
end
| uu____4472 -> begin
(

let uu____4473 = (((FStar_Options.ml_ish ()) && (

let uu____4474 = (FStar_ToSyntax_Env.try_lookup_effect_name env FStar_Syntax_Const.effect_ML_lid)
in (FStar_Option.isSome uu____4474))) && ((not (is_rec)) || ((FStar_List.length args) <> (Prims.parse_int "0"))))
in (match (uu____4473) with
| true -> begin
(FStar_Parser_AST.ml_comp t)
end
| uu____4478 -> begin
(FStar_Parser_AST.tot_comp t)
end))
end))
in (

let uu____4479 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) uu____4479 FStar_Parser_AST.Expr)))
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| uu____4481 -> begin
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
(

let uu____4491 = (

let uu____4492 = (FStar_Syntax_Util.incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l uu____4492 None))
in FStar_Util.Inr (uu____4491))
end)
in (

let body = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.close rec_bindings body)
end
| uu____4494 -> begin
body
end)
in (mk_lb ((lbname), (FStar_Syntax_Syntax.tun), (body)))))))))
end))
in (

let lbs = (FStar_List.map2 (desugar_one_def (match (is_rec) with
| true -> begin
env'
end
| uu____4510 -> begin
env
end)) fnames funs)
in (

let body = (desugar_term env' body)
in (

let uu____4512 = (

let uu____4513 = (

let uu____4521 = (FStar_Syntax_Subst.close rec_bindings body)
in ((((is_rec), (lbs))), (uu____4521)))
in FStar_Syntax_Syntax.Tm_let (uu____4513))
in (FStar_All.pipe_left mk uu____4512)))))))
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
| uu____4547 -> begin
t1
end)
in (

let uu____4548 = (desugar_binding_pat_maybe_top top_level env pat is_mutable)
in (match (uu____4548) with
| (env, binder, pat) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body = (desugar_term env t2)
in (

let fv = (

let uu____4569 = (FStar_Syntax_Util.incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l uu____4569 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]))), (body)))))))
end
| LocalBinder (x, uu____4577) -> begin
(

let body = (desugar_term env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(

let uu____4586 = (

let uu____4589 = (

let uu____4590 = (

let uu____4606 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____4607 = (

let uu____4609 = (FStar_Syntax_Util.branch ((pat), (None), (body)))
in (uu____4609)::[])
in ((uu____4606), (uu____4607))))
in FStar_Syntax_Syntax.Tm_match (uu____4590))
in (FStar_Syntax_Syntax.mk uu____4589))
in (uu____4586 None body.FStar_Syntax_Syntax.pos))
end)
in (

let uu____4624 = (

let uu____4625 = (

let uu____4633 = (

let uu____4634 = (

let uu____4635 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4635)::[])
in (FStar_Syntax_Subst.close uu____4634 body))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t1))))::[]))), (uu____4633)))
in FStar_Syntax_Syntax.Tm_let (uu____4625))
in (FStar_All.pipe_left mk uu____4624))))
end)
in (match (is_mutable) with
| true -> begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc))))))
end
| uu____4654 -> begin
tm
end))
end))))))
in (

let uu____4655 = (is_rec || (is_app_pattern pat))
in (match (uu____4655) with
| true -> begin
(ds_let_rec_or_app ())
end
| uu____4656 -> begin
(ds_non_rec pat _snd body)
end)))))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let uu____4661 = (

let uu____4662 = (

let uu____4678 = (desugar_term env t1)
in (

let uu____4679 = (

let uu____4689 = (

let uu____4698 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (

let uu____4701 = (desugar_term env t2)
in ((uu____4698), (None), (uu____4701))))
in (

let uu____4709 = (

let uu____4719 = (

let uu____4728 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (

let uu____4731 = (desugar_term env t3)
in ((uu____4728), (None), (uu____4731))))
in (uu____4719)::[])
in (uu____4689)::uu____4709))
in ((uu____4678), (uu____4679))))
in FStar_Syntax_Syntax.Tm_match (uu____4662))
in (mk uu____4661)))
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

let desugar_branch = (fun uu____4817 -> (match (uu____4817) with
| (pat, wopt, b) -> begin
(

let uu____4827 = (desugar_match_pat env pat)
in (match (uu____4827) with
| (env, pat) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(

let uu____4836 = (desugar_term env e)
in Some (uu____4836))
end)
in (

let b = (desugar_term env b)
in (FStar_Syntax_Util.branch ((pat), (wopt), (b)))))
end))
end))
in (

let uu____4839 = (

let uu____4840 = (

let uu____4856 = (desugar_term env e)
in (

let uu____4857 = (FStar_List.map desugar_branch branches)
in ((uu____4856), (uu____4857))))
in FStar_Syntax_Syntax.Tm_match (uu____4840))
in (FStar_All.pipe_left mk uu____4839)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(

let annot = (

let uu____4873 = (is_comp_type env t)
in (match (uu____4873) with
| true -> begin
(

let uu____4878 = (desugar_comp t.FStar_Parser_AST.range env t)
in FStar_Util.Inr (uu____4878))
end
| uu____4883 -> begin
(

let uu____4884 = (desugar_term env t)
in FStar_Util.Inl (uu____4884))
end))
in (

let uu____4887 = (

let uu____4888 = (

let uu____4901 = (desugar_term env e)
in ((uu____4901), (annot), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____4888))
in (FStar_All.pipe_left mk uu____4887)))
end
| FStar_Parser_AST.Record (uu____4909, []) -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let uu____4930 = (FStar_List.hd fields)
in (match (uu____4930) with
| (f, uu____4937) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun uu____4961 -> (match (uu____4961) with
| (g, uu____4965) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| Some (uu____4969, e) -> begin
((fn), (e))
end
| None -> begin
(match (xopt) with
| None -> begin
(

let uu____4977 = (

let uu____4978 = (

let uu____4981 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_ToSyntax_Env.typename.FStar_Ident.str)
in ((uu____4981), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____4978))
in (Prims.raise uu____4977))
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
(

let uu____4987 = (

let uu____4993 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____5007 -> (match (uu____5007) with
| (f, uu____5013) -> begin
(

let uu____5014 = (

let uu____5015 = (get_field None f)
in (FStar_All.pipe_left Prims.snd uu____5015))
in ((uu____5014), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (uu____4993)))
in FStar_Parser_AST.Construct (uu____4987))
end
| Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (

let uu____5026 = (

let uu____5027 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____5027))
in (FStar_Parser_AST.mk_term uu____5026 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = (

let uu____5029 = (

let uu____5036 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____5050 -> (match (uu____5050) with
| (f, uu____5056) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (uu____5036)))
in FStar_Parser_AST.Record (uu____5029))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____5072; FStar_Syntax_Syntax.pos = uu____5073; FStar_Syntax_Syntax.vars = uu____5074}, args); FStar_Syntax_Syntax.tk = uu____5076; FStar_Syntax_Syntax.pos = uu____5077; FStar_Syntax_Syntax.vars = uu____5078}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e = (

let uu____5100 = (

let uu____5101 = (

let uu____5111 = (

let uu____5112 = (

let uu____5114 = (

let uu____5115 = (

let uu____5119 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_ToSyntax_Env.typename), (uu____5119)))
in FStar_Syntax_Syntax.Record_ctor (uu____5115))
in Some (uu____5114))
in (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant uu____5112))
in ((uu____5111), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____5101))
in (FStar_All.pipe_left mk uu____5100))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| uu____5143 -> begin
e
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let uu____5146 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f)
in (match (uu____5146) with
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
| uu____5158 -> begin
None
end)
in (

let uu____5159 = (

let uu____5160 = (

let uu____5170 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projname (FStar_Ident.range_of_lid f)) FStar_Syntax_Syntax.Delta_equational qual)
in (

let uu____5171 = (

let uu____5173 = (FStar_Syntax_Syntax.as_arg e)
in (uu____5173)::[])
in ((uu____5170), (uu____5171))))
in FStar_Syntax_Syntax.Tm_app (uu____5160))
in (FStar_All.pipe_left mk uu____5159)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| uu____5179 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| uu____5180 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Let (uu____5181, uu____5182, uu____5183) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QForall (uu____5190, uu____5191, uu____5192) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QExists (uu____5199, uu____5200, uu____5201) -> begin
(failwith "Not implemented yet")
end)))))
and desugar_args : FStar_ToSyntax_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____5225 -> (match (uu____5225) with
| (a, imp) -> begin
(

let uu____5233 = (desugar_term env a)
in (arg_withimp_e imp uu____5233))
end)))))
and desugar_comp : FStar_Range.range  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Errors.Error (((msg), (r))))))
in (

let is_requires = (fun uu____5250 -> (match (uu____5250) with
| (t, uu____5254) -> begin
(

let uu____5255 = (

let uu____5256 = (unparen t)
in uu____5256.FStar_Parser_AST.tm)
in (match (uu____5255) with
| FStar_Parser_AST.Requires (uu____5257) -> begin
true
end
| uu____5261 -> begin
false
end))
end))
in (

let is_ensures = (fun uu____5267 -> (match (uu____5267) with
| (t, uu____5271) -> begin
(

let uu____5272 = (

let uu____5273 = (unparen t)
in uu____5273.FStar_Parser_AST.tm)
in (match (uu____5272) with
| FStar_Parser_AST.Ensures (uu____5274) -> begin
true
end
| uu____5278 -> begin
false
end))
end))
in (

let is_app = (fun head uu____5287 -> (match (uu____5287) with
| (t, uu____5291) -> begin
(

let uu____5292 = (

let uu____5293 = (unparen t)
in uu____5293.FStar_Parser_AST.tm)
in (match (uu____5292) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = uu____5295; FStar_Parser_AST.level = uu____5296}, uu____5297, uu____5298) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| uu____5299 -> begin
false
end))
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t -> (

let uu____5317 = (head_and_args t)
in (match (uu____5317) with
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
(

let uu____5482 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes env) l)
in ((uu____5482), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____5496 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals uu____5496 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((

let uu____5505 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals uu____5505 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when (((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)), ([]))), ((((t), (FStar_Parser_AST.Nothing)))::[]))
end
| uu____5525 -> begin
(

let default_effect = (

let uu____5527 = (FStar_Options.ml_ish ())
in (match (uu____5527) with
| true -> begin
FStar_Syntax_Const.effect_ML_lid
end
| uu____5528 -> begin
((

let uu____5530 = (FStar_Options.warn_default_effects ())
in (match (uu____5530) with
| true -> begin
(FStar_Errors.warn head.FStar_Parser_AST.range "Using default effect Tot")
end
| uu____5531 -> begin
()
end));
FStar_Syntax_Const.effect_Tot_lid;
)
end))
in (((((FStar_Ident.set_lid_range default_effect head.FStar_Parser_AST.range)), ([]))), ((((t), (FStar_Parser_AST.Nothing)))::[])))
end)
end)))
in (

let uu____5543 = (pre_process_comp_typ t)
in (match (uu____5543) with
| ((eff, cattributes), args) -> begin
((match (((FStar_List.length args) = (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5573 = (

let uu____5574 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" uu____5574))
in (fail uu____5573))
end
| uu____5575 -> begin
()
end);
(

let is_universe = (fun uu____5581 -> (match (uu____5581) with
| (uu____5584, imp) -> begin
(imp = FStar_Parser_AST.UnivApp)
end))
in (

let uu____5586 = (FStar_Util.take is_universe args)
in (match (uu____5586) with
| (universes, args) -> begin
(

let universes = (FStar_List.map (fun uu____5617 -> (match (uu____5617) with
| (u, imp) -> begin
(desugar_universe u)
end)) universes)
in (

let uu____5622 = (

let uu____5630 = (FStar_List.hd args)
in (

let uu____5635 = (FStar_List.tl args)
in ((uu____5630), (uu____5635))))
in (match (uu____5622) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (Prims.fst result_arg))
in (

let rest = (desugar_args env rest)
in (

let uu____5666 = (FStar_All.pipe_right rest (FStar_List.partition (fun uu____5704 -> (match (uu____5704) with
| (t, uu____5711) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____5719; FStar_Syntax_Syntax.pos = uu____5720; FStar_Syntax_Syntax.vars = uu____5721}, (uu____5722)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| uu____5744 -> begin
false
end)
end))))
in (match (uu____5666) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun uu____5787 -> (match (uu____5787) with
| (t, uu____5794) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____5801, ((arg, uu____5803))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| uu____5825 -> begin
(failwith "impos")
end)
end))))
in (

let no_additional_args = (

let is_empty = (fun l -> (match (l) with
| [] -> begin
true
end
| uu____5837 -> begin
false
end))
in ((((is_empty decreases_clause) && (is_empty rest)) && (is_empty cattributes)) && (is_empty universes)))
in (match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end
| uu____5846 -> begin
(match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end
| uu____5849 -> begin
(

let flags = (match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid)) with
| true -> begin
(FStar_Syntax_Syntax.LEMMA)::[]
end
| uu____5853 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____5855 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_ML_lid)) with
| true -> begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end
| uu____5857 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____5859 -> begin
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

let pattern = (

let uu____5929 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5929 ((FStar_Syntax_Syntax.U_zero)::[])))
in ((FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (Some (FStar_Syntax_Syntax.imp_tag))))::[])) None pat.FStar_Syntax_Syntax.pos)))
end
| uu____5941 -> begin
pat
end)
in (

let uu____5942 = (

let uu____5949 = (

let uu____5956 = (

let uu____5962 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))))) None pat.FStar_Syntax_Syntax.pos)
in ((uu____5962), (aq)))
in (uu____5956)::[])
in (ens)::uu____5949)
in (req)::uu____5942))
end
| uu____5998 -> begin
rest
end)
end
| uu____6005 -> begin
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
| uu____6014 -> begin
None
end))
in (

let mk = (fun t -> ((FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let uu___217_6055 = t
in {FStar_Syntax_Syntax.n = uu___217_6055.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___217_6055.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___217_6055.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let uu___218_6085 = b
in {FStar_Parser_AST.b = uu___218_6085.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___218_6085.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___218_6085.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (

let uu____6118 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) uu____6118)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(

let uu____6127 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____6127) with
| (env, a) -> begin
(

let a = (

let uu___219_6135 = a
in {FStar_Syntax_Syntax.ppname = uu___219_6135.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___219_6135.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats = (desugar_pats env pats)
in (

let body = (desugar_formula env body)
in (

let body = (match (pats) with
| [] -> begin
body
end
| uu____6148 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_pattern (pats))))))
end)
in (

let body = (

let uu____6157 = (

let uu____6160 = (

let uu____6164 = (FStar_Syntax_Syntax.mk_binder a)
in (uu____6164)::[])
in (no_annot_abs uu____6160 body))
in (FStar_All.pipe_left setpos uu____6157))
in (

let uu____6169 = (

let uu____6170 = (

let uu____6180 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let uu____6181 = (

let uu____6183 = (FStar_Syntax_Syntax.as_arg body)
in (uu____6183)::[])
in ((uu____6180), (uu____6181))))
in FStar_Syntax_Syntax.Tm_app (uu____6170))
in (FStar_All.pipe_left mk uu____6169)))))))
end))
end
| uu____6187 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (

let uu____6236 = (q ((rest), (pats), (body)))
in (

let uu____6240 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term uu____6236 uu____6240 FStar_Parser_AST.Formula)))
in (

let uu____6241 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term uu____6241 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| uu____6246 -> begin
(failwith "impossible")
end))
in (

let uu____6248 = (

let uu____6249 = (unparen f)
in uu____6249.FStar_Parser_AST.tm)
in (match (uu____6248) with
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
in (

let uu____6279 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env uu____6279)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____6300 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env uu____6300)))
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
| uu____6325 -> begin
(desugar_term env f)
end)))))))))
and typars_of_binders : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let uu____6329 = (FStar_List.fold_left (fun uu____6342 b -> (match (uu____6342) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let uu___220_6370 = b
in {FStar_Parser_AST.b = uu___220_6370.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___220_6370.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___220_6370.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(

let uu____6380 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____6380) with
| (env, a) -> begin
(

let a = (

let uu___221_6392 = a
in {FStar_Syntax_Syntax.ppname = uu___221_6392.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___221_6392.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env), ((((a), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| uu____6401 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (uu____6329) with
| (env, tpars) -> begin
((env), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(

let uu____6451 = (desugar_typ env t)
in ((Some (x)), (uu____6451)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____6454 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown))) None x.FStar_Ident.idRange)
in ((Some (x)), (uu____6454)))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____6469 = (desugar_typ env t)
in ((None), (uu____6469)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators = (fun quals env t tps k datas -> (

let quals = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___196_6518 -> (match (uu___196_6518) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| uu____6519 -> begin
false
end))))
in (

let quals = (fun q -> (

let uu____6527 = ((FStar_All.pipe_left Prims.op_Negation env.FStar_ToSyntax_Env.iface) || env.FStar_ToSyntax_Env.admitted_iface)
in (match (uu____6527) with
| true -> begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end
| uu____6529 -> begin
(FStar_List.append q quals)
end)))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (

let uu____6534 = (

let uu____6541 = (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in ((disc_name), ([]), (FStar_Syntax_Syntax.tun), (uu____6541), ((FStar_Ident.range_of_lid disc_name))))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____6534)))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_ToSyntax_Env.env  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let uu____6566 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____6576 -> (match (uu____6576) with
| (x, uu____6581) -> begin
(

let uu____6582 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____6582) with
| (field_name, uu____6587) -> begin
(

let only_decl = (((

let uu____6589 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____6589)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (

let uu____6590 = (

let uu____6591 = (FStar_ToSyntax_Env.current_module env)
in uu____6591.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____6590)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____6601 = (FStar_List.filter (fun uu___197_6603 -> (match (uu___197_6603) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____6604 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____6601)
end
| uu____6605 -> begin
q
end))
in (

let quals = (

let iquals = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___198_6612 -> (match (uu___198_6612) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| uu____6613 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun), (quals), ((FStar_Ident.range_of_lid field_name))))
in (match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____6618 -> begin
(

let dd = (

let uu____6620 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____6620) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____6622 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lb = (

let uu____6624 = (

let uu____6627 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (uu____6627))
in {FStar_Syntax_Syntax.lbname = uu____6624; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun})
in (

let impl = (

let uu____6629 = (

let uu____6638 = (

let uu____6640 = (

let uu____6641 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____6641 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____6640)::[])
in ((((false), ((lb)::[]))), (p), (uu____6638), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____6629))
in (match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____6657 -> begin
(decl)::(impl)::[]
end))))
end))))))
end))
end))))
in (FStar_All.pipe_right uu____6566 FStar_List.flatten))))


let mk_data_projector_names = (fun iquals env uu____6681 -> (match (uu____6681) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____6689, t, uu____6691, n, quals, uu____6694, uu____6695) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let uu____6700 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____6700) with
| (formals, uu____6710) -> begin
(match (formals) with
| [] -> begin
[]
end
| uu____6724 -> begin
(

let filter_records = (fun uu___199_6732 -> (match (uu___199_6732) with
| FStar_Syntax_Syntax.RecordConstructor (uu____6734, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| uu____6741 -> begin
None
end))
in (

let fv_qual = (

let uu____6743 = (FStar_Util.find_map quals filter_records)
in (match (uu____6743) with
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
| uu____6749 -> begin
iquals
end)
in (

let uu____6750 = (FStar_Util.first_N n formals)
in (match (uu____6750) with
| (uu____6762, rest) -> begin
(mk_indexed_projector_names iquals fv_qual env lid rest)
end)))))
end)
end))
end
| uu____6776 -> begin
[]
end)
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = (

let uu____6814 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____6814) with
| true -> begin
(

let uu____6816 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (uu____6816))
end
| uu____6817 -> begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end))
in (

let lb = (

let uu____6819 = (

let uu____6822 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (uu____6822))
in (

let uu____6823 = (

let uu____6826 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars uu____6826))
in (

let uu____6829 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = uu____6819; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____6823; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____6829})))
in FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (rng), (lids), (quals), ([]))))))


let rec desugar_tycon : FStar_ToSyntax_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (

let tycon_id = (fun uu___200_6862 -> (match (uu___200_6862) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(

let uu____6901 = (

let uu____6902 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____6902))
in (FStar_Parser_AST.mk_term uu____6901 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| uu____6924 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (

let uu____6927 = (

let uu____6928 = (

let uu____6932 = (binder_to_term b)
in ((out), (uu____6932), ((imp_of_aqual b))))
in FStar_Parser_AST.App (uu____6928))
in (FStar_Parser_AST.mk_term uu____6927 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun uu___201_6939 -> (match (uu___201_6939) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun uu____6968 -> (match (uu____6968) with
| (x, t, uu____6975) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (

let uu____6979 = (

let uu____6980 = (

let uu____6981 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (uu____6981))
in (FStar_Parser_AST.mk_term uu____6980 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____6979 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type_level)
in (

let uu____6984 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____6996 -> (match (uu____6996) with
| (x, uu____7002, uu____7003) -> begin
(FStar_Syntax_Util.unmangle_field_name x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (uu____6984)))))))
end
| uu____7030 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals uu___202_7052 -> (match (uu___202_7052) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let uu____7066 = (typars_of_binders _env binders)
in (match (uu____7066) with
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

let tconstr = (

let uu____7094 = (

let uu____7095 = (

let uu____7096 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (uu____7096))
in (FStar_Parser_AST.mk_term uu____7095 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____7094 binders))
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
| uu____7107 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env bs -> (

let uu____7133 = (FStar_List.fold_left (fun uu____7149 uu____7150 -> (match (((uu____7149), (uu____7150))) with
| ((env, tps), (x, imp)) -> begin
(

let uu____7198 = (FStar_ToSyntax_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (uu____7198) with
| (env, y) -> begin
((env), ((((y), (imp)))::tps))
end))
end)) ((env), ([])) bs)
in (match (uu____7133) with
| (env, bs) -> begin
((env), ((FStar_List.rev bs)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt = (match (kopt) with
| None -> begin
(

let uu____7259 = (tm_type_z id.FStar_Ident.idRange)
in Some (uu____7259))
end
| uu____7260 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt)))
in (

let uu____7265 = (desugar_abstract_tc quals env [] tc)
in (match (uu____7265) with
| (uu____7272, uu____7273, se, uu____7275) -> begin
(

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, uu____7278, typars, k, [], [], quals, rng) -> begin
(

let quals = (

let uu____7289 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (match (uu____7289) with
| true -> begin
quals
end
| uu____7292 -> begin
((

let uu____7294 = (FStar_Range.string_of_range rng)
in (

let uu____7295 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" uu____7294 uu____7295)));
(FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals;
)
end))
in (

let t = (match (typars) with
| [] -> begin
k
end
| uu____7299 -> begin
(

let uu____7300 = (

let uu____7303 = (

let uu____7304 = (

let uu____7312 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (uu____7312)))
in FStar_Syntax_Syntax.Tm_arrow (uu____7304))
in (FStar_Syntax_Syntax.mk uu____7303))
in (uu____7300 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t), (quals), (rng)))))
end
| uu____7323 -> begin
se
end)
in (

let env = (FStar_ToSyntax_Env.push_sigelt env se)
in ((env), ((se)::[]))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let uu____7334 = (typars_of_binders env binders)
in (match (uu____7334) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
(

let uu____7354 = (FStar_Util.for_some (fun uu___203_7355 -> (match (uu___203_7355) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| uu____7356 -> begin
false
end)) quals)
in (match (uu____7354) with
| true -> begin
FStar_Syntax_Syntax.teff
end
| uu____7357 -> begin
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

let uu____7362 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___204_7364 -> (match (uu___204_7364) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| uu____7365 -> begin
false
end))))
in (match (uu____7362) with
| true -> begin
quals
end
| uu____7367 -> begin
(match ((t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula)) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____7369 -> begin
quals
end)
end))
in (

let se = (

let uu____7371 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Effect))
in (match (uu____7371) with
| true -> begin
(

let uu____7373 = (

let uu____7377 = (

let uu____7378 = (unparen t)
in uu____7378.FStar_Parser_AST.tm)
in (match (uu____7377) with
| FStar_Parser_AST.Construct (head, args) -> begin
(

let uu____7390 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____7406))::args_rev -> begin
(

let uu____7413 = (

let uu____7414 = (unparen last_arg)
in uu____7414.FStar_Parser_AST.tm)
in (match (uu____7413) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____7429 -> begin
(([]), (args))
end))
end
| uu____7434 -> begin
(([]), (args))
end)
in (match (uu____7390) with
| (cattributes, args) -> begin
(

let uu____7455 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head), (args)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (uu____7455)))
end))
end
| uu____7461 -> begin
((t), ([]))
end))
in (match (uu____7373) with
| (t, cattributes) -> begin
(

let c = (desugar_comp t.FStar_Parser_AST.range env' t)
in (

let typars = (FStar_Syntax_Subst.close_binders typars)
in (

let c = (FStar_Syntax_Subst.close_comp typars c)
in (

let uu____7472 = (

let uu____7482 = (FStar_ToSyntax_Env.qualify env id)
in (

let uu____7483 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___205_7487 -> (match (uu___205_7487) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| uu____7488 -> begin
true
end))))
in ((uu____7482), ([]), (typars), (c), (uu____7483), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c))), (rng))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (uu____7472)))))
end))
end
| uu____7492 -> begin
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
| (FStar_Parser_AST.TyconRecord (uu____7497))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let uu____7510 = (tycon_record_as_variant trec)
in (match (uu____7510) with
| (t, fs) -> begin
(

let uu____7520 = (

let uu____7522 = (

let uu____7523 = (

let uu____7528 = (

let uu____7530 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.ids_of_lid uu____7530))
in ((uu____7528), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____7523))
in (uu____7522)::quals)
in (desugar_tycon env rng uu____7520 ((t)::[])))
end)))
end
| (uu____7533)::uu____7534 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let uu____7621 = et
in (match (uu____7621) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (uu____7735) -> begin
(

let trec = tc
in (

let uu____7748 = (tycon_record_as_variant trec)
in (match (uu____7748) with
| (t, fs) -> begin
(

let uu____7779 = (

let uu____7781 = (

let uu____7782 = (

let uu____7787 = (

let uu____7789 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.ids_of_lid uu____7789))
in ((uu____7787), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____7782))
in (uu____7781)::quals)
in (collect_tcs uu____7779 ((env), (tcs)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let uu____7835 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____7835) with
| (env, uu____7866, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let uu____7944 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____7944) with
| (env, uu____7975, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (binders), (t), (quals))))::tcs))
end))
end
| uu____8039 -> begin
(failwith "Unrecognized mutual type definition")
end)
end)))
in (

let uu____8063 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (uu____8063) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun uu___207_8301 -> (match (uu___207_8301) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, uu____8333, uu____8334, uu____8335, uu____8336), binders, t, quals) -> begin
(

let t = (

let uu____8369 = (typars_of_binders env binders)
in (match (uu____8369) with
| (env, tpars) -> begin
(

let uu____8386 = (push_tparams env tpars)
in (match (uu____8386) with
| (env_tps, tpars) -> begin
(

let t = (desugar_typ env_tps t)
in (

let tpars = (FStar_Syntax_Subst.close_binders tpars)
in (FStar_Syntax_Subst.close tpars t)))
end))
end))
in (

let uu____8405 = (

let uu____8412 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in (([]), (uu____8412)))
in (uu____8405)::[]))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, uu____8437, tags, uu____8439), constrs, tconstr, quals) -> begin
(

let mk_tot = (fun t -> (

let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)))
in (

let tycon = ((tname), (tpars), (k))
in (

let uu____8492 = (push_tparams env tpars)
in (match (uu____8492) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun uu____8527 -> (match (uu____8527) with
| (x, uu____8535) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let tot_tconstr = (mk_tot tconstr)
in (

let uu____8540 = (

let uu____8551 = (FStar_All.pipe_right constrs (FStar_List.map (fun uu____8591 -> (match (uu____8591) with
| (id, topt, uu____8608, of_notation) -> begin
(

let t = (match (of_notation) with
| true -> begin
(match (topt) with
| Some (t) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level None))::[]), (tot_tconstr)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end
| None -> begin
tconstr
end)
end
| uu____8617 -> begin
(match (topt) with
| None -> begin
(failwith "Impossible")
end
| Some (t) -> begin
t
end)
end)
in (

let t = (

let uu____8620 = (close env_tps t)
in (desugar_term env_tps uu____8620))
in (

let name = (FStar_ToSyntax_Env.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun uu___206_8626 -> (match (uu___206_8626) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| uu____8633 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (

let uu____8639 = (

let uu____8646 = (

let uu____8647 = (

let uu____8658 = (

let uu____8661 = (

let uu____8664 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total uu____8664))
in (FStar_Syntax_Util.arrow data_tpars uu____8661))
in ((name), (univs), (uu____8658), (tname), (ntps), (quals), (mutuals), (rng)))
in FStar_Syntax_Syntax.Sig_datacon (uu____8647))
in ((tps), (uu____8646)))
in ((name), (uu____8639))))))))
end))))
in (FStar_All.pipe_left FStar_List.split uu____8551))
in (match (uu____8540) with
| (constrNames, constrs) -> begin
((([]), (FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))))::constrs
end))))
end))))
end
| uu____8749 -> begin
(failwith "impossible")
end))))
in (

let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (

let uu____8797 = (

let uu____8801 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals uu____8801 rng))
in (match (uu____8797) with
| (bundle, abbrevs) -> begin
(

let env = (FStar_ToSyntax_Env.push_sigelt env0 bundle)
in (

let env = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env abbrevs)
in (

let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projector_names quals env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun uu___208_8835 -> (match (uu___208_8835) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, uu____8838, tps, k, uu____8841, constrs, quals, uu____8844) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::quals
end
| uu____8857 -> begin
quals
end)
in (mk_data_discriminators quals env tname tps k constrs))
end
| uu____8858 -> begin
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

let uu____8876 = (FStar_List.fold_left (fun uu____8883 b -> (match (uu____8883) with
| (env, binders) -> begin
(

let uu____8895 = (desugar_binder env b)
in (match (uu____8895) with
| (Some (a), k) -> begin
(

let uu____8905 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____8905) with
| (env, a) -> begin
(

let uu____8913 = (

let uu____8915 = (FStar_Syntax_Syntax.mk_binder (

let uu___222_8916 = a
in {FStar_Syntax_Syntax.ppname = uu___222_8916.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___222_8916.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (uu____8915)::binders)
in ((env), (uu____8913)))
end))
end
| uu____8918 -> begin
(Prims.raise (FStar_Errors.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) binders)
in (match (uu____8876) with
| (env, binders) -> begin
((env), ((FStar_List.rev binders)))
end)))


let rec desugar_effect : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  Prims.bool  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_kind eff_decls actions for_free -> (

let env0 = env
in (

let monad_env = (FStar_ToSyntax_Env.enter_monad_scope env eff_name)
in (

let uu____9012 = (desugar_binders monad_env eff_binders)
in (match (uu____9012) with
| (env, binders) -> begin
(

let eff_k = (desugar_term env eff_kind)
in (

let uu____9024 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun uu____9035 decl -> (match (uu____9035) with
| (env, out) -> begin
(

let uu____9047 = (desugar_decl env decl)
in (match (uu____9047) with
| (env, ses) -> begin
(

let uu____9055 = (

let uu____9057 = (FStar_List.hd ses)
in (uu____9057)::out)
in ((env), (uu____9055)))
end))
end)) ((env), ([]))))
in (match (uu____9024) with
| (env, decls) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let actions = (FStar_All.pipe_right actions (FStar_List.map (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____9073, ((FStar_Parser_AST.TyconAbbrev (name, uu____9075, uu____9076, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (uu____9077, ((def, uu____9079))::((cps_type, uu____9081))::[]); FStar_Parser_AST.range = uu____9082; FStar_Parser_AST.level = uu____9083}), uu____9084))::[]) when (not (for_free)) -> begin
(

let uu____9110 = (FStar_ToSyntax_Env.qualify env name)
in (

let uu____9111 = (

let uu____9112 = (desugar_term env def)
in (FStar_Syntax_Subst.close binders uu____9112))
in (

let uu____9113 = (

let uu____9114 = (desugar_typ env cps_type)
in (FStar_Syntax_Subst.close binders uu____9114))
in {FStar_Syntax_Syntax.action_name = uu____9110; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = uu____9111; FStar_Syntax_Syntax.action_typ = uu____9113})))
end
| FStar_Parser_AST.Tycon (uu____9115, ((FStar_Parser_AST.TyconAbbrev (name, uu____9117, uu____9118, defn), uu____9120))::[]) when for_free -> begin
(

let uu____9137 = (FStar_ToSyntax_Env.qualify env name)
in (

let uu____9138 = (

let uu____9139 = (desugar_term env defn)
in (FStar_Syntax_Subst.close binders uu____9139))
in {FStar_Syntax_Syntax.action_name = uu____9137; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = uu____9138; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
end
| uu____9140 -> begin
(Prims.raise (FStar_Errors.Error ((("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples)."), (d.FStar_Parser_AST.drange)))))
end))))
in (

let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (

let lookup = (fun s -> (

let l = (FStar_ToSyntax_Env.qualify env (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange))))
in (

let uu____9150 = (

let uu____9151 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) uu____9151))
in (([]), (uu____9150)))))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (Some (mname))) quals)
in (

let se = (match (for_free) with
| true -> begin
(

let dummy_tscheme = (

let uu____9163 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (([]), (uu____9163)))
in (

let uu____9173 = (

let uu____9176 = (

let uu____9177 = (

let uu____9178 = (lookup "repr")
in (Prims.snd uu____9178))
in (

let uu____9183 = (lookup "return")
in (

let uu____9184 = (lookup "bind")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = uu____9177; FStar_Syntax_Syntax.return_repr = uu____9183; FStar_Syntax_Syntax.bind_repr = uu____9184; FStar_Syntax_Syntax.actions = actions})))
in ((uu____9176), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____9173)))
end
| uu____9185 -> begin
(

let rr = ((FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right qualifiers FStar_Syntax_Syntax.contains_reflectable))
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (

let uu____9194 = (

let uu____9197 = (

let uu____9198 = (lookup "return_wp")
in (

let uu____9199 = (lookup "bind_wp")
in (

let uu____9200 = (lookup "if_then_else")
in (

let uu____9201 = (lookup "ite_wp")
in (

let uu____9202 = (lookup "stronger")
in (

let uu____9203 = (lookup "close_wp")
in (

let uu____9204 = (lookup "assert_p")
in (

let uu____9205 = (lookup "assume_p")
in (

let uu____9206 = (lookup "null_wp")
in (

let uu____9207 = (lookup "trivial")
in (

let uu____9208 = (match (rr) with
| true -> begin
(

let uu____9209 = (lookup "repr")
in (FStar_All.pipe_left Prims.snd uu____9209))
end
| uu____9217 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let uu____9218 = (match (rr) with
| true -> begin
(lookup "return")
end
| uu____9219 -> begin
un_ts
end)
in (

let uu____9220 = (match (rr) with
| true -> begin
(lookup "bind")
end
| uu____9221 -> begin
un_ts
end)
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = uu____9198; FStar_Syntax_Syntax.bind_wp = uu____9199; FStar_Syntax_Syntax.if_then_else = uu____9200; FStar_Syntax_Syntax.ite_wp = uu____9201; FStar_Syntax_Syntax.stronger = uu____9202; FStar_Syntax_Syntax.close_wp = uu____9203; FStar_Syntax_Syntax.assert_p = uu____9204; FStar_Syntax_Syntax.assume_p = uu____9205; FStar_Syntax_Syntax.null_wp = uu____9206; FStar_Syntax_Syntax.trivial = uu____9207; FStar_Syntax_Syntax.repr = uu____9208; FStar_Syntax_Syntax.return_repr = uu____9218; FStar_Syntax_Syntax.bind_repr = uu____9220; FStar_Syntax_Syntax.actions = actions})))))))))))))
in ((uu____9197), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect (uu____9194))))
end)
in (

let env = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right actions (FStar_List.fold_left (fun env a -> (

let uu____9227 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env uu____9227))) env))
in (

let env = (

let uu____9229 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____9229) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let refl_decl = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]), (d.FStar_Parser_AST.drange)))
in (FStar_ToSyntax_Env.push_sigelt env refl_decl)))
end
| uu____9234 -> begin
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

let uu____9257 = (desugar_binders env eff_binders)
in (match (uu____9257) with
| (env, binders) -> begin
(

let uu____9268 = (

let uu____9277 = (head_and_args defn)
in (match (uu____9277) with
| (head, args) -> begin
(

let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_defn env) l)
end
| uu____9301 -> begin
(

let uu____9302 = (

let uu____9303 = (

let uu____9306 = (

let uu____9307 = (

let uu____9308 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat uu____9308 " not found"))
in (Prims.strcat "Effect " uu____9307))
in ((uu____9306), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____9303))
in (Prims.raise uu____9302))
end)
in (

let uu____9309 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____9325))::args_rev -> begin
(

let uu____9332 = (

let uu____9333 = (unparen last_arg)
in uu____9333.FStar_Parser_AST.tm)
in (match (uu____9332) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____9348 -> begin
(([]), (args))
end))
end
| uu____9353 -> begin
(([]), (args))
end)
in (match (uu____9309) with
| (cattributes, args) -> begin
(

let uu____9379 = (desugar_args env args)
in (

let uu____9384 = (desugar_attributes env cattributes)
in ((ed), (uu____9379), (uu____9384))))
end)))
end))
in (match (uu____9268) with
| (ed, args, cattributes) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let sub = (fun uu____9417 -> (match (uu____9417) with
| (uu____9424, x) -> begin
(

let uu____9428 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (uu____9428) with
| (edb, x) -> begin
((match (((FStar_List.length args) <> (FStar_List.length edb))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end
| uu____9446 -> begin
()
end);
(

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (

let uu____9448 = (

let uu____9449 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders uu____9449))
in (([]), (uu____9448))));
)
end))
end))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let ed = (

let uu____9453 = (

let uu____9455 = (trans_qual (Some (mname)))
in (FStar_List.map uu____9455 quals))
in (

let uu____9458 = (

let uu____9459 = (sub (([]), (ed.FStar_Syntax_Syntax.signature)))
in (Prims.snd uu____9459))
in (

let uu____9465 = (sub ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____9466 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____9467 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____9468 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____9469 = (sub ed.FStar_Syntax_Syntax.stronger)
in (

let uu____9470 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____9471 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____9472 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____9473 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____9474 = (sub ed.FStar_Syntax_Syntax.trivial)
in (

let uu____9475 = (

let uu____9476 = (sub (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd uu____9476))
in (

let uu____9482 = (sub ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____9483 = (sub ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____9484 = (FStar_List.map (fun action -> (

let uu____9487 = (FStar_ToSyntax_Env.qualify env action.FStar_Syntax_Syntax.action_unqualified_name)
in (

let uu____9488 = (

let uu____9489 = (sub (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd uu____9489))
in (

let uu____9495 = (

let uu____9496 = (sub (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd uu____9496))
in {FStar_Syntax_Syntax.action_name = uu____9487; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = uu____9488; FStar_Syntax_Syntax.action_typ = uu____9495})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = uu____9453; FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = uu____9458; FStar_Syntax_Syntax.ret_wp = uu____9465; FStar_Syntax_Syntax.bind_wp = uu____9466; FStar_Syntax_Syntax.if_then_else = uu____9467; FStar_Syntax_Syntax.ite_wp = uu____9468; FStar_Syntax_Syntax.stronger = uu____9469; FStar_Syntax_Syntax.close_wp = uu____9470; FStar_Syntax_Syntax.assert_p = uu____9471; FStar_Syntax_Syntax.assume_p = uu____9472; FStar_Syntax_Syntax.null_wp = uu____9473; FStar_Syntax_Syntax.trivial = uu____9474; FStar_Syntax_Syntax.repr = uu____9475; FStar_Syntax_Syntax.return_repr = uu____9482; FStar_Syntax_Syntax.bind_repr = uu____9483; FStar_Syntax_Syntax.actions = uu____9484}))))))))))))))))
in (

let se = (build_sigelt ed d.FStar_Parser_AST.drange)
in (

let monad_env = env
in (

let env = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun env a -> (

let uu____9509 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env uu____9509))) env))
in (

let env = (

let uu____9511 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____9511) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let refl_decl = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]), (d.FStar_Parser_AST.drange)))
in (FStar_ToSyntax_Env.push_sigelt env refl_decl)))
end
| uu____9517 -> begin
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
in ((match ((p = FStar_Parser_AST.LightOff)) with
| true -> begin
(FStar_Options.set_ml_ish ())
end
| uu____9534 -> begin
()
end);
((env), ((se)::[]));
))
end
| FStar_Parser_AST.Fsdoc (uu____9536) -> begin
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
(

let uu____9548 = (FStar_ToSyntax_Env.push_module_abbrev env x l)
in ((uu____9548), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, tcs) -> begin
(

let quals = (match (is_effect) with
| true -> begin
(FStar_Parser_AST.Effect_qual)::d.FStar_Parser_AST.quals
end
| uu____9563 -> begin
d.FStar_Parser_AST.quals
end)
in (

let tcs = (FStar_List.map (fun uu____9569 -> (match (uu____9569) with
| (x, uu____9574) -> begin
x
end)) tcs)
in (

let uu____9577 = (FStar_List.map (trans_qual None) quals)
in (desugar_tycon env d.FStar_Parser_AST.drange uu____9577 tcs))))
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
| ((p, uu____9616))::[] -> begin
(

let uu____9621 = (is_app_pattern p)
in (not (uu____9621)))
end
| uu____9622 -> begin
false
end))
in (match ((not (expand_toplevel_pattern))) with
| true -> begin
(

let as_inner_let = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let ds_lets = (desugar_term_maybe_top true env as_inner_let)
in (

let uu____9633 = (

let uu____9634 = (FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets)
in uu____9634.FStar_Syntax_Syntax.n)
in (match (uu____9633) with
| FStar_Syntax_Syntax.Tm_let (lbs, uu____9640) -> begin
(

let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals = (match (quals) with
| (uu____9660)::uu____9661 -> begin
(FStar_List.map (trans_qual None) quals)
end
| uu____9663 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun uu___209_9667 -> (match (uu___209_9667) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (uu____9669); FStar_Syntax_Syntax.lbunivs = uu____9670; FStar_Syntax_Syntax.lbtyp = uu____9671; FStar_Syntax_Syntax.lbeff = uu____9672; FStar_Syntax_Syntax.lbdef = uu____9673} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____9680; FStar_Syntax_Syntax.lbtyp = uu____9681; FStar_Syntax_Syntax.lbeff = uu____9682; FStar_Syntax_Syntax.lbdef = uu____9683} -> begin
(FStar_ToSyntax_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals = (

let uu____9695 = (FStar_All.pipe_right lets (FStar_Util.for_some (fun uu____9701 -> (match (uu____9701) with
| (uu____9704, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end))))
in (match (uu____9695) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____9707 -> begin
quals
end))
in (

let lbs = (

let uu____9712 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____9712) with
| true -> begin
(

let uu____9717 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu___223_9724 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let uu___224_9725 = fv
in {FStar_Syntax_Syntax.fv_name = uu___224_9725.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = uu___224_9725.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = uu___223_9724.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___223_9724.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___223_9724.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___223_9724.FStar_Syntax_Syntax.lbdef})))))
in (((Prims.fst lbs)), (uu____9717)))
end
| uu____9731 -> begin
lbs
end))
in (

let s = (

let uu____9733 = (

let uu____9742 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in ((lbs), (d.FStar_Parser_AST.drange), (uu____9742), (quals), (attrs)))
in FStar_Syntax_Syntax.Sig_let (uu____9733))
in (

let env = (FStar_ToSyntax_Env.push_sigelt env s)
in ((env), ((s)::[]))))))))
end
| uu____9759 -> begin
(failwith "Desugaring a let did not produce a let")
end))))
end
| uu____9762 -> begin
(

let uu____9763 = (match (lets) with
| ((pat, body))::[] -> begin
((pat), (body))
end
| uu____9774 -> begin
(failwith "expand_toplevel_pattern should only allow single definition lets")
end)
in (match (uu____9763) with
| (pat, body) -> begin
(

let fresh_toplevel_name = (FStar_Ident.gen FStar_Range.dummyRange)
in (

let fresh_pat = (

let var_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((fresh_toplevel_name), (None)))) FStar_Range.dummyRange)
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, ty) -> begin
(

let uu___225_9790 = pat
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed (((var_pat), (ty))); FStar_Parser_AST.prange = uu___225_9790.FStar_Parser_AST.prange})
end
| uu____9791 -> begin
var_pat
end))
in (

let main_let = (desugar_decl env (

let uu___226_9795 = d
in {FStar_Parser_AST.d = FStar_Parser_AST.TopLevelLet (((isrec), ((((fresh_pat), (body)))::[]))); FStar_Parser_AST.drange = uu___226_9795.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___226_9795.FStar_Parser_AST.doc; FStar_Parser_AST.quals = (FStar_Parser_AST.Private)::d.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = uu___226_9795.FStar_Parser_AST.attrs}))
in (

let build_projection = (fun uu____9814 id -> (match (uu____9814) with
| (env, ses) -> begin
(

let main = (

let uu____9827 = (

let uu____9828 = (FStar_Ident.lid_of_ids ((fresh_toplevel_name)::[]))
in FStar_Parser_AST.Var (uu____9828))
in (FStar_Parser_AST.mk_term uu____9827 FStar_Range.dummyRange FStar_Parser_AST.Expr))
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

let uu____9856 = (desugar_decl env id_decl)
in (match (uu____9856) with
| (env, ses') -> begin
((env), ((FStar_List.append ses ses')))
end))))))))
end))
in (

let bvs = (

let uu____9867 = (gather_pattern_bound_vars pat)
in (FStar_All.pipe_right uu____9867 FStar_Util.set_elements))
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
in (

let uu____9881 = (

let uu____9883 = (

let uu____9884 = (

let uu____9890 = (FStar_ToSyntax_Env.qualify env id)
in ((uu____9890), (f), ((FStar_Syntax_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_assume (uu____9884))
in (uu____9883)::[])
in ((env), (uu____9881))))
end
| FStar_Parser_AST.Val (id, t) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let t = (

let uu____9897 = (close_fun env t)
in (desugar_term env uu____9897))
in (

let quals = (match ((env.FStar_ToSyntax_Env.iface && env.FStar_ToSyntax_Env.admitted_iface)) with
| true -> begin
(FStar_Parser_AST.Assumption)::quals
end
| uu____9901 -> begin
quals
end)
in (

let se = (

let uu____9903 = (

let uu____9910 = (FStar_ToSyntax_Env.qualify env id)
in (

let uu____9911 = (FStar_List.map (trans_qual None) quals)
in ((uu____9910), ([]), (t), (uu____9911), (d.FStar_Parser_AST.drange))))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____9903))
in (

let env = (FStar_ToSyntax_Env.push_sigelt env se)
in ((env), ((se)::[])))))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(

let uu____9919 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (match (uu____9919) with
| (t, uu____9927) -> begin
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

let t = (

let uu____9954 = (

let uu____9958 = (FStar_Syntax_Syntax.null_binder t)
in (uu____9958)::[])
in (

let uu____9959 = (

let uu____9962 = (

let uu____9963 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (Prims.fst uu____9963))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____9962))
in (FStar_Syntax_Util.arrow uu____9954 uu____9959)))
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

let uu____10034 = (FStar_ToSyntax_Env.try_lookup_effect_name env l)
in (match (uu____10034) with
| None -> begin
(

let uu____10036 = (

let uu____10037 = (

let uu____10040 = (

let uu____10041 = (

let uu____10042 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat uu____10042 " not found"))
in (Prims.strcat "Effect name " uu____10041))
in ((uu____10040), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____10037))
in (Prims.raise uu____10036))
end
| Some (l) -> begin
l
end)))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let uu____10046 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(

let uu____10068 = (

let uu____10073 = (

let uu____10077 = (desugar_term env t)
in (([]), (uu____10077)))
in Some (uu____10073))
in ((uu____10068), (None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(

let uu____10095 = (

let uu____10100 = (

let uu____10104 = (desugar_term env wp)
in (([]), (uu____10104)))
in Some (uu____10100))
in (

let uu____10109 = (

let uu____10114 = (

let uu____10118 = (desugar_term env t)
in (([]), (uu____10118)))
in Some (uu____10114))
in ((uu____10095), (uu____10109))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(

let uu____10132 = (

let uu____10137 = (

let uu____10141 = (desugar_term env t)
in (([]), (uu____10141)))
in Some (uu____10137))
in ((None), (uu____10132)))
end)
in (match (uu____10046) with
| (lift_wp, lift) -> begin
(

let se = FStar_Syntax_Syntax.Sig_sub_effect ((({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun uu____10192 d -> (match (uu____10192) with
| (env, sigelts) -> begin
(

let uu____10204 = (desugar_decl env d)
in (match (uu____10204) with
| (env, se) -> begin
((env), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))


let open_prims_all : (FStar_Parser_AST.decoration Prims.list  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]


let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env = (match (((curmod), (m))) with
| (None, uu____10246) -> begin
env
end
| (Some ({FStar_Syntax_Syntax.name = prev_lid; FStar_Syntax_Syntax.declarations = uu____10249; FStar_Syntax_Syntax.exports = uu____10250; FStar_Syntax_Syntax.is_interface = uu____10251}), FStar_Parser_AST.Module (current_lid, uu____10253)) when ((FStar_Ident.lid_equals prev_lid current_lid) && (FStar_Options.interactive ())) -> begin
env
end
| (Some (prev_mod), uu____10258) -> begin
(FStar_ToSyntax_Env.finish_module_or_interface env prev_mod)
end)
in (

let uu____10260 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(

let uu____10280 = (FStar_ToSyntax_Env.prepare_module_or_interface true admitted env mname)
in ((uu____10280), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(

let uu____10290 = (FStar_ToSyntax_Env.prepare_module_or_interface false false env mname)
in ((uu____10290), (mname), (decls), (false)))
end)
in (match (uu____10260) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let uu____10308 = (desugar_decls env decls)
in (match (uu____10308) with
| (env, sigelts) -> begin
(

let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in ((env), (modul), (pop_when_done)))
end))
end))))


let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (

let m = (

let uu____10333 = ((FStar_Options.interactive ()) && (

let uu____10334 = (

let uu____10335 = (

let uu____10336 = (FStar_Options.file_list ())
in (FStar_List.hd uu____10336))
in (FStar_Util.get_file_extension uu____10335))
in (uu____10334 = "fsti")))
in (match (uu____10333) with
| true -> begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface (((mname), (decls), (true)))
end
| FStar_Parser_AST.Interface (mname, uu____10344, uu____10345) -> begin
(failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end
| uu____10348 -> begin
m
end))
in (

let uu____10349 = (desugar_modul_common curmod env m)
in (match (uu____10349) with
| (x, y, pop_when_done) -> begin
((match (pop_when_done) with
| true -> begin
(

let uu____10359 = (FStar_ToSyntax_Env.pop ())
in ())
end
| uu____10360 -> begin
()
end);
((x), (y));
)
end))))


let desugar_modul : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun env m -> (

let uu____10371 = (desugar_modul_common None env m)
in (match (uu____10371) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_ToSyntax_Env.finish_module_or_interface env modul)
in ((

let uu____10382 = (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____10382) with
| true -> begin
(

let uu____10383 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" uu____10383))
end
| uu____10384 -> begin
()
end));
(

let uu____10385 = (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end
| uu____10386 -> begin
env
end)
in ((uu____10385), (modul)));
))
end)))


let desugar_file : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (

let uu____10396 = (FStar_List.fold_left (fun uu____10403 m -> (match (uu____10403) with
| (env, mods) -> begin
(

let uu____10415 = (desugar_modul env m)
in (match (uu____10415) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (uu____10396) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_ToSyntax_Env.env  ->  FStar_ToSyntax_Env.env = (fun m en -> (

let uu____10439 = (FStar_ToSyntax_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (uu____10439) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt (

let uu___227_10445 = en
in {FStar_ToSyntax_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_ToSyntax_Env.curmonad = uu___227_10445.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = uu___227_10445.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = uu___227_10445.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = uu___227_10445.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = uu___227_10445.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = uu___227_10445.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = uu___227_10445.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = uu___227_10445.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.iface = uu___227_10445.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = uu___227_10445.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = uu___227_10445.FStar_ToSyntax_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (

let env = (FStar_ToSyntax_Env.finish_module_or_interface en m)
in (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name env)
end
| uu____10447 -> begin
env
end)))
end)))




