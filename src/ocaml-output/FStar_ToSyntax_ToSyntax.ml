
open Prims

let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun uu___183_5 -> (match (uu___183_5) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| uu____8 -> begin
None
end))


let trans_qual : FStar_Range.range  ->  FStar_Ident.lident Prims.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r maybe_effect_id uu___184_19 -> (match (uu___184_19) with
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


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun uu___185_25 -> (match (uu___185_25) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end
| FStar_Parser_AST.LightOff -> begin
FStar_Syntax_Syntax.LightOff
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun uu___186_32 -> (match (uu___186_32) with
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


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun uu___187_750 -> (match (uu___187_750) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| uu____755 -> begin
(failwith "Impossible")
end))


let as_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_ToSyntax_Env.env) = (fun env imp uu___188_772 -> (match (uu___188_772) with
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

let uu___209_796 = a
in {FStar_Syntax_Syntax.ppname = uu___209_796.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___209_796.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env))
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


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun uu___189_1056 -> (match (uu___189_1056) with
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
(match ((FStar_List.existsb (fun uu___190_1182 -> (match (uu___190_1182) with
| FStar_Util.Inr (uu____1185) -> begin
true
end
| uu____1186 -> begin
false
end)) univargs)) with
| true -> begin
(

let uu____1189 = (

let uu____1190 = (FStar_List.map (fun uu___191_1194 -> (match (uu___191_1194) with
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

let nargs = (FStar_List.map (fun uu___192_1204 -> (match (uu___192_1204) with
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
| FStar_Syntax_Syntax.Pat_cons (uu____1446, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out uu____1468 -> (match (uu____1468) with
| (p, uu____1474) -> begin
(

let uu____1475 = (pat_vars p)
in (FStar_Util.set_union out uu____1475))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let xs = (pat_vars hd)
in (

let uu____1489 = (

let uu____1490 = (FStar_Util.for_all (fun p -> (

let ys = (pat_vars p)
in ((FStar_Util.set_is_subset_of xs ys) && (FStar_Util.set_is_subset_of ys xs)))) tl)
in (not (uu____1490)))
in (match (uu____1489) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Disjunctive pattern binds different variables in each case"), (p.FStar_Syntax_Syntax.p)))))
end
| uu____1493 -> begin
xs
end)))
end))
in (pat_vars p)))
in ((match (((is_mut), (p.FStar_Parser_AST.pat))) with
| ((false, _)) | ((true, FStar_Parser_AST.PatVar (_))) -> begin
()
end
| (true, uu____1497) -> begin
(Prims.raise (FStar_Errors.Error ((("let-mutable is for variables only"), (p.FStar_Parser_AST.prange)))))
end);
(

let push_bv_maybe_mut = (match (is_mut) with
| true -> begin
FStar_ToSyntax_Env.push_bv_mutable
end
| uu____1511 -> begin
FStar_ToSyntax_Env.push_bv
end)
in (

let resolvex = (fun l e x -> (

let uu____1525 = (FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))
in (match (uu____1525) with
| Some (y) -> begin
((l), (e), (y))
end
| uu____1533 -> begin
(

let uu____1535 = (push_bv_maybe_mut e x)
in (match (uu____1535) with
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

let uu____1584 = (

let uu____1585 = (

let uu____1586 = (

let uu____1590 = (

let uu____1591 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") op)
in (FStar_Ident.id_of_text uu____1591))
in ((uu____1590), (None)))
in FStar_Parser_AST.PatVar (uu____1586))
in {FStar_Parser_AST.pat = uu____1585; FStar_Parser_AST.prange = p.FStar_Parser_AST.prange})
in (aux loc env uu____1584))
end
| FStar_Parser_AST.PatOr ([]) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(

let uu____1603 = (aux loc env p)
in (match (uu____1603) with
| (loc, env, var, p, uu____1622) -> begin
(

let uu____1627 = (FStar_List.fold_left (fun uu____1640 p -> (match (uu____1640) with
| (loc, env, ps) -> begin
(

let uu____1663 = (aux loc env p)
in (match (uu____1663) with
| (loc, env, uu____1679, p, uu____1681) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (uu____1627) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in ((loc), (env), (var), (pat), (false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let uu____1725 = (aux loc env p)
in (match (uu____1725) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (uu____1750) -> begin
(failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t = (

let uu____1756 = (close_fun env t)
in (desugar_term env uu____1756))
in ((match ((match (x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| uu____1758 -> begin
true
end)) with
| true -> begin
(

let uu____1759 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____1760 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____1761 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3_warning "Multiple ascriptions for %s in pattern, type %s was shadowed by %s" uu____1759 uu____1760 uu____1761))))
end
| uu____1762 -> begin
()
end);
LocalBinder ((((

let uu___210_1763 = x
in {FStar_Syntax_Syntax.ppname = uu___210_1763.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___210_1763.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (aq)));
))
end)
in ((loc), (env'), (binder), (p), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1767 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env), (LocalBinder (((x), (None)))), (uu____1767), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1777 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env), (LocalBinder (((x), (None)))), (uu____1777), (false))))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let uu____1795 = (resolvex loc env x)
in (match (uu____1795) with
| (loc, env, xbv) -> begin
(

let uu____1809 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc), (env), (LocalBinder (((xbv), (aq)))), (uu____1809), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1820 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), ([])))))
in ((loc), (env), (LocalBinder (((x), (None)))), (uu____1820), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = uu____1838}, args) -> begin
(

let uu____1842 = (FStar_List.fold_right (fun arg uu____1860 -> (match (uu____1860) with
| (loc, env, args) -> begin
(

let uu____1890 = (aux loc env arg)
in (match (uu____1890) with
| (loc, env, uu____1908, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (uu____1842) with
| (loc, env, args) -> begin
(

let l = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1957 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (uu____1957), (false)))))
end))
end
| FStar_Parser_AST.PatApp (uu____1970) -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____1983 = (FStar_List.fold_right (fun pat uu____1997 -> (match (uu____1997) with
| (loc, env, pats) -> begin
(

let uu____2019 = (aux loc env pat)
in (match (uu____2019) with
| (loc, env, uu____2035, pat, uu____2037) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (uu____1983) with
| (loc, env, pats) -> begin
(

let pat = (

let uu____2071 = (

let uu____2074 = (

let uu____2079 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r uu____2079))
in (

let uu____2080 = (

let uu____2081 = (

let uu____2089 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____2089), ([])))
in FStar_Syntax_Syntax.Pat_cons (uu____2081))
in (FStar_All.pipe_left uu____2074 uu____2080)))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (

let uu____2112 = (

let uu____2113 = (

let uu____2121 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____2121), ((((hd), (false)))::(((tl), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (uu____2113))
in (FStar_All.pipe_left (pos_r r) uu____2112)))) pats uu____2071))
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc), (env), (LocalBinder (((x), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let uu____2153 = (FStar_List.fold_left (fun uu____2170 p -> (match (uu____2170) with
| (loc, env, pats) -> begin
(

let uu____2201 = (aux loc env p)
in (match (uu____2201) with
| (loc, env, uu____2219, pat, uu____2221) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (uu____2153) with
| (loc, env, args) -> begin
(

let args = (FStar_List.rev args)
in (

let l = (match (dep) with
| true -> begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
| uu____2284 -> begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end)
in (

let uu____2292 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) l)
in (match (uu____2292) with
| (constr, uu____2305) -> begin
(

let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____2308 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____2310 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (uu____2310), (false)))))
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

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun uu____2351 -> (match (uu____2351) with
| (f, p) -> begin
((f.FStar_Ident.ident), (p))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____2366 -> (match (uu____2366) with
| (f, uu____2370) -> begin
(

let uu____2371 = (FStar_All.pipe_right fields (FStar_List.tryFind (fun uu____2383 -> (match (uu____2383) with
| (g, uu____2387) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.idText)
end))))
in (match (uu____2371) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (uu____2390, p) -> begin
p
end))
end))))
in (

let app = (

let uu____2395 = (

let uu____2396 = (

let uu____2400 = (

let uu____2401 = (

let uu____2402 = (FStar_Ident.lid_of_ids (FStar_List.append record.FStar_ToSyntax_Env.typename.FStar_Ident.ns ((record.FStar_ToSyntax_Env.constrname)::[])))
in FStar_Parser_AST.PatName (uu____2402))
in (FStar_Parser_AST.mk_pattern uu____2401 p.FStar_Parser_AST.prange))
in ((uu____2400), (args)))
in FStar_Parser_AST.PatApp (uu____2396))
in (FStar_Parser_AST.mk_pattern uu____2395 p.FStar_Parser_AST.prange))
in (

let uu____2404 = (aux loc env app)
in (match (uu____2404) with
| (env, e, b, p, uu____2423) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(

let uu____2445 = (

let uu____2446 = (

let uu____2454 = (

let uu___211_2455 = fv
in (

let uu____2456 = (

let uu____2458 = (

let uu____2459 = (

let uu____2463 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_ToSyntax_Env.typename), (uu____2463)))
in FStar_Syntax_Syntax.Record_ctor (uu____2459))
in Some (uu____2458))
in {FStar_Syntax_Syntax.fv_name = uu___211_2455.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = uu___211_2455.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu____2456}))
in ((uu____2454), (args)))
in FStar_Syntax_Syntax.Pat_cons (uu____2446))
in (FStar_All.pipe_left pos uu____2445))
end
| uu____2482 -> begin
p
end)
in ((env), (e), (b), (p), (false)))
end))))))
end))))
in (

let uu____2485 = (aux [] env p)
in (match (uu____2485) with
| (uu____2496, env, b, p, uu____2500) -> begin
((

let uu____2506 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore uu____2506));
((env), (b), (p));
)
end)))));
)))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p is_mut -> (

let mklet = (fun x -> (

let uu____2525 = (

let uu____2526 = (

let uu____2529 = (FStar_ToSyntax_Env.qualify env x)
in ((uu____2529), (FStar_Syntax_Syntax.tun)))
in LetBinder (uu____2526))
in ((env), (uu____2525), (None))))
in (match (top) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(

let uu____2540 = (

let uu____2541 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") x)
in (FStar_Ident.id_of_text uu____2541))
in (mklet uu____2540))
end
| FStar_Parser_AST.PatVar (x, uu____2543) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2547); FStar_Parser_AST.prange = uu____2548}, t) -> begin
(

let uu____2552 = (

let uu____2553 = (

let uu____2556 = (FStar_ToSyntax_Env.qualify env x)
in (

let uu____2557 = (desugar_term env t)
in ((uu____2556), (uu____2557))))
in LetBinder (uu____2553))
in ((env), (uu____2552), (None)))
end
| uu____2559 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end
| uu____2564 -> begin
(

let uu____2565 = (desugar_data_pat env p is_mut)
in (match (uu____2565) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| uu____2581 -> begin
Some (p)
end)
in ((env), (binder), (p)))
end))
end)))
and desugar_binding_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun uu____2585 env pat -> (

let uu____2588 = (desugar_data_pat env pat false)
in (match (uu____2588) with
| (env, uu____2595, pat) -> begin
((env), (pat))
end)))
and desugar_match_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let uu___212_2602 = env
in {FStar_ToSyntax_Env.curmodule = uu___212_2602.FStar_ToSyntax_Env.curmodule; FStar_ToSyntax_Env.curmonad = uu___212_2602.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = uu___212_2602.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = uu___212_2602.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = uu___212_2602.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = uu___212_2602.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = uu___212_2602.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = uu___212_2602.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = uu___212_2602.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.iface = uu___212_2602.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = uu___212_2602.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let uu___213_2606 = env
in {FStar_ToSyntax_Env.curmodule = uu___213_2606.FStar_ToSyntax_Env.curmodule; FStar_ToSyntax_Env.curmonad = uu___213_2606.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = uu___213_2606.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = uu___213_2606.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = uu___213_2606.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = uu___213_2606.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = uu___213_2606.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = uu___213_2606.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = uu___213_2606.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.iface = uu___213_2606.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = uu___213_2606.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_machine_integer : FStar_ToSyntax_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env repr uu____2609 range -> (match (uu____2609) with
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

let uu____2620 = (FStar_ToSyntax_Env.try_lookup_lid env lid)
in (match (uu____2620) with
| Some (lid) -> begin
(Prims.fst lid)
end
| None -> begin
(

let uu____2631 = (FStar_Util.format1 "%s not in scope\n" (FStar_Ident.text_of_lid lid))
in (failwith uu____2631))
end))
in (

let repr = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (None)))))) None range)
in (

let uu____2648 = (

let uu____2651 = (

let uu____2652 = (

let uu____2662 = (

let uu____2668 = (

let uu____2673 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr), (uu____2673)))
in (uu____2668)::[])
in ((lid), (uu____2662)))
in FStar_Syntax_Syntax.Tm_app (uu____2652))
in (FStar_Syntax_Syntax.mk uu____2651))
in (uu____2648 None range))))))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env_t  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk setpos env l -> (

let uu____2707 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) l)
in (match (uu____2707) with
| (tm, mut) -> begin
(

let tm = (setpos tm)
in (match (mut) with
| true -> begin
(

let uu____2717 = (

let uu____2718 = (

let uu____2723 = (mk_ref_read tm)
in ((uu____2723), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (uu____2718))
in (FStar_All.pipe_left mk uu____2717))
end
| uu____2728 -> begin
tm
end))
end)))
and desugar_attributes : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (

let uu____2737 = (

let uu____2738 = (unparen t)
in uu____2738.FStar_Parser_AST.tm)
in (match (uu____2737) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = uu____2739; FStar_Ident.ident = uu____2740; FStar_Ident.nsstr = uu____2741; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| uu____2743 -> begin
(

let uu____2744 = (

let uu____2745 = (

let uu____2748 = (

let uu____2749 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " uu____2749))
in ((uu____2748), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____2745))
in (Prims.raise uu____2744))
end)))
in (FStar_List.map desugar_attribute cattributes)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk = (fun e -> ((FStar_Syntax_Syntax.mk e) None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let uu___214_2777 = e
in {FStar_Syntax_Syntax.n = uu___214_2777.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___214_2777.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___214_2777.FStar_Syntax_Syntax.vars}))
in (

let uu____2784 = (

let uu____2785 = (unparen top)
in uu____2785.FStar_Parser_AST.tm)
in (match (uu____2784) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (uu____2786) -> begin
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
| FStar_Parser_AST.Op ("*", (uu____2815)::(uu____2816)::[]) when (

let uu____2818 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right uu____2818 FStar_Option.isNone)) -> begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(

let uu____2830 = (flatten t1)
in (FStar_List.append uu____2830 ((t2)::[])))
end
| uu____2832 -> begin
(t)::[]
end))
in (

let targs = (

let uu____2835 = (

let uu____2837 = (unparen top)
in (flatten uu____2837))
in (FStar_All.pipe_right uu____2835 (FStar_List.map (fun t -> (

let uu____2841 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg uu____2841))))))
in (

let uu____2842 = (

let uu____2845 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) uu____2845))
in (match (uu____2842) with
| (tup, uu____2852) -> begin
(mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____2855 = (

let uu____2858 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) a)
in (Prims.fst uu____2858))
in (FStar_All.pipe_left setpos uu____2855))
end
| FStar_Parser_AST.Uvar (u) -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected universe variable " (Prims.strcat (FStar_Ident.text_of_id u) " in non-universe context"))), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(

let uu____2872 = (op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)
in (match (uu____2872) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected or unbound operator: " s)), (top.FStar_Parser_AST.range)))))
end
| Some (op) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (

let uu____2894 = (desugar_term env t)
in ((uu____2894), (None))))))
in (mk (FStar_Syntax_Syntax.Tm_app (((op), (args))))))
end
| uu____2900 -> begin
op
end)
end))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2901; FStar_Ident.ident = uu____2902; FStar_Ident.nsstr = uu____2903; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2905; FStar_Ident.ident = uu____2906; FStar_Ident.nsstr = uu____2907; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = uu____2909; FStar_Ident.ident = uu____2910; FStar_Ident.nsstr = uu____2911; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(

let uu____2921 = (

let uu____2922 = (desugar_universe t)
in FStar_Syntax_Syntax.Tm_type (uu____2922))
in (mk uu____2921))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2923; FStar_Ident.ident = uu____2924; FStar_Ident.nsstr = uu____2925; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2927; FStar_Ident.ident = uu____2928; FStar_Ident.nsstr = uu____2929; FStar_Ident.str = "True"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2931; FStar_Ident.ident = uu____2932; FStar_Ident.nsstr = uu____2933; FStar_Ident.str = "False"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = uu____2937}) when ((is_special_effect_combinator txt) && (FStar_ToSyntax_Env.is_effect_name env eff_name)) -> begin
(

let uu____2938 = (FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name)
in (match (uu____2938) with
| Some (ed) -> begin
(

let uu____2941 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" txt))) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.fvar uu____2941 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
end
| None -> begin
(failwith "immpossible special_effect_combinator")
end))
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t2 = (desugar_term env t2)
in (

let uu____2945 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) ident)
in (match (uu____2945) with
| (t1, mut) -> begin
((match ((not (mut))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
end
| uu____2953 -> begin
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

let found = ((

let uu____2958 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (FStar_Option.isSome uu____2958)) || (

let uu____2960 = (FStar_ToSyntax_Env.try_lookup_effect_defn env l)
in (FStar_Option.isSome uu____2960)))
in (match (found) with
| true -> begin
(

let uu____2962 = (FStar_Syntax_Util.mk_field_projector_name_from_ident l i)
in (desugar_name mk setpos env uu____2962))
end
| uu____2963 -> begin
(

let uu____2964 = (

let uu____2965 = (

let uu____2968 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((uu____2968), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____2965))
in (Prims.raise uu____2964))
end))
end
| FStar_Parser_AST.Discrim (lid) -> begin
(

let uu____2970 = (FStar_ToSyntax_Env.try_lookup_datacon env lid)
in (match (uu____2970) with
| None -> begin
(

let uu____2972 = (

let uu____2973 = (

let uu____2976 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((uu____2976), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____2973))
in (Prims.raise uu____2972))
end
| uu____2977 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (desugar_name mk setpos env lid'))
end))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(

let uu____2988 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____2988) with
| Some (head) -> begin
(

let uu____2991 = (

let uu____2996 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in ((uu____2996), (true)))
in (match (uu____2991) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| uu____3009 -> begin
(

let uu____3013 = (FStar_Util.take (fun uu____3024 -> (match (uu____3024) with
| (uu____3027, imp) -> begin
(imp = FStar_Parser_AST.UnivApp)
end)) args)
in (match (uu____3013) with
| (universes, args) -> begin
(

let universes = (FStar_List.map (fun x -> (desugar_universe (Prims.fst x))) universes)
in (

let args = (FStar_List.map (fun uu____3060 -> (match (uu____3060) with
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
| uu____3075 -> begin
(mk (FStar_Syntax_Syntax.Tm_uinst (((head), (universes)))))
end)
in (

let app = (mk (FStar_Syntax_Syntax.Tm_app (((head), (args)))))
in (match (is_data) with
| true -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((app), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| uu____3090 -> begin
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

let uu____3095 = (FStar_List.fold_left (fun uu____3112 b -> (match (uu____3112) with
| (env, tparams, typs) -> begin
(

let uu____3143 = (desugar_binder env b)
in (match (uu____3143) with
| (xopt, t) -> begin
(

let uu____3159 = (match (xopt) with
| None -> begin
(

let uu____3164 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env), (uu____3164)))
end
| Some (x) -> begin
(FStar_ToSyntax_Env.push_bv env x)
end)
in (match (uu____3159) with
| (env, x) -> begin
(

let uu____3176 = (

let uu____3178 = (

let uu____3180 = (

let uu____3181 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3181))
in (uu____3180)::[])
in (FStar_List.append typs uu____3178))
in ((env), ((FStar_List.append tparams (((((

let uu___215_3194 = x
in {FStar_Syntax_Syntax.ppname = uu___215_3194.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___215_3194.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (None)))::[]))), (uu____3176)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level None))::[])))
in (match (uu____3095) with
| (env, uu____3207, targs) -> begin
(

let uu____3219 = (

let uu____3222 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) uu____3222))
in (match (uu____3219) with
| (tup, uu____3229) -> begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let uu____3237 = (uncurry binders t)
in (match (uu____3237) with
| (bs, t) -> begin
(

let rec aux = (fun env bs uu___193_3260 -> (match (uu___193_3260) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range env t)
in (

let uu____3270 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos uu____3270)))
end
| (hd)::tl -> begin
(

let bb = (desugar_binder env hd)
in (

let uu____3286 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (uu____3286) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end)))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(

let uu____3297 = (desugar_binder env b)
in (match (uu____3297) with
| (None, uu____3301) -> begin
(failwith "Missing binder in refinement")
end
| b -> begin
(

let uu____3307 = (as_binder env None b)
in (match (uu____3307) with
| ((x, uu____3311), env) -> begin
(

let f = (desugar_formula env f)
in (

let uu____3316 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos uu____3316)))
end))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let uu____3331 = (FStar_List.fold_left (fun uu____3338 pat -> (match (uu____3338) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (uu____3353, t) -> begin
(

let uu____3355 = (

let uu____3357 = (free_type_vars env t)
in (FStar_List.append uu____3357 ftvs))
in ((env), (uu____3355)))
end
| uu____3360 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (uu____3331) with
| (uu____3363, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (

let uu____3371 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append uu____3371 binders))
in (

let rec aux = (fun env bs sc_pat_opt uu___194_3400 -> (match (uu___194_3400) with
| [] -> begin
(

let body = (desugar_term env body)
in (

let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(

let body = (

let uu____3429 = (

let uu____3430 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right uu____3430 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close uu____3429 body))
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (None), (body)))::[]))))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (

let uu____3472 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos uu____3472))))
end
| (p)::rest -> begin
(

let uu____3480 = (desugar_binding_pat env p)
in (match (uu____3480) with
| (env, b, pat) -> begin
(

let uu____3492 = (match (b) with
| LetBinder (uu____3511) -> begin
(failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, uu____3542) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(

let uu____3565 = (

let uu____3568 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____3568), (p)))
in Some (uu____3565))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (uu____3593), uu____3594) -> begin
(

let tup2 = (

let uu____3596 = (FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____3596 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (

let uu____3600 = (

let uu____3603 = (

let uu____3604 = (

let uu____3614 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (

let uu____3617 = (

let uu____3619 = (FStar_Syntax_Syntax.as_arg sc)
in (

let uu____3620 = (

let uu____3622 = (

let uu____3623 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3623))
in (uu____3622)::[])
in (uu____3619)::uu____3620))
in ((uu____3614), (uu____3617))))
in FStar_Syntax_Syntax.Tm_app (uu____3604))
in (FStar_Syntax_Syntax.mk uu____3603))
in (uu____3600 None top.FStar_Parser_AST.range))
in (

let p = (

let uu____3638 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p), (false)))::[])))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n uu____3638))
in Some (((sc), (p))))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____3658, args), FStar_Syntax_Syntax.Pat_cons (uu____3660, pats)) -> begin
(

let tupn = (

let uu____3687 = (FStar_Syntax_Util.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____3687 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (

let uu____3697 = (

let uu____3698 = (

let uu____3708 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (

let uu____3711 = (

let uu____3717 = (

let uu____3723 = (

let uu____3724 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3724))
in (uu____3723)::[])
in (FStar_List.append args uu____3717))
in ((uu____3708), (uu____3711))))
in FStar_Syntax_Syntax.Tm_app (uu____3698))
in (mk uu____3697))
in (

let p = (

let uu____3739 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p), (false)))::[])))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n uu____3739))
in Some (((sc), (p))))))
end
| uu____3763 -> begin
(failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt)))
end)
in (match (uu____3492) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end)))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = rng; FStar_Parser_AST.level = uu____3806}, phi, uu____3808) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env phi)
in (

let a = (FStar_Ident.set_lid_range a rng)
in (

let uu____3811 = (

let uu____3812 = (

let uu____3822 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (

let uu____3823 = (

let uu____3825 = (FStar_Syntax_Syntax.as_arg phi)
in (

let uu____3826 = (

let uu____3828 = (

let uu____3829 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3829))
in (uu____3828)::[])
in (uu____3825)::uu____3826))
in ((uu____3822), (uu____3823))))
in FStar_Syntax_Syntax.Tm_app (uu____3812))
in (mk uu____3811))))
end
| FStar_Parser_AST.App (uu____3831, uu____3832, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (

let uu____3844 = (

let uu____3845 = (unparen e)
in uu____3845.FStar_Parser_AST.tm)
in (match (uu____3844) with
| FStar_Parser_AST.App (e, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e))
end
| uu____3851 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_uinst (((head), (universes))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.App (uu____3854) -> begin
(

let rec aux = (fun args e -> (

let uu____3875 = (

let uu____3876 = (unparen e)
in uu____3876.FStar_Parser_AST.tm)
in (match (uu____3875) with
| FStar_Parser_AST.App (e, t, imp) when (imp <> FStar_Parser_AST.UnivApp) -> begin
(

let arg = (

let uu____3886 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) uu____3886))
in (aux ((arg)::args) e))
end
| uu____3893 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let uu____3904 = (

let uu____3905 = (

let uu____3910 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((uu____3910), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))
in FStar_Syntax_Syntax.Tm_meta (uu____3905))
in (mk uu____3904))
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

let ds_let_rec_or_app = (fun uu____3940 -> (

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun uu____3982 -> (match (uu____3982) with
| (p, def) -> begin
(

let uu____3996 = (is_app_pattern p)
in (match (uu____3996) with
| true -> begin
(

let uu____4006 = (destruct_app_pattern env top_level p)
in ((uu____4006), (def)))
end
| uu____4021 -> begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(

let uu____4035 = (destruct_app_pattern env top_level p)
in ((uu____4035), (def)))
end
| uu____4050 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____4064); FStar_Parser_AST.prange = uu____4065}, t) -> begin
(match (top_level) with
| true -> begin
(

let uu____4078 = (

let uu____4086 = (

let uu____4089 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____4089))
in ((uu____4086), ([]), (Some (t))))
in ((uu____4078), (def)))
end
| uu____4101 -> begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end)
end
| FStar_Parser_AST.PatVar (id, uu____4114) -> begin
(match (top_level) with
| true -> begin
(

let uu____4126 = (

let uu____4134 = (

let uu____4137 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____4137))
in ((uu____4134), ([]), (None)))
in ((uu____4126), (def)))
end
| uu____4149 -> begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end)
end
| uu____4161 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end))
end))))
in (

let uu____4171 = (FStar_List.fold_left (fun uu____4195 uu____4196 -> (match (((uu____4195), (uu____4196))) with
| ((env, fnames, rec_bindings), ((f, uu____4240, uu____4241), uu____4242)) -> begin
(

let uu____4282 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let uu____4296 = (FStar_ToSyntax_Env.push_bv env x)
in (match (uu____4296) with
| (env, xx) -> begin
(

let uu____4307 = (

let uu____4309 = (FStar_Syntax_Syntax.mk_binder xx)
in (uu____4309)::rec_bindings)
in ((env), (FStar_Util.Inl (xx)), (uu____4307)))
end))
end
| FStar_Util.Inr (l) -> begin
(

let uu____4314 = (FStar_ToSyntax_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((uu____4314), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (uu____4282) with
| (env, lbname, rec_bindings) -> begin
((env), ((lbname)::fnames), (rec_bindings))
end))
end)) ((env), ([]), ([])) funs)
in (match (uu____4171) with
| (env', fnames, rec_bindings) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let rec_bindings = (FStar_List.rev rec_bindings)
in (

let desugar_one_def = (fun env lbname uu____4387 -> (match (uu____4387) with
| ((uu____4399, args, result_t), def) -> begin
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

let uu____4425 = (is_comp_type env t)
in (match (uu____4425) with
| true -> begin
((

let uu____4427 = (FStar_All.pipe_right args (FStar_List.tryFind (fun x -> (

let uu____4432 = (is_var_pattern x)
in (not (uu____4432))))))
in (match (uu____4427) with
| None -> begin
()
end
| Some (p) -> begin
(Prims.raise (FStar_Errors.Error ((("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable"), (p.FStar_Parser_AST.prange)))))
end));
t;
)
end
| uu____4434 -> begin
(

let uu____4435 = (((FStar_Options.ml_ish ()) && (

let uu____4436 = (FStar_ToSyntax_Env.try_lookup_effect_name env FStar_Syntax_Const.effect_ML_lid)
in (FStar_Option.isSome uu____4436))) && ((not (is_rec)) || ((FStar_List.length args) <> (Prims.parse_int "0"))))
in (match (uu____4435) with
| true -> begin
(FStar_Parser_AST.ml_comp t)
end
| uu____4440 -> begin
(FStar_Parser_AST.tot_comp t)
end))
end))
in (

let uu____4441 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) uu____4441 FStar_Parser_AST.Expr)))
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| uu____4443 -> begin
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

let uu____4453 = (

let uu____4454 = (FStar_Syntax_Util.incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l uu____4454 None))
in FStar_Util.Inr (uu____4453))
end)
in (

let body = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.close rec_bindings body)
end
| uu____4456 -> begin
body
end)
in (mk_lb ((lbname), (FStar_Syntax_Syntax.tun), (body)))))))))
end))
in (

let lbs = (FStar_List.map2 (desugar_one_def (match (is_rec) with
| true -> begin
env'
end
| uu____4472 -> begin
env
end)) fnames funs)
in (

let body = (desugar_term env' body)
in (

let uu____4474 = (

let uu____4475 = (

let uu____4483 = (FStar_Syntax_Subst.close rec_bindings body)
in ((((is_rec), (lbs))), (uu____4483)))
in FStar_Syntax_Syntax.Tm_let (uu____4475))
in (FStar_All.pipe_left mk uu____4474)))))))
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
| uu____4509 -> begin
t1
end)
in (

let uu____4510 = (desugar_binding_pat_maybe_top top_level env pat is_mutable)
in (match (uu____4510) with
| (env, binder, pat) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body = (desugar_term env t2)
in (

let fv = (

let uu____4531 = (FStar_Syntax_Util.incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l uu____4531 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]))), (body)))))))
end
| LocalBinder (x, uu____4539) -> begin
(

let body = (desugar_term env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(

let uu____4548 = (

let uu____4551 = (

let uu____4552 = (

let uu____4568 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____4569 = (

let uu____4571 = (FStar_Syntax_Util.branch ((pat), (None), (body)))
in (uu____4571)::[])
in ((uu____4568), (uu____4569))))
in FStar_Syntax_Syntax.Tm_match (uu____4552))
in (FStar_Syntax_Syntax.mk uu____4551))
in (uu____4548 None body.FStar_Syntax_Syntax.pos))
end)
in (

let uu____4586 = (

let uu____4587 = (

let uu____4595 = (

let uu____4596 = (

let uu____4597 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4597)::[])
in (FStar_Syntax_Subst.close uu____4596 body))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t1))))::[]))), (uu____4595)))
in FStar_Syntax_Syntax.Tm_let (uu____4587))
in (FStar_All.pipe_left mk uu____4586))))
end)
in (match (is_mutable) with
| true -> begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc))))))
end
| uu____4616 -> begin
tm
end))
end))))))
in (

let uu____4617 = (is_rec || (is_app_pattern pat))
in (match (uu____4617) with
| true -> begin
(ds_let_rec_or_app ())
end
| uu____4618 -> begin
(ds_non_rec pat _snd body)
end)))))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let uu____4623 = (

let uu____4624 = (

let uu____4640 = (desugar_term env t1)
in (

let uu____4641 = (

let uu____4651 = (

let uu____4660 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (

let uu____4663 = (desugar_term env t2)
in ((uu____4660), (None), (uu____4663))))
in (

let uu____4671 = (

let uu____4681 = (

let uu____4690 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (

let uu____4693 = (desugar_term env t3)
in ((uu____4690), (None), (uu____4693))))
in (uu____4681)::[])
in (uu____4651)::uu____4671))
in ((uu____4640), (uu____4641))))
in FStar_Syntax_Syntax.Tm_match (uu____4624))
in (mk uu____4623)))
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

let desugar_branch = (fun uu____4779 -> (match (uu____4779) with
| (pat, wopt, b) -> begin
(

let uu____4789 = (desugar_match_pat env pat)
in (match (uu____4789) with
| (env, pat) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(

let uu____4798 = (desugar_term env e)
in Some (uu____4798))
end)
in (

let b = (desugar_term env b)
in (FStar_Syntax_Util.branch ((pat), (wopt), (b)))))
end))
end))
in (

let uu____4801 = (

let uu____4802 = (

let uu____4818 = (desugar_term env e)
in (

let uu____4819 = (FStar_List.map desugar_branch branches)
in ((uu____4818), (uu____4819))))
in FStar_Syntax_Syntax.Tm_match (uu____4802))
in (FStar_All.pipe_left mk uu____4801)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(

let annot = (

let uu____4835 = (is_comp_type env t)
in (match (uu____4835) with
| true -> begin
(

let uu____4840 = (desugar_comp t.FStar_Parser_AST.range env t)
in FStar_Util.Inr (uu____4840))
end
| uu____4845 -> begin
(

let uu____4846 = (desugar_term env t)
in FStar_Util.Inl (uu____4846))
end))
in (

let uu____4849 = (

let uu____4850 = (

let uu____4863 = (desugar_term env e)
in ((uu____4863), (annot), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____4850))
in (FStar_All.pipe_left mk uu____4849)))
end
| FStar_Parser_AST.Record (uu____4871, []) -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let uu____4892 = (FStar_List.hd fields)
in (match (uu____4892) with
| (f, uu____4899) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun uu____4923 -> (match (uu____4923) with
| (g, uu____4927) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| Some (uu____4931, e) -> begin
((fn), (e))
end
| None -> begin
(match (xopt) with
| None -> begin
(

let uu____4939 = (

let uu____4940 = (

let uu____4943 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_ToSyntax_Env.typename.FStar_Ident.str)
in ((uu____4943), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____4940))
in (Prims.raise uu____4939))
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

let uu____4949 = (

let uu____4955 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____4969 -> (match (uu____4969) with
| (f, uu____4975) -> begin
(

let uu____4976 = (

let uu____4977 = (get_field None f)
in (FStar_All.pipe_left Prims.snd uu____4977))
in ((uu____4976), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (uu____4955)))
in FStar_Parser_AST.Construct (uu____4949))
end
| Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (

let uu____4988 = (

let uu____4989 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____4989))
in (FStar_Parser_AST.mk_term uu____4988 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = (

let uu____4991 = (

let uu____4998 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____5012 -> (match (uu____5012) with
| (f, uu____5018) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (uu____4998)))
in FStar_Parser_AST.Record (uu____4991))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____5034; FStar_Syntax_Syntax.pos = uu____5035; FStar_Syntax_Syntax.vars = uu____5036}, args); FStar_Syntax_Syntax.tk = uu____5038; FStar_Syntax_Syntax.pos = uu____5039; FStar_Syntax_Syntax.vars = uu____5040}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e = (

let uu____5062 = (

let uu____5063 = (

let uu____5073 = (

let uu____5074 = (

let uu____5076 = (

let uu____5077 = (

let uu____5081 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_ToSyntax_Env.typename), (uu____5081)))
in FStar_Syntax_Syntax.Record_ctor (uu____5077))
in Some (uu____5076))
in (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant uu____5074))
in ((uu____5073), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____5063))
in (FStar_All.pipe_left mk uu____5062))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| uu____5105 -> begin
e
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let uu____5108 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f)
in (match (uu____5108) with
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
| uu____5120 -> begin
None
end)
in (

let uu____5121 = (

let uu____5122 = (

let uu____5132 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projname (FStar_Ident.range_of_lid f)) FStar_Syntax_Syntax.Delta_equational qual)
in (

let uu____5133 = (

let uu____5135 = (FStar_Syntax_Syntax.as_arg e)
in (uu____5135)::[])
in ((uu____5132), (uu____5133))))
in FStar_Syntax_Syntax.Tm_app (uu____5122))
in (FStar_All.pipe_left mk uu____5121)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| uu____5141 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| uu____5142 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Let (uu____5143, uu____5144, uu____5145) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QForall (uu____5152, uu____5153, uu____5154) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QExists (uu____5161, uu____5162, uu____5163) -> begin
(failwith "Not implemented yet")
end)))))
and desugar_args : FStar_ToSyntax_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____5187 -> (match (uu____5187) with
| (a, imp) -> begin
(

let uu____5195 = (desugar_term env a)
in (arg_withimp_e imp uu____5195))
end)))))
and desugar_comp : FStar_Range.range  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Errors.Error (((msg), (r))))))
in (

let is_requires = (fun uu____5212 -> (match (uu____5212) with
| (t, uu____5216) -> begin
(

let uu____5217 = (

let uu____5218 = (unparen t)
in uu____5218.FStar_Parser_AST.tm)
in (match (uu____5217) with
| FStar_Parser_AST.Requires (uu____5219) -> begin
true
end
| uu____5223 -> begin
false
end))
end))
in (

let is_ensures = (fun uu____5229 -> (match (uu____5229) with
| (t, uu____5233) -> begin
(

let uu____5234 = (

let uu____5235 = (unparen t)
in uu____5235.FStar_Parser_AST.tm)
in (match (uu____5234) with
| FStar_Parser_AST.Ensures (uu____5236) -> begin
true
end
| uu____5240 -> begin
false
end))
end))
in (

let is_app = (fun head uu____5249 -> (match (uu____5249) with
| (t, uu____5253) -> begin
(

let uu____5254 = (

let uu____5255 = (unparen t)
in uu____5255.FStar_Parser_AST.tm)
in (match (uu____5254) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = uu____5257; FStar_Parser_AST.level = uu____5258}, uu____5259, uu____5260) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| uu____5261 -> begin
false
end))
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t -> (

let uu____5279 = (head_and_args t)
in (match (uu____5279) with
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

let uu____5444 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes env) l)
in ((uu____5444), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____5458 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals uu____5458 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((

let uu____5467 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals uu____5467 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when (((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)), ([]))), ((((t), (FStar_Parser_AST.Nothing)))::[]))
end
| uu____5487 -> begin
(

let default_effect = (

let uu____5489 = (FStar_Options.ml_ish ())
in (match (uu____5489) with
| true -> begin
FStar_Syntax_Const.effect_ML_lid
end
| uu____5490 -> begin
((

let uu____5492 = (FStar_Options.warn_default_effects ())
in (match (uu____5492) with
| true -> begin
(FStar_Errors.warn head.FStar_Parser_AST.range "Using default effect Tot")
end
| uu____5493 -> begin
()
end));
FStar_Syntax_Const.effect_Tot_lid;
)
end))
in (((((FStar_Ident.set_lid_range default_effect head.FStar_Parser_AST.range)), ([]))), ((((t), (FStar_Parser_AST.Nothing)))::[])))
end)
end)))
in (

let uu____5505 = (pre_process_comp_typ t)
in (match (uu____5505) with
| ((eff, cattributes), args) -> begin
((match (((FStar_List.length args) = (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5535 = (

let uu____5536 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" uu____5536))
in (fail uu____5535))
end
| uu____5537 -> begin
()
end);
(

let is_universe = (fun uu____5543 -> (match (uu____5543) with
| (uu____5546, imp) -> begin
(imp = FStar_Parser_AST.UnivApp)
end))
in (

let uu____5548 = (FStar_Util.take is_universe args)
in (match (uu____5548) with
| (universes, args) -> begin
(

let universes = (FStar_List.map (fun uu____5579 -> (match (uu____5579) with
| (u, imp) -> begin
(desugar_universe u)
end)) universes)
in (

let uu____5584 = (

let uu____5592 = (FStar_List.hd args)
in (

let uu____5597 = (FStar_List.tl args)
in ((uu____5592), (uu____5597))))
in (match (uu____5584) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (Prims.fst result_arg))
in (

let rest = (desugar_args env rest)
in (

let uu____5628 = (FStar_All.pipe_right rest (FStar_List.partition (fun uu____5666 -> (match (uu____5666) with
| (t, uu____5673) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____5681; FStar_Syntax_Syntax.pos = uu____5682; FStar_Syntax_Syntax.vars = uu____5683}, (uu____5684)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| uu____5706 -> begin
false
end)
end))))
in (match (uu____5628) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun uu____5749 -> (match (uu____5749) with
| (t, uu____5756) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____5763, ((arg, uu____5765))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| uu____5787 -> begin
(failwith "impos")
end)
end))))
in (

let no_additional_args = (

let is_empty = (fun l -> (match (l) with
| [] -> begin
true
end
| uu____5799 -> begin
false
end))
in ((((is_empty decreases_clause) && (is_empty rest)) && (is_empty cattributes)) && (is_empty universes)))
in (match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end
| uu____5808 -> begin
(match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end
| uu____5811 -> begin
(

let flags = (match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid)) with
| true -> begin
(FStar_Syntax_Syntax.LEMMA)::[]
end
| uu____5815 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____5817 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_ML_lid)) with
| true -> begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end
| uu____5819 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____5821 -> begin
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

let uu____5891 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5891 ((FStar_Syntax_Syntax.U_zero)::[])))
in ((FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (Some (FStar_Syntax_Syntax.imp_tag))))::[])) None pat.FStar_Syntax_Syntax.pos)))
end
| uu____5903 -> begin
pat
end)
in (

let uu____5904 = (

let uu____5911 = (

let uu____5918 = (

let uu____5924 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))))) None pat.FStar_Syntax_Syntax.pos)
in ((uu____5924), (aq)))
in (uu____5918)::[])
in (ens)::uu____5911)
in (req)::uu____5904))
end
| uu____5960 -> begin
rest
end)
end
| uu____5967 -> begin
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
| uu____5976 -> begin
None
end))
in (

let mk = (fun t -> ((FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let uu___216_6017 = t
in {FStar_Syntax_Syntax.n = uu___216_6017.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___216_6017.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___216_6017.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let uu___217_6047 = b
in {FStar_Parser_AST.b = uu___217_6047.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___217_6047.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___217_6047.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (

let uu____6080 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) uu____6080)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(

let uu____6089 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____6089) with
| (env, a) -> begin
(

let a = (

let uu___218_6097 = a
in {FStar_Syntax_Syntax.ppname = uu___218_6097.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___218_6097.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats = (desugar_pats env pats)
in (

let body = (desugar_formula env body)
in (

let body = (match (pats) with
| [] -> begin
body
end
| uu____6110 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_pattern (pats))))))
end)
in (

let body = (

let uu____6119 = (

let uu____6122 = (

let uu____6126 = (FStar_Syntax_Syntax.mk_binder a)
in (uu____6126)::[])
in (no_annot_abs uu____6122 body))
in (FStar_All.pipe_left setpos uu____6119))
in (

let uu____6131 = (

let uu____6132 = (

let uu____6142 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let uu____6143 = (

let uu____6145 = (FStar_Syntax_Syntax.as_arg body)
in (uu____6145)::[])
in ((uu____6142), (uu____6143))))
in FStar_Syntax_Syntax.Tm_app (uu____6132))
in (FStar_All.pipe_left mk uu____6131)))))))
end))
end
| uu____6149 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (

let uu____6198 = (q ((rest), (pats), (body)))
in (

let uu____6202 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term uu____6198 uu____6202 FStar_Parser_AST.Formula)))
in (

let uu____6203 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term uu____6203 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| uu____6208 -> begin
(failwith "impossible")
end))
in (

let uu____6210 = (

let uu____6211 = (unparen f)
in uu____6211.FStar_Parser_AST.tm)
in (match (uu____6210) with
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

let uu____6241 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env uu____6241)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____6262 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env uu____6262)))
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
| uu____6287 -> begin
(desugar_term env f)
end)))))))))
and typars_of_binders : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let uu____6291 = (FStar_List.fold_left (fun uu____6304 b -> (match (uu____6304) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let uu___219_6332 = b
in {FStar_Parser_AST.b = uu___219_6332.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___219_6332.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___219_6332.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(

let uu____6342 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____6342) with
| (env, a) -> begin
(

let a = (

let uu___220_6354 = a
in {FStar_Syntax_Syntax.ppname = uu___220_6354.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___220_6354.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env), ((((a), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| uu____6363 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (uu____6291) with
| (env, tpars) -> begin
((env), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(

let uu____6413 = (desugar_typ env t)
in ((Some (x)), (uu____6413)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____6416 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown))) None x.FStar_Ident.idRange)
in ((Some (x)), (uu____6416)))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____6431 = (desugar_typ env t)
in ((None), (uu____6431)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators = (fun quals env t tps k datas -> (

let quals = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___195_6480 -> (match (uu___195_6480) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| uu____6481 -> begin
false
end))))
in (

let quals = (fun q -> (

let uu____6489 = ((FStar_All.pipe_left Prims.op_Negation env.FStar_ToSyntax_Env.iface) || env.FStar_ToSyntax_Env.admitted_iface)
in (match (uu____6489) with
| true -> begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end
| uu____6491 -> begin
(FStar_List.append q quals)
end)))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (

let uu____6496 = (

let uu____6503 = (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in ((disc_name), ([]), (FStar_Syntax_Syntax.tun), (uu____6503), ((FStar_Ident.range_of_lid disc_name))))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____6496)))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_ToSyntax_Env.env  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let uu____6528 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____6538 -> (match (uu____6538) with
| (x, uu____6543) -> begin
(

let uu____6544 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____6544) with
| (field_name, uu____6549) -> begin
(

let only_decl = (((

let uu____6551 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____6551)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (

let uu____6552 = (

let uu____6553 = (FStar_ToSyntax_Env.current_module env)
in uu____6553.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____6552)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____6563 = (FStar_List.filter (fun uu___196_6565 -> (match (uu___196_6565) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____6566 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____6563)
end
| uu____6567 -> begin
q
end))
in (

let quals = (

let iquals = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___197_6574 -> (match (uu___197_6574) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| uu____6575 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun), (quals), ((FStar_Ident.range_of_lid field_name))))
in (match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____6580 -> begin
(

let dd = (

let uu____6582 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____6582) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____6584 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lb = (

let uu____6586 = (

let uu____6589 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (uu____6589))
in {FStar_Syntax_Syntax.lbname = uu____6586; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun})
in (

let impl = (

let uu____6591 = (

let uu____6600 = (

let uu____6602 = (

let uu____6603 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____6603 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____6602)::[])
in ((((false), ((lb)::[]))), (p), (uu____6600), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____6591))
in (match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____6619 -> begin
(decl)::(impl)::[]
end))))
end))))))
end))
end))))
in (FStar_All.pipe_right uu____6528 FStar_List.flatten))))


let mk_data_projector_names = (fun iquals env uu____6643 -> (match (uu____6643) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____6651, t, uu____6653, n, quals, uu____6656, uu____6657) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let uu____6662 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____6662) with
| (formals, uu____6672) -> begin
(match (formals) with
| [] -> begin
[]
end
| uu____6686 -> begin
(

let filter_records = (fun uu___198_6694 -> (match (uu___198_6694) with
| FStar_Syntax_Syntax.RecordConstructor (uu____6696, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| uu____6703 -> begin
None
end))
in (

let fv_qual = (

let uu____6705 = (FStar_Util.find_map quals filter_records)
in (match (uu____6705) with
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
| uu____6711 -> begin
iquals
end)
in (

let uu____6712 = (FStar_Util.first_N n formals)
in (match (uu____6712) with
| (uu____6724, rest) -> begin
(mk_indexed_projector_names iquals fv_qual env lid rest)
end)))))
end)
end))
end
| uu____6738 -> begin
[]
end)
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = (

let uu____6776 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____6776) with
| true -> begin
(

let uu____6778 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (uu____6778))
end
| uu____6779 -> begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end))
in (

let lb = (

let uu____6781 = (

let uu____6784 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (uu____6784))
in (

let uu____6785 = (

let uu____6788 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars uu____6788))
in (

let uu____6791 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = uu____6781; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____6785; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____6791})))
in FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (rng), (lids), (quals), ([]))))))


let rec desugar_tycon : FStar_ToSyntax_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (

let tycon_id = (fun uu___199_6824 -> (match (uu___199_6824) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(

let uu____6863 = (

let uu____6864 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____6864))
in (FStar_Parser_AST.mk_term uu____6863 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| uu____6886 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (

let uu____6889 = (

let uu____6890 = (

let uu____6894 = (binder_to_term b)
in ((out), (uu____6894), ((imp_of_aqual b))))
in FStar_Parser_AST.App (uu____6890))
in (FStar_Parser_AST.mk_term uu____6889 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun uu___200_6901 -> (match (uu___200_6901) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun uu____6930 -> (match (uu____6930) with
| (x, t, uu____6937) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (

let uu____6941 = (

let uu____6942 = (

let uu____6943 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (uu____6943))
in (FStar_Parser_AST.mk_term uu____6942 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____6941 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type_level)
in (

let uu____6946 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____6958 -> (match (uu____6958) with
| (x, uu____6964, uu____6965) -> begin
(FStar_Syntax_Util.unmangle_field_name x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (uu____6946)))))))
end
| uu____6992 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals uu___201_7014 -> (match (uu___201_7014) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let uu____7028 = (typars_of_binders _env binders)
in (match (uu____7028) with
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

let uu____7056 = (

let uu____7057 = (

let uu____7058 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (uu____7058))
in (FStar_Parser_AST.mk_term uu____7057 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____7056 binders))
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
| uu____7069 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env bs -> (

let uu____7095 = (FStar_List.fold_left (fun uu____7111 uu____7112 -> (match (((uu____7111), (uu____7112))) with
| ((env, tps), (x, imp)) -> begin
(

let uu____7160 = (FStar_ToSyntax_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (uu____7160) with
| (env, y) -> begin
((env), ((((y), (imp)))::tps))
end))
end)) ((env), ([])) bs)
in (match (uu____7095) with
| (env, bs) -> begin
((env), ((FStar_List.rev bs)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt = (match (kopt) with
| None -> begin
(

let uu____7221 = (tm_type_z id.FStar_Ident.idRange)
in Some (uu____7221))
end
| uu____7222 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt)))
in (

let uu____7227 = (desugar_abstract_tc quals env [] tc)
in (match (uu____7227) with
| (uu____7234, uu____7235, se, uu____7237) -> begin
(

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, uu____7240, typars, k, [], [], quals, rng) -> begin
(

let quals = (

let uu____7251 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (match (uu____7251) with
| true -> begin
quals
end
| uu____7254 -> begin
((

let uu____7256 = (FStar_Range.string_of_range rng)
in (

let uu____7257 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" uu____7256 uu____7257)));
(FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals;
)
end))
in (

let t = (match (typars) with
| [] -> begin
k
end
| uu____7261 -> begin
(

let uu____7262 = (

let uu____7265 = (

let uu____7266 = (

let uu____7274 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (uu____7274)))
in FStar_Syntax_Syntax.Tm_arrow (uu____7266))
in (FStar_Syntax_Syntax.mk uu____7265))
in (uu____7262 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t), (quals), (rng)))))
end
| uu____7285 -> begin
se
end)
in (

let env = (FStar_ToSyntax_Env.push_sigelt env se)
in ((env), ((se)::[]))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let uu____7296 = (typars_of_binders env binders)
in (match (uu____7296) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
(

let uu____7316 = (FStar_Util.for_some (fun uu___202_7317 -> (match (uu___202_7317) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| uu____7318 -> begin
false
end)) quals)
in (match (uu____7316) with
| true -> begin
FStar_Syntax_Syntax.teff
end
| uu____7319 -> begin
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

let uu____7324 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___203_7326 -> (match (uu___203_7326) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| uu____7327 -> begin
false
end))))
in (match (uu____7324) with
| true -> begin
quals
end
| uu____7329 -> begin
(match ((t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula)) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____7331 -> begin
quals
end)
end))
in (

let se = (

let uu____7333 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Effect))
in (match (uu____7333) with
| true -> begin
(

let uu____7335 = (

let uu____7339 = (

let uu____7340 = (unparen t)
in uu____7340.FStar_Parser_AST.tm)
in (match (uu____7339) with
| FStar_Parser_AST.Construct (head, args) -> begin
(

let uu____7352 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____7368))::args_rev -> begin
(

let uu____7375 = (

let uu____7376 = (unparen last_arg)
in uu____7376.FStar_Parser_AST.tm)
in (match (uu____7375) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____7391 -> begin
(([]), (args))
end))
end
| uu____7396 -> begin
(([]), (args))
end)
in (match (uu____7352) with
| (cattributes, args) -> begin
(

let uu____7417 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head), (args)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (uu____7417)))
end))
end
| uu____7423 -> begin
((t), ([]))
end))
in (match (uu____7335) with
| (t, cattributes) -> begin
(

let c = (desugar_comp t.FStar_Parser_AST.range env' t)
in (

let typars = (FStar_Syntax_Subst.close_binders typars)
in (

let c = (FStar_Syntax_Subst.close_comp typars c)
in (

let uu____7434 = (

let uu____7444 = (FStar_ToSyntax_Env.qualify env id)
in (

let uu____7445 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___204_7449 -> (match (uu___204_7449) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| uu____7450 -> begin
true
end))))
in ((uu____7444), ([]), (typars), (c), (uu____7445), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c))), (rng))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (uu____7434)))))
end))
end
| uu____7454 -> begin
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
| (FStar_Parser_AST.TyconRecord (uu____7459))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let uu____7472 = (tycon_record_as_variant trec)
in (match (uu____7472) with
| (t, fs) -> begin
(

let uu____7482 = (

let uu____7484 = (

let uu____7485 = (

let uu____7490 = (

let uu____7492 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.ids_of_lid uu____7492))
in ((uu____7490), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____7485))
in (uu____7484)::quals)
in (desugar_tycon env rng uu____7482 ((t)::[])))
end)))
end
| (uu____7495)::uu____7496 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let uu____7583 = et
in (match (uu____7583) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (uu____7697) -> begin
(

let trec = tc
in (

let uu____7710 = (tycon_record_as_variant trec)
in (match (uu____7710) with
| (t, fs) -> begin
(

let uu____7741 = (

let uu____7743 = (

let uu____7744 = (

let uu____7749 = (

let uu____7751 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.ids_of_lid uu____7751))
in ((uu____7749), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____7744))
in (uu____7743)::quals)
in (collect_tcs uu____7741 ((env), (tcs)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let uu____7797 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____7797) with
| (env, uu____7828, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let uu____7906 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____7906) with
| (env, uu____7937, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (binders), (t), (quals))))::tcs))
end))
end
| uu____8001 -> begin
(failwith "Unrecognized mutual type definition")
end)
end)))
in (

let uu____8025 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (uu____8025) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun uu___206_8263 -> (match (uu___206_8263) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, uu____8295, uu____8296, uu____8297, uu____8298), binders, t, quals) -> begin
(

let t = (

let uu____8331 = (typars_of_binders env binders)
in (match (uu____8331) with
| (env, tpars) -> begin
(

let uu____8348 = (push_tparams env tpars)
in (match (uu____8348) with
| (env_tps, tpars) -> begin
(

let t = (desugar_typ env_tps t)
in (

let tpars = (FStar_Syntax_Subst.close_binders tpars)
in (FStar_Syntax_Subst.close tpars t)))
end))
end))
in (

let uu____8367 = (

let uu____8374 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in (([]), (uu____8374)))
in (uu____8367)::[]))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, uu____8399, tags, uu____8401), constrs, tconstr, quals) -> begin
(

let mk_tot = (fun t -> (

let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)))
in (

let tycon = ((tname), (tpars), (k))
in (

let uu____8454 = (push_tparams env tpars)
in (match (uu____8454) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun uu____8489 -> (match (uu____8489) with
| (x, uu____8497) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let tot_tconstr = (mk_tot tconstr)
in (

let uu____8502 = (

let uu____8513 = (FStar_All.pipe_right constrs (FStar_List.map (fun uu____8553 -> (match (uu____8553) with
| (id, topt, uu____8570, of_notation) -> begin
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
| uu____8579 -> begin
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

let uu____8582 = (close env_tps t)
in (desugar_term env_tps uu____8582))
in (

let name = (FStar_ToSyntax_Env.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun uu___205_8588 -> (match (uu___205_8588) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| uu____8595 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (

let uu____8601 = (

let uu____8608 = (

let uu____8609 = (

let uu____8620 = (

let uu____8623 = (

let uu____8626 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total uu____8626))
in (FStar_Syntax_Util.arrow data_tpars uu____8623))
in ((name), (univs), (uu____8620), (tname), (ntps), (quals), (mutuals), (rng)))
in FStar_Syntax_Syntax.Sig_datacon (uu____8609))
in ((tps), (uu____8608)))
in ((name), (uu____8601))))))))
end))))
in (FStar_All.pipe_left FStar_List.split uu____8513))
in (match (uu____8502) with
| (constrNames, constrs) -> begin
((([]), (FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))))::constrs
end))))
end))))
end
| uu____8711 -> begin
(failwith "impossible")
end))))
in (

let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (

let uu____8759 = (

let uu____8763 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals uu____8763 rng))
in (match (uu____8759) with
| (bundle, abbrevs) -> begin
(

let env = (FStar_ToSyntax_Env.push_sigelt env0 bundle)
in (

let env = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env abbrevs)
in (

let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projector_names quals env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun uu___207_8797 -> (match (uu___207_8797) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, uu____8800, tps, k, uu____8803, constrs, quals, uu____8806) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::quals
end
| uu____8819 -> begin
quals
end)
in (mk_data_discriminators quals env tname tps k constrs))
end
| uu____8820 -> begin
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

let uu____8838 = (FStar_List.fold_left (fun uu____8845 b -> (match (uu____8845) with
| (env, binders) -> begin
(

let uu____8857 = (desugar_binder env b)
in (match (uu____8857) with
| (Some (a), k) -> begin
(

let uu____8867 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____8867) with
| (env, a) -> begin
(

let uu____8875 = (

let uu____8877 = (FStar_Syntax_Syntax.mk_binder (

let uu___221_8878 = a
in {FStar_Syntax_Syntax.ppname = uu___221_8878.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___221_8878.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (uu____8877)::binders)
in ((env), (uu____8875)))
end))
end
| uu____8880 -> begin
(Prims.raise (FStar_Errors.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) binders)
in (match (uu____8838) with
| (env, binders) -> begin
((env), ((FStar_List.rev binders)))
end)))


let rec desugar_effect : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  Prims.bool  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_kind eff_decls actions for_free -> (

let env0 = env
in (

let monad_env = (FStar_ToSyntax_Env.enter_monad_scope env eff_name)
in (

let uu____8974 = (desugar_binders monad_env eff_binders)
in (match (uu____8974) with
| (env, binders) -> begin
(

let eff_k = (desugar_term env eff_kind)
in (

let uu____8986 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun uu____8997 decl -> (match (uu____8997) with
| (env, out) -> begin
(

let uu____9009 = (desugar_decl env decl)
in (match (uu____9009) with
| (env, ses) -> begin
(

let uu____9017 = (

let uu____9019 = (FStar_List.hd ses)
in (uu____9019)::out)
in ((env), (uu____9017)))
end))
end)) ((env), ([]))))
in (match (uu____8986) with
| (env, decls) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let actions = (FStar_All.pipe_right actions (FStar_List.map (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____9035, ((FStar_Parser_AST.TyconAbbrev (name, uu____9037, uu____9038, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (uu____9039, ((def, uu____9041))::((cps_type, uu____9043))::[]); FStar_Parser_AST.range = uu____9044; FStar_Parser_AST.level = uu____9045}), uu____9046))::[]) when (not (for_free)) -> begin
(

let uu____9072 = (FStar_ToSyntax_Env.qualify env name)
in (

let uu____9073 = (

let uu____9074 = (desugar_term env def)
in (FStar_Syntax_Subst.close binders uu____9074))
in (

let uu____9075 = (

let uu____9076 = (desugar_typ env cps_type)
in (FStar_Syntax_Subst.close binders uu____9076))
in {FStar_Syntax_Syntax.action_name = uu____9072; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = uu____9073; FStar_Syntax_Syntax.action_typ = uu____9075})))
end
| FStar_Parser_AST.Tycon (uu____9077, ((FStar_Parser_AST.TyconAbbrev (name, uu____9079, uu____9080, defn), uu____9082))::[]) when for_free -> begin
(

let uu____9099 = (FStar_ToSyntax_Env.qualify env name)
in (

let uu____9100 = (

let uu____9101 = (desugar_term env defn)
in (FStar_Syntax_Subst.close binders uu____9101))
in {FStar_Syntax_Syntax.action_name = uu____9099; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = uu____9100; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
end
| uu____9102 -> begin
(Prims.raise (FStar_Errors.Error ((("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples)."), (d.FStar_Parser_AST.drange)))))
end))))
in (

let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (

let lookup = (fun s -> (

let l = (FStar_ToSyntax_Env.qualify env (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange))))
in (

let uu____9112 = (

let uu____9113 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) uu____9113))
in (([]), (uu____9112)))))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (Some (mname))) quals)
in (

let se = (match (for_free) with
| true -> begin
(

let dummy_tscheme = (

let uu____9125 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (([]), (uu____9125)))
in (

let uu____9135 = (

let uu____9138 = (

let uu____9139 = (

let uu____9140 = (lookup "repr")
in (Prims.snd uu____9140))
in (

let uu____9145 = (lookup "return")
in (

let uu____9146 = (lookup "bind")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = uu____9139; FStar_Syntax_Syntax.return_repr = uu____9145; FStar_Syntax_Syntax.bind_repr = uu____9146; FStar_Syntax_Syntax.actions = actions})))
in ((uu____9138), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____9135)))
end
| uu____9147 -> begin
(

let rr = ((FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right qualifiers FStar_Syntax_Syntax.contains_reflectable))
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (

let uu____9156 = (

let uu____9159 = (

let uu____9160 = (lookup "return_wp")
in (

let uu____9161 = (lookup "bind_wp")
in (

let uu____9162 = (lookup "if_then_else")
in (

let uu____9163 = (lookup "ite_wp")
in (

let uu____9164 = (lookup "stronger")
in (

let uu____9165 = (lookup "close_wp")
in (

let uu____9166 = (lookup "assert_p")
in (

let uu____9167 = (lookup "assume_p")
in (

let uu____9168 = (lookup "null_wp")
in (

let uu____9169 = (lookup "trivial")
in (

let uu____9170 = (match (rr) with
| true -> begin
(

let uu____9171 = (lookup "repr")
in (FStar_All.pipe_left Prims.snd uu____9171))
end
| uu____9179 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let uu____9180 = (match (rr) with
| true -> begin
(lookup "return")
end
| uu____9181 -> begin
un_ts
end)
in (

let uu____9182 = (match (rr) with
| true -> begin
(lookup "bind")
end
| uu____9183 -> begin
un_ts
end)
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = uu____9160; FStar_Syntax_Syntax.bind_wp = uu____9161; FStar_Syntax_Syntax.if_then_else = uu____9162; FStar_Syntax_Syntax.ite_wp = uu____9163; FStar_Syntax_Syntax.stronger = uu____9164; FStar_Syntax_Syntax.close_wp = uu____9165; FStar_Syntax_Syntax.assert_p = uu____9166; FStar_Syntax_Syntax.assume_p = uu____9167; FStar_Syntax_Syntax.null_wp = uu____9168; FStar_Syntax_Syntax.trivial = uu____9169; FStar_Syntax_Syntax.repr = uu____9170; FStar_Syntax_Syntax.return_repr = uu____9180; FStar_Syntax_Syntax.bind_repr = uu____9182; FStar_Syntax_Syntax.actions = actions})))))))))))))
in ((uu____9159), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect (uu____9156))))
end)
in (

let env = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right actions (FStar_List.fold_left (fun env a -> (

let uu____9189 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env uu____9189))) env))
in (

let env = (

let uu____9191 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____9191) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let refl_decl = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]), (d.FStar_Parser_AST.drange)))
in (FStar_ToSyntax_Env.push_sigelt env refl_decl)))
end
| uu____9196 -> begin
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

let uu____9219 = (desugar_binders env eff_binders)
in (match (uu____9219) with
| (env, binders) -> begin
(

let uu____9230 = (

let uu____9239 = (head_and_args defn)
in (match (uu____9239) with
| (head, args) -> begin
(

let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_defn env) l)
end
| uu____9263 -> begin
(

let uu____9264 = (

let uu____9265 = (

let uu____9268 = (

let uu____9269 = (

let uu____9270 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat uu____9270 " not found"))
in (Prims.strcat "Effect " uu____9269))
in ((uu____9268), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____9265))
in (Prims.raise uu____9264))
end)
in (

let uu____9271 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____9287))::args_rev -> begin
(

let uu____9294 = (

let uu____9295 = (unparen last_arg)
in uu____9295.FStar_Parser_AST.tm)
in (match (uu____9294) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____9310 -> begin
(([]), (args))
end))
end
| uu____9315 -> begin
(([]), (args))
end)
in (match (uu____9271) with
| (cattributes, args) -> begin
(

let uu____9341 = (desugar_args env args)
in (

let uu____9346 = (desugar_attributes env cattributes)
in ((ed), (uu____9341), (uu____9346))))
end)))
end))
in (match (uu____9230) with
| (ed, args, cattributes) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let sub = (fun uu____9379 -> (match (uu____9379) with
| (uu____9386, x) -> begin
(

let uu____9390 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (uu____9390) with
| (edb, x) -> begin
((match (((FStar_List.length args) <> (FStar_List.length edb))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end
| uu____9408 -> begin
()
end);
(

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (

let uu____9410 = (

let uu____9411 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders uu____9411))
in (([]), (uu____9410))));
)
end))
end))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let ed = (

let uu____9415 = (

let uu____9417 = (trans_qual (Some (mname)))
in (FStar_List.map uu____9417 quals))
in (

let uu____9420 = (

let uu____9421 = (sub (([]), (ed.FStar_Syntax_Syntax.signature)))
in (Prims.snd uu____9421))
in (

let uu____9427 = (sub ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____9428 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____9429 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____9430 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____9431 = (sub ed.FStar_Syntax_Syntax.stronger)
in (

let uu____9432 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____9433 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____9434 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____9435 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____9436 = (sub ed.FStar_Syntax_Syntax.trivial)
in (

let uu____9437 = (

let uu____9438 = (sub (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd uu____9438))
in (

let uu____9444 = (sub ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____9445 = (sub ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____9446 = (FStar_List.map (fun action -> (

let uu____9449 = (FStar_ToSyntax_Env.qualify env action.FStar_Syntax_Syntax.action_unqualified_name)
in (

let uu____9450 = (

let uu____9451 = (sub (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd uu____9451))
in (

let uu____9457 = (

let uu____9458 = (sub (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd uu____9458))
in {FStar_Syntax_Syntax.action_name = uu____9449; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = uu____9450; FStar_Syntax_Syntax.action_typ = uu____9457})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = uu____9415; FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = uu____9420; FStar_Syntax_Syntax.ret_wp = uu____9427; FStar_Syntax_Syntax.bind_wp = uu____9428; FStar_Syntax_Syntax.if_then_else = uu____9429; FStar_Syntax_Syntax.ite_wp = uu____9430; FStar_Syntax_Syntax.stronger = uu____9431; FStar_Syntax_Syntax.close_wp = uu____9432; FStar_Syntax_Syntax.assert_p = uu____9433; FStar_Syntax_Syntax.assume_p = uu____9434; FStar_Syntax_Syntax.null_wp = uu____9435; FStar_Syntax_Syntax.trivial = uu____9436; FStar_Syntax_Syntax.repr = uu____9437; FStar_Syntax_Syntax.return_repr = uu____9444; FStar_Syntax_Syntax.bind_repr = uu____9445; FStar_Syntax_Syntax.actions = uu____9446}))))))))))))))))
in (

let se = (build_sigelt ed d.FStar_Parser_AST.drange)
in (

let monad_env = env
in (

let env = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun env a -> (

let uu____9471 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env uu____9471))) env))
in (

let env = (

let uu____9473 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____9473) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let refl_decl = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]), (d.FStar_Parser_AST.drange)))
in (FStar_ToSyntax_Env.push_sigelt env refl_decl)))
end
| uu____9479 -> begin
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
| uu____9496 -> begin
()
end);
((env), ((se)::[]));
))
end
| FStar_Parser_AST.Fsdoc (uu____9498) -> begin
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

let uu____9510 = (FStar_ToSyntax_Env.push_module_abbrev env x l)
in ((uu____9510), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, tcs) -> begin
(

let quals = (match (is_effect) with
| true -> begin
(FStar_Parser_AST.Effect_qual)::d.FStar_Parser_AST.quals
end
| uu____9525 -> begin
d.FStar_Parser_AST.quals
end)
in (

let tcs = (FStar_List.map (fun uu____9531 -> (match (uu____9531) with
| (x, uu____9536) -> begin
x
end)) tcs)
in (

let uu____9539 = (FStar_List.map (trans_qual None) quals)
in (desugar_tycon env d.FStar_Parser_AST.drange uu____9539 tcs))))
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
| ((p, uu____9578))::[] -> begin
(

let uu____9583 = (is_app_pattern p)
in (not (uu____9583)))
end
| uu____9584 -> begin
false
end))
in (match ((not (expand_toplevel_pattern))) with
| true -> begin
(

let as_inner_let = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let ds_lets = (desugar_term_maybe_top true env as_inner_let)
in (

let uu____9595 = (

let uu____9596 = (FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets)
in uu____9596.FStar_Syntax_Syntax.n)
in (match (uu____9595) with
| FStar_Syntax_Syntax.Tm_let (lbs, uu____9602) -> begin
(

let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals = (match (quals) with
| (uu____9622)::uu____9623 -> begin
(FStar_List.map (trans_qual None) quals)
end
| uu____9625 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun uu___208_9629 -> (match (uu___208_9629) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (uu____9631); FStar_Syntax_Syntax.lbunivs = uu____9632; FStar_Syntax_Syntax.lbtyp = uu____9633; FStar_Syntax_Syntax.lbeff = uu____9634; FStar_Syntax_Syntax.lbdef = uu____9635} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____9642; FStar_Syntax_Syntax.lbtyp = uu____9643; FStar_Syntax_Syntax.lbeff = uu____9644; FStar_Syntax_Syntax.lbdef = uu____9645} -> begin
(FStar_ToSyntax_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals = (

let uu____9657 = (FStar_All.pipe_right lets (FStar_Util.for_some (fun uu____9663 -> (match (uu____9663) with
| (uu____9666, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end))))
in (match (uu____9657) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____9669 -> begin
quals
end))
in (

let lbs = (

let uu____9674 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____9674) with
| true -> begin
(

let uu____9679 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu___222_9686 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let uu___223_9687 = fv
in {FStar_Syntax_Syntax.fv_name = uu___223_9687.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = uu___223_9687.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = uu___222_9686.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___222_9686.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___222_9686.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___222_9686.FStar_Syntax_Syntax.lbdef})))))
in (((Prims.fst lbs)), (uu____9679)))
end
| uu____9693 -> begin
lbs
end))
in (

let s = (

let uu____9695 = (

let uu____9704 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in ((lbs), (d.FStar_Parser_AST.drange), (uu____9704), (quals), (attrs)))
in FStar_Syntax_Syntax.Sig_let (uu____9695))
in (

let env = (FStar_ToSyntax_Env.push_sigelt env s)
in ((env), ((s)::[]))))))))
end
| uu____9721 -> begin
(failwith "Desugaring a let did not produce a let")
end))))
end
| uu____9724 -> begin
(

let uu____9725 = (match (lets) with
| ((pat, body))::[] -> begin
((pat), (body))
end
| uu____9736 -> begin
(failwith "expand_toplevel_pattern should only allow single definition lets")
end)
in (match (uu____9725) with
| (pat, body) -> begin
(

let fresh_toplevel_name = (FStar_Ident.gen FStar_Range.dummyRange)
in (

let fresh_pat = (

let var_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((fresh_toplevel_name), (None)))) FStar_Range.dummyRange)
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, ty) -> begin
(

let uu___224_9752 = pat
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed (((var_pat), (ty))); FStar_Parser_AST.prange = uu___224_9752.FStar_Parser_AST.prange})
end
| uu____9753 -> begin
var_pat
end))
in (

let main_let = (desugar_decl env (

let uu___225_9757 = d
in {FStar_Parser_AST.d = FStar_Parser_AST.TopLevelLet (((isrec), ((((fresh_pat), (body)))::[]))); FStar_Parser_AST.drange = uu___225_9757.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___225_9757.FStar_Parser_AST.doc; FStar_Parser_AST.quals = (FStar_Parser_AST.Private)::d.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = uu___225_9757.FStar_Parser_AST.attrs}))
in (

let build_projection = (fun uu____9776 id -> (match (uu____9776) with
| (env, ses) -> begin
(

let main = (

let uu____9789 = (

let uu____9790 = (FStar_Ident.lid_of_ids ((fresh_toplevel_name)::[]))
in FStar_Parser_AST.Var (uu____9790))
in (FStar_Parser_AST.mk_term uu____9789 FStar_Range.dummyRange FStar_Parser_AST.Expr))
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

let uu____9818 = (desugar_decl env id_decl)
in (match (uu____9818) with
| (env, ses') -> begin
((env), ((FStar_List.append ses ses')))
end))))))))
end))
in (

let bvs = (

let uu____9829 = (gather_pattern_bound_vars pat)
in (FStar_All.pipe_right uu____9829 FStar_Util.set_elements))
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

let uu____9843 = (

let uu____9845 = (

let uu____9846 = (

let uu____9852 = (FStar_ToSyntax_Env.qualify env id)
in ((uu____9852), (f), ((FStar_Syntax_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_assume (uu____9846))
in (uu____9845)::[])
in ((env), (uu____9843))))
end
| FStar_Parser_AST.Val (id, t) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let t = (

let uu____9859 = (close_fun env t)
in (desugar_term env uu____9859))
in (

let quals = (match ((env.FStar_ToSyntax_Env.iface && env.FStar_ToSyntax_Env.admitted_iface)) with
| true -> begin
(FStar_Parser_AST.Assumption)::quals
end
| uu____9863 -> begin
quals
end)
in (

let se = (

let uu____9865 = (

let uu____9872 = (FStar_ToSyntax_Env.qualify env id)
in (

let uu____9873 = (FStar_List.map (trans_qual None) quals)
in ((uu____9872), ([]), (t), (uu____9873), (d.FStar_Parser_AST.drange))))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____9865))
in (

let env = (FStar_ToSyntax_Env.push_sigelt env se)
in ((env), ((se)::[])))))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(

let uu____9881 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (match (uu____9881) with
| (t, uu____9889) -> begin
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

let uu____9916 = (

let uu____9920 = (FStar_Syntax_Syntax.null_binder t)
in (uu____9920)::[])
in (

let uu____9921 = (

let uu____9924 = (

let uu____9925 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (Prims.fst uu____9925))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____9924))
in (FStar_Syntax_Util.arrow uu____9916 uu____9921)))
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

let uu____9996 = (FStar_ToSyntax_Env.try_lookup_effect_name env l)
in (match (uu____9996) with
| None -> begin
(

let uu____9998 = (

let uu____9999 = (

let uu____10002 = (

let uu____10003 = (

let uu____10004 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat uu____10004 " not found"))
in (Prims.strcat "Effect name " uu____10003))
in ((uu____10002), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____9999))
in (Prims.raise uu____9998))
end
| Some (l) -> begin
l
end)))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let uu____10008 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(

let uu____10030 = (

let uu____10035 = (

let uu____10039 = (desugar_term env t)
in (([]), (uu____10039)))
in Some (uu____10035))
in ((uu____10030), (None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(

let uu____10057 = (

let uu____10062 = (

let uu____10066 = (desugar_term env wp)
in (([]), (uu____10066)))
in Some (uu____10062))
in (

let uu____10071 = (

let uu____10076 = (

let uu____10080 = (desugar_term env t)
in (([]), (uu____10080)))
in Some (uu____10076))
in ((uu____10057), (uu____10071))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(

let uu____10094 = (

let uu____10099 = (

let uu____10103 = (desugar_term env t)
in (([]), (uu____10103)))
in Some (uu____10099))
in ((None), (uu____10094)))
end)
in (match (uu____10008) with
| (lift_wp, lift) -> begin
(

let se = FStar_Syntax_Syntax.Sig_sub_effect ((({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun uu____10154 d -> (match (uu____10154) with
| (env, sigelts) -> begin
(

let uu____10166 = (desugar_decl env d)
in (match (uu____10166) with
| (env, se) -> begin
((env), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))


let open_prims_all : (FStar_Parser_AST.decoration Prims.list  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]


let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env = (match (((curmod), (m))) with
| (None, uu____10208) -> begin
env
end
| (Some ({FStar_Syntax_Syntax.name = prev_lid; FStar_Syntax_Syntax.declarations = uu____10211; FStar_Syntax_Syntax.exports = uu____10212; FStar_Syntax_Syntax.is_interface = uu____10213}), FStar_Parser_AST.Module (current_lid, uu____10215)) when ((FStar_Ident.lid_equals prev_lid current_lid) && (FStar_Options.interactive ())) -> begin
env
end
| (Some (prev_mod), uu____10220) -> begin
(FStar_ToSyntax_Env.finish_module_or_interface env prev_mod)
end)
in (

let uu____10222 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(

let uu____10242 = (FStar_ToSyntax_Env.prepare_module_or_interface true admitted env mname)
in ((uu____10242), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(

let uu____10252 = (FStar_ToSyntax_Env.prepare_module_or_interface false false env mname)
in ((uu____10252), (mname), (decls), (false)))
end)
in (match (uu____10222) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let uu____10270 = (desugar_decls env decls)
in (match (uu____10270) with
| (env, sigelts) -> begin
(

let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in ((env), (modul), (pop_when_done)))
end))
end))))


let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (

let m = (

let uu____10295 = ((FStar_Options.interactive ()) && (

let uu____10296 = (

let uu____10297 = (

let uu____10298 = (FStar_Options.file_list ())
in (FStar_List.hd uu____10298))
in (FStar_Util.get_file_extension uu____10297))
in (uu____10296 = "fsti")))
in (match (uu____10295) with
| true -> begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface (((mname), (decls), (true)))
end
| FStar_Parser_AST.Interface (mname, uu____10306, uu____10307) -> begin
(failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end
| uu____10310 -> begin
m
end))
in (

let uu____10311 = (desugar_modul_common curmod env m)
in (match (uu____10311) with
| (x, y, pop_when_done) -> begin
((match (pop_when_done) with
| true -> begin
(

let uu____10321 = (FStar_ToSyntax_Env.pop ())
in ())
end
| uu____10322 -> begin
()
end);
((x), (y));
)
end))))


let desugar_modul : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun env m -> (

let uu____10333 = (desugar_modul_common None env m)
in (match (uu____10333) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_ToSyntax_Env.finish_module_or_interface env modul)
in ((

let uu____10344 = (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____10344) with
| true -> begin
(

let uu____10345 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" uu____10345))
end
| uu____10346 -> begin
()
end));
(

let uu____10347 = (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end
| uu____10348 -> begin
env
end)
in ((uu____10347), (modul)));
))
end)))


let desugar_file : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (

let uu____10358 = (FStar_List.fold_left (fun uu____10365 m -> (match (uu____10365) with
| (env, mods) -> begin
(

let uu____10377 = (desugar_modul env m)
in (match (uu____10377) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (uu____10358) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_ToSyntax_Env.env  ->  FStar_ToSyntax_Env.env = (fun m en -> (

let uu____10401 = (FStar_ToSyntax_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (uu____10401) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt (

let uu___226_10407 = en
in {FStar_ToSyntax_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_ToSyntax_Env.curmonad = uu___226_10407.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = uu___226_10407.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = uu___226_10407.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = uu___226_10407.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = uu___226_10407.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = uu___226_10407.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = uu___226_10407.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = uu___226_10407.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.iface = uu___226_10407.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = uu___226_10407.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = uu___226_10407.FStar_ToSyntax_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (

let env = (FStar_ToSyntax_Env.finish_module_or_interface en m)
in (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name env)
end
| uu____10409 -> begin
env
end)))
end)))




