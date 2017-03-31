
open Prims

let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun uu___181_5 -> (match (uu___181_5) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| uu____8 -> begin
None
end))


let trans_qual : FStar_Range.range  ->  FStar_Ident.lident Prims.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r maybe_effect_id uu___182_19 -> (match (uu___182_19) with
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


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun uu___183_25 -> (match (uu___183_25) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end
| FStar_Parser_AST.LightOff -> begin
FStar_Syntax_Syntax.LightOff
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun uu___184_32 -> (match (uu___184_32) with
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
| FStar_Parser_AST.Paren (t1) -> begin
(unparen t1)
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
| FStar_Parser_AST.App (head1, uu____110, uu____111) -> begin
(is_comp_type env head1)
end
| (FStar_Parser_AST.Paren (t1)) | (FStar_Parser_AST.Ascribed (t1, _, _)) | (FStar_Parser_AST.LetOpen (_, t1)) -> begin
(is_comp_type env t1)
end
| uu____117 -> begin
false
end))


let unit_ty : FStar_Parser_AST.term = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) FStar_Range.dummyRange FStar_Parser_AST.Type_level)


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n1 s r -> (

let uu____127 = (

let uu____129 = (

let uu____130 = (

let uu____133 = (FStar_Parser_AST.compile_op n1 s)
in ((uu____133), (r)))
in (FStar_Ident.mk_ident uu____130))
in (uu____129)::[])
in (FStar_All.pipe_right uu____127 FStar_Ident.lid_of_ids)))


let op_as_term : FStar_ToSyntax_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (

let r = (fun l dd -> (

let uu____157 = (

let uu____158 = (FStar_Syntax_Syntax.lid_as_fv (FStar_Ident.set_lid_range l rng) dd None)
in (FStar_All.pipe_right uu____158 FStar_Syntax_Syntax.fv_to_tm))
in Some (uu____157)))
in (

let fallback = (fun uu____163 -> (match (s) with
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

let uu____165 = (FStar_Options.ml_ish ())
in (match (uu____165) with
| true -> begin
(r FStar_Syntax_Const.list_append_lid FStar_Syntax_Syntax.Delta_equational)
end
| uu____167 -> begin
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
| uu____168 -> begin
None
end))
in (

let uu____169 = (

let uu____173 = (compile_op_lid arity s rng)
in (FStar_ToSyntax_Env.try_lookup_lid env uu____173))
in (match (uu____169) with
| Some (t) -> begin
Some ((Prims.fst t))
end
| uu____180 -> begin
(fallback ())
end)))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (

let uu____190 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) uu____190)))


let rec free_type_vars_b : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_ToSyntax_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (uu____215) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____218 = (FStar_ToSyntax_Env.push_bv env x)
in (match (uu____218) with
| (env1, uu____225) -> begin
((env1), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (uu____227, term) -> begin
(

let uu____229 = (free_type_vars env term)
in ((env), (uu____229)))
end
| FStar_Parser_AST.TAnnotated (id, uu____233) -> begin
(

let uu____234 = (FStar_ToSyntax_Env.push_bv env id)
in (match (uu____234) with
| (env1, uu____241) -> begin
((env1), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____244 = (free_type_vars env t)
in ((env), (uu____244)))
end))
and free_type_vars : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (

let uu____249 = (

let uu____250 = (unparen t)
in uu____250.FStar_Parser_AST.tm)
in (match (uu____249) with
| FStar_Parser_AST.Labeled (uu____252) -> begin
(failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____258 = (FStar_ToSyntax_Env.try_lookup_id env a)
in (match (uu____258) with
| None -> begin
(a)::[]
end
| uu____265 -> begin
[]
end))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Projector (_)) | (FStar_Parser_AST.Discrim (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Assign (_, t1)) | (FStar_Parser_AST.Requires (t1, _)) | (FStar_Parser_AST.Ensures (t1, _)) | (FStar_Parser_AST.NamedTyp (_, t1)) | (FStar_Parser_AST.Paren (t1)) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.Ascribed (t1, t', tacopt) -> begin
(

let ts = (t1)::(t')::(match (tacopt) with
| None -> begin
[]
end
| Some (t2) -> begin
(t2)::[]
end)
in (FStar_List.collect (free_type_vars env) ts))
end
| FStar_Parser_AST.Construct (uu____291, ts) -> begin
(FStar_List.collect (fun uu____301 -> (match (uu____301) with
| (t1, uu____306) -> begin
(free_type_vars env t1)
end)) ts)
end
| FStar_Parser_AST.Op (uu____307, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, uu____313) -> begin
(

let uu____314 = (free_type_vars env t1)
in (

let uu____316 = (free_type_vars env t2)
in (FStar_List.append uu____314 uu____316)))
end
| FStar_Parser_AST.Refine (b, t1) -> begin
(

let uu____320 = (free_type_vars_b env b)
in (match (uu____320) with
| (env1, f) -> begin
(

let uu____329 = (free_type_vars env1 t1)
in (FStar_List.append f uu____329))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(

let uu____337 = (FStar_List.fold_left (fun uu____344 binder -> (match (uu____344) with
| (env1, free) -> begin
(

let uu____356 = (free_type_vars_b env1 binder)
in (match (uu____356) with
| (env2, f) -> begin
((env2), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (uu____337) with
| (env1, free) -> begin
(

let uu____374 = (free_type_vars env1 body)
in (FStar_List.append free uu____374))
end))
end
| FStar_Parser_AST.Project (t1, uu____377) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.collect (free_type_vars env) cattributes)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end)))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t1 -> (

let uu____416 = (

let uu____417 = (unparen t1)
in uu____417.FStar_Parser_AST.tm)
in (match (uu____416) with
| FStar_Parser_AST.App (t2, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t2)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t1.FStar_Parser_AST.range; FStar_Parser_AST.level = t1.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| uu____441 -> begin
((t1), (args))
end)))
in (aux [] t)))


let close : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____455 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____455))
in (match (((FStar_List.length ftv) = (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____461 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____467 = (

let uu____468 = (

let uu____471 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____471)))
in FStar_Parser_AST.TAnnotated (uu____468))
in (FStar_Parser_AST.mk_binder uu____467 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end)))


let close_fun : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____482 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____482))
in (match (((FStar_List.length ftv) = (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____488 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____494 = (

let uu____495 = (

let uu____498 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____498)))
in FStar_Parser_AST.TAnnotated (uu____495))
in (FStar_Parser_AST.mk_binder uu____494 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (Some (FStar_Parser_AST.Implicit)))))))
in (

let t1 = (

let uu____500 = (

let uu____501 = (unparen t)
in uu____501.FStar_Parser_AST.tm)
in (match (uu____500) with
| FStar_Parser_AST.Product (uu____502) -> begin
t
end
| uu____506 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t1)))) t1.FStar_Parser_AST.range t1.FStar_Parser_AST.level)
in result)))
end)))


let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t1) -> begin
(uncurry (FStar_List.append bs binders) t1)
end
| uu____527 -> begin
((bs), (t))
end))


let rec is_var_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatTvar (_, _)) | (FStar_Parser_AST.PatVar (_, _)) -> begin
true
end
| FStar_Parser_AST.PatAscribed (p1, uu____539) -> begin
(is_var_pattern p1)
end
| uu____540 -> begin
false
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p1, uu____545) -> begin
(is_app_pattern p1)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____546); FStar_Parser_AST.prange = uu____547}, uu____548) -> begin
true
end
| uu____554 -> begin
false
end))


let replace_unit_pattern : FStar_Parser_AST.pattern  ->  FStar_Parser_AST.pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatConst (FStar_Const.Const_unit) -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatAscribed ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)), (unit_ty)))) p.FStar_Parser_AST.prange)
end
| uu____558 -> begin
p
end))


let rec destruct_app_pattern : FStar_ToSyntax_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level1 p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p1, t) -> begin
(

let uu____584 = (destruct_app_pattern env is_top_level1 p1)
in (match (uu____584) with
| (name, args, uu____601) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____615); FStar_Parser_AST.prange = uu____616}, args) when is_top_level1 -> begin
(

let uu____622 = (

let uu____625 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____625))
in ((uu____622), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____631); FStar_Parser_AST.prange = uu____632}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| uu____642 -> begin
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
| FStar_Parser_AST.PatVar (x, uu____677) -> begin
(FStar_Util.set_add x acc)
end
| (FStar_Parser_AST.PatList (pats)) | (FStar_Parser_AST.PatTuple (pats, _)) | (FStar_Parser_AST.PatOr (pats)) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatRecord (guarded_pats) -> begin
(

let uu____690 = (FStar_List.map Prims.snd guarded_pats)
in (gather_pattern_bound_vars_from_list uu____690))
end
| FStar_Parser_AST.PatAscribed (pat, uu____695) -> begin
(gather_pattern_bound_vars_maybe_top acc pat)
end)))


let gather_pattern_bound_vars : FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (

let acc = (FStar_Util.new_set (fun id1 id2 -> (match ((id1.FStar_Ident.idText = id2.FStar_Ident.idText)) with
| true -> begin
(Prims.parse_int "0")
end
| uu____703 -> begin
(Prims.parse_int "1")
end)) (fun uu____704 -> (Prims.parse_int "0")))
in (fun p -> (gather_pattern_bound_vars_maybe_top acc p)))

type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term)


let uu___is_LocalBinder : bnd  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LocalBinder (_0) -> begin
true
end
| uu____722 -> begin
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
| uu____742 -> begin
false
end))


let __proj__LetBinder__item___0 : bnd  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| LetBinder (_0) -> begin
_0
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun uu___185_760 -> (match (uu___185_760) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| uu____765 -> begin
(failwith "Impossible")
end))


let as_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_ToSyntax_Env.env) = (fun env imp uu___186_782 -> (match (uu___186_782) with
| (None, k) -> begin
(

let uu____791 = (FStar_Syntax_Syntax.null_binder k)
in ((uu____791), (env)))
end
| (Some (a), k) -> begin
(

let uu____795 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____795) with
| (env1, a1) -> begin
(((((

let uu___207_806 = a1
in {FStar_Syntax_Syntax.ppname = uu___207_806.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___207_806.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env1))
end))
end))


type env_t =
FStar_ToSyntax_Env.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : ((FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.letbinding = (fun uu____819 -> (match (uu____819) with
| (n1, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n1; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))


let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))


let mk_ref_read = (fun tm -> (

let tm' = (

let uu____875 = (

let uu____885 = (

let uu____886 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm uu____886))
in (

let uu____887 = (

let uu____893 = (

let uu____898 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____898)))
in (uu____893)::[])
in ((uu____885), (uu____887))))
in FStar_Syntax_Syntax.Tm_app (uu____875))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc = (fun tm -> (

let tm' = (

let uu____932 = (

let uu____942 = (

let uu____943 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm uu____943))
in (

let uu____944 = (

let uu____950 = (

let uu____955 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____955)))
in (uu____950)::[])
in ((uu____942), (uu____944))))
in FStar_Syntax_Syntax.Tm_app (uu____932))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign = (fun t1 t2 pos -> (

let tm = (

let uu____1003 = (

let uu____1013 = (

let uu____1014 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1014))
in (

let uu____1015 = (

let uu____1021 = (

let uu____1026 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (uu____1026)))
in (

let uu____1029 = (

let uu____1035 = (

let uu____1040 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (uu____1040)))
in (uu____1035)::[])
in (uu____1021)::uu____1029))
in ((uu____1013), (uu____1015))))
in FStar_Syntax_Syntax.Tm_app (uu____1003))
in (FStar_Syntax_Syntax.mk tm None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun uu___187_1066 -> (match (uu___187_1066) with
| ("repr") | ("post") | ("pre") | ("wp") -> begin
true
end
| uu____1067 -> begin
false
end))


let rec sum_to_universe : FStar_Syntax_Syntax.universe  ->  Prims.int  ->  FStar_Syntax_Syntax.universe = (fun u n1 -> (match ((n1 = (Prims.parse_int "0"))) with
| true -> begin
u
end
| uu____1074 -> begin
(

let uu____1075 = (sum_to_universe u (n1 - (Prims.parse_int "1")))
in FStar_Syntax_Syntax.U_succ (uu____1075))
end))


let int_to_universe : Prims.int  ->  FStar_Syntax_Syntax.universe = (fun n1 -> (sum_to_universe FStar_Syntax_Syntax.U_zero n1))


let rec desugar_maybe_non_constant_universe : FStar_Parser_AST.term  ->  (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun t -> (

let uu____1086 = (

let uu____1087 = (unparen t)
in uu____1087.FStar_Parser_AST.tm)
in (match (uu____1086) with
| FStar_Parser_AST.Wild -> begin
(

let uu____1090 = (

let uu____1091 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (uu____1091))
in FStar_Util.Inr (uu____1090))
end
| FStar_Parser_AST.Uvar (u) -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_name (u))
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____1097)) -> begin
(

let n1 = (FStar_Util.int_of_string repr)
in ((match ((n1 < (Prims.parse_int "0"))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Negative universe constant  are not supported : " repr)), (t.FStar_Parser_AST.range)))))
end
| uu____1106 -> begin
()
end);
FStar_Util.Inl (n1);
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
| ((FStar_Util.Inl (n1), FStar_Util.Inr (u))) | ((FStar_Util.Inr (u), FStar_Util.Inl (n1))) -> begin
(

let uu____1140 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____1140))
end
| (FStar_Util.Inr (u11), FStar_Util.Inr (u21)) -> begin
(

let uu____1147 = (

let uu____1148 = (

let uu____1151 = (

let uu____1152 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "This universe might contain a sum of two universe variables " uu____1152))
in ((uu____1151), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____1148))
in (Prims.raise uu____1147))
end)))
end
| FStar_Parser_AST.App (uu____1155) -> begin
(

let rec aux = (fun t1 univargs -> (

let uu____1174 = (

let uu____1175 = (unparen t1)
in uu____1175.FStar_Parser_AST.tm)
in (match (uu____1174) with
| FStar_Parser_AST.App (t2, targ, uu____1180) -> begin
(

let uarg = (desugar_maybe_non_constant_universe targ)
in (aux t2 ((uarg)::univargs)))
end
| FStar_Parser_AST.Var (max_lid1) -> begin
(match ((FStar_List.existsb (fun uu___188_1192 -> (match (uu___188_1192) with
| FStar_Util.Inr (uu____1195) -> begin
true
end
| uu____1196 -> begin
false
end)) univargs)) with
| true -> begin
(

let uu____1199 = (

let uu____1200 = (FStar_List.map (fun uu___189_1204 -> (match (uu___189_1204) with
| FStar_Util.Inl (n1) -> begin
(int_to_universe n1)
end
| FStar_Util.Inr (u) -> begin
u
end)) univargs)
in FStar_Syntax_Syntax.U_max (uu____1200))
in FStar_Util.Inr (uu____1199))
end
| uu____1209 -> begin
(

let nargs = (FStar_List.map (fun uu___190_1214 -> (match (uu___190_1214) with
| FStar_Util.Inl (n1) -> begin
n1
end
| FStar_Util.Inr (uu____1218) -> begin
(failwith "impossible")
end)) univargs)
in (

let uu____1219 = (FStar_List.fold_left (fun m n1 -> (match ((m > n1)) with
| true -> begin
m
end
| uu____1222 -> begin
n1
end)) (Prims.parse_int "0") nargs)
in FStar_Util.Inl (uu____1219)))
end)
end
| uu____1223 -> begin
(

let uu____1224 = (

let uu____1225 = (

let uu____1228 = (

let uu____1229 = (

let uu____1230 = (FStar_Parser_AST.term_to_string t1)
in (Prims.strcat uu____1230 " in universe context"))
in (Prims.strcat "Unexpected term " uu____1229))
in ((uu____1228), (t1.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____1225))
in (Prims.raise uu____1224))
end)))
in (aux t []))
end
| uu____1235 -> begin
(

let uu____1236 = (

let uu____1237 = (

let uu____1240 = (

let uu____1241 = (

let uu____1242 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat uu____1242 " in universe context"))
in (Prims.strcat "Unexpected term " uu____1241))
in ((uu____1240), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____1237))
in (Prims.raise uu____1236))
end)))


let rec desugar_universe : FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.universe = (fun t -> (

let u = (desugar_maybe_non_constant_universe t)
in (match (u) with
| FStar_Util.Inl (n1) -> begin
(int_to_universe n1)
end
| FStar_Util.Inr (u1) -> begin
u1
end)))


let check_fields = (fun env fields rg -> (

let uu____1276 = (FStar_List.hd fields)
in (match (uu____1276) with
| (f, uu____1282) -> begin
(

let record = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f)
in (

let check_field = (fun uu____1289 -> (match (uu____1289) with
| (f', uu____1293) -> begin
(

let uu____1294 = (FStar_ToSyntax_Env.belongs_to_record env f' record)
in (match (uu____1294) with
| true -> begin
()
end
| uu____1295 -> begin
(

let msg = (FStar_Util.format3 "Field %s belongs to record type %s, whereas field %s does not" f.FStar_Ident.str record.FStar_ToSyntax_Env.typename.FStar_Ident.str f'.FStar_Ident.str)
in (Prims.raise (FStar_Errors.Error (((msg), (rg))))))
end))
end))
in ((

let uu____1298 = (FStar_List.tl fields)
in (FStar_List.iter check_field uu____1298));
(match (()) with
| () -> begin
record
end);
)))
end)))


let rec desugar_data_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat) = (fun env p is_mut -> (

let check_linear_pattern_variables = (fun p1 -> (

let rec pat_vars = (fun p2 -> (match (p2.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_dot_term (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_constant (_)) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (uu____1458, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out uu____1480 -> (match (uu____1480) with
| (p3, uu____1486) -> begin
(

let uu____1487 = (pat_vars p3)
in (FStar_Util.set_union out uu____1487))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd1)::tl1) -> begin
(

let xs = (pat_vars hd1)
in (

let uu____1501 = (

let uu____1502 = (FStar_Util.for_all (fun p3 -> (

let ys = (pat_vars p3)
in ((FStar_Util.set_is_subset_of xs ys) && (FStar_Util.set_is_subset_of ys xs)))) tl1)
in (not (uu____1502)))
in (match (uu____1501) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Disjunctive pattern binds different variables in each case"), (p2.FStar_Syntax_Syntax.p)))))
end
| uu____1505 -> begin
xs
end)))
end))
in (pat_vars p1)))
in ((match (((is_mut), (p.FStar_Parser_AST.pat))) with
| ((false, _)) | ((true, FStar_Parser_AST.PatVar (_))) -> begin
()
end
| (true, uu____1509) -> begin
(Prims.raise (FStar_Errors.Error ((("let-mutable is for variables only"), (p.FStar_Parser_AST.prange)))))
end);
(

let push_bv_maybe_mut = (match (is_mut) with
| true -> begin
FStar_ToSyntax_Env.push_bv_mutable
end
| uu____1523 -> begin
FStar_ToSyntax_Env.push_bv
end)
in (

let resolvex = (fun l e x -> (

let uu____1537 = (FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))
in (match (uu____1537) with
| Some (y) -> begin
((l), (e), (y))
end
| uu____1545 -> begin
(

let uu____1547 = (push_bv_maybe_mut e x)
in (match (uu____1547) with
| (e1, x1) -> begin
(((x1)::l), (e1), (x1))
end))
end)))
in (

let rec aux = (fun loc env1 p1 -> (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p1.FStar_Parser_AST.prange))
in (

let pos_r = (fun r q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r))
in (match (p1.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____1596 = (

let uu____1597 = (

let uu____1598 = (

let uu____1602 = (

let uu____1603 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") op)
in (FStar_Ident.id_of_text uu____1603))
in ((uu____1602), (None)))
in FStar_Parser_AST.PatVar (uu____1598))
in {FStar_Parser_AST.pat = uu____1597; FStar_Parser_AST.prange = p1.FStar_Parser_AST.prange})
in (aux loc env1 uu____1596))
end
| FStar_Parser_AST.PatOr ([]) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p2)::ps) -> begin
(

let uu____1615 = (aux loc env1 p2)
in (match (uu____1615) with
| (loc1, env2, var, p3, uu____1634) -> begin
(

let uu____1639 = (FStar_List.fold_left (fun uu____1652 p4 -> (match (uu____1652) with
| (loc2, env3, ps1) -> begin
(

let uu____1675 = (aux loc2 env3 p4)
in (match (uu____1675) with
| (loc3, env4, uu____1691, p5, uu____1693) -> begin
((loc3), (env4), ((p5)::ps1))
end))
end)) ((loc1), (env2), ([])) ps)
in (match (uu____1639) with
| (loc2, env3, ps1) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p3)::(FStar_List.rev ps1))))
in ((loc2), (env3), (var), (pat), (false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p2, t) -> begin
(

let uu____1737 = (aux loc env1 p2)
in (match (uu____1737) with
| (loc1, env', binder, p3, imp) -> begin
(

let binder1 = (match (binder) with
| LetBinder (uu____1762) -> begin
(failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t1 = (

let uu____1768 = (close_fun env1 t)
in (desugar_term env1 uu____1768))
in ((match ((match (x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| uu____1770 -> begin
true
end)) with
| true -> begin
(

let uu____1771 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____1772 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____1773 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3_warning "Multiple ascriptions for %s in pattern, type %s was shadowed by %s" uu____1771 uu____1772 uu____1773))))
end
| uu____1774 -> begin
()
end);
LocalBinder ((((

let uu___208_1775 = x
in {FStar_Syntax_Syntax.ppname = uu___208_1775.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___208_1775.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (aq)));
))
end)
in ((loc1), (env'), (binder1), (p3), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1779 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env1), (LocalBinder (((x), (None)))), (uu____1779), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1789 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env1), (LocalBinder (((x), (None)))), (uu____1789), (false))))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq1 = (trans_aqual aq)
in (

let uu____1807 = (resolvex loc env1 x)
in (match (uu____1807) with
| (loc1, env2, xbv) -> begin
(

let uu____1821 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____1821), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l1 = (FStar_ToSyntax_Env.fail_or env1 (FStar_ToSyntax_Env.try_lookup_datacon env1) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1832 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), ([])))))
in ((loc), (env1), (LocalBinder (((x), (None)))), (uu____1832), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = uu____1850}, args) -> begin
(

let uu____1854 = (FStar_List.fold_right (fun arg uu____1872 -> (match (uu____1872) with
| (loc1, env2, args1) -> begin
(

let uu____1902 = (aux loc1 env2 arg)
in (match (uu____1902) with
| (loc2, env3, uu____1920, arg1, imp) -> begin
((loc2), (env3), ((((arg1), (imp)))::args1))
end))
end)) args ((loc), (env1), ([])))
in (match (uu____1854) with
| (loc1, env2, args1) -> begin
(

let l1 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_datacon env2) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1969 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args1)))))
in ((loc1), (env2), (LocalBinder (((x), (None)))), (uu____1969), (false)))))
end))
end
| FStar_Parser_AST.PatApp (uu____1982) -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected pattern"), (p1.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____1995 = (FStar_List.fold_right (fun pat uu____2009 -> (match (uu____2009) with
| (loc1, env2, pats1) -> begin
(

let uu____2031 = (aux loc1 env2 pat)
in (match (uu____2031) with
| (loc2, env3, uu____2047, pat1, uu____2049) -> begin
((loc2), (env3), ((pat1)::pats1))
end))
end)) pats ((loc), (env1), ([])))
in (match (uu____1995) with
| (loc1, env2, pats1) -> begin
(

let pat = (

let uu____2083 = (

let uu____2086 = (

let uu____2091 = (FStar_Range.end_range p1.FStar_Parser_AST.prange)
in (pos_r uu____2091))
in (

let uu____2092 = (

let uu____2093 = (

let uu____2101 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____2101), ([])))
in FStar_Syntax_Syntax.Pat_cons (uu____2093))
in (FStar_All.pipe_left uu____2086 uu____2092)))
in (FStar_List.fold_right (fun hd1 tl1 -> (

let r = (FStar_Range.union_ranges hd1.FStar_Syntax_Syntax.p tl1.FStar_Syntax_Syntax.p)
in (

let uu____2124 = (

let uu____2125 = (

let uu____2133 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____2133), ((((hd1), (false)))::(((tl1), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (uu____2125))
in (FStar_All.pipe_left (pos_r r) uu____2124)))) pats1 uu____2083))
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc1), (env2), (LocalBinder (((x), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep1) -> begin
(

let uu____2165 = (FStar_List.fold_left (fun uu____2182 p2 -> (match (uu____2182) with
| (loc1, env2, pats) -> begin
(

let uu____2213 = (aux loc1 env2 p2)
in (match (uu____2213) with
| (loc2, env3, uu____2231, pat, uu____2233) -> begin
((loc2), (env3), ((((pat), (false)))::pats))
end))
end)) ((loc), (env1), ([])) args)
in (match (uu____2165) with
| (loc1, env2, args1) -> begin
(

let args2 = (FStar_List.rev args1)
in (

let l = (match (dep1) with
| true -> begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end
| uu____2296 -> begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end)
in (

let uu____2304 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_lid env2) l)
in (match (uu____2304) with
| (constr, uu____2317) -> begin
(

let l1 = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____2320 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____2322 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args2)))))
in ((loc1), (env2), (LocalBinder (((x), (None)))), (uu____2322), (false)))))
end))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected pattern"), (p1.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let record = (check_fields env1 fields p1.FStar_Parser_AST.prange)
in (

let fields1 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____2363 -> (match (uu____2363) with
| (f, p2) -> begin
((f.FStar_Ident.ident), (p2))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____2378 -> (match (uu____2378) with
| (f, uu____2382) -> begin
(

let uu____2383 = (FStar_All.pipe_right fields1 (FStar_List.tryFind (fun uu____2395 -> (match (uu____2395) with
| (g, uu____2399) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.idText)
end))))
in (match (uu____2383) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p1.FStar_Parser_AST.prange)
end
| Some (uu____2402, p2) -> begin
p2
end))
end))))
in (

let app = (

let uu____2407 = (

let uu____2408 = (

let uu____2412 = (

let uu____2413 = (

let uu____2414 = (FStar_Ident.lid_of_ids (FStar_List.append record.FStar_ToSyntax_Env.typename.FStar_Ident.ns ((record.FStar_ToSyntax_Env.constrname)::[])))
in FStar_Parser_AST.PatName (uu____2414))
in (FStar_Parser_AST.mk_pattern uu____2413 p1.FStar_Parser_AST.prange))
in ((uu____2412), (args)))
in FStar_Parser_AST.PatApp (uu____2408))
in (FStar_Parser_AST.mk_pattern uu____2407 p1.FStar_Parser_AST.prange))
in (

let uu____2416 = (aux loc env1 app)
in (match (uu____2416) with
| (env2, e, b, p2, uu____2435) -> begin
(

let p3 = (match (p2.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args1) -> begin
(

let uu____2457 = (

let uu____2458 = (

let uu____2466 = (

let uu___209_2467 = fv
in (

let uu____2468 = (

let uu____2470 = (

let uu____2471 = (

let uu____2475 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_ToSyntax_Env.typename), (uu____2475)))
in FStar_Syntax_Syntax.Record_ctor (uu____2471))
in Some (uu____2470))
in {FStar_Syntax_Syntax.fv_name = uu___209_2467.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = uu___209_2467.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu____2468}))
in ((uu____2466), (args1)))
in FStar_Syntax_Syntax.Pat_cons (uu____2458))
in (FStar_All.pipe_left pos uu____2457))
end
| uu____2494 -> begin
p2
end)
in ((env2), (e), (b), (p3), (false)))
end))))))
end))))
in (

let uu____2497 = (aux [] env p)
in (match (uu____2497) with
| (uu____2508, env1, b, p1, uu____2512) -> begin
((

let uu____2518 = (check_linear_pattern_variables p1)
in (FStar_All.pipe_left Prims.ignore uu____2518));
((env1), (b), (p1));
)
end)))));
)))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p is_mut -> (

let mklet = (fun x -> (

let uu____2537 = (

let uu____2538 = (

let uu____2541 = (FStar_ToSyntax_Env.qualify env x)
in ((uu____2541), (FStar_Syntax_Syntax.tun)))
in LetBinder (uu____2538))
in ((env), (uu____2537), (None))))
in (match (top) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(

let uu____2552 = (

let uu____2553 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") x)
in (FStar_Ident.id_of_text uu____2553))
in (mklet uu____2552))
end
| FStar_Parser_AST.PatVar (x, uu____2555) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2559); FStar_Parser_AST.prange = uu____2560}, t) -> begin
(

let uu____2564 = (

let uu____2565 = (

let uu____2568 = (FStar_ToSyntax_Env.qualify env x)
in (

let uu____2569 = (desugar_term env t)
in ((uu____2568), (uu____2569))))
in LetBinder (uu____2565))
in ((env), (uu____2564), (None)))
end
| uu____2571 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end
| uu____2576 -> begin
(

let uu____2577 = (desugar_data_pat env p is_mut)
in (match (uu____2577) with
| (env1, binder, p1) -> begin
(

let p2 = (match (p1.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| uu____2593 -> begin
Some (p1)
end)
in ((env1), (binder), (p2)))
end))
end)))
and desugar_binding_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun uu____2597 env pat -> (

let uu____2600 = (desugar_data_pat env pat false)
in (match (uu____2600) with
| (env1, uu____2607, pat1) -> begin
((env1), (pat1))
end)))
and desugar_match_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env1 = (

let uu___210_2614 = env
in {FStar_ToSyntax_Env.curmodule = uu___210_2614.FStar_ToSyntax_Env.curmodule; FStar_ToSyntax_Env.curmonad = uu___210_2614.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = uu___210_2614.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = uu___210_2614.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = uu___210_2614.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = uu___210_2614.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = uu___210_2614.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = uu___210_2614.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = uu___210_2614.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.iface = uu___210_2614.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = uu___210_2614.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = false})
in (desugar_term_maybe_top false env1 e)))
and desugar_typ : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env1 = (

let uu___211_2618 = env
in {FStar_ToSyntax_Env.curmodule = uu___211_2618.FStar_ToSyntax_Env.curmodule; FStar_ToSyntax_Env.curmonad = uu___211_2618.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = uu___211_2618.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = uu___211_2618.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = uu___211_2618.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = uu___211_2618.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = uu___211_2618.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = uu___211_2618.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = uu___211_2618.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.iface = uu___211_2618.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = uu___211_2618.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = true})
in (desugar_term_maybe_top false env1 e)))
and desugar_machine_integer : FStar_ToSyntax_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env repr uu____2621 range -> (match (uu____2621) with
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

let lid1 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text lid) range)
in (

let lid2 = (

let uu____2632 = (FStar_ToSyntax_Env.try_lookup_lid env lid1)
in (match (uu____2632) with
| Some (lid2) -> begin
(Prims.fst lid2)
end
| None -> begin
(

let uu____2643 = (FStar_Util.format1 "%s not in scope\n" (FStar_Ident.text_of_lid lid1))
in (failwith uu____2643))
end))
in (

let repr1 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (None)))))) None range)
in (

let uu____2660 = (

let uu____2663 = (

let uu____2664 = (

let uu____2674 = (

let uu____2680 = (

let uu____2685 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr1), (uu____2685)))
in (uu____2680)::[])
in ((lid2), (uu____2674)))
in FStar_Syntax_Syntax.Tm_app (uu____2664))
in (FStar_Syntax_Syntax.mk uu____2663))
in (uu____2660 None range))))))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env_t  ->  Prims.bool  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk1 setpos env resolve l -> (

let uu____2720 = (FStar_ToSyntax_Env.fail_or env ((match (resolve) with
| true -> begin
FStar_ToSyntax_Env.try_lookup_lid
end
| uu____2732 -> begin
FStar_ToSyntax_Env.try_lookup_lid_no_resolve
end) env) l)
in (match (uu____2720) with
| (tm, mut) -> begin
(

let tm1 = (setpos tm)
in (match (mut) with
| true -> begin
(

let uu____2738 = (

let uu____2739 = (

let uu____2744 = (mk_ref_read tm1)
in ((uu____2744), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (uu____2739))
in (FStar_All.pipe_left mk1 uu____2738))
end
| uu____2749 -> begin
tm1
end))
end)))
and desugar_attributes : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (

let uu____2758 = (

let uu____2759 = (unparen t)
in uu____2759.FStar_Parser_AST.tm)
in (match (uu____2758) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = uu____2760; FStar_Ident.ident = uu____2761; FStar_Ident.nsstr = uu____2762; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| uu____2764 -> begin
(

let uu____2765 = (

let uu____2766 = (

let uu____2769 = (

let uu____2770 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " uu____2770))
in ((uu____2769), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____2766))
in (Prims.raise uu____2765))
end)))
in (FStar_List.map desugar_attribute cattributes)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk1 = (fun e -> ((FStar_Syntax_Syntax.mk e) None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let uu___212_2798 = e
in {FStar_Syntax_Syntax.n = uu___212_2798.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___212_2798.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___212_2798.FStar_Syntax_Syntax.vars}))
in (

let uu____2805 = (

let uu____2806 = (unparen top)
in uu____2806.FStar_Parser_AST.tm)
in (match (uu____2805) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (uu____2807) -> begin
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
(mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("~"), (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("=="), (args)))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[])))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("*", (uu____2836)::(uu____2837)::[]) when (

let uu____2839 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right uu____2839 FStar_Option.isNone)) -> begin
(

let rec flatten1 = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(

let uu____2851 = (flatten1 t1)
in (FStar_List.append uu____2851 ((t2)::[])))
end
| uu____2853 -> begin
(t)::[]
end))
in (

let targs = (

let uu____2856 = (

let uu____2858 = (unparen top)
in (flatten1 uu____2858))
in (FStar_All.pipe_right uu____2856 (FStar_List.map (fun t -> (

let uu____2862 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg uu____2862))))))
in (

let uu____2863 = (

let uu____2866 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) uu____2866))
in (match (uu____2863) with
| (tup, uu____2873) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____2876 = (

let uu____2879 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) a)
in (Prims.fst uu____2879))
in (FStar_All.pipe_left setpos uu____2876))
end
| FStar_Parser_AST.Uvar (u) -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected universe variable " (Prims.strcat (FStar_Ident.text_of_id u) " in non-universe context"))), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(

let uu____2893 = (op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)
in (match (uu____2893) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected or unbound operator: " s)), (top.FStar_Parser_AST.range)))))
end
| Some (op) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let args1 = (FStar_All.pipe_right args (FStar_List.map (fun t -> (

let uu____2915 = (desugar_term env t)
in ((uu____2915), (None))))))
in (mk1 (FStar_Syntax_Syntax.Tm_app (((op), (args1))))))
end
| uu____2921 -> begin
op
end)
end))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2922; FStar_Ident.ident = uu____2923; FStar_Ident.nsstr = uu____2924; FStar_Ident.str = "Type0"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2926; FStar_Ident.ident = uu____2927; FStar_Ident.nsstr = uu____2928; FStar_Ident.str = "Type"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = uu____2930; FStar_Ident.ident = uu____2931; FStar_Ident.nsstr = uu____2932; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(

let uu____2942 = (

let uu____2943 = (desugar_universe t)
in FStar_Syntax_Syntax.Tm_type (uu____2943))
in (mk1 uu____2942))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2944; FStar_Ident.ident = uu____2945; FStar_Ident.nsstr = uu____2946; FStar_Ident.str = "Effect"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2948; FStar_Ident.ident = uu____2949; FStar_Ident.nsstr = uu____2950; FStar_Ident.str = "True"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2952; FStar_Ident.ident = uu____2953; FStar_Ident.nsstr = uu____2954; FStar_Ident.str = "False"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = uu____2958}) when ((is_special_effect_combinator txt) && (FStar_ToSyntax_Env.is_effect_name env eff_name)) -> begin
(

let uu____2959 = (FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name)
in (match (uu____2959) with
| Some (ed) -> begin
(

let uu____2962 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" txt))) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.fvar uu____2962 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
end
| None -> begin
(

let uu____2963 = (FStar_Util.format2 "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)" (FStar_Ident.text_of_lid eff_name) txt)
in (failwith uu____2963))
end))
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t21 = (desugar_term env t2)
in (

let uu____2967 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) ident)
in (match (uu____2967) with
| (t1, mut) -> begin
((match ((not (mut))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
end
| uu____2975 -> begin
()
end);
(mk_ref_assign t1 t21 top.FStar_Parser_AST.range);
)
end)))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(desugar_name mk1 setpos env true l)
end
| FStar_Parser_AST.Projector (l, i) -> begin
(

let name = (

let uu____2983 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____2983) with
| Some (uu____2988) -> begin
Some (((true), (l)))
end
| None -> begin
(

let uu____2991 = (FStar_ToSyntax_Env.try_lookup_root_effect_name env l)
in (match (uu____2991) with
| Some (new_name) -> begin
Some (((false), (new_name)))
end
| uu____2999 -> begin
None
end))
end))
in (match (name) with
| Some (resolve, new_name) -> begin
(

let uu____3007 = (FStar_Syntax_Util.mk_field_projector_name_from_ident new_name i)
in (desugar_name mk1 setpos env resolve uu____3007))
end
| uu____3008 -> begin
(

let uu____3012 = (

let uu____3013 = (

let uu____3016 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((uu____3016), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____3013))
in (Prims.raise uu____3012))
end))
end
| FStar_Parser_AST.Discrim (lid) -> begin
(

let uu____3018 = (FStar_ToSyntax_Env.try_lookup_datacon env lid)
in (match (uu____3018) with
| None -> begin
(

let uu____3020 = (

let uu____3021 = (

let uu____3024 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((uu____3024), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____3021))
in (Prims.raise uu____3020))
end
| uu____3025 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (desugar_name mk1 setpos env true lid'))
end))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(

let uu____3036 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____3036) with
| Some (head1) -> begin
(

let uu____3039 = (

let uu____3044 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (head1)))
in ((uu____3044), (true)))
in (match (uu____3039) with
| (head2, is_data) -> begin
(match (args) with
| [] -> begin
head2
end
| uu____3057 -> begin
(

let uu____3061 = (FStar_Util.take (fun uu____3072 -> (match (uu____3072) with
| (uu____3075, imp) -> begin
(imp = FStar_Parser_AST.UnivApp)
end)) args)
in (match (uu____3061) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun x -> (desugar_universe (Prims.fst x))) universes)
in (

let args2 = (FStar_List.map (fun uu____3108 -> (match (uu____3108) with
| (t, imp) -> begin
(

let te = (desugar_term env t)
in (arg_withimp_e imp te))
end)) args1)
in (

let head3 = (match ((universes1 = [])) with
| true -> begin
head2
end
| uu____3123 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_uinst (((head2), (universes1)))))
end)
in (

let app = (mk1 (FStar_Syntax_Syntax.Tm_app (((head3), (args2)))))
in (match (is_data) with
| true -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((app), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| uu____3138 -> begin
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

let uu____3143 = (FStar_List.fold_left (fun uu____3160 b -> (match (uu____3160) with
| (env1, tparams, typs) -> begin
(

let uu____3191 = (desugar_binder env1 b)
in (match (uu____3191) with
| (xopt, t1) -> begin
(

let uu____3207 = (match (xopt) with
| None -> begin
(

let uu____3212 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env1), (uu____3212)))
end
| Some (x) -> begin
(FStar_ToSyntax_Env.push_bv env1 x)
end)
in (match (uu____3207) with
| (env2, x) -> begin
(

let uu____3224 = (

let uu____3226 = (

let uu____3228 = (

let uu____3229 = (no_annot_abs tparams t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3229))
in (uu____3228)::[])
in (FStar_List.append typs uu____3226))
in ((env2), ((FStar_List.append tparams (((((

let uu___213_3242 = x
in {FStar_Syntax_Syntax.ppname = uu___213_3242.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___213_3242.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (None)))::[]))), (uu____3224)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level None))::[])))
in (match (uu____3143) with
| (env1, uu____3255, targs) -> begin
(

let uu____3267 = (

let uu____3270 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env1 (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3270))
in (match (uu____3267) with
| (tup, uu____3277) -> begin
(FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let uu____3285 = (uncurry binders t)
in (match (uu____3285) with
| (bs, t1) -> begin
(

let rec aux = (fun env1 bs1 uu___191_3308 -> (match (uu___191_3308) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range env1 t1)
in (

let uu____3318 = (FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod)
in (FStar_All.pipe_left setpos uu____3318)))
end
| (hd1)::tl1 -> begin
(

let bb = (desugar_binder env1 hd1)
in (

let uu____3334 = (as_binder env1 hd1.FStar_Parser_AST.aqual bb)
in (match (uu____3334) with
| (b, env2) -> begin
(aux env2 ((b)::bs1) tl1)
end)))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(

let uu____3345 = (desugar_binder env b)
in (match (uu____3345) with
| (None, uu____3349) -> begin
(failwith "Missing binder in refinement")
end
| b1 -> begin
(

let uu____3355 = (as_binder env None b1)
in (match (uu____3355) with
| ((x, uu____3359), env1) -> begin
(

let f1 = (desugar_formula env1 f)
in (

let uu____3364 = (FStar_Syntax_Util.refine x f1)
in (FStar_All.pipe_left setpos uu____3364)))
end))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders1 = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let uu____3379 = (FStar_List.fold_left (fun uu____3386 pat -> (match (uu____3386) with
| (env1, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (uu____3401, t) -> begin
(

let uu____3403 = (

let uu____3405 = (free_type_vars env1 t)
in (FStar_List.append uu____3405 ftvs))
in ((env1), (uu____3403)))
end
| uu____3408 -> begin
((env1), (ftvs))
end)
end)) ((env), ([])) binders1)
in (match (uu____3379) with
| (uu____3411, ftv) -> begin
(

let ftv1 = (sort_ftv ftv)
in (

let binders2 = (

let uu____3419 = (FStar_All.pipe_right ftv1 (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append uu____3419 binders1))
in (

let rec aux = (fun env1 bs sc_pat_opt uu___192_3448 -> (match (uu___192_3448) with
| [] -> begin
(

let body1 = (desugar_term env1 body)
in (

let body2 = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(

let body2 = (

let uu____3477 = (

let uu____3478 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right uu____3478 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close uu____3477 body1))
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (None), (body2)))::[]))))) None body2.FStar_Syntax_Syntax.pos))
end
| None -> begin
body1
end)
in (

let uu____3520 = (no_annot_abs (FStar_List.rev bs) body2)
in (setpos uu____3520))))
end
| (p)::rest -> begin
(

let uu____3528 = (desugar_binding_pat env1 p)
in (match (uu____3528) with
| (env2, b, pat) -> begin
(

let uu____3540 = (match (b) with
| LetBinder (uu____3559) -> begin
(failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt1 = (match (((pat), (sc_pat_opt))) with
| (None, uu____3590) -> begin
sc_pat_opt
end
| (Some (p1), None) -> begin
(

let uu____3613 = (

let uu____3616 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____3616), (p1)))
in Some (uu____3613))
end
| (Some (p1), Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (uu____3641), uu____3642) -> begin
(

let tup2 = (

let uu____3644 = (FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____3644 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____3648 = (

let uu____3651 = (

let uu____3652 = (

let uu____3662 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (

let uu____3665 = (

let uu____3667 = (FStar_Syntax_Syntax.as_arg sc)
in (

let uu____3668 = (

let uu____3670 = (

let uu____3671 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3671))
in (uu____3670)::[])
in (uu____3667)::uu____3668))
in ((uu____3662), (uu____3665))))
in FStar_Syntax_Syntax.Tm_app (uu____3652))
in (FStar_Syntax_Syntax.mk uu____3651))
in (uu____3648 None top.FStar_Parser_AST.range))
in (

let p2 = (

let uu____3686 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p1), (false)))::[])))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n uu____3686))
in Some (((sc1), (p2))))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____3706, args), FStar_Syntax_Syntax.Pat_cons (uu____3708, pats)) -> begin
(

let tupn = (

let uu____3735 = (FStar_Syntax_Util.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____3735 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____3745 = (

let uu____3746 = (

let uu____3756 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (

let uu____3759 = (

let uu____3765 = (

let uu____3771 = (

let uu____3772 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3772))
in (uu____3771)::[])
in (FStar_List.append args uu____3765))
in ((uu____3756), (uu____3759))))
in FStar_Syntax_Syntax.Tm_app (uu____3746))
in (mk1 uu____3745))
in (

let p2 = (

let uu____3787 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p1), (false)))::[])))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n uu____3787))
in Some (((sc1), (p2))))))
end
| uu____3811 -> begin
(failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt1)))
end)
in (match (uu____3540) with
| (b1, sc_pat_opt1) -> begin
(aux env2 ((b1)::bs) sc_pat_opt1 rest)
end))
end))
end))
in (aux env [] None binders2))))
end)))
end
| FStar_Parser_AST.App (uu____3852, uu____3853, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (

let uu____3865 = (

let uu____3866 = (unparen e)
in uu____3866.FStar_Parser_AST.tm)
in (match (uu____3865) with
| FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e1))
end
| uu____3872 -> begin
(

let head1 = (desugar_term env e)
in (mk1 (FStar_Syntax_Syntax.Tm_uinst (((head1), (universes))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.App (uu____3875) -> begin
(

let rec aux = (fun args e -> (

let uu____3896 = (

let uu____3897 = (unparen e)
in uu____3897.FStar_Parser_AST.tm)
in (match (uu____3896) with
| FStar_Parser_AST.App (e1, t, imp) when (imp <> FStar_Parser_AST.UnivApp) -> begin
(

let arg = (

let uu____3907 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) uu____3907))
in (aux ((arg)::args) e1))
end
| uu____3914 -> begin
(

let head1 = (desugar_term env e)
in (mk1 (FStar_Syntax_Syntax.Tm_app (((head1), (args))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let uu____3925 = (

let uu____3926 = (

let uu____3931 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((uu____3931), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))
in FStar_Syntax_Syntax.Tm_meta (uu____3926))
in (mk1 uu____3925))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let env1 = (FStar_ToSyntax_Env.push_namespace env lid)
in (desugar_term_maybe_top top_level env1 e))
end
| FStar_Parser_AST.Let (qual1, ((pat, _snd))::_tl, body) -> begin
(

let is_rec = (qual1 = FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun uu____3961 -> (

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun uu____4003 -> (match (uu____4003) with
| (p, def) -> begin
(

let uu____4017 = (is_app_pattern p)
in (match (uu____4017) with
| true -> begin
(

let uu____4027 = (destruct_app_pattern env top_level p)
in ((uu____4027), (def)))
end
| uu____4042 -> begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p1, def1) -> begin
(

let uu____4056 = (destruct_app_pattern env top_level p1)
in ((uu____4056), (def1)))
end
| uu____4071 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____4085); FStar_Parser_AST.prange = uu____4086}, t) -> begin
(match (top_level) with
| true -> begin
(

let uu____4099 = (

let uu____4107 = (

let uu____4110 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____4110))
in ((uu____4107), ([]), (Some (t))))
in ((uu____4099), (def)))
end
| uu____4122 -> begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end)
end
| FStar_Parser_AST.PatVar (id, uu____4135) -> begin
(match (top_level) with
| true -> begin
(

let uu____4147 = (

let uu____4155 = (

let uu____4158 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____4158))
in ((uu____4155), ([]), (None)))
in ((uu____4147), (def)))
end
| uu____4170 -> begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end)
end
| uu____4182 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end))
end))))
in (

let uu____4192 = (FStar_List.fold_left (fun uu____4216 uu____4217 -> (match (((uu____4216), (uu____4217))) with
| ((env1, fnames, rec_bindings), ((f, uu____4261, uu____4262), uu____4263)) -> begin
(

let uu____4303 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let uu____4317 = (FStar_ToSyntax_Env.push_bv env1 x)
in (match (uu____4317) with
| (env2, xx) -> begin
(

let uu____4328 = (

let uu____4330 = (FStar_Syntax_Syntax.mk_binder xx)
in (uu____4330)::rec_bindings)
in ((env2), (FStar_Util.Inl (xx)), (uu____4328)))
end))
end
| FStar_Util.Inr (l) -> begin
(

let uu____4335 = (FStar_ToSyntax_Env.push_top_level_rec_binding env1 l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((uu____4335), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (uu____4303) with
| (env2, lbname, rec_bindings1) -> begin
((env2), ((lbname)::fnames), (rec_bindings1))
end))
end)) ((env), ([]), ([])) funs)
in (match (uu____4192) with
| (env', fnames, rec_bindings) -> begin
(

let fnames1 = (FStar_List.rev fnames)
in (

let rec_bindings1 = (FStar_List.rev rec_bindings)
in (

let desugar_one_def = (fun env1 lbname uu____4408 -> (match (uu____4408) with
| ((uu____4420, args, result_t), def) -> begin
(

let args1 = (FStar_All.pipe_right args (FStar_List.map replace_unit_pattern))
in (

let def1 = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(

let t1 = (

let uu____4446 = (is_comp_type env1 t)
in (match (uu____4446) with
| true -> begin
((

let uu____4448 = (FStar_All.pipe_right args1 (FStar_List.tryFind (fun x -> (

let uu____4453 = (is_var_pattern x)
in (not (uu____4453))))))
in (match (uu____4448) with
| None -> begin
()
end
| Some (p) -> begin
(Prims.raise (FStar_Errors.Error ((("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable"), (p.FStar_Parser_AST.prange)))))
end));
t;
)
end
| uu____4455 -> begin
(

let uu____4456 = (((FStar_Options.ml_ish ()) && (

let uu____4457 = (FStar_ToSyntax_Env.try_lookup_effect_name env1 FStar_Syntax_Const.effect_ML_lid)
in (FStar_Option.isSome uu____4457))) && ((not (is_rec)) || ((FStar_List.length args1) <> (Prims.parse_int "0"))))
in (match (uu____4456) with
| true -> begin
(FStar_Parser_AST.ml_comp t)
end
| uu____4461 -> begin
(FStar_Parser_AST.tot_comp t)
end))
end))
in (

let uu____4462 = (FStar_Range.union_ranges t1.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t1), (None)))) uu____4462 FStar_Parser_AST.Expr)))
end)
in (

let def2 = (match (args1) with
| [] -> begin
def1
end
| uu____4465 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args1 def1) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (

let body1 = (desugar_term env1 def2)
in (

let lbname1 = (match (lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl (x)
end
| FStar_Util.Inr (l) -> begin
(

let uu____4475 = (

let uu____4476 = (FStar_Syntax_Util.incr_delta_qualifier body1)
in (FStar_Syntax_Syntax.lid_as_fv l uu____4476 None))
in FStar_Util.Inr (uu____4475))
end)
in (

let body2 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.close rec_bindings1 body1)
end
| uu____4478 -> begin
body1
end)
in (mk_lb ((lbname1), (FStar_Syntax_Syntax.tun), (body2)))))))))
end))
in (

let lbs = (FStar_List.map2 (desugar_one_def (match (is_rec) with
| true -> begin
env'
end
| uu____4494 -> begin
env
end)) fnames1 funs)
in (

let body1 = (desugar_term env' body)
in (

let uu____4496 = (

let uu____4497 = (

let uu____4505 = (FStar_Syntax_Subst.close rec_bindings1 body1)
in ((((is_rec), (lbs))), (uu____4505)))
in FStar_Syntax_Syntax.Tm_let (uu____4497))
in (FStar_All.pipe_left mk1 uu____4496)))))))
end)))))
in (

let ds_non_rec = (fun pat1 t1 t2 -> (

let t11 = (desugar_term env t1)
in (

let is_mutable = (qual1 = FStar_Parser_AST.Mutable)
in (

let t12 = (match (is_mutable) with
| true -> begin
(mk_ref_alloc t11)
end
| uu____4531 -> begin
t11
end)
in (

let uu____4532 = (desugar_binding_pat_maybe_top top_level env pat1 is_mutable)
in (match (uu____4532) with
| (env1, binder, pat2) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body1 = (desugar_term env1 t2)
in (

let fv = (

let uu____4553 = (FStar_Syntax_Util.incr_delta_qualifier t12)
in (FStar_Syntax_Syntax.lid_as_fv l uu____4553 None))
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t12})::[]))), (body1)))))))
end
| LocalBinder (x, uu____4561) -> begin
(

let body1 = (desugar_term env1 t2)
in (

let body2 = (match (pat2) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body1
end
| Some (pat3) -> begin
(

let uu____4570 = (

let uu____4573 = (

let uu____4574 = (

let uu____4590 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____4591 = (

let uu____4593 = (FStar_Syntax_Util.branch ((pat3), (None), (body1)))
in (uu____4593)::[])
in ((uu____4590), (uu____4591))))
in FStar_Syntax_Syntax.Tm_match (uu____4574))
in (FStar_Syntax_Syntax.mk uu____4573))
in (uu____4570 None body1.FStar_Syntax_Syntax.pos))
end)
in (

let uu____4608 = (

let uu____4609 = (

let uu____4617 = (

let uu____4618 = (

let uu____4619 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4619)::[])
in (FStar_Syntax_Subst.close uu____4618 body2))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t12))))::[]))), (uu____4617)))
in FStar_Syntax_Syntax.Tm_let (uu____4609))
in (FStar_All.pipe_left mk1 uu____4608))))
end)
in (match (is_mutable) with
| true -> begin
(FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc))))))
end
| uu____4638 -> begin
tm
end))
end))))))
in (

let uu____4639 = (is_rec || (is_app_pattern pat))
in (match (uu____4639) with
| true -> begin
(ds_let_rec_or_app ())
end
| uu____4640 -> begin
(ds_non_rec pat _snd body)
end)))))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let uu____4645 = (

let uu____4646 = (

let uu____4662 = (desugar_term env t1)
in (

let uu____4663 = (

let uu____4673 = (

let uu____4682 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (

let uu____4685 = (desugar_term env t2)
in ((uu____4682), (None), (uu____4685))))
in (

let uu____4693 = (

let uu____4703 = (

let uu____4712 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (

let uu____4715 = (desugar_term env t3)
in ((uu____4712), (None), (uu____4715))))
in (uu____4703)::[])
in (uu____4673)::uu____4693))
in ((uu____4662), (uu____4663))))
in FStar_Syntax_Syntax.Tm_match (uu____4646))
in (mk1 uu____4645)))
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

let desugar_branch = (fun uu____4801 -> (match (uu____4801) with
| (pat, wopt, b) -> begin
(

let uu____4811 = (desugar_match_pat env pat)
in (match (uu____4811) with
| (env1, pat1) -> begin
(

let wopt1 = (match (wopt) with
| None -> begin
None
end
| Some (e1) -> begin
(

let uu____4820 = (desugar_term env1 e1)
in Some (uu____4820))
end)
in (

let b1 = (desugar_term env1 b)
in (FStar_Syntax_Util.branch ((pat1), (wopt1), (b1)))))
end))
end))
in (

let uu____4823 = (

let uu____4824 = (

let uu____4840 = (desugar_term env e)
in (

let uu____4841 = (FStar_List.map desugar_branch branches)
in ((uu____4840), (uu____4841))))
in FStar_Syntax_Syntax.Tm_match (uu____4824))
in (FStar_All.pipe_left mk1 uu____4823)))
end
| FStar_Parser_AST.Ascribed (e, t, tac_opt) -> begin
(

let annot = (

let uu____4860 = (is_comp_type env t)
in (match (uu____4860) with
| true -> begin
(

let uu____4865 = (desugar_comp t.FStar_Parser_AST.range env t)
in FStar_Util.Inr (uu____4865))
end
| uu____4870 -> begin
(

let uu____4871 = (desugar_term env t)
in FStar_Util.Inl (uu____4871))
end))
in (

let tac_opt1 = (FStar_Util.map_opt tac_opt (desugar_term env))
in (

let uu____4876 = (

let uu____4877 = (

let uu____4895 = (desugar_term env e)
in ((uu____4895), (((annot), (tac_opt1))), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____4877))
in (FStar_All.pipe_left mk1 uu____4876))))
end
| FStar_Parser_AST.Record (uu____4911, []) -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let uu____4932 = (FStar_List.hd fields)
in (match (uu____4932) with
| (f, uu____4939) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun uu____4963 -> (match (uu____4963) with
| (g, uu____4967) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| Some (uu____4971, e) -> begin
((fn), (e))
end
| None -> begin
(match (xopt) with
| None -> begin
(

let uu____4979 = (

let uu____4980 = (

let uu____4983 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_ToSyntax_Env.typename.FStar_Ident.str)
in ((uu____4983), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____4980))
in (Prims.raise uu____4979))
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

let uu____4989 = (

let uu____4995 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____5009 -> (match (uu____5009) with
| (f, uu____5015) -> begin
(

let uu____5016 = (

let uu____5017 = (get_field None f)
in (FStar_All.pipe_left Prims.snd uu____5017))
in ((uu____5016), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (uu____4995)))
in FStar_Parser_AST.Construct (uu____4989))
end
| Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (

let uu____5028 = (

let uu____5029 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____5029))
in (FStar_Parser_AST.mk_term uu____5028 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record1 = (

let uu____5031 = (

let uu____5038 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____5052 -> (match (uu____5052) with
| (f, uu____5058) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (uu____5038)))
in FStar_Parser_AST.Record (uu____5031))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record1 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm1 = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm1)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____5074; FStar_Syntax_Syntax.pos = uu____5075; FStar_Syntax_Syntax.vars = uu____5076}, args); FStar_Syntax_Syntax.tk = uu____5078; FStar_Syntax_Syntax.pos = uu____5079; FStar_Syntax_Syntax.vars = uu____5080}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e1 = (

let uu____5102 = (

let uu____5103 = (

let uu____5113 = (

let uu____5114 = (

let uu____5116 = (

let uu____5117 = (

let uu____5121 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_ToSyntax_Env.typename), (uu____5121)))
in FStar_Syntax_Syntax.Record_ctor (uu____5117))
in Some (uu____5116))
in (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant uu____5114))
in ((uu____5113), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____5103))
in (FStar_All.pipe_left mk1 uu____5102))
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((e1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| uu____5145 -> begin
e
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let uu____5148 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f)
in (match (uu____5148) with
| (constrname, is_rec) -> begin
(

let e1 = (desugar_term env e)
in (

let projname = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname f.FStar_Ident.ident)
in (

let qual1 = (match (is_rec) with
| true -> begin
Some (FStar_Syntax_Syntax.Record_projector (((constrname), (f.FStar_Ident.ident))))
end
| uu____5160 -> begin
None
end)
in (

let uu____5161 = (

let uu____5162 = (

let uu____5172 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projname (FStar_Ident.range_of_lid f)) FStar_Syntax_Syntax.Delta_equational qual1)
in (

let uu____5173 = (

let uu____5175 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____5175)::[])
in ((uu____5172), (uu____5173))))
in FStar_Syntax_Syntax.Tm_app (uu____5162))
in (FStar_All.pipe_left mk1 uu____5161)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| uu____5181 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| uu____5182 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Let (uu____5183, uu____5184, uu____5185) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QForall (uu____5192, uu____5193, uu____5194) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QExists (uu____5201, uu____5202, uu____5203) -> begin
(failwith "Not implemented yet")
end)))))
and desugar_args : FStar_ToSyntax_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____5227 -> (match (uu____5227) with
| (a, imp) -> begin
(

let uu____5235 = (desugar_term env a)
in (arg_withimp_e imp uu____5235))
end)))))
and desugar_comp : FStar_Range.range  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Errors.Error (((msg), (r))))))
in (

let is_requires = (fun uu____5252 -> (match (uu____5252) with
| (t1, uu____5256) -> begin
(

let uu____5257 = (

let uu____5258 = (unparen t1)
in uu____5258.FStar_Parser_AST.tm)
in (match (uu____5257) with
| FStar_Parser_AST.Requires (uu____5259) -> begin
true
end
| uu____5263 -> begin
false
end))
end))
in (

let is_ensures = (fun uu____5269 -> (match (uu____5269) with
| (t1, uu____5273) -> begin
(

let uu____5274 = (

let uu____5275 = (unparen t1)
in uu____5275.FStar_Parser_AST.tm)
in (match (uu____5274) with
| FStar_Parser_AST.Ensures (uu____5276) -> begin
true
end
| uu____5280 -> begin
false
end))
end))
in (

let is_app = (fun head1 uu____5289 -> (match (uu____5289) with
| (t1, uu____5293) -> begin
(

let uu____5294 = (

let uu____5295 = (unparen t1)
in uu____5295.FStar_Parser_AST.tm)
in (match (uu____5294) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = uu____5297; FStar_Parser_AST.level = uu____5298}, uu____5299, uu____5300) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head1)
end
| uu____5301 -> begin
false
end))
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t1 -> (

let uu____5319 = (head_and_args t1)
in (match (uu____5319) with
| (head1, args) -> begin
(match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(

let unit_tm = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) t1.FStar_Parser_AST.range FStar_Parser_AST.Type_level)), (FStar_Parser_AST.Nothing))
in (

let nil_pat = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.nil_lid)) t1.FStar_Parser_AST.range FStar_Parser_AST.Expr)), (FStar_Parser_AST.Nothing))
in (

let req_true = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Requires ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.true_lid)) t1.FStar_Parser_AST.range FStar_Parser_AST.Formula)), (None)))) t1.FStar_Parser_AST.range FStar_Parser_AST.Type_level)), (FStar_Parser_AST.Nothing))
in (

let args1 = (match (args) with
| [] -> begin
(Prims.raise (FStar_Errors.Error ((("Not enough arguments to \'Lemma\'"), (t1.FStar_Parser_AST.range)))))
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
in ((head_and_attributes), (args1)))))))
end
| FStar_Parser_AST.Name (l) when (FStar_ToSyntax_Env.is_effect_name env l) -> begin
(

let uu____5484 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes env) l)
in ((uu____5484), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____5498 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals uu____5498 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head1.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((

let uu____5507 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals uu____5507 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head1.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when (((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head1.FStar_Parser_AST.range)), ([]))), ((((t1), (FStar_Parser_AST.Nothing)))::[]))
end
| uu____5527 -> begin
(

let default_effect = (

let uu____5529 = (FStar_Options.ml_ish ())
in (match (uu____5529) with
| true -> begin
FStar_Syntax_Const.effect_ML_lid
end
| uu____5530 -> begin
((

let uu____5532 = (FStar_Options.warn_default_effects ())
in (match (uu____5532) with
| true -> begin
(FStar_Errors.warn head1.FStar_Parser_AST.range "Using default effect Tot")
end
| uu____5533 -> begin
()
end));
FStar_Syntax_Const.effect_Tot_lid;
)
end))
in (((((FStar_Ident.set_lid_range default_effect head1.FStar_Parser_AST.range)), ([]))), ((((t1), (FStar_Parser_AST.Nothing)))::[])))
end)
end)))
in (

let uu____5545 = (pre_process_comp_typ t)
in (match (uu____5545) with
| ((eff, cattributes), args) -> begin
((match (((FStar_List.length args) = (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5575 = (

let uu____5576 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" uu____5576))
in (fail uu____5575))
end
| uu____5577 -> begin
()
end);
(

let is_universe = (fun uu____5583 -> (match (uu____5583) with
| (uu____5586, imp) -> begin
(imp = FStar_Parser_AST.UnivApp)
end))
in (

let uu____5588 = (FStar_Util.take is_universe args)
in (match (uu____5588) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun uu____5619 -> (match (uu____5619) with
| (u, imp) -> begin
(desugar_universe u)
end)) universes)
in (

let uu____5624 = (

let uu____5632 = (FStar_List.hd args1)
in (

let uu____5637 = (FStar_List.tl args1)
in ((uu____5632), (uu____5637))))
in (match (uu____5624) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (Prims.fst result_arg))
in (

let rest1 = (desugar_args env rest)
in (

let uu____5668 = (FStar_All.pipe_right rest1 (FStar_List.partition (fun uu____5706 -> (match (uu____5706) with
| (t1, uu____5713) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____5721; FStar_Syntax_Syntax.pos = uu____5722; FStar_Syntax_Syntax.vars = uu____5723}, (uu____5724)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| uu____5746 -> begin
false
end)
end))))
in (match (uu____5668) with
| (dec, rest2) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun uu____5789 -> (match (uu____5789) with
| (t1, uu____5796) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____5803, ((arg, uu____5805))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| uu____5827 -> begin
(failwith "impos")
end)
end))))
in (

let no_additional_args = (

let is_empty = (fun l -> (match (l) with
| [] -> begin
true
end
| uu____5839 -> begin
false
end))
in ((((is_empty decreases_clause) && (is_empty rest2)) && (is_empty cattributes)) && (is_empty universes1)))
in (match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end
| uu____5848 -> begin
(match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end
| uu____5851 -> begin
(

let flags = (match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid)) with
| true -> begin
(FStar_Syntax_Syntax.LEMMA)::[]
end
| uu____5855 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____5857 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_ML_lid)) with
| true -> begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end
| uu____5859 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____5861 -> begin
[]
end)
end)
end)
end)
in (

let flags1 = (FStar_List.append flags cattributes)
in (

let rest3 = (match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid)) with
| true -> begin
(match (rest2) with
| (req)::(ens)::((pat, aq))::[] -> begin
(

let pat1 = (match (pat.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
(

let nil = (FStar_Syntax_Syntax.mk_Tm_uinst pat ((FStar_Syntax_Syntax.U_succ (FStar_Syntax_Syntax.U_zero))::[]))
in (

let pattern = (

let uu____5931 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5931 ((FStar_Syntax_Syntax.U_zero)::[])))
in ((FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (Some (FStar_Syntax_Syntax.imp_tag))))::[])) None pat.FStar_Syntax_Syntax.pos)))
end
| uu____5943 -> begin
pat
end)
in (

let uu____5944 = (

let uu____5951 = (

let uu____5958 = (

let uu____5964 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))))) None pat1.FStar_Syntax_Syntax.pos)
in ((uu____5964), (aq)))
in (uu____5958)::[])
in (ens)::uu____5951)
in (req)::uu____5944))
end
| uu____6000 -> begin
rest2
end)
end
| uu____6007 -> begin
rest2
end)
in (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = universes1; FStar_Syntax_Syntax.effect_name = eff; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = rest3; FStar_Syntax_Syntax.flags = (FStar_List.append flags1 decreases_clause)}))))
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
| uu____6016 -> begin
None
end))
in (

let mk1 = (fun t -> ((FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let uu___214_6057 = t
in {FStar_Syntax_Syntax.n = uu___214_6057.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___214_6057.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___214_6057.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let uu___215_6087 = b
in {FStar_Parser_AST.b = uu___215_6087.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___215_6087.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___215_6087.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env1 pats1 -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (

let uu____6120 = (desugar_term env1 e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) uu____6120)))))) pats1))
in (match (tk) with
| (Some (a), k) -> begin
(

let uu____6129 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____6129) with
| (env1, a1) -> begin
(

let a2 = (

let uu___216_6137 = a1
in {FStar_Syntax_Syntax.ppname = uu___216_6137.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___216_6137.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats1 = (desugar_pats env1 pats)
in (

let body1 = (desugar_formula env1 body)
in (

let body2 = (match (pats1) with
| [] -> begin
body1
end
| uu____6150 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((body1), (FStar_Syntax_Syntax.Meta_pattern (pats1))))))
end)
in (

let body3 = (

let uu____6159 = (

let uu____6162 = (

let uu____6166 = (FStar_Syntax_Syntax.mk_binder a2)
in (uu____6166)::[])
in (no_annot_abs uu____6162 body2))
in (FStar_All.pipe_left setpos uu____6159))
in (

let uu____6171 = (

let uu____6172 = (

let uu____6182 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let uu____6183 = (

let uu____6185 = (FStar_Syntax_Syntax.as_arg body3)
in (uu____6185)::[])
in ((uu____6182), (uu____6183))))
in FStar_Syntax_Syntax.Tm_app (uu____6172))
in (FStar_All.pipe_left mk1 uu____6171)))))))
end))
end
| uu____6189 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body1 = (

let uu____6238 = (q ((rest), (pats), (body)))
in (

let uu____6242 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term uu____6238 uu____6242 FStar_Parser_AST.Formula)))
in (

let uu____6243 = (q (((b)::[]), ([]), (body1)))
in (FStar_Parser_AST.mk_term uu____6243 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| uu____6248 -> begin
(failwith "impossible")
end))
in (

let uu____6250 = (

let uu____6251 = (unparen f)
in uu____6251.FStar_Parser_AST.tm)
in (match (uu____6250) with
| FStar_Parser_AST.Labeled (f1, l, p) -> begin
(

let f2 = (desugar_formula env f1)
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((f2), (FStar_Syntax_Syntax.Meta_labeled (((l), (f2.FStar_Syntax_Syntax.pos), (p)))))))))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____6281 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env uu____6281)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____6302 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env uu____6302)))
end
| FStar_Parser_AST.QForall ((b)::[], pats, body) -> begin
(desugar_quant FStar_Syntax_Const.forall_lid b pats body)
end
| FStar_Parser_AST.QExists ((b)::[], pats, body) -> begin
(desugar_quant FStar_Syntax_Const.exists_lid b pats body)
end
| FStar_Parser_AST.Paren (f1) -> begin
(desugar_formula env f1)
end
| uu____6327 -> begin
(desugar_term env f)
end)))))))))
and typars_of_binders : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let uu____6331 = (FStar_List.fold_left (fun uu____6344 b -> (match (uu____6344) with
| (env1, out) -> begin
(

let tk = (desugar_binder env1 (

let uu___217_6372 = b
in {FStar_Parser_AST.b = uu___217_6372.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___217_6372.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___217_6372.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(

let uu____6382 = (FStar_ToSyntax_Env.push_bv env1 a)
in (match (uu____6382) with
| (env2, a1) -> begin
(

let a2 = (

let uu___218_6394 = a1
in {FStar_Syntax_Syntax.ppname = uu___218_6394.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___218_6394.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env2), ((((a2), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| uu____6403 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (uu____6331) with
| (env1, tpars) -> begin
((env1), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(

let uu____6453 = (desugar_typ env t)
in ((Some (x)), (uu____6453)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____6456 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown))) None x.FStar_Ident.idRange)
in ((Some (x)), (uu____6456)))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____6471 = (desugar_typ env t)
in ((None), (uu____6471)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators = (fun quals env t tps k datas -> (

let quals1 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___193_6520 -> (match (uu___193_6520) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| uu____6521 -> begin
false
end))))
in (

let quals2 = (fun q -> (

let uu____6529 = ((FStar_All.pipe_left Prims.op_Negation env.FStar_ToSyntax_Env.iface) || env.FStar_ToSyntax_Env.admitted_iface)
in (match (uu____6529) with
| true -> begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals1)
end
| uu____6531 -> begin
(FStar_List.append q quals1)
end)))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (

let uu____6536 = (

let uu____6537 = (

let uu____6543 = (quals2 ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in ((disc_name), ([]), (FStar_Syntax_Syntax.tun), (uu____6543)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____6537))
in {FStar_Syntax_Syntax.sigel = uu____6536; FStar_Syntax_Syntax.sigdoc = None; FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid disc_name)}))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_ToSyntax_Env.env  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let uu____6568 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____6578 -> (match (uu____6578) with
| (x, uu____6583) -> begin
(

let uu____6584 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____6584) with
| (field_name, uu____6589) -> begin
(

let only_decl = (((

let uu____6591 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____6591)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (

let uu____6592 = (

let uu____6593 = (FStar_ToSyntax_Env.current_module env)
in uu____6593.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____6592)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____6603 = (FStar_List.filter (fun uu___194_6605 -> (match (uu___194_6605) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____6606 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____6603)
end
| uu____6607 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___195_6614 -> (match (uu___195_6614) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| uu____6615 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun), (quals1))); FStar_Syntax_Syntax.sigdoc = None; FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid field_name)}
in (match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____6620 -> begin
(

let dd = (

let uu____6622 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____6622) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____6624 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lb = (

let uu____6626 = (

let uu____6629 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (uu____6629))
in {FStar_Syntax_Syntax.lbname = uu____6626; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun})
in (

let impl = (

let uu____6631 = (

let uu____6632 = (

let uu____6640 = (

let uu____6642 = (

let uu____6643 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____6643 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____6642)::[])
in ((((false), ((lb)::[]))), (uu____6640), (quals1), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____6632))
in {FStar_Syntax_Syntax.sigel = uu____6631; FStar_Syntax_Syntax.sigdoc = None; FStar_Syntax_Syntax.sigrng = p})
in (match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____6659 -> begin
(decl)::(impl)::[]
end))))
end))))))
end))
end))))
in (FStar_All.pipe_right uu____6568 FStar_List.flatten))))


let mk_data_projector_names = (fun iquals env uu____6683 -> (match (uu____6683) with
| (inductive_tps, se) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____6691, t, uu____6693, n1, quals, uu____6696) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let uu____6701 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____6701) with
| (formals, uu____6711) -> begin
(match (formals) with
| [] -> begin
[]
end
| uu____6725 -> begin
(

let filter_records = (fun uu___196_6733 -> (match (uu___196_6733) with
| FStar_Syntax_Syntax.RecordConstructor (uu____6735, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| uu____6742 -> begin
None
end))
in (

let fv_qual = (

let uu____6744 = (FStar_Util.find_map quals filter_records)
in (match (uu____6744) with
| None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| Some (q) -> begin
q
end))
in (

let iquals1 = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract iquals)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::iquals
end
| uu____6750 -> begin
iquals
end)
in (

let uu____6751 = (FStar_Util.first_N n1 formals)
in (match (uu____6751) with
| (uu____6763, rest) -> begin
(mk_indexed_projector_names iquals1 fv_qual env lid rest)
end)))))
end)
end))
end
| uu____6777 -> begin
[]
end)
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.fsdoc Prims.option  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng doc1 -> (

let dd = (

let uu____6820 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____6820) with
| true -> begin
(

let uu____6822 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (uu____6822))
end
| uu____6823 -> begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end))
in (

let lb = (

let uu____6825 = (

let uu____6828 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (uu____6828))
in (

let uu____6829 = (

let uu____6832 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars uu____6832))
in (

let uu____6835 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = uu____6825; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____6829; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____6835})))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (lids), (quals), ([]))); FStar_Syntax_Syntax.sigdoc = doc1; FStar_Syntax_Syntax.sigrng = rng})))


let rec desugar_tycon : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d quals tcs -> (

let rng = d.FStar_Parser_AST.drange
in (

let tycon_id = (fun uu___197_6869 -> (match (uu___197_6869) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(

let uu____6908 = (

let uu____6909 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____6909))
in (FStar_Parser_AST.mk_term uu____6908 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| uu____6931 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (

let uu____6934 = (

let uu____6935 = (

let uu____6939 = (binder_to_term b)
in ((out), (uu____6939), ((imp_of_aqual b))))
in FStar_Parser_AST.App (uu____6935))
in (FStar_Parser_AST.mk_term uu____6934 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun uu___198_6946 -> (match (uu___198_6946) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun uu____6975 -> (match (uu____6975) with
| (x, t, uu____6982) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (

let uu____6986 = (

let uu____6987 = (

let uu____6988 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (uu____6988))
in (FStar_Parser_AST.mk_term uu____6987 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____6986 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type_level)
in (

let uu____6991 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____7003 -> (match (uu____7003) with
| (x, uu____7009, uu____7010) -> begin
(FStar_Syntax_Util.unmangle_field_name x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (uu____6991)))))))
end
| uu____7037 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals1 _env mutuals uu___199_7059 -> (match (uu___199_7059) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let uu____7073 = (typars_of_binders _env binders)
in (match (uu____7073) with
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

let uu____7101 = (

let uu____7102 = (

let uu____7103 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (uu____7103))
in (FStar_Parser_AST.mk_term uu____7102 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____7101 binders))
in (

let qlid = (FStar_ToSyntax_Env.qualify _env id)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let k1 = (FStar_Syntax_Subst.close typars1 k)
in (

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((qlid), ([]), (typars1), (k1), (mutuals), ([]), (quals1))); FStar_Syntax_Syntax.sigdoc = d.FStar_Parser_AST.doc; FStar_Syntax_Syntax.sigrng = rng}
in (

let _env1 = (FStar_ToSyntax_Env.push_top_level_rec_binding _env id FStar_Syntax_Syntax.Delta_constant)
in (

let _env2 = (FStar_ToSyntax_Env.push_top_level_rec_binding _env' id FStar_Syntax_Syntax.Delta_constant)
in ((_env1), (_env2), (se), (tconstr))))))))))
end))
end
| uu____7114 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env1 bs -> (

let uu____7140 = (FStar_List.fold_left (fun uu____7156 uu____7157 -> (match (((uu____7156), (uu____7157))) with
| ((env2, tps), (x, imp)) -> begin
(

let uu____7205 = (FStar_ToSyntax_Env.push_bv env2 x.FStar_Syntax_Syntax.ppname)
in (match (uu____7205) with
| (env3, y) -> begin
((env3), ((((y), (imp)))::tps))
end))
end)) ((env1), ([])) bs)
in (match (uu____7140) with
| (env2, bs1) -> begin
((env2), ((FStar_List.rev bs1)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt1 = (match (kopt) with
| None -> begin
(

let uu____7266 = (tm_type_z id.FStar_Ident.idRange)
in Some (uu____7266))
end
| uu____7267 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt1)))
in (

let uu____7272 = (desugar_abstract_tc quals env [] tc)
in (match (uu____7272) with
| (uu____7279, uu____7280, se, uu____7282) -> begin
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, uu____7285, typars, k, [], [], quals1) -> begin
(

let quals2 = (

let uu____7295 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (match (uu____7295) with
| true -> begin
quals1
end
| uu____7298 -> begin
((

let uu____7300 = (FStar_Range.string_of_range se.FStar_Syntax_Syntax.sigrng)
in (

let uu____7301 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" uu____7300 uu____7301)));
(FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals1;
)
end))
in (

let t = (match (typars) with
| [] -> begin
k
end
| uu____7305 -> begin
(

let uu____7306 = (

let uu____7309 = (

let uu____7310 = (

let uu____7318 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (uu____7318)))
in FStar_Syntax_Syntax.Tm_arrow (uu____7310))
in (FStar_Syntax_Syntax.mk uu____7309))
in (uu____7306 None se.FStar_Syntax_Syntax.sigrng))
end)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t), (quals2))); FStar_Syntax_Syntax.sigdoc = None; FStar_Syntax_Syntax.sigrng = se.FStar_Syntax_Syntax.sigrng}))
end
| uu____7329 -> begin
se
end)
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se1)
in ((env1), ((se1)::[]))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let uu____7340 = (typars_of_binders env binders)
in (match (uu____7340) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
(

let uu____7360 = (FStar_Util.for_some (fun uu___200_7361 -> (match (uu___200_7361) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| uu____7362 -> begin
false
end)) quals)
in (match (uu____7360) with
| true -> begin
FStar_Syntax_Syntax.teff
end
| uu____7363 -> begin
FStar_Syntax_Syntax.tun
end))
end
| Some (k) -> begin
(desugar_term env' k)
end)
in (

let t0 = t
in (

let quals1 = (

let uu____7368 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___201_7370 -> (match (uu___201_7370) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| uu____7371 -> begin
false
end))))
in (match (uu____7368) with
| true -> begin
quals
end
| uu____7373 -> begin
(match ((t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula)) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____7375 -> begin
quals
end)
end))
in (

let se = (

let uu____7377 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Effect))
in (match (uu____7377) with
| true -> begin
(

let uu____7379 = (

let uu____7383 = (

let uu____7384 = (unparen t)
in uu____7384.FStar_Parser_AST.tm)
in (match (uu____7383) with
| FStar_Parser_AST.Construct (head1, args) -> begin
(

let uu____7396 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____7412))::args_rev -> begin
(

let uu____7419 = (

let uu____7420 = (unparen last_arg)
in uu____7420.FStar_Parser_AST.tm)
in (match (uu____7419) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____7435 -> begin
(([]), (args))
end))
end
| uu____7440 -> begin
(([]), (args))
end)
in (match (uu____7396) with
| (cattributes, args1) -> begin
(

let uu____7461 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head1), (args1)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (uu____7461)))
end))
end
| uu____7467 -> begin
((t), ([]))
end))
in (match (uu____7379) with
| (t1, cattributes) -> begin
(

let c = (desugar_comp t1.FStar_Parser_AST.range env' t1)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let c1 = (FStar_Syntax_Subst.close_comp typars1 c)
in (

let uu____7478 = (

let uu____7479 = (

let uu____7488 = (FStar_ToSyntax_Env.qualify env id)
in (

let uu____7489 = (FStar_All.pipe_right quals1 (FStar_List.filter (fun uu___202_7493 -> (match (uu___202_7493) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| uu____7494 -> begin
true
end))))
in ((uu____7488), ([]), (typars1), (c1), (uu____7489), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c1))))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (uu____7479))
in {FStar_Syntax_Syntax.sigel = uu____7478; FStar_Syntax_Syntax.sigdoc = d.FStar_Parser_AST.doc; FStar_Syntax_Syntax.sigrng = rng}))))
end))
end
| uu____7498 -> begin
(

let t1 = (desugar_typ env' t)
in (

let nm = (FStar_ToSyntax_Env.qualify env id)
in (mk_typ_abbrev nm [] typars k t1 ((nm)::[]) quals1 rng d.FStar_Parser_AST.doc)))
end))
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se)
in ((env1), ((se)::[])))))))
end))
end
| (FStar_Parser_AST.TyconRecord (uu____7503))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let uu____7516 = (tycon_record_as_variant trec)
in (match (uu____7516) with
| (t, fs) -> begin
(

let uu____7526 = (

let uu____7528 = (

let uu____7529 = (

let uu____7534 = (

let uu____7536 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.ids_of_lid uu____7536))
in ((uu____7534), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____7529))
in (uu____7528)::quals)
in (desugar_tycon env d uu____7526 ((t)::[])))
end)))
end
| (uu____7539)::uu____7540 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals1 et tc -> (

let uu____7627 = et
in (match (uu____7627) with
| (env1, tcs1) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (uu____7741) -> begin
(

let trec = tc
in (

let uu____7754 = (tycon_record_as_variant trec)
in (match (uu____7754) with
| (t, fs) -> begin
(

let uu____7785 = (

let uu____7787 = (

let uu____7788 = (

let uu____7793 = (

let uu____7795 = (FStar_ToSyntax_Env.current_module env1)
in (FStar_Ident.ids_of_lid uu____7795))
in ((uu____7793), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____7788))
in (uu____7787)::quals1)
in (collect_tcs uu____7785 ((env1), (tcs1)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let uu____7841 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____7841) with
| (env2, uu____7872, se, tconstr) -> begin
((env2), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals1))))::tcs1))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let uu____7950 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____7950) with
| (env2, uu____7981, se, tconstr) -> begin
((env2), ((FStar_Util.Inr (((se), (binders), (t), (quals1))))::tcs1))
end))
end
| uu____8045 -> begin
(failwith "Unrecognized mutual type definition")
end)
end)))
in (

let uu____8069 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (uu____8069) with
| (env1, tcs1) -> begin
(

let tcs2 = (FStar_List.rev tcs1)
in (

let tps_sigelts = (FStar_All.pipe_right tcs2 (FStar_List.collect (fun uu___204_8307 -> (match (uu___204_8307) with
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, uu____8339, uu____8340, uu____8341); FStar_Syntax_Syntax.sigdoc = uu____8342; FStar_Syntax_Syntax.sigrng = uu____8343}, binders, t, quals1) -> begin
(

let t1 = (

let uu____8377 = (typars_of_binders env1 binders)
in (match (uu____8377) with
| (env2, tpars1) -> begin
(

let uu____8394 = (push_tparams env2 tpars1)
in (match (uu____8394) with
| (env_tps, tpars2) -> begin
(

let t1 = (desugar_typ env_tps t)
in (

let tpars3 = (FStar_Syntax_Subst.close_binders tpars2)
in (FStar_Syntax_Subst.close tpars3 t1)))
end))
end))
in (

let uu____8413 = (

let uu____8420 = (mk_typ_abbrev id uvs tpars k t1 ((id)::[]) quals1 rng d.FStar_Parser_AST.doc)
in (([]), (uu____8420)))
in (uu____8413)::[]))
end
| FStar_Util.Inl ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals1, uu____8445, tags); FStar_Syntax_Syntax.sigdoc = uu____8447; FStar_Syntax_Syntax.sigrng = uu____8448}, constrs, tconstr, quals1) -> begin
(

let mk_tot = (fun t -> (

let tot1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot1), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)))
in (

let tycon = ((tname), (tpars), (k))
in (

let uu____8502 = (push_tparams env1 tpars)
in (match (uu____8502) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun uu____8537 -> (match (uu____8537) with
| (x, uu____8545) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let tot_tconstr = (mk_tot tconstr)
in (

let uu____8550 = (

let uu____8561 = (FStar_All.pipe_right constrs (FStar_List.map (fun uu____8601 -> (match (uu____8601) with
| (id, topt, uu____8618, of_notation) -> begin
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
| uu____8627 -> begin
(match (topt) with
| None -> begin
(failwith "Impossible")
end
| Some (t) -> begin
t
end)
end)
in (

let t1 = (

let uu____8630 = (close env_tps t)
in (desugar_term env_tps uu____8630))
in (

let name = (FStar_ToSyntax_Env.qualify env1 id)
in (

let quals2 = (FStar_All.pipe_right tags (FStar_List.collect (fun uu___203_8636 -> (match (uu___203_8636) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| uu____8643 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (

let uu____8649 = (

let uu____8656 = (

let uu____8657 = (

let uu____8658 = (

let uu____8668 = (

let uu____8671 = (

let uu____8674 = (FStar_All.pipe_right t1 FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total uu____8674))
in (FStar_Syntax_Util.arrow data_tpars uu____8671))
in ((name), (univs), (uu____8668), (tname), (ntps), (quals2), (mutuals1)))
in FStar_Syntax_Syntax.Sig_datacon (uu____8658))
in {FStar_Syntax_Syntax.sigel = uu____8657; FStar_Syntax_Syntax.sigdoc = d.FStar_Parser_AST.doc; FStar_Syntax_Syntax.sigrng = rng})
in ((tps), (uu____8656)))
in ((name), (uu____8649))))))))
end))))
in (FStar_All.pipe_left FStar_List.split uu____8561))
in (match (uu____8550) with
| (constrNames, constrs1) -> begin
((([]), ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs), (tpars), (k), (mutuals1), (constrNames), (tags))); FStar_Syntax_Syntax.sigdoc = d.FStar_Parser_AST.doc; FStar_Syntax_Syntax.sigrng = rng})))::constrs1
end))))
end))))
end
| uu____8759 -> begin
(failwith "impossible")
end))))
in (

let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (

let uu____8807 = (

let uu____8811 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals uu____8811 rng d.FStar_Parser_AST.doc))
in (match (uu____8807) with
| (bundle, abbrevs) -> begin
(

let env2 = (FStar_ToSyntax_Env.push_sigelt env0 bundle)
in (

let env3 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2 abbrevs)
in (

let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projector_names quals env3)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, uu____8848, tps, k, uu____8851, constrs, quals1) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals1)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::quals1
end
| uu____8866 -> begin
quals1
end)
in (mk_data_discriminators quals2 env3 tname tps k constrs))
end
| uu____8867 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env4 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env3 ops)
in ((env4), ((FStar_List.append ((bundle)::[]) (FStar_List.append abbrevs ops))))))))))
end)))))
end)))))
end
| [] -> begin
(failwith "impossible")
end)))))))))))


let desugar_binders : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (

let uu____8885 = (FStar_List.fold_left (fun uu____8892 b -> (match (uu____8892) with
| (env1, binders1) -> begin
(

let uu____8904 = (desugar_binder env1 b)
in (match (uu____8904) with
| (Some (a), k) -> begin
(

let uu____8914 = (FStar_ToSyntax_Env.push_bv env1 a)
in (match (uu____8914) with
| (env2, a1) -> begin
(

let uu____8922 = (

let uu____8924 = (FStar_Syntax_Syntax.mk_binder (

let uu___219_8925 = a1
in {FStar_Syntax_Syntax.ppname = uu___219_8925.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___219_8925.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (uu____8924)::binders1)
in ((env2), (uu____8922)))
end))
end
| uu____8927 -> begin
(Prims.raise (FStar_Errors.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) binders)
in (match (uu____8885) with
| (env1, binders1) -> begin
((env1), ((FStar_List.rev binders1)))
end)))


let rec desugar_effect : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_typ eff_decls -> (

let env0 = env
in (

let monad_env = (FStar_ToSyntax_Env.enter_monad_scope env eff_name)
in (

let uu____9005 = (desugar_binders monad_env eff_binders)
in (match (uu____9005) with
| (env1, binders) -> begin
(

let eff_t = (desugar_term env1 eff_typ)
in (

let for_free = (

let uu____9018 = (

let uu____9019 = (

let uu____9023 = (FStar_Syntax_Util.arrow_formals eff_t)
in (Prims.fst uu____9023))
in (FStar_List.length uu____9019))
in (uu____9018 = (Prims.parse_int "1")))
in (

let mandatory_members = (

let rr_members = ("repr")::("return")::("bind")::[]
in (match (for_free) with
| true -> begin
rr_members
end
| uu____9046 -> begin
(FStar_List.append rr_members (("return_wp")::("bind_wp")::("if_then_else")::("ite_wp")::("stronger")::("close_wp")::("assert_p")::("assume_p")::("null_wp")::("trivial")::[]))
end))
in (

let name_of_eff_decl = (fun decl -> (match (decl.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____9051, ((FStar_Parser_AST.TyconAbbrev (name, uu____9053, uu____9054, uu____9055), uu____9056))::[]) -> begin
(FStar_Ident.text_of_id name)
end
| uu____9073 -> begin
(failwith "Malformed effect member declaration.")
end))
in (

let uu____9074 = (FStar_List.partition (fun decl -> (

let uu____9080 = (name_of_eff_decl decl)
in (FStar_List.mem uu____9080 mandatory_members))) eff_decls)
in (match (uu____9074) with
| (mandatory_members_decls, actions) -> begin
(

let uu____9090 = (FStar_All.pipe_right mandatory_members_decls (FStar_List.fold_left (fun uu____9101 decl -> (match (uu____9101) with
| (env2, out) -> begin
(

let uu____9113 = (desugar_decl env2 decl)
in (match (uu____9113) with
| (env3, ses) -> begin
(

let uu____9121 = (

let uu____9123 = (FStar_List.hd ses)
in (uu____9123)::out)
in ((env3), (uu____9121)))
end))
end)) ((env1), ([]))))
in (match (uu____9090) with
| (env2, decls) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let actions1 = (FStar_All.pipe_right actions (FStar_List.map (fun d1 -> (match (d1.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____9139, ((FStar_Parser_AST.TyconAbbrev (name, uu____9141, uu____9142, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (uu____9143, ((def, uu____9145))::((cps_type, uu____9147))::[]); FStar_Parser_AST.range = uu____9148; FStar_Parser_AST.level = uu____9149}), uu____9150))::[]) when (not (for_free)) -> begin
(

let uu____9176 = (FStar_ToSyntax_Env.qualify env2 name)
in (

let uu____9177 = (

let uu____9178 = (desugar_term env2 def)
in (FStar_Syntax_Subst.close binders1 uu____9178))
in (

let uu____9179 = (

let uu____9180 = (desugar_typ env2 cps_type)
in (FStar_Syntax_Subst.close binders1 uu____9180))
in {FStar_Syntax_Syntax.action_name = uu____9176; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = uu____9177; FStar_Syntax_Syntax.action_typ = uu____9179})))
end
| FStar_Parser_AST.Tycon (uu____9181, ((FStar_Parser_AST.TyconAbbrev (name, uu____9183, uu____9184, defn), uu____9186))::[]) when for_free -> begin
(

let uu____9203 = (FStar_ToSyntax_Env.qualify env2 name)
in (

let uu____9204 = (

let uu____9205 = (desugar_term env2 defn)
in (FStar_Syntax_Subst.close binders1 uu____9205))
in {FStar_Syntax_Syntax.action_name = uu____9203; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = uu____9204; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
end
| uu____9206 -> begin
(Prims.raise (FStar_Errors.Error ((("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples)."), (d1.FStar_Parser_AST.drange)))))
end))))
in (

let eff_t1 = (FStar_Syntax_Subst.close binders1 eff_t)
in (

let lookup = (fun s -> (

let l = (FStar_ToSyntax_Env.qualify env2 (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange))))
in (

let uu____9216 = (

let uu____9217 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_definition env2) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders1) uu____9217))
in (([]), (uu____9216)))))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (Some (mname))) quals)
in (

let se = (match (for_free) with
| true -> begin
(

let dummy_tscheme = (

let uu____9229 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (([]), (uu____9229)))
in (

let uu____9239 = (

let uu____9240 = (

let uu____9241 = (

let uu____9242 = (lookup "repr")
in (Prims.snd uu____9242))
in (

let uu____9247 = (lookup "return")
in (

let uu____9248 = (lookup "bind")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = uu____9241; FStar_Syntax_Syntax.return_repr = uu____9247; FStar_Syntax_Syntax.bind_repr = uu____9248; FStar_Syntax_Syntax.actions = actions1})))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____9240))
in (FStar_Parser_AST.sigelt_of_decl d uu____9239)))
end
| uu____9249 -> begin
(

let rr = (FStar_Util.for_some (fun uu___205_9251 -> (match (uu___205_9251) with
| (FStar_Syntax_Syntax.Reifiable) | (FStar_Syntax_Syntax.Reflectable (_)) -> begin
true
end
| uu____9253 -> begin
false
end)) qualifiers)
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (

let uu____9259 = (

let uu____9260 = (

let uu____9261 = (lookup "return_wp")
in (

let uu____9262 = (lookup "bind_wp")
in (

let uu____9263 = (lookup "if_then_else")
in (

let uu____9264 = (lookup "ite_wp")
in (

let uu____9265 = (lookup "stronger")
in (

let uu____9266 = (lookup "close_wp")
in (

let uu____9267 = (lookup "assert_p")
in (

let uu____9268 = (lookup "assume_p")
in (

let uu____9269 = (lookup "null_wp")
in (

let uu____9270 = (lookup "trivial")
in (

let uu____9271 = (match (rr) with
| true -> begin
(

let uu____9272 = (lookup "repr")
in (FStar_All.pipe_left Prims.snd uu____9272))
end
| uu____9280 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let uu____9281 = (match (rr) with
| true -> begin
(lookup "return")
end
| uu____9282 -> begin
un_ts
end)
in (

let uu____9283 = (match (rr) with
| true -> begin
(lookup "bind")
end
| uu____9284 -> begin
un_ts
end)
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = uu____9261; FStar_Syntax_Syntax.bind_wp = uu____9262; FStar_Syntax_Syntax.if_then_else = uu____9263; FStar_Syntax_Syntax.ite_wp = uu____9264; FStar_Syntax_Syntax.stronger = uu____9265; FStar_Syntax_Syntax.close_wp = uu____9266; FStar_Syntax_Syntax.assert_p = uu____9267; FStar_Syntax_Syntax.assume_p = uu____9268; FStar_Syntax_Syntax.null_wp = uu____9269; FStar_Syntax_Syntax.trivial = uu____9270; FStar_Syntax_Syntax.repr = uu____9271; FStar_Syntax_Syntax.return_repr = uu____9281; FStar_Syntax_Syntax.bind_repr = uu____9283; FStar_Syntax_Syntax.actions = actions1})))))))))))))
in FStar_Syntax_Syntax.Sig_new_effect (uu____9260))
in (FStar_Parser_AST.sigelt_of_decl d uu____9259))))
end)
in (

let env3 = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env4 = (FStar_All.pipe_right actions1 (FStar_List.fold_left (fun env4 a -> (

let uu____9290 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env4 uu____9290))) env3))
in (

let env5 = (

let uu____9292 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____9292) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let refl_decl = (FStar_Parser_AST.sigelt_of_decl d (FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[])))))
in (FStar_ToSyntax_Env.push_sigelt env4 refl_decl)))
end
| uu____9297 -> begin
env4
end))
in ((env5), ((se)::[]))))))))))))
end))
end))))))
end)))))
and desugar_redefine_effect : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  (FStar_Ident.lident Prims.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier)  ->  FStar_Parser_AST.qualifier Prims.list  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d trans_qual1 quals eff_name eff_binders defn -> (

let env0 = env
in (

let env1 = (FStar_ToSyntax_Env.enter_monad_scope env eff_name)
in (

let uu____9315 = (desugar_binders env1 eff_binders)
in (match (uu____9315) with
| (env2, binders) -> begin
(

let uu____9326 = (

let uu____9335 = (head_and_args defn)
in (match (uu____9335) with
| (head1, args) -> begin
(

let ed = (match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_effect_defn env2) l)
end
| uu____9359 -> begin
(

let uu____9360 = (

let uu____9361 = (

let uu____9364 = (

let uu____9365 = (

let uu____9366 = (FStar_Parser_AST.term_to_string head1)
in (Prims.strcat uu____9366 " not found"))
in (Prims.strcat "Effect " uu____9365))
in ((uu____9364), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____9361))
in (Prims.raise uu____9360))
end)
in (

let uu____9367 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____9383))::args_rev -> begin
(

let uu____9390 = (

let uu____9391 = (unparen last_arg)
in uu____9391.FStar_Parser_AST.tm)
in (match (uu____9390) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____9406 -> begin
(([]), (args))
end))
end
| uu____9411 -> begin
(([]), (args))
end)
in (match (uu____9367) with
| (cattributes, args1) -> begin
(

let uu____9437 = (desugar_args env2 args1)
in (

let uu____9442 = (desugar_attributes env2 cattributes)
in ((ed), (uu____9437), (uu____9442))))
end)))
end))
in (match (uu____9326) with
| (ed, args, cattributes) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let sub1 = (fun uu____9475 -> (match (uu____9475) with
| (uu____9482, x) -> begin
(

let uu____9486 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (uu____9486) with
| (edb, x1) -> begin
((match (((FStar_List.length args) <> (FStar_List.length edb))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end
| uu____9504 -> begin
()
end);
(

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (

let uu____9506 = (

let uu____9507 = (FStar_Syntax_Subst.subst s x1)
in (FStar_Syntax_Subst.close binders1 uu____9507))
in (([]), (uu____9506))));
)
end))
end))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let ed1 = (

let uu____9511 = (

let uu____9513 = (trans_qual1 (Some (mname)))
in (FStar_List.map uu____9513 quals))
in (

let uu____9516 = (

let uu____9517 = (sub1 (([]), (ed.FStar_Syntax_Syntax.signature)))
in (Prims.snd uu____9517))
in (

let uu____9523 = (sub1 ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____9524 = (sub1 ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____9525 = (sub1 ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____9526 = (sub1 ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____9527 = (sub1 ed.FStar_Syntax_Syntax.stronger)
in (

let uu____9528 = (sub1 ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____9529 = (sub1 ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____9530 = (sub1 ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____9531 = (sub1 ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____9532 = (sub1 ed.FStar_Syntax_Syntax.trivial)
in (

let uu____9533 = (

let uu____9534 = (sub1 (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd uu____9534))
in (

let uu____9540 = (sub1 ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____9541 = (sub1 ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____9542 = (FStar_List.map (fun action -> (

let uu____9545 = (FStar_ToSyntax_Env.qualify env2 action.FStar_Syntax_Syntax.action_unqualified_name)
in (

let uu____9546 = (

let uu____9547 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd uu____9547))
in (

let uu____9553 = (

let uu____9554 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd uu____9554))
in {FStar_Syntax_Syntax.action_name = uu____9545; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = uu____9546; FStar_Syntax_Syntax.action_typ = uu____9553})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = uu____9511; FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = uu____9516; FStar_Syntax_Syntax.ret_wp = uu____9523; FStar_Syntax_Syntax.bind_wp = uu____9524; FStar_Syntax_Syntax.if_then_else = uu____9525; FStar_Syntax_Syntax.ite_wp = uu____9526; FStar_Syntax_Syntax.stronger = uu____9527; FStar_Syntax_Syntax.close_wp = uu____9528; FStar_Syntax_Syntax.assert_p = uu____9529; FStar_Syntax_Syntax.assume_p = uu____9530; FStar_Syntax_Syntax.null_wp = uu____9531; FStar_Syntax_Syntax.trivial = uu____9532; FStar_Syntax_Syntax.repr = uu____9533; FStar_Syntax_Syntax.return_repr = uu____9540; FStar_Syntax_Syntax.bind_repr = uu____9541; FStar_Syntax_Syntax.actions = uu____9542}))))))))))))))))
in (

let se = (

let for_free = (

let uu____9562 = (

let uu____9563 = (

let uu____9567 = (FStar_Syntax_Util.arrow_formals ed1.FStar_Syntax_Syntax.signature)
in (Prims.fst uu____9567))
in (FStar_List.length uu____9563))
in (uu____9562 = (Prims.parse_int "1")))
in (FStar_Parser_AST.sigelt_of_decl d (match (for_free) with
| true -> begin
FStar_Syntax_Syntax.Sig_new_effect_for_free (ed1)
end
| uu____9585 -> begin
FStar_Syntax_Syntax.Sig_new_effect (ed1)
end)))
in (

let monad_env = env2
in (

let env3 = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env4 = (FStar_All.pipe_right ed1.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun env4 a -> (

let uu____9592 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env4 uu____9592))) env3))
in (

let env5 = (

let uu____9594 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____9594) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let refl_decl = (FStar_Parser_AST.sigelt_of_decl d (FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[])))))
in (FStar_ToSyntax_Env.push_sigelt env4 refl_decl)))
end
| uu____9600 -> begin
env4
end))
in ((env5), ((se)::[])))))))))))
end))
end)))))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let trans_qual1 = (trans_qual d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(

let se = (FStar_Parser_AST.sigelt_of_decl d (FStar_Syntax_Syntax.Sig_pragma ((trans_pragma p))))
in ((match ((p = FStar_Parser_AST.LightOff)) with
| true -> begin
(FStar_Options.set_ml_ish ())
end
| uu____9617 -> begin
()
end);
((env), ((se)::[]));
))
end
| FStar_Parser_AST.Fsdoc (uu____9619) -> begin
((env), ([]))
end
| FStar_Parser_AST.TopLevelModule (id) -> begin
((env), ([]))
end
| FStar_Parser_AST.Open (lid) -> begin
(

let env1 = (FStar_ToSyntax_Env.push_namespace env lid)
in ((env1), ([])))
end
| FStar_Parser_AST.Include (lid) -> begin
(

let env1 = (FStar_ToSyntax_Env.push_include env lid)
in ((env1), ([])))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(

let uu____9631 = (FStar_ToSyntax_Env.push_module_abbrev env x l)
in ((uu____9631), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, tcs) -> begin
(

let quals = (match (is_effect) with
| true -> begin
(FStar_Parser_AST.Effect_qual)::d.FStar_Parser_AST.quals
end
| uu____9646 -> begin
d.FStar_Parser_AST.quals
end)
in (

let tcs1 = (FStar_List.map (fun uu____9652 -> (match (uu____9652) with
| (x, uu____9657) -> begin
x
end)) tcs)
in (

let uu____9660 = (FStar_List.map (trans_qual1 None) quals)
in (desugar_tycon env d uu____9660 tcs1))))
end
| FStar_Parser_AST.TopLevelLet (isrec, lets) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let attrs = d.FStar_Parser_AST.attrs
in (

let attrs1 = (FStar_List.map (desugar_term env) attrs)
in (

let expand_toplevel_pattern = ((isrec = FStar_Parser_AST.NoLetQualifier) && (match (lets) with
| ((({FStar_Parser_AST.pat = FStar_Parser_AST.PatOp (_); FStar_Parser_AST.prange = _}, _))::[]) | ((({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_); FStar_Parser_AST.prange = _}, _))::[]) | ((({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_); FStar_Parser_AST.prange = _}, _); FStar_Parser_AST.prange = _}, _))::[]) -> begin
false
end
| ((p, uu____9699))::[] -> begin
(

let uu____9704 = (is_app_pattern p)
in (not (uu____9704)))
end
| uu____9705 -> begin
false
end))
in (match ((not (expand_toplevel_pattern))) with
| true -> begin
(

let as_inner_let = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let ds_lets = (desugar_term_maybe_top true env as_inner_let)
in (

let uu____9716 = (

let uu____9717 = (FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets)
in uu____9717.FStar_Syntax_Syntax.n)
in (match (uu____9716) with
| FStar_Syntax_Syntax.Tm_let (lbs, uu____9723) -> begin
(

let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals1 = (match (quals) with
| (uu____9743)::uu____9744 -> begin
(FStar_List.map (trans_qual1 None) quals)
end
| uu____9746 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun uu___206_9750 -> (match (uu___206_9750) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (uu____9752); FStar_Syntax_Syntax.lbunivs = uu____9753; FStar_Syntax_Syntax.lbtyp = uu____9754; FStar_Syntax_Syntax.lbeff = uu____9755; FStar_Syntax_Syntax.lbdef = uu____9756} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____9763; FStar_Syntax_Syntax.lbtyp = uu____9764; FStar_Syntax_Syntax.lbeff = uu____9765; FStar_Syntax_Syntax.lbdef = uu____9766} -> begin
(FStar_ToSyntax_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals2 = (

let uu____9778 = (FStar_All.pipe_right lets (FStar_Util.for_some (fun uu____9784 -> (match (uu____9784) with
| (uu____9787, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end))))
in (match (uu____9778) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals1
end
| uu____9790 -> begin
quals1
end))
in (

let lbs1 = (

let uu____9795 = (FStar_All.pipe_right quals2 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____9795) with
| true -> begin
(

let uu____9800 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu___220_9807 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let uu___221_9808 = fv
in {FStar_Syntax_Syntax.fv_name = uu___221_9808.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = uu___221_9808.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = uu___220_9807.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___220_9807.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___220_9807.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___220_9807.FStar_Syntax_Syntax.lbdef})))))
in (((Prims.fst lbs)), (uu____9800)))
end
| uu____9814 -> begin
lbs
end))
in (

let s = (

let uu____9816 = (

let uu____9817 = (

let uu____9825 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in ((lbs1), (uu____9825), (quals2), (attrs1)))
in FStar_Syntax_Syntax.Sig_let (uu____9817))
in (FStar_Parser_AST.sigelt_of_decl d uu____9816))
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env s)
in ((env1), ((s)::[]))))))))
end
| uu____9842 -> begin
(failwith "Desugaring a let did not produce a let")
end))))
end
| uu____9845 -> begin
(

let uu____9846 = (match (lets) with
| ((pat, body))::[] -> begin
((pat), (body))
end
| uu____9857 -> begin
(failwith "expand_toplevel_pattern should only allow single definition lets")
end)
in (match (uu____9846) with
| (pat, body) -> begin
(

let fresh_toplevel_name = (FStar_Ident.gen FStar_Range.dummyRange)
in (

let fresh_pat = (

let var_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((fresh_toplevel_name), (None)))) FStar_Range.dummyRange)
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, ty) -> begin
(

let uu___222_9873 = pat1
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed (((var_pat), (ty))); FStar_Parser_AST.prange = uu___222_9873.FStar_Parser_AST.prange})
end
| uu____9874 -> begin
var_pat
end))
in (

let main_let = (desugar_decl env (

let uu___223_9878 = d
in {FStar_Parser_AST.d = FStar_Parser_AST.TopLevelLet (((isrec), ((((fresh_pat), (body)))::[]))); FStar_Parser_AST.drange = uu___223_9878.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___223_9878.FStar_Parser_AST.doc; FStar_Parser_AST.quals = (FStar_Parser_AST.Private)::d.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = uu___223_9878.FStar_Parser_AST.attrs}))
in (

let build_projection = (fun uu____9897 id -> (match (uu____9897) with
| (env1, ses) -> begin
(

let main = (

let uu____9910 = (

let uu____9911 = (FStar_Ident.lid_of_ids ((fresh_toplevel_name)::[]))
in FStar_Parser_AST.Var (uu____9911))
in (FStar_Parser_AST.mk_term uu____9910 FStar_Range.dummyRange FStar_Parser_AST.Expr))
in (

let lid = (FStar_Ident.lid_of_ids ((id)::[]))
in (

let projectee = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (lid)) FStar_Range.dummyRange FStar_Parser_AST.Expr)
in (

let body1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Match (((main), ((((pat), (None), (projectee)))::[])))) FStar_Range.dummyRange FStar_Parser_AST.Expr)
in (

let bv_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((id), (None)))) FStar_Range.dummyRange)
in (

let id_decl = (FStar_Parser_AST.mk_decl (FStar_Parser_AST.TopLevelLet (((FStar_Parser_AST.NoLetQualifier), ((((bv_pat), (body1)))::[])))) FStar_Range.dummyRange [])
in (

let uu____9939 = (desugar_decl env1 id_decl)
in (match (uu____9939) with
| (env2, ses') -> begin
((env2), ((FStar_List.append ses ses')))
end))))))))
end))
in (

let bvs = (

let uu____9950 = (gather_pattern_bound_vars pat)
in (FStar_All.pipe_right uu____9950 FStar_Util.set_elements))
in (FStar_List.fold_left build_projection main_let bvs))))))
end))
end)))))
end
| FStar_Parser_AST.Main (t) -> begin
(

let e = (desugar_term env t)
in (

let se = (FStar_Parser_AST.sigelt_of_decl d (FStar_Syntax_Syntax.Sig_main (e)))
in ((env), ((se)::[]))))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let f = (desugar_formula env t)
in (

let uu____9964 = (

let uu____9966 = (

let uu____9967 = (

let uu____9968 = (

let uu____9973 = (FStar_ToSyntax_Env.qualify env id)
in ((uu____9973), (f), ((FStar_Syntax_Syntax.Assumption)::[])))
in FStar_Syntax_Syntax.Sig_assume (uu____9968))
in (FStar_Parser_AST.sigelt_of_decl d uu____9967))
in (uu____9966)::[])
in ((env), (uu____9964))))
end
| FStar_Parser_AST.Val (id, t) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let t1 = (

let uu____9980 = (close_fun env t)
in (desugar_term env uu____9980))
in (

let quals1 = (match ((env.FStar_ToSyntax_Env.iface && env.FStar_ToSyntax_Env.admitted_iface)) with
| true -> begin
(FStar_Parser_AST.Assumption)::quals
end
| uu____9984 -> begin
quals
end)
in (

let se = (

let uu____9986 = (

let uu____9987 = (

let uu____9993 = (FStar_ToSyntax_Env.qualify env id)
in (

let uu____9994 = (FStar_List.map (trans_qual1 None) quals1)
in ((uu____9993), ([]), (t1), (uu____9994))))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____9987))
in (FStar_Parser_AST.sigelt_of_decl d uu____9986))
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se)
in ((env1), ((se)::[])))))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(

let uu____10002 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (match (uu____10002) with
| (t, uu____10010) -> begin
(

let l = (FStar_ToSyntax_Env.qualify env id)
in (

let se = (FStar_Parser_AST.sigelt_of_decl d (FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Syntax_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((FStar_Syntax_Const.exn_lid)::[])))))
in (

let se' = (FStar_Parser_AST.sigelt_of_decl d (FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((l)::[])))))
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se')
in (

let data_ops = (mk_data_projector_names [] env1 (([]), (se)))
in (

let discs = (mk_data_discriminators [] env1 FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (

let env2 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env1 (FStar_List.append discs data_ops))
in ((env2), ((FStar_List.append ((se')::discs) data_ops))))))))))
end))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(

let t = (desugar_term env term)
in (

let t1 = (

let uu____10037 = (

let uu____10041 = (FStar_Syntax_Syntax.null_binder t)
in (uu____10041)::[])
in (

let uu____10042 = (

let uu____10045 = (

let uu____10046 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (Prims.fst uu____10046))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____10045))
in (FStar_Syntax_Util.arrow uu____10037 uu____10042)))
in (

let l = (FStar_ToSyntax_Env.qualify env id)
in (

let se = (FStar_Parser_AST.sigelt_of_decl d (FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t1), (FStar_Syntax_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((FStar_Syntax_Const.exn_lid)::[])))))
in (

let se' = (FStar_Parser_AST.sigelt_of_decl d (FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((l)::[])))))
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se')
in (

let data_ops = (mk_data_projector_names [] env1 (([]), (se)))
in (

let discs = (mk_data_discriminators [] env1 FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (

let env2 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env1 (FStar_List.append discs data_ops))
in ((env2), ((FStar_List.append ((se')::discs) data_ops))))))))))))
end
| FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (desugar_redefine_effect env d trans_qual1 quals eff_name eff_binders defn))
end
| FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_typ, eff_decls)) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (desugar_effect env d quals eff_name eff_binders eff_typ eff_decls))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(

let lookup = (fun l1 -> (

let uu____10092 = (FStar_ToSyntax_Env.try_lookup_effect_name env l1)
in (match (uu____10092) with
| None -> begin
(

let uu____10094 = (

let uu____10095 = (

let uu____10098 = (

let uu____10099 = (

let uu____10100 = (FStar_Syntax_Print.lid_to_string l1)
in (Prims.strcat uu____10100 " not found"))
in (Prims.strcat "Effect name " uu____10099))
in ((uu____10098), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____10095))
in (Prims.raise uu____10094))
end
| Some (l2) -> begin
l2
end)))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let uu____10104 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(

let uu____10126 = (

let uu____10131 = (

let uu____10135 = (desugar_term env t)
in (([]), (uu____10135)))
in Some (uu____10131))
in ((uu____10126), (None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(

let uu____10153 = (

let uu____10158 = (

let uu____10162 = (desugar_term env wp)
in (([]), (uu____10162)))
in Some (uu____10158))
in (

let uu____10167 = (

let uu____10172 = (

let uu____10176 = (desugar_term env t)
in (([]), (uu____10176)))
in Some (uu____10172))
in ((uu____10153), (uu____10167))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(

let uu____10190 = (

let uu____10195 = (

let uu____10199 = (desugar_term env t)
in (([]), (uu____10199)))
in Some (uu____10195))
in ((None), (uu____10190)))
end)
in (match (uu____10104) with
| (lift_wp, lift) -> begin
(

let se = (FStar_Parser_AST.sigelt_of_decl d (FStar_Syntax_Syntax.Sig_sub_effect ({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift})))
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun uu____10250 d -> (match (uu____10250) with
| (env1, sigelts) -> begin
(

let uu____10262 = (desugar_decl env1 d)
in (match (uu____10262) with
| (env2, se) -> begin
((env2), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))


let open_prims_all : (FStar_Parser_AST.decoration Prims.list  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]


let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env1 = (match (((curmod), (m))) with
| (None, uu____10304) -> begin
env
end
| (Some ({FStar_Syntax_Syntax.name = prev_lid; FStar_Syntax_Syntax.declarations = uu____10307; FStar_Syntax_Syntax.exports = uu____10308; FStar_Syntax_Syntax.is_interface = uu____10309}), FStar_Parser_AST.Module (current_lid, uu____10311)) when ((FStar_Ident.lid_equals prev_lid current_lid) && (FStar_Options.interactive ())) -> begin
env
end
| (Some (prev_mod), uu____10316) -> begin
(FStar_ToSyntax_Env.finish_module_or_interface env prev_mod)
end)
in (

let uu____10318 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(

let uu____10338 = (FStar_ToSyntax_Env.prepare_module_or_interface true admitted env1 mname)
in ((uu____10338), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(

let uu____10348 = (FStar_ToSyntax_Env.prepare_module_or_interface false false env1 mname)
in ((uu____10348), (mname), (decls), (false)))
end)
in (match (uu____10318) with
| ((env2, pop_when_done), mname, decls, intf) -> begin
(

let uu____10366 = (desugar_decls env2 decls)
in (match (uu____10366) with
| (env3, sigelts) -> begin
(

let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in ((env3), (modul), (pop_when_done)))
end))
end))))


let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (

let m1 = (

let uu____10391 = ((FStar_Options.interactive ()) && (

let uu____10392 = (

let uu____10393 = (

let uu____10394 = (FStar_Options.file_list ())
in (FStar_List.hd uu____10394))
in (FStar_Util.get_file_extension uu____10393))
in (uu____10392 = "fsti")))
in (match (uu____10391) with
| true -> begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface (((mname), (decls), (true)))
end
| FStar_Parser_AST.Interface (mname, uu____10402, uu____10403) -> begin
(failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end
| uu____10406 -> begin
m
end))
in (

let uu____10407 = (desugar_modul_common curmod env m1)
in (match (uu____10407) with
| (x, y, pop_when_done) -> begin
((match (pop_when_done) with
| true -> begin
(

let uu____10417 = (FStar_ToSyntax_Env.pop ())
in ())
end
| uu____10418 -> begin
()
end);
((x), (y));
)
end))))


let desugar_modul : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun env m -> (

let uu____10429 = (desugar_modul_common None env m)
in (match (uu____10429) with
| (env1, modul, pop_when_done) -> begin
(

let env2 = (FStar_ToSyntax_Env.finish_module_or_interface env1 modul)
in ((

let uu____10440 = (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____10440) with
| true -> begin
(

let uu____10441 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" uu____10441))
end
| uu____10442 -> begin
()
end));
(

let uu____10443 = (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface modul.FStar_Syntax_Syntax.name env2)
end
| uu____10444 -> begin
env2
end)
in ((uu____10443), (modul)));
))
end)))


let desugar_file : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (

let uu____10454 = (FStar_List.fold_left (fun uu____10461 m -> (match (uu____10461) with
| (env1, mods) -> begin
(

let uu____10473 = (desugar_modul env1 m)
in (match (uu____10473) with
| (env2, m1) -> begin
((env2), ((m1)::mods))
end))
end)) ((env), ([])) f)
in (match (uu____10454) with
| (env1, mods) -> begin
((env1), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_ToSyntax_Env.env  ->  FStar_ToSyntax_Env.env = (fun m en -> (

let uu____10497 = (FStar_ToSyntax_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (uu____10497) with
| (en1, pop_when_done) -> begin
(

let en2 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt (

let uu___224_10503 = en1
in {FStar_ToSyntax_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_ToSyntax_Env.curmonad = uu___224_10503.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = uu___224_10503.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = uu___224_10503.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = uu___224_10503.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = uu___224_10503.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = uu___224_10503.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = uu___224_10503.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = uu___224_10503.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.iface = uu___224_10503.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = uu___224_10503.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = uu___224_10503.FStar_ToSyntax_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (

let env = (FStar_ToSyntax_Env.finish_module_or_interface en2 m)
in (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name env)
end
| uu____10505 -> begin
env
end)))
end)))




