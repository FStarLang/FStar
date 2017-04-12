
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


let no_annot_abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))


let mk_ref_read = (fun tm -> (

let tm' = (

let uu____869 = (

let uu____879 = (

let uu____880 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm uu____880))
in (

let uu____881 = (

let uu____887 = (

let uu____892 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____892)))
in (uu____887)::[])
in ((uu____879), (uu____881))))
in FStar_Syntax_Syntax.Tm_app (uu____869))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc = (fun tm -> (

let tm' = (

let uu____926 = (

let uu____936 = (

let uu____937 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm uu____937))
in (

let uu____938 = (

let uu____944 = (

let uu____949 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____949)))
in (uu____944)::[])
in ((uu____936), (uu____938))))
in FStar_Syntax_Syntax.Tm_app (uu____926))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign = (fun t1 t2 pos -> (

let tm = (

let uu____997 = (

let uu____1007 = (

let uu____1008 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1008))
in (

let uu____1009 = (

let uu____1015 = (

let uu____1020 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (uu____1020)))
in (

let uu____1023 = (

let uu____1029 = (

let uu____1034 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (uu____1034)))
in (uu____1029)::[])
in (uu____1015)::uu____1023))
in ((uu____1007), (uu____1009))))
in FStar_Syntax_Syntax.Tm_app (uu____997))
in (FStar_Syntax_Syntax.mk tm None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun uu___187_1060 -> (match (uu___187_1060) with
| ("repr") | ("post") | ("pre") | ("wp") -> begin
true
end
| uu____1061 -> begin
false
end))


let rec sum_to_universe : FStar_Syntax_Syntax.universe  ->  Prims.int  ->  FStar_Syntax_Syntax.universe = (fun u n1 -> (match ((n1 = (Prims.parse_int "0"))) with
| true -> begin
u
end
| uu____1068 -> begin
(

let uu____1069 = (sum_to_universe u (n1 - (Prims.parse_int "1")))
in FStar_Syntax_Syntax.U_succ (uu____1069))
end))


let int_to_universe : Prims.int  ->  FStar_Syntax_Syntax.universe = (fun n1 -> (sum_to_universe FStar_Syntax_Syntax.U_zero n1))


let rec desugar_maybe_non_constant_universe : FStar_Parser_AST.term  ->  (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun t -> (

let uu____1080 = (

let uu____1081 = (unparen t)
in uu____1081.FStar_Parser_AST.tm)
in (match (uu____1080) with
| FStar_Parser_AST.Wild -> begin
(

let uu____1084 = (

let uu____1085 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (uu____1085))
in FStar_Util.Inr (uu____1084))
end
| FStar_Parser_AST.Uvar (u) -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_name (u))
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____1091)) -> begin
(

let n1 = (FStar_Util.int_of_string repr)
in ((match ((n1 < (Prims.parse_int "0"))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Negative universe constant  are not supported : " repr)), (t.FStar_Parser_AST.range)))))
end
| uu____1100 -> begin
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

let uu____1134 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____1134))
end
| (FStar_Util.Inr (u11), FStar_Util.Inr (u21)) -> begin
(

let uu____1141 = (

let uu____1142 = (

let uu____1145 = (

let uu____1146 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "This universe might contain a sum of two universe variables " uu____1146))
in ((uu____1145), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____1142))
in (Prims.raise uu____1141))
end)))
end
| FStar_Parser_AST.App (uu____1149) -> begin
(

let rec aux = (fun t1 univargs -> (

let uu____1168 = (

let uu____1169 = (unparen t1)
in uu____1169.FStar_Parser_AST.tm)
in (match (uu____1168) with
| FStar_Parser_AST.App (t2, targ, uu____1174) -> begin
(

let uarg = (desugar_maybe_non_constant_universe targ)
in (aux t2 ((uarg)::univargs)))
end
| FStar_Parser_AST.Var (max_lid1) -> begin
(match ((FStar_List.existsb (fun uu___188_1186 -> (match (uu___188_1186) with
| FStar_Util.Inr (uu____1189) -> begin
true
end
| uu____1190 -> begin
false
end)) univargs)) with
| true -> begin
(

let uu____1193 = (

let uu____1194 = (FStar_List.map (fun uu___189_1198 -> (match (uu___189_1198) with
| FStar_Util.Inl (n1) -> begin
(int_to_universe n1)
end
| FStar_Util.Inr (u) -> begin
u
end)) univargs)
in FStar_Syntax_Syntax.U_max (uu____1194))
in FStar_Util.Inr (uu____1193))
end
| uu____1203 -> begin
(

let nargs = (FStar_List.map (fun uu___190_1208 -> (match (uu___190_1208) with
| FStar_Util.Inl (n1) -> begin
n1
end
| FStar_Util.Inr (uu____1212) -> begin
(failwith "impossible")
end)) univargs)
in (

let uu____1213 = (FStar_List.fold_left (fun m n1 -> (match ((m > n1)) with
| true -> begin
m
end
| uu____1216 -> begin
n1
end)) (Prims.parse_int "0") nargs)
in FStar_Util.Inl (uu____1213)))
end)
end
| uu____1217 -> begin
(

let uu____1218 = (

let uu____1219 = (

let uu____1222 = (

let uu____1223 = (

let uu____1224 = (FStar_Parser_AST.term_to_string t1)
in (Prims.strcat uu____1224 " in universe context"))
in (Prims.strcat "Unexpected term " uu____1223))
in ((uu____1222), (t1.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____1219))
in (Prims.raise uu____1218))
end)))
in (aux t []))
end
| uu____1229 -> begin
(

let uu____1230 = (

let uu____1231 = (

let uu____1234 = (

let uu____1235 = (

let uu____1236 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat uu____1236 " in universe context"))
in (Prims.strcat "Unexpected term " uu____1235))
in ((uu____1234), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____1231))
in (Prims.raise uu____1230))
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

let uu____1270 = (FStar_List.hd fields)
in (match (uu____1270) with
| (f, uu____1276) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f);
(

let record = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f)
in (

let check_field = (fun uu____1284 -> (match (uu____1284) with
| (f', uu____1288) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f');
(

let uu____1290 = (FStar_ToSyntax_Env.belongs_to_record env f' record)
in (match (uu____1290) with
| true -> begin
()
end
| uu____1291 -> begin
(

let msg = (FStar_Util.format3 "Field %s belongs to record type %s, whereas field %s does not" f.FStar_Ident.str record.FStar_ToSyntax_Env.typename.FStar_Ident.str f'.FStar_Ident.str)
in (Prims.raise (FStar_Errors.Error (((msg), (rg))))))
end));
)
end))
in ((

let uu____1294 = (FStar_List.tl fields)
in (FStar_List.iter check_field uu____1294));
(match (()) with
| () -> begin
record
end);
)));
)
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
| FStar_Syntax_Syntax.Pat_cons (uu____1454, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out uu____1476 -> (match (uu____1476) with
| (p3, uu____1482) -> begin
(

let uu____1483 = (pat_vars p3)
in (FStar_Util.set_union out uu____1483))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd1)::tl1) -> begin
(

let xs = (pat_vars hd1)
in (

let uu____1497 = (

let uu____1498 = (FStar_Util.for_all (fun p3 -> (

let ys = (pat_vars p3)
in ((FStar_Util.set_is_subset_of xs ys) && (FStar_Util.set_is_subset_of ys xs)))) tl1)
in (not (uu____1498)))
in (match (uu____1497) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Disjunctive pattern binds different variables in each case"), (p2.FStar_Syntax_Syntax.p)))))
end
| uu____1501 -> begin
xs
end)))
end))
in (pat_vars p1)))
in ((match (((is_mut), (p.FStar_Parser_AST.pat))) with
| ((false, _)) | ((true, FStar_Parser_AST.PatVar (_))) -> begin
()
end
| (true, uu____1505) -> begin
(Prims.raise (FStar_Errors.Error ((("let-mutable is for variables only"), (p.FStar_Parser_AST.prange)))))
end);
(

let push_bv_maybe_mut = (match (is_mut) with
| true -> begin
FStar_ToSyntax_Env.push_bv_mutable
end
| uu____1519 -> begin
FStar_ToSyntax_Env.push_bv
end)
in (

let resolvex = (fun l e x -> (

let uu____1533 = (FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))
in (match (uu____1533) with
| Some (y) -> begin
((l), (e), (y))
end
| uu____1541 -> begin
(

let uu____1543 = (push_bv_maybe_mut e x)
in (match (uu____1543) with
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

let uu____1592 = (

let uu____1593 = (

let uu____1594 = (

let uu____1598 = (

let uu____1599 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") op)
in (FStar_Ident.id_of_text uu____1599))
in ((uu____1598), (None)))
in FStar_Parser_AST.PatVar (uu____1594))
in {FStar_Parser_AST.pat = uu____1593; FStar_Parser_AST.prange = p1.FStar_Parser_AST.prange})
in (aux loc env1 uu____1592))
end
| FStar_Parser_AST.PatOr ([]) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p2)::ps) -> begin
(

let uu____1611 = (aux loc env1 p2)
in (match (uu____1611) with
| (loc1, env2, var, p3, uu____1630) -> begin
(

let uu____1635 = (FStar_List.fold_left (fun uu____1648 p4 -> (match (uu____1648) with
| (loc2, env3, ps1) -> begin
(

let uu____1671 = (aux loc2 env3 p4)
in (match (uu____1671) with
| (loc3, env4, uu____1687, p5, uu____1689) -> begin
((loc3), (env4), ((p5)::ps1))
end))
end)) ((loc1), (env2), ([])) ps)
in (match (uu____1635) with
| (loc2, env3, ps1) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p3)::(FStar_List.rev ps1))))
in ((loc2), (env3), (var), (pat), (false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p2, t) -> begin
(

let uu____1733 = (aux loc env1 p2)
in (match (uu____1733) with
| (loc1, env', binder, p3, imp) -> begin
(

let binder1 = (match (binder) with
| LetBinder (uu____1758) -> begin
(failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t1 = (

let uu____1764 = (close_fun env1 t)
in (desugar_term env1 uu____1764))
in ((match ((match (x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| uu____1766 -> begin
true
end)) with
| true -> begin
(

let uu____1767 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____1768 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____1769 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3_warning "Multiple ascriptions for %s in pattern, type %s was shadowed by %s" uu____1767 uu____1768 uu____1769))))
end
| uu____1770 -> begin
()
end);
LocalBinder ((((

let uu___208_1771 = x
in {FStar_Syntax_Syntax.ppname = uu___208_1771.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___208_1771.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (aq)));
))
end)
in ((loc1), (env'), (binder1), (p3), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1775 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env1), (LocalBinder (((x), (None)))), (uu____1775), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1785 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env1), (LocalBinder (((x), (None)))), (uu____1785), (false))))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq1 = (trans_aqual aq)
in (

let uu____1803 = (resolvex loc env1 x)
in (match (uu____1803) with
| (loc1, env2, xbv) -> begin
(

let uu____1817 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____1817), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l1 = (FStar_ToSyntax_Env.fail_or env1 (FStar_ToSyntax_Env.try_lookup_datacon env1) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1828 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), ([])))))
in ((loc), (env1), (LocalBinder (((x), (None)))), (uu____1828), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = uu____1846}, args) -> begin
(

let uu____1850 = (FStar_List.fold_right (fun arg uu____1868 -> (match (uu____1868) with
| (loc1, env2, args1) -> begin
(

let uu____1898 = (aux loc1 env2 arg)
in (match (uu____1898) with
| (loc2, env3, uu____1916, arg1, imp) -> begin
((loc2), (env3), ((((arg1), (imp)))::args1))
end))
end)) args ((loc), (env1), ([])))
in (match (uu____1850) with
| (loc1, env2, args1) -> begin
(

let l1 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_datacon env2) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1965 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args1)))))
in ((loc1), (env2), (LocalBinder (((x), (None)))), (uu____1965), (false)))))
end))
end
| FStar_Parser_AST.PatApp (uu____1978) -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected pattern"), (p1.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____1991 = (FStar_List.fold_right (fun pat uu____2005 -> (match (uu____2005) with
| (loc1, env2, pats1) -> begin
(

let uu____2027 = (aux loc1 env2 pat)
in (match (uu____2027) with
| (loc2, env3, uu____2043, pat1, uu____2045) -> begin
((loc2), (env3), ((pat1)::pats1))
end))
end)) pats ((loc), (env1), ([])))
in (match (uu____1991) with
| (loc1, env2, pats1) -> begin
(

let pat = (

let uu____2079 = (

let uu____2082 = (

let uu____2087 = (FStar_Range.end_range p1.FStar_Parser_AST.prange)
in (pos_r uu____2087))
in (

let uu____2088 = (

let uu____2089 = (

let uu____2097 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____2097), ([])))
in FStar_Syntax_Syntax.Pat_cons (uu____2089))
in (FStar_All.pipe_left uu____2082 uu____2088)))
in (FStar_List.fold_right (fun hd1 tl1 -> (

let r = (FStar_Range.union_ranges hd1.FStar_Syntax_Syntax.p tl1.FStar_Syntax_Syntax.p)
in (

let uu____2120 = (

let uu____2121 = (

let uu____2129 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____2129), ((((hd1), (false)))::(((tl1), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (uu____2121))
in (FStar_All.pipe_left (pos_r r) uu____2120)))) pats1 uu____2079))
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc1), (env2), (LocalBinder (((x), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep1) -> begin
(

let uu____2161 = (FStar_List.fold_left (fun uu____2178 p2 -> (match (uu____2178) with
| (loc1, env2, pats) -> begin
(

let uu____2209 = (aux loc1 env2 p2)
in (match (uu____2209) with
| (loc2, env3, uu____2227, pat, uu____2229) -> begin
((loc2), (env3), ((((pat), (false)))::pats))
end))
end)) ((loc), (env1), ([])) args)
in (match (uu____2161) with
| (loc1, env2, args1) -> begin
(

let args2 = (FStar_List.rev args1)
in (

let l = (match (dep1) with
| true -> begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end
| uu____2292 -> begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end)
in (

let uu____2300 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_lid env2) l)
in (match (uu____2300) with
| (constr, uu____2313) -> begin
(

let l1 = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____2316 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____2318 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args2)))))
in ((loc1), (env2), (LocalBinder (((x), (None)))), (uu____2318), (false)))))
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

let fields1 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____2359 -> (match (uu____2359) with
| (f, p2) -> begin
((f.FStar_Ident.ident), (p2))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____2374 -> (match (uu____2374) with
| (f, uu____2378) -> begin
(

let uu____2379 = (FStar_All.pipe_right fields1 (FStar_List.tryFind (fun uu____2391 -> (match (uu____2391) with
| (g, uu____2395) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.idText)
end))))
in (match (uu____2379) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p1.FStar_Parser_AST.prange)
end
| Some (uu____2398, p2) -> begin
p2
end))
end))))
in (

let app = (

let uu____2403 = (

let uu____2404 = (

let uu____2408 = (

let uu____2409 = (

let uu____2410 = (FStar_Ident.lid_of_ids (FStar_List.append record.FStar_ToSyntax_Env.typename.FStar_Ident.ns ((record.FStar_ToSyntax_Env.constrname)::[])))
in FStar_Parser_AST.PatName (uu____2410))
in (FStar_Parser_AST.mk_pattern uu____2409 p1.FStar_Parser_AST.prange))
in ((uu____2408), (args)))
in FStar_Parser_AST.PatApp (uu____2404))
in (FStar_Parser_AST.mk_pattern uu____2403 p1.FStar_Parser_AST.prange))
in (

let uu____2412 = (aux loc env1 app)
in (match (uu____2412) with
| (env2, e, b, p2, uu____2431) -> begin
(

let p3 = (match (p2.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args1) -> begin
(

let uu____2453 = (

let uu____2454 = (

let uu____2462 = (

let uu___209_2463 = fv
in (

let uu____2464 = (

let uu____2466 = (

let uu____2467 = (

let uu____2471 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_ToSyntax_Env.typename), (uu____2471)))
in FStar_Syntax_Syntax.Record_ctor (uu____2467))
in Some (uu____2466))
in {FStar_Syntax_Syntax.fv_name = uu___209_2463.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = uu___209_2463.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu____2464}))
in ((uu____2462), (args1)))
in FStar_Syntax_Syntax.Pat_cons (uu____2454))
in (FStar_All.pipe_left pos uu____2453))
end
| uu____2490 -> begin
p2
end)
in ((env2), (e), (b), (p3), (false)))
end))))))
end))))
in (

let uu____2493 = (aux [] env p)
in (match (uu____2493) with
| (uu____2504, env1, b, p1, uu____2508) -> begin
((

let uu____2514 = (check_linear_pattern_variables p1)
in (FStar_All.pipe_left Prims.ignore uu____2514));
((env1), (b), (p1));
)
end)))));
)))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p is_mut -> (

let mklet = (fun x -> (

let uu____2533 = (

let uu____2534 = (

let uu____2537 = (FStar_ToSyntax_Env.qualify env x)
in ((uu____2537), (FStar_Syntax_Syntax.tun)))
in LetBinder (uu____2534))
in ((env), (uu____2533), (None))))
in (match (top) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(

let uu____2548 = (

let uu____2549 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") x)
in (FStar_Ident.id_of_text uu____2549))
in (mklet uu____2548))
end
| FStar_Parser_AST.PatVar (x, uu____2551) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2555); FStar_Parser_AST.prange = uu____2556}, t) -> begin
(

let uu____2560 = (

let uu____2561 = (

let uu____2564 = (FStar_ToSyntax_Env.qualify env x)
in (

let uu____2565 = (desugar_term env t)
in ((uu____2564), (uu____2565))))
in LetBinder (uu____2561))
in ((env), (uu____2560), (None)))
end
| uu____2567 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end
| uu____2572 -> begin
(

let uu____2573 = (desugar_data_pat env p is_mut)
in (match (uu____2573) with
| (env1, binder, p1) -> begin
(

let p2 = (match (p1.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| uu____2589 -> begin
Some (p1)
end)
in ((env1), (binder), (p2)))
end))
end)))
and desugar_binding_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun uu____2593 env pat -> (

let uu____2596 = (desugar_data_pat env pat false)
in (match (uu____2596) with
| (env1, uu____2603, pat1) -> begin
((env1), (pat1))
end)))
and desugar_match_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env1 = (

let uu___210_2610 = env
in {FStar_ToSyntax_Env.curmodule = uu___210_2610.FStar_ToSyntax_Env.curmodule; FStar_ToSyntax_Env.curmonad = uu___210_2610.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = uu___210_2610.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = uu___210_2610.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = uu___210_2610.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = uu___210_2610.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = uu___210_2610.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = uu___210_2610.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = uu___210_2610.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.iface = uu___210_2610.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = uu___210_2610.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = false; FStar_ToSyntax_Env.docs = uu___210_2610.FStar_ToSyntax_Env.docs})
in (desugar_term_maybe_top false env1 e)))
and desugar_typ : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env1 = (

let uu___211_2614 = env
in {FStar_ToSyntax_Env.curmodule = uu___211_2614.FStar_ToSyntax_Env.curmodule; FStar_ToSyntax_Env.curmonad = uu___211_2614.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = uu___211_2614.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = uu___211_2614.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = uu___211_2614.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = uu___211_2614.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = uu___211_2614.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = uu___211_2614.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = uu___211_2614.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.iface = uu___211_2614.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = uu___211_2614.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = true; FStar_ToSyntax_Env.docs = uu___211_2614.FStar_ToSyntax_Env.docs})
in (desugar_term_maybe_top false env1 e)))
and desugar_machine_integer : FStar_ToSyntax_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env repr uu____2617 range -> (match (uu____2617) with
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

let uu____2628 = (FStar_ToSyntax_Env.try_lookup_lid env lid1)
in (match (uu____2628) with
| Some (lid2) -> begin
(Prims.fst lid2)
end
| None -> begin
(

let uu____2639 = (FStar_Util.format1 "%s not in scope\n" (FStar_Ident.text_of_lid lid1))
in (failwith uu____2639))
end))
in (

let repr1 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (None)))))) None range)
in (

let uu____2656 = (

let uu____2659 = (

let uu____2660 = (

let uu____2670 = (

let uu____2676 = (

let uu____2681 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr1), (uu____2681)))
in (uu____2676)::[])
in ((lid2), (uu____2670)))
in FStar_Syntax_Syntax.Tm_app (uu____2660))
in (FStar_Syntax_Syntax.mk uu____2659))
in (uu____2656 None range))))))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env_t  ->  Prims.bool  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk1 setpos env resolve l -> (

let uu____2716 = (FStar_ToSyntax_Env.fail_or env ((match (resolve) with
| true -> begin
FStar_ToSyntax_Env.try_lookup_lid
end
| uu____2728 -> begin
FStar_ToSyntax_Env.try_lookup_lid_no_resolve
end) env) l)
in (match (uu____2716) with
| (tm, mut) -> begin
(

let tm1 = (setpos tm)
in (match (mut) with
| true -> begin
(

let uu____2734 = (

let uu____2735 = (

let uu____2740 = (mk_ref_read tm1)
in ((uu____2740), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (uu____2735))
in (FStar_All.pipe_left mk1 uu____2734))
end
| uu____2745 -> begin
tm1
end))
end)))
and desugar_attributes : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (

let uu____2754 = (

let uu____2755 = (unparen t)
in uu____2755.FStar_Parser_AST.tm)
in (match (uu____2754) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = uu____2756; FStar_Ident.ident = uu____2757; FStar_Ident.nsstr = uu____2758; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| uu____2760 -> begin
(

let uu____2761 = (

let uu____2762 = (

let uu____2765 = (

let uu____2766 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " uu____2766))
in ((uu____2765), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____2762))
in (Prims.raise uu____2761))
end)))
in (FStar_List.map desugar_attribute cattributes)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk1 = (fun e -> ((FStar_Syntax_Syntax.mk e) None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let uu___212_2794 = e
in {FStar_Syntax_Syntax.n = uu___212_2794.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___212_2794.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___212_2794.FStar_Syntax_Syntax.vars}))
in (

let uu____2801 = (

let uu____2802 = (unparen top)
in uu____2802.FStar_Parser_AST.tm)
in (match (uu____2801) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (uu____2803) -> begin
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
| FStar_Parser_AST.Op ("*", (uu____2832)::(uu____2833)::[]) when (

let uu____2835 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right uu____2835 FStar_Option.isNone)) -> begin
(

let rec flatten1 = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(

let uu____2847 = (flatten1 t1)
in (FStar_List.append uu____2847 ((t2)::[])))
end
| uu____2849 -> begin
(t)::[]
end))
in (

let targs = (

let uu____2852 = (

let uu____2854 = (unparen top)
in (flatten1 uu____2854))
in (FStar_All.pipe_right uu____2852 (FStar_List.map (fun t -> (

let uu____2858 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg uu____2858))))))
in (

let uu____2859 = (

let uu____2862 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) uu____2862))
in (match (uu____2859) with
| (tup, uu____2869) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____2872 = (

let uu____2875 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) a)
in (Prims.fst uu____2875))
in (FStar_All.pipe_left setpos uu____2872))
end
| FStar_Parser_AST.Uvar (u) -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected universe variable " (Prims.strcat (FStar_Ident.text_of_id u) " in non-universe context"))), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(

let uu____2889 = (op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)
in (match (uu____2889) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected or unbound operator: " s)), (top.FStar_Parser_AST.range)))))
end
| Some (op) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let args1 = (FStar_All.pipe_right args (FStar_List.map (fun t -> (

let uu____2911 = (desugar_term env t)
in ((uu____2911), (None))))))
in (mk1 (FStar_Syntax_Syntax.Tm_app (((op), (args1))))))
end
| uu____2917 -> begin
op
end)
end))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2918; FStar_Ident.ident = uu____2919; FStar_Ident.nsstr = uu____2920; FStar_Ident.str = "Type0"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2922; FStar_Ident.ident = uu____2923; FStar_Ident.nsstr = uu____2924; FStar_Ident.str = "Type"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = uu____2926; FStar_Ident.ident = uu____2927; FStar_Ident.nsstr = uu____2928; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(

let uu____2938 = (

let uu____2939 = (desugar_universe t)
in FStar_Syntax_Syntax.Tm_type (uu____2939))
in (mk1 uu____2938))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2940; FStar_Ident.ident = uu____2941; FStar_Ident.nsstr = uu____2942; FStar_Ident.str = "Effect"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2944; FStar_Ident.ident = uu____2945; FStar_Ident.nsstr = uu____2946; FStar_Ident.str = "True"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2948; FStar_Ident.ident = uu____2949; FStar_Ident.nsstr = uu____2950; FStar_Ident.str = "False"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = uu____2954}) when ((is_special_effect_combinator txt) && (FStar_ToSyntax_Env.is_effect_name env eff_name)) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name);
(

let uu____2956 = (FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name)
in (match (uu____2956) with
| Some (ed) -> begin
(

let uu____2959 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" txt))) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.fvar uu____2959 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
end
| None -> begin
(

let uu____2960 = (FStar_Util.format2 "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)" (FStar_Ident.text_of_lid eff_name) txt)
in (failwith uu____2960))
end));
)
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t21 = (desugar_term env t2)
in (

let uu____2964 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) ident)
in (match (uu____2964) with
| (t1, mut) -> begin
((match ((not (mut))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
end
| uu____2972 -> begin
()
end);
(mk_ref_assign t1 t21 top.FStar_Parser_AST.range);
)
end)))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l);
(desugar_name mk1 setpos env true l);
)
end
| FStar_Parser_AST.Projector (l, i) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l);
(

let name = (

let uu____2982 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____2982) with
| Some (uu____2987) -> begin
Some (((true), (l)))
end
| None -> begin
(

let uu____2990 = (FStar_ToSyntax_Env.try_lookup_root_effect_name env l)
in (match (uu____2990) with
| Some (new_name) -> begin
Some (((false), (new_name)))
end
| uu____2998 -> begin
None
end))
end))
in (match (name) with
| Some (resolve, new_name) -> begin
(

let uu____3006 = (FStar_Syntax_Util.mk_field_projector_name_from_ident new_name i)
in (desugar_name mk1 setpos env resolve uu____3006))
end
| uu____3007 -> begin
(

let uu____3011 = (

let uu____3012 = (

let uu____3015 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((uu____3015), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____3012))
in (Prims.raise uu____3011))
end));
)
end
| FStar_Parser_AST.Discrim (lid) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid);
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
end));
)
end
| FStar_Parser_AST.Construct (l, args) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l);
(

let uu____3037 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____3037) with
| Some (head1) -> begin
(

let uu____3040 = (

let uu____3045 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (head1)))
in ((uu____3045), (true)))
in (match (uu____3040) with
| (head2, is_data) -> begin
(match (args) with
| [] -> begin
head2
end
| uu____3058 -> begin
(

let uu____3062 = (FStar_Util.take (fun uu____3073 -> (match (uu____3073) with
| (uu____3076, imp) -> begin
(imp = FStar_Parser_AST.UnivApp)
end)) args)
in (match (uu____3062) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun x -> (desugar_universe (Prims.fst x))) universes)
in (

let args2 = (FStar_List.map (fun uu____3109 -> (match (uu____3109) with
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
| uu____3124 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_uinst (((head2), (universes1)))))
end)
in (

let app = (mk1 (FStar_Syntax_Syntax.Tm_app (((head3), (args2)))))
in (match (is_data) with
| true -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((app), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| uu____3139 -> begin
app
end)))))
end))
end)
end))
end
| None -> begin
(

let error_msg = (

let uu____3141 = (FStar_ToSyntax_Env.try_lookup_effect_name env l)
in (match (uu____3141) with
| None -> begin
(Prims.strcat "Constructor " (Prims.strcat l.FStar_Ident.str " not found"))
end
| Some (uu____3143) -> begin
(Prims.strcat "Effect " (Prims.strcat l.FStar_Ident.str " used at an unexpected position"))
end))
in (Prims.raise (FStar_Errors.Error (((error_msg), (top.FStar_Parser_AST.range))))))
end));
)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let uu____3148 = (FStar_List.fold_left (fun uu____3165 b -> (match (uu____3165) with
| (env1, tparams, typs) -> begin
(

let uu____3196 = (desugar_binder env1 b)
in (match (uu____3196) with
| (xopt, t1) -> begin
(

let uu____3212 = (match (xopt) with
| None -> begin
(

let uu____3217 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env1), (uu____3217)))
end
| Some (x) -> begin
(FStar_ToSyntax_Env.push_bv env1 x)
end)
in (match (uu____3212) with
| (env2, x) -> begin
(

let uu____3229 = (

let uu____3231 = (

let uu____3233 = (

let uu____3234 = (no_annot_abs tparams t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3234))
in (uu____3233)::[])
in (FStar_List.append typs uu____3231))
in ((env2), ((FStar_List.append tparams (((((

let uu___213_3247 = x
in {FStar_Syntax_Syntax.ppname = uu___213_3247.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___213_3247.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (None)))::[]))), (uu____3229)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level None))::[])))
in (match (uu____3148) with
| (env1, uu____3260, targs) -> begin
(

let uu____3272 = (

let uu____3275 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env1 (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3275))
in (match (uu____3272) with
| (tup, uu____3282) -> begin
(FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let uu____3290 = (uncurry binders t)
in (match (uu____3290) with
| (bs, t1) -> begin
(

let rec aux = (fun env1 bs1 uu___191_3313 -> (match (uu___191_3313) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range env1 t1)
in (

let uu____3323 = (FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod)
in (FStar_All.pipe_left setpos uu____3323)))
end
| (hd1)::tl1 -> begin
(

let bb = (desugar_binder env1 hd1)
in (

let uu____3339 = (as_binder env1 hd1.FStar_Parser_AST.aqual bb)
in (match (uu____3339) with
| (b, env2) -> begin
(aux env2 ((b)::bs1) tl1)
end)))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(

let uu____3350 = (desugar_binder env b)
in (match (uu____3350) with
| (None, uu____3354) -> begin
(failwith "Missing binder in refinement")
end
| b1 -> begin
(

let uu____3360 = (as_binder env None b1)
in (match (uu____3360) with
| ((x, uu____3364), env1) -> begin
(

let f1 = (desugar_formula env1 f)
in (

let uu____3369 = (FStar_Syntax_Util.refine x f1)
in (FStar_All.pipe_left setpos uu____3369)))
end))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders1 = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let uu____3384 = (FStar_List.fold_left (fun uu____3391 pat -> (match (uu____3391) with
| (env1, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (uu____3406, t) -> begin
(

let uu____3408 = (

let uu____3410 = (free_type_vars env1 t)
in (FStar_List.append uu____3410 ftvs))
in ((env1), (uu____3408)))
end
| uu____3413 -> begin
((env1), (ftvs))
end)
end)) ((env), ([])) binders1)
in (match (uu____3384) with
| (uu____3416, ftv) -> begin
(

let ftv1 = (sort_ftv ftv)
in (

let binders2 = (

let uu____3424 = (FStar_All.pipe_right ftv1 (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append uu____3424 binders1))
in (

let rec aux = (fun env1 bs sc_pat_opt uu___192_3453 -> (match (uu___192_3453) with
| [] -> begin
(

let body1 = (desugar_term env1 body)
in (

let body2 = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(

let body2 = (

let uu____3482 = (

let uu____3483 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right uu____3483 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close uu____3482 body1))
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (None), (body2)))::[]))))) None body2.FStar_Syntax_Syntax.pos))
end
| None -> begin
body1
end)
in (

let uu____3525 = (no_annot_abs (FStar_List.rev bs) body2)
in (setpos uu____3525))))
end
| (p)::rest -> begin
(

let uu____3533 = (desugar_binding_pat env1 p)
in (match (uu____3533) with
| (env2, b, pat) -> begin
(

let uu____3545 = (match (b) with
| LetBinder (uu____3564) -> begin
(failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt1 = (match (((pat), (sc_pat_opt))) with
| (None, uu____3595) -> begin
sc_pat_opt
end
| (Some (p1), None) -> begin
(

let uu____3618 = (

let uu____3621 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____3621), (p1)))
in Some (uu____3618))
end
| (Some (p1), Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (uu____3646), uu____3647) -> begin
(

let tup2 = (

let uu____3649 = (FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____3649 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____3653 = (

let uu____3656 = (

let uu____3657 = (

let uu____3667 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (

let uu____3670 = (

let uu____3672 = (FStar_Syntax_Syntax.as_arg sc)
in (

let uu____3673 = (

let uu____3675 = (

let uu____3676 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3676))
in (uu____3675)::[])
in (uu____3672)::uu____3673))
in ((uu____3667), (uu____3670))))
in FStar_Syntax_Syntax.Tm_app (uu____3657))
in (FStar_Syntax_Syntax.mk uu____3656))
in (uu____3653 None top.FStar_Parser_AST.range))
in (

let p2 = (

let uu____3691 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p1), (false)))::[])))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n uu____3691))
in Some (((sc1), (p2))))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____3711, args), FStar_Syntax_Syntax.Pat_cons (uu____3713, pats)) -> begin
(

let tupn = (

let uu____3740 = (FStar_Syntax_Util.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____3740 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____3750 = (

let uu____3751 = (

let uu____3761 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (

let uu____3764 = (

let uu____3770 = (

let uu____3776 = (

let uu____3777 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3777))
in (uu____3776)::[])
in (FStar_List.append args uu____3770))
in ((uu____3761), (uu____3764))))
in FStar_Syntax_Syntax.Tm_app (uu____3751))
in (mk1 uu____3750))
in (

let p2 = (

let uu____3792 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p1), (false)))::[])))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n uu____3792))
in Some (((sc1), (p2))))))
end
| uu____3816 -> begin
(failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt1)))
end)
in (match (uu____3545) with
| (b1, sc_pat_opt1) -> begin
(aux env2 ((b1)::bs) sc_pat_opt1 rest)
end))
end))
end))
in (aux env [] None binders2))))
end)))
end
| FStar_Parser_AST.App (uu____3857, uu____3858, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (

let uu____3870 = (

let uu____3871 = (unparen e)
in uu____3871.FStar_Parser_AST.tm)
in (match (uu____3870) with
| FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e1))
end
| uu____3877 -> begin
(

let head1 = (desugar_term env e)
in (mk1 (FStar_Syntax_Syntax.Tm_uinst (((head1), (universes))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.App (uu____3880) -> begin
(

let rec aux = (fun args e -> (

let uu____3901 = (

let uu____3902 = (unparen e)
in uu____3902.FStar_Parser_AST.tm)
in (match (uu____3901) with
| FStar_Parser_AST.App (e1, t, imp) when (imp <> FStar_Parser_AST.UnivApp) -> begin
(

let arg = (

let uu____3912 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) uu____3912))
in (aux ((arg)::args) e1))
end
| uu____3919 -> begin
(

let head1 = (desugar_term env e)
in (mk1 (FStar_Syntax_Syntax.Tm_app (((head1), (args))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let uu____3930 = (

let uu____3931 = (

let uu____3936 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((uu____3936), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))
in FStar_Syntax_Syntax.Tm_meta (uu____3931))
in (mk1 uu____3930))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let env1 = (FStar_ToSyntax_Env.push_namespace env lid)
in ((match (env1.FStar_ToSyntax_Env.expect_typ) with
| true -> begin
desugar_typ
end
| uu____3951 -> begin
desugar_term
end) env1 e))
end
| FStar_Parser_AST.Let (qual1, ((pat, _snd))::_tl, body) -> begin
(

let is_rec = (qual1 = FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun uu____3971 -> (

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun uu____4013 -> (match (uu____4013) with
| (p, def) -> begin
(

let uu____4027 = (is_app_pattern p)
in (match (uu____4027) with
| true -> begin
(

let uu____4037 = (destruct_app_pattern env top_level p)
in ((uu____4037), (def)))
end
| uu____4052 -> begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p1, def1) -> begin
(

let uu____4066 = (destruct_app_pattern env top_level p1)
in ((uu____4066), (def1)))
end
| uu____4081 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____4095); FStar_Parser_AST.prange = uu____4096}, t) -> begin
(match (top_level) with
| true -> begin
(

let uu____4109 = (

let uu____4117 = (

let uu____4120 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____4120))
in ((uu____4117), ([]), (Some (t))))
in ((uu____4109), (def)))
end
| uu____4132 -> begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end)
end
| FStar_Parser_AST.PatVar (id, uu____4145) -> begin
(match (top_level) with
| true -> begin
(

let uu____4157 = (

let uu____4165 = (

let uu____4168 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____4168))
in ((uu____4165), ([]), (None)))
in ((uu____4157), (def)))
end
| uu____4180 -> begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end)
end
| uu____4192 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end))
end))))
in (

let uu____4202 = (FStar_List.fold_left (fun uu____4226 uu____4227 -> (match (((uu____4226), (uu____4227))) with
| ((env1, fnames, rec_bindings), ((f, uu____4271, uu____4272), uu____4273)) -> begin
(

let uu____4313 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let uu____4327 = (FStar_ToSyntax_Env.push_bv env1 x)
in (match (uu____4327) with
| (env2, xx) -> begin
(

let uu____4338 = (

let uu____4340 = (FStar_Syntax_Syntax.mk_binder xx)
in (uu____4340)::rec_bindings)
in ((env2), (FStar_Util.Inl (xx)), (uu____4338)))
end))
end
| FStar_Util.Inr (l) -> begin
(

let uu____4345 = (FStar_ToSyntax_Env.push_top_level_rec_binding env1 l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((uu____4345), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (uu____4313) with
| (env2, lbname, rec_bindings1) -> begin
((env2), ((lbname)::fnames), (rec_bindings1))
end))
end)) ((env), ([]), ([])) funs)
in (match (uu____4202) with
| (env', fnames, rec_bindings) -> begin
(

let fnames1 = (FStar_List.rev fnames)
in (

let rec_bindings1 = (FStar_List.rev rec_bindings)
in (

let desugar_one_def = (fun env1 lbname uu____4418 -> (match (uu____4418) with
| ((uu____4430, args, result_t), def) -> begin
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

let uu____4456 = (is_comp_type env1 t)
in (match (uu____4456) with
| true -> begin
((

let uu____4458 = (FStar_All.pipe_right args1 (FStar_List.tryFind (fun x -> (

let uu____4463 = (is_var_pattern x)
in (not (uu____4463))))))
in (match (uu____4458) with
| None -> begin
()
end
| Some (p) -> begin
(Prims.raise (FStar_Errors.Error ((("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable"), (p.FStar_Parser_AST.prange)))))
end));
t;
)
end
| uu____4465 -> begin
(

let uu____4466 = (((FStar_Options.ml_ish ()) && (

let uu____4467 = (FStar_ToSyntax_Env.try_lookup_effect_name env1 FStar_Syntax_Const.effect_ML_lid)
in (FStar_Option.isSome uu____4467))) && ((not (is_rec)) || ((FStar_List.length args1) <> (Prims.parse_int "0"))))
in (match (uu____4466) with
| true -> begin
(FStar_Parser_AST.ml_comp t)
end
| uu____4471 -> begin
(FStar_Parser_AST.tot_comp t)
end))
end))
in (

let uu____4472 = (FStar_Range.union_ranges t1.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t1), (None)))) uu____4472 FStar_Parser_AST.Expr)))
end)
in (

let def2 = (match (args1) with
| [] -> begin
def1
end
| uu____4475 -> begin
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

let uu____4485 = (

let uu____4486 = (FStar_Syntax_Util.incr_delta_qualifier body1)
in (FStar_Syntax_Syntax.lid_as_fv l uu____4486 None))
in FStar_Util.Inr (uu____4485))
end)
in (

let body2 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.close rec_bindings1 body1)
end
| uu____4488 -> begin
body1
end)
in (mk_lb ((lbname1), (FStar_Syntax_Syntax.tun), (body2)))))))))
end))
in (

let lbs = (FStar_List.map2 (desugar_one_def (match (is_rec) with
| true -> begin
env'
end
| uu____4504 -> begin
env
end)) fnames1 funs)
in (

let body1 = (desugar_term env' body)
in (

let uu____4506 = (

let uu____4507 = (

let uu____4515 = (FStar_Syntax_Subst.close rec_bindings1 body1)
in ((((is_rec), (lbs))), (uu____4515)))
in FStar_Syntax_Syntax.Tm_let (uu____4507))
in (FStar_All.pipe_left mk1 uu____4506)))))))
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
| uu____4541 -> begin
t11
end)
in (

let uu____4542 = (desugar_binding_pat_maybe_top top_level env pat1 is_mutable)
in (match (uu____4542) with
| (env1, binder, pat2) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body1 = (desugar_term env1 t2)
in (

let fv = (

let uu____4563 = (FStar_Syntax_Util.incr_delta_qualifier t12)
in (FStar_Syntax_Syntax.lid_as_fv l uu____4563 None))
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t12})::[]))), (body1)))))))
end
| LocalBinder (x, uu____4571) -> begin
(

let body1 = (desugar_term env1 t2)
in (

let body2 = (match (pat2) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body1
end
| Some (pat3) -> begin
(

let uu____4580 = (

let uu____4583 = (

let uu____4584 = (

let uu____4600 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____4601 = (

let uu____4603 = (FStar_Syntax_Util.branch ((pat3), (None), (body1)))
in (uu____4603)::[])
in ((uu____4600), (uu____4601))))
in FStar_Syntax_Syntax.Tm_match (uu____4584))
in (FStar_Syntax_Syntax.mk uu____4583))
in (uu____4580 None body1.FStar_Syntax_Syntax.pos))
end)
in (

let uu____4618 = (

let uu____4619 = (

let uu____4627 = (

let uu____4628 = (

let uu____4629 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4629)::[])
in (FStar_Syntax_Subst.close uu____4628 body2))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t12))))::[]))), (uu____4627)))
in FStar_Syntax_Syntax.Tm_let (uu____4619))
in (FStar_All.pipe_left mk1 uu____4618))))
end)
in (match (is_mutable) with
| true -> begin
(FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc))))))
end
| uu____4648 -> begin
tm
end))
end))))))
in (

let uu____4649 = (is_rec || (is_app_pattern pat))
in (match (uu____4649) with
| true -> begin
(ds_let_rec_or_app ())
end
| uu____4650 -> begin
(ds_non_rec pat _snd body)
end)))))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let uu____4655 = (

let uu____4656 = (

let uu____4672 = (desugar_term env t1)
in (

let uu____4673 = (

let uu____4683 = (

let uu____4692 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (

let uu____4695 = (desugar_term env t2)
in ((uu____4692), (None), (uu____4695))))
in (

let uu____4703 = (

let uu____4713 = (

let uu____4722 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (

let uu____4725 = (desugar_term env t3)
in ((uu____4722), (None), (uu____4725))))
in (uu____4713)::[])
in (uu____4683)::uu____4703))
in ((uu____4672), (uu____4673))))
in FStar_Syntax_Syntax.Tm_match (uu____4656))
in (mk1 uu____4655)))
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

let desugar_branch = (fun uu____4811 -> (match (uu____4811) with
| (pat, wopt, b) -> begin
(

let uu____4821 = (desugar_match_pat env pat)
in (match (uu____4821) with
| (env1, pat1) -> begin
(

let wopt1 = (match (wopt) with
| None -> begin
None
end
| Some (e1) -> begin
(

let uu____4830 = (desugar_term env1 e1)
in Some (uu____4830))
end)
in (

let b1 = (desugar_term env1 b)
in (FStar_Syntax_Util.branch ((pat1), (wopt1), (b1)))))
end))
end))
in (

let uu____4833 = (

let uu____4834 = (

let uu____4850 = (desugar_term env e)
in (

let uu____4851 = (FStar_List.map desugar_branch branches)
in ((uu____4850), (uu____4851))))
in FStar_Syntax_Syntax.Tm_match (uu____4834))
in (FStar_All.pipe_left mk1 uu____4833)))
end
| FStar_Parser_AST.Ascribed (e, t, tac_opt) -> begin
(

let annot = (

let uu____4870 = (is_comp_type env t)
in (match (uu____4870) with
| true -> begin
(

let uu____4875 = (desugar_comp t.FStar_Parser_AST.range env t)
in FStar_Util.Inr (uu____4875))
end
| uu____4880 -> begin
(

let uu____4881 = (desugar_term env t)
in FStar_Util.Inl (uu____4881))
end))
in (

let tac_opt1 = (FStar_Util.map_opt tac_opt (desugar_term env))
in (

let uu____4886 = (

let uu____4887 = (

let uu____4905 = (desugar_term env e)
in ((uu____4905), (((annot), (tac_opt1))), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____4887))
in (FStar_All.pipe_left mk1 uu____4886))))
end
| FStar_Parser_AST.Record (uu____4921, []) -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let uu____4942 = (FStar_List.hd fields)
in (match (uu____4942) with
| (f, uu____4949) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun uu____4973 -> (match (uu____4973) with
| (g, uu____4977) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| Some (uu____4981, e) -> begin
((fn), (e))
end
| None -> begin
(match (xopt) with
| None -> begin
(

let uu____4989 = (

let uu____4990 = (

let uu____4993 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_ToSyntax_Env.typename.FStar_Ident.str)
in ((uu____4993), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____4990))
in (Prims.raise uu____4989))
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

let uu____4999 = (

let uu____5005 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____5019 -> (match (uu____5019) with
| (f, uu____5025) -> begin
(

let uu____5026 = (

let uu____5027 = (get_field None f)
in (FStar_All.pipe_left Prims.snd uu____5027))
in ((uu____5026), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (uu____5005)))
in FStar_Parser_AST.Construct (uu____4999))
end
| Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (

let uu____5038 = (

let uu____5039 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____5039))
in (FStar_Parser_AST.mk_term uu____5038 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record1 = (

let uu____5041 = (

let uu____5048 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____5062 -> (match (uu____5062) with
| (f, uu____5068) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (uu____5048)))
in FStar_Parser_AST.Record (uu____5041))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record1 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm1 = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm1)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____5084; FStar_Syntax_Syntax.pos = uu____5085; FStar_Syntax_Syntax.vars = uu____5086}, args); FStar_Syntax_Syntax.tk = uu____5088; FStar_Syntax_Syntax.pos = uu____5089; FStar_Syntax_Syntax.vars = uu____5090}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e1 = (

let uu____5112 = (

let uu____5113 = (

let uu____5123 = (

let uu____5124 = (

let uu____5126 = (

let uu____5127 = (

let uu____5131 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_ToSyntax_Env.typename), (uu____5131)))
in FStar_Syntax_Syntax.Record_ctor (uu____5127))
in Some (uu____5126))
in (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant uu____5124))
in ((uu____5123), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____5113))
in (FStar_All.pipe_left mk1 uu____5112))
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((e1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| uu____5155 -> begin
e
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f);
(

let uu____5159 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f)
in (match (uu____5159) with
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
| uu____5171 -> begin
None
end)
in (

let uu____5172 = (

let uu____5173 = (

let uu____5183 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projname (FStar_Ident.range_of_lid f)) FStar_Syntax_Syntax.Delta_equational qual1)
in (

let uu____5184 = (

let uu____5186 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____5186)::[])
in ((uu____5183), (uu____5184))))
in FStar_Syntax_Syntax.Tm_app (uu____5173))
in (FStar_All.pipe_left mk1 uu____5172)))))
end));
)
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| uu____5192 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| uu____5193 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Let (uu____5194, uu____5195, uu____5196) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QForall (uu____5203, uu____5204, uu____5205) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QExists (uu____5212, uu____5213, uu____5214) -> begin
(failwith "Not implemented yet")
end)))))
and desugar_args : FStar_ToSyntax_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____5238 -> (match (uu____5238) with
| (a, imp) -> begin
(

let uu____5246 = (desugar_term env a)
in (arg_withimp_e imp uu____5246))
end)))))
and desugar_comp : FStar_Range.range  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Errors.Error (((msg), (r))))))
in (

let is_requires = (fun uu____5263 -> (match (uu____5263) with
| (t1, uu____5267) -> begin
(

let uu____5268 = (

let uu____5269 = (unparen t1)
in uu____5269.FStar_Parser_AST.tm)
in (match (uu____5268) with
| FStar_Parser_AST.Requires (uu____5270) -> begin
true
end
| uu____5274 -> begin
false
end))
end))
in (

let is_ensures = (fun uu____5280 -> (match (uu____5280) with
| (t1, uu____5284) -> begin
(

let uu____5285 = (

let uu____5286 = (unparen t1)
in uu____5286.FStar_Parser_AST.tm)
in (match (uu____5285) with
| FStar_Parser_AST.Ensures (uu____5287) -> begin
true
end
| uu____5291 -> begin
false
end))
end))
in (

let is_app = (fun head1 uu____5300 -> (match (uu____5300) with
| (t1, uu____5304) -> begin
(

let uu____5305 = (

let uu____5306 = (unparen t1)
in uu____5306.FStar_Parser_AST.tm)
in (match (uu____5305) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = uu____5308; FStar_Parser_AST.level = uu____5309}, uu____5310, uu____5311) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head1)
end
| uu____5312 -> begin
false
end))
end))
in (

let is_smt_pat = (fun uu____5318 -> (match (uu____5318) with
| (t1, uu____5322) -> begin
(

let uu____5323 = (

let uu____5324 = (unparen t1)
in uu____5324.FStar_Parser_AST.tm)
in (match (uu____5323) with
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Construct (smtpat, uu____5327); FStar_Parser_AST.range = uu____5328; FStar_Parser_AST.level = uu____5329}, uu____5330))::(uu____5331)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Syntax_Const.cons_lid) && (FStar_Util.for_some (fun s -> (smtpat.FStar_Ident.str = s)) (("SMTPat")::("SMTPatT")::("SMTPatOr")::[])))
end
| uu____5350 -> begin
false
end))
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t1 -> (

let uu____5368 = (head_and_args t1)
in (match (uu____5368) with
| (head1, args) -> begin
(match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(

let unit_tm = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) t1.FStar_Parser_AST.range FStar_Parser_AST.Type_level)), (FStar_Parser_AST.Nothing))
in (

let nil_pat = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.nil_lid)) t1.FStar_Parser_AST.range FStar_Parser_AST.Expr)), (FStar_Parser_AST.Nothing))
in (

let req_true = (

let req = FStar_Parser_AST.Requires ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.true_lid)) t1.FStar_Parser_AST.range FStar_Parser_AST.Formula)), (None)))
in (((FStar_Parser_AST.mk_term req t1.FStar_Parser_AST.range FStar_Parser_AST.Type_level)), (FStar_Parser_AST.Nothing)))
in (

let args1 = (match (args) with
| [] -> begin
(Prims.raise (FStar_Errors.Error ((("Not enough arguments to \'Lemma\'"), (t1.FStar_Parser_AST.range)))))
end
| (ens)::[] -> begin
(unit_tm)::(req_true)::(ens)::(nil_pat)::[]
end
| (ens)::(smtpat)::[] when (is_smt_pat smtpat) -> begin
(unit_tm)::(req_true)::(ens)::(smtpat)::[]
end
| (req)::(ens)::[] when ((is_requires req) && (is_ensures ens)) -> begin
(unit_tm)::(req)::(ens)::(nil_pat)::[]
end
| (ens)::(dec)::[] when ((is_ensures ens) && (is_decreases dec)) -> begin
(unit_tm)::(req_true)::(ens)::(nil_pat)::(dec)::[]
end
| (ens)::(dec)::(smtpat)::[] when (((is_ensures ens) && (is_decreases dec)) && (is_smt_pat smtpat)) -> begin
(unit_tm)::(req_true)::(ens)::(smtpat)::(dec)::[]
end
| (req)::(ens)::(dec)::[] when (((is_requires req) && (is_ensures ens)) && (is_decreases dec)) -> begin
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

let uu____5585 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes env) l)
in ((uu____5585), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____5599 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals uu____5599 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head1.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((

let uu____5608 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals uu____5608 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head1.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when (((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head1.FStar_Parser_AST.range)), ([]))), ((((t1), (FStar_Parser_AST.Nothing)))::[]))
end
| uu____5628 -> begin
(

let default_effect = (

let uu____5630 = (FStar_Options.ml_ish ())
in (match (uu____5630) with
| true -> begin
FStar_Syntax_Const.effect_ML_lid
end
| uu____5631 -> begin
((

let uu____5633 = (FStar_Options.warn_default_effects ())
in (match (uu____5633) with
| true -> begin
(FStar_Errors.warn head1.FStar_Parser_AST.range "Using default effect Tot")
end
| uu____5634 -> begin
()
end));
FStar_Syntax_Const.effect_Tot_lid;
)
end))
in (((((FStar_Ident.set_lid_range default_effect head1.FStar_Parser_AST.range)), ([]))), ((((t1), (FStar_Parser_AST.Nothing)))::[])))
end)
end)))
in (

let uu____5646 = (pre_process_comp_typ t)
in (match (uu____5646) with
| ((eff, cattributes), args) -> begin
((match (((FStar_List.length args) = (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5676 = (

let uu____5677 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" uu____5677))
in (fail uu____5676))
end
| uu____5678 -> begin
()
end);
(

let is_universe = (fun uu____5684 -> (match (uu____5684) with
| (uu____5687, imp) -> begin
(imp = FStar_Parser_AST.UnivApp)
end))
in (

let uu____5689 = (FStar_Util.take is_universe args)
in (match (uu____5689) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun uu____5720 -> (match (uu____5720) with
| (u, imp) -> begin
(desugar_universe u)
end)) universes)
in (

let uu____5725 = (

let uu____5733 = (FStar_List.hd args1)
in (

let uu____5738 = (FStar_List.tl args1)
in ((uu____5733), (uu____5738))))
in (match (uu____5725) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (Prims.fst result_arg))
in (

let rest1 = (desugar_args env rest)
in (

let uu____5769 = (

let is_decrease = (fun uu____5792 -> (match (uu____5792) with
| (t1, uu____5799) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____5807; FStar_Syntax_Syntax.pos = uu____5808; FStar_Syntax_Syntax.vars = uu____5809}, (uu____5810)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| uu____5832 -> begin
false
end)
end))
in (FStar_All.pipe_right rest1 (FStar_List.partition is_decrease)))
in (match (uu____5769) with
| (dec, rest2) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun uu____5898 -> (match (uu____5898) with
| (t1, uu____5905) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____5912, ((arg, uu____5914))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| uu____5936 -> begin
(failwith "impos")
end)
end))))
in (

let no_additional_args = (

let is_empty = (fun l -> (match (l) with
| [] -> begin
true
end
| uu____5948 -> begin
false
end))
in ((((is_empty decreases_clause) && (is_empty rest2)) && (is_empty cattributes)) && (is_empty universes1)))
in (match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end
| uu____5957 -> begin
(match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end
| uu____5960 -> begin
(

let flags = (match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid)) with
| true -> begin
(FStar_Syntax_Syntax.LEMMA)::[]
end
| uu____5964 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____5966 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_ML_lid)) with
| true -> begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end
| uu____5968 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____5970 -> begin
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

let uu____6040 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6040 ((FStar_Syntax_Syntax.U_zero)::[])))
in ((FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (Some (FStar_Syntax_Syntax.imp_tag))))::[])) None pat.FStar_Syntax_Syntax.pos)))
end
| uu____6052 -> begin
pat
end)
in (

let uu____6053 = (

let uu____6060 = (

let uu____6067 = (

let uu____6073 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))))) None pat1.FStar_Syntax_Syntax.pos)
in ((uu____6073), (aq)))
in (uu____6067)::[])
in (ens)::uu____6060)
in (req)::uu____6053))
end
| uu____6109 -> begin
rest2
end)
end
| uu____6116 -> begin
rest2
end)
in (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = universes1; FStar_Syntax_Syntax.effect_name = eff; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = rest3; FStar_Syntax_Syntax.flags = (FStar_List.append flags1 decreases_clause)}))))
end)
end)))
end))))
end)))
end)));
)
end))))))))))
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
| uu____6125 -> begin
None
end))
in (

let mk1 = (fun t -> ((FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let uu___214_6166 = t
in {FStar_Syntax_Syntax.n = uu___214_6166.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___214_6166.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___214_6166.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let uu___215_6196 = b
in {FStar_Parser_AST.b = uu___215_6196.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___215_6196.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___215_6196.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env1 pats1 -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (

let uu____6229 = (desugar_term env1 e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) uu____6229)))))) pats1))
in (match (tk) with
| (Some (a), k) -> begin
(

let uu____6238 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____6238) with
| (env1, a1) -> begin
(

let a2 = (

let uu___216_6246 = a1
in {FStar_Syntax_Syntax.ppname = uu___216_6246.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___216_6246.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats1 = (desugar_pats env1 pats)
in (

let body1 = (desugar_formula env1 body)
in (

let body2 = (match (pats1) with
| [] -> begin
body1
end
| uu____6259 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((body1), (FStar_Syntax_Syntax.Meta_pattern (pats1))))))
end)
in (

let body3 = (

let uu____6268 = (

let uu____6271 = (

let uu____6272 = (FStar_Syntax_Syntax.mk_binder a2)
in (uu____6272)::[])
in (no_annot_abs uu____6271 body2))
in (FStar_All.pipe_left setpos uu____6268))
in (

let uu____6277 = (

let uu____6278 = (

let uu____6288 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let uu____6289 = (

let uu____6291 = (FStar_Syntax_Syntax.as_arg body3)
in (uu____6291)::[])
in ((uu____6288), (uu____6289))))
in FStar_Syntax_Syntax.Tm_app (uu____6278))
in (FStar_All.pipe_left mk1 uu____6277)))))))
end))
end
| uu____6295 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body1 = (

let uu____6344 = (q ((rest), (pats), (body)))
in (

let uu____6348 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term uu____6344 uu____6348 FStar_Parser_AST.Formula)))
in (

let uu____6349 = (q (((b)::[]), ([]), (body1)))
in (FStar_Parser_AST.mk_term uu____6349 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| uu____6354 -> begin
(failwith "impossible")
end))
in (

let uu____6356 = (

let uu____6357 = (unparen f)
in uu____6357.FStar_Parser_AST.tm)
in (match (uu____6356) with
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

let uu____6387 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env uu____6387)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____6408 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env uu____6408)))
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
| uu____6433 -> begin
(desugar_term env f)
end)))))))))
and typars_of_binders : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let uu____6437 = (FStar_List.fold_left (fun uu____6450 b -> (match (uu____6450) with
| (env1, out) -> begin
(

let tk = (desugar_binder env1 (

let uu___217_6478 = b
in {FStar_Parser_AST.b = uu___217_6478.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___217_6478.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___217_6478.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(

let uu____6488 = (FStar_ToSyntax_Env.push_bv env1 a)
in (match (uu____6488) with
| (env2, a1) -> begin
(

let a2 = (

let uu___218_6500 = a1
in {FStar_Syntax_Syntax.ppname = uu___218_6500.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___218_6500.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env2), ((((a2), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| uu____6509 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (uu____6437) with
| (env1, tpars) -> begin
((env1), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(

let uu____6559 = (desugar_typ env t)
in ((Some (x)), (uu____6559)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____6562 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown))) None x.FStar_Ident.idRange)
in ((Some (x)), (uu____6562)))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____6577 = (desugar_typ env t)
in ((None), (uu____6577)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators = (fun quals env t tps k datas -> (

let quals1 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___193_6626 -> (match (uu___193_6626) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| uu____6627 -> begin
false
end))))
in (

let quals2 = (fun q -> (

let uu____6635 = ((FStar_All.pipe_left Prims.op_Negation env.FStar_ToSyntax_Env.iface) || env.FStar_ToSyntax_Env.admitted_iface)
in (match (uu____6635) with
| true -> begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals1)
end
| uu____6637 -> begin
(FStar_List.append q quals1)
end)))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (

let uu____6642 = (

let uu____6643 = (

let uu____6649 = (quals2 ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in ((disc_name), ([]), (FStar_Syntax_Syntax.tun), (uu____6649)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____6643))
in {FStar_Syntax_Syntax.sigel = uu____6642; FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid disc_name)}))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_ToSyntax_Env.env  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let uu____6674 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____6684 -> (match (uu____6684) with
| (x, uu____6689) -> begin
(

let uu____6690 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____6690) with
| (field_name, uu____6695) -> begin
(

let only_decl = (((

let uu____6697 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____6697)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (

let uu____6698 = (

let uu____6699 = (FStar_ToSyntax_Env.current_module env)
in uu____6699.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____6698)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____6709 = (FStar_List.filter (fun uu___194_6711 -> (match (uu___194_6711) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____6712 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____6709)
end
| uu____6713 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___195_6720 -> (match (uu___195_6720) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| uu____6721 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun), (quals1))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid field_name)}
in (match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____6726 -> begin
(

let dd = (

let uu____6728 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____6728) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____6730 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lb = (

let uu____6732 = (

let uu____6735 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (uu____6735))
in {FStar_Syntax_Syntax.lbname = uu____6732; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun})
in (

let impl = (

let uu____6737 = (

let uu____6738 = (

let uu____6746 = (

let uu____6748 = (

let uu____6749 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____6749 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____6748)::[])
in ((((false), ((lb)::[]))), (uu____6746), (quals1), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____6738))
in {FStar_Syntax_Syntax.sigel = uu____6737; FStar_Syntax_Syntax.sigrng = p})
in (match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____6765 -> begin
(decl)::(impl)::[]
end))))
end))))))
end))
end))))
in (FStar_All.pipe_right uu____6674 FStar_List.flatten))))


let mk_data_projector_names = (fun iquals env uu____6789 -> (match (uu____6789) with
| (inductive_tps, se) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____6797, t, uu____6799, n1, quals, uu____6802) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let uu____6807 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____6807) with
| (formals, uu____6817) -> begin
(match (formals) with
| [] -> begin
[]
end
| uu____6831 -> begin
(

let filter_records = (fun uu___196_6839 -> (match (uu___196_6839) with
| FStar_Syntax_Syntax.RecordConstructor (uu____6841, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| uu____6848 -> begin
None
end))
in (

let fv_qual = (

let uu____6850 = (FStar_Util.find_map quals filter_records)
in (match (uu____6850) with
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
| uu____6856 -> begin
iquals
end)
in (

let uu____6857 = (FStar_Util.first_N n1 formals)
in (match (uu____6857) with
| (uu____6869, rest) -> begin
(mk_indexed_projector_names iquals1 fv_qual env lid rest)
end)))))
end)
end))
end
| uu____6883 -> begin
[]
end)
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = (

let uu____6921 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____6921) with
| true -> begin
(

let uu____6923 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (uu____6923))
end
| uu____6924 -> begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end))
in (

let lb = (

let uu____6926 = (

let uu____6929 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (uu____6929))
in (

let uu____6930 = (

let uu____6933 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars uu____6933))
in (

let uu____6936 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = uu____6926; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____6930; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____6936})))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (lids), (quals), ([]))); FStar_Syntax_Syntax.sigrng = rng})))


let rec desugar_tycon : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d quals tcs -> (

let rng = d.FStar_Parser_AST.drange
in (

let tycon_id = (fun uu___197_6970 -> (match (uu___197_6970) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(

let uu____7009 = (

let uu____7010 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____7010))
in (FStar_Parser_AST.mk_term uu____7009 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| uu____7032 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (

let uu____7035 = (

let uu____7036 = (

let uu____7040 = (binder_to_term b)
in ((out), (uu____7040), ((imp_of_aqual b))))
in FStar_Parser_AST.App (uu____7036))
in (FStar_Parser_AST.mk_term uu____7035 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun uu___198_7047 -> (match (uu___198_7047) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun uu____7076 -> (match (uu____7076) with
| (x, t, uu____7083) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (

let uu____7087 = (

let uu____7088 = (

let uu____7089 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (uu____7089))
in (FStar_Parser_AST.mk_term uu____7088 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____7087 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type_level)
in (

let uu____7092 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____7104 -> (match (uu____7104) with
| (x, uu____7110, uu____7111) -> begin
(FStar_Syntax_Util.unmangle_field_name x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (uu____7092)))))))
end
| uu____7138 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals1 _env mutuals uu___199_7160 -> (match (uu___199_7160) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let uu____7174 = (typars_of_binders _env binders)
in (match (uu____7174) with
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

let uu____7202 = (

let uu____7203 = (

let uu____7204 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (uu____7204))
in (FStar_Parser_AST.mk_term uu____7203 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____7202 binders))
in (

let qlid = (FStar_ToSyntax_Env.qualify _env id)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let k1 = (FStar_Syntax_Subst.close typars1 k)
in (

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((qlid), ([]), (typars1), (k1), (mutuals), ([]), (quals1))); FStar_Syntax_Syntax.sigrng = rng}
in (

let _env1 = (FStar_ToSyntax_Env.push_top_level_rec_binding _env id FStar_Syntax_Syntax.Delta_constant)
in (

let _env2 = (FStar_ToSyntax_Env.push_top_level_rec_binding _env' id FStar_Syntax_Syntax.Delta_constant)
in ((_env1), (_env2), (se), (tconstr))))))))))
end))
end
| uu____7215 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env1 bs -> (

let uu____7241 = (FStar_List.fold_left (fun uu____7257 uu____7258 -> (match (((uu____7257), (uu____7258))) with
| ((env2, tps), (x, imp)) -> begin
(

let uu____7306 = (FStar_ToSyntax_Env.push_bv env2 x.FStar_Syntax_Syntax.ppname)
in (match (uu____7306) with
| (env3, y) -> begin
((env3), ((((y), (imp)))::tps))
end))
end)) ((env1), ([])) bs)
in (match (uu____7241) with
| (env2, bs1) -> begin
((env2), ((FStar_List.rev bs1)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt1 = (match (kopt) with
| None -> begin
(

let uu____7367 = (tm_type_z id.FStar_Ident.idRange)
in Some (uu____7367))
end
| uu____7368 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt1)))
in (

let uu____7373 = (desugar_abstract_tc quals env [] tc)
in (match (uu____7373) with
| (uu____7380, uu____7381, se, uu____7383) -> begin
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, uu____7386, typars, k, [], [], quals1) -> begin
(

let quals2 = (

let uu____7396 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (match (uu____7396) with
| true -> begin
quals1
end
| uu____7399 -> begin
((

let uu____7401 = (FStar_Range.string_of_range se.FStar_Syntax_Syntax.sigrng)
in (

let uu____7402 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" uu____7401 uu____7402)));
(FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals1;
)
end))
in (

let t = (match (typars) with
| [] -> begin
k
end
| uu____7406 -> begin
(

let uu____7407 = (

let uu____7410 = (

let uu____7411 = (

let uu____7419 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (uu____7419)))
in FStar_Syntax_Syntax.Tm_arrow (uu____7411))
in (FStar_Syntax_Syntax.mk uu____7410))
in (uu____7407 None se.FStar_Syntax_Syntax.sigrng))
end)
in (

let uu___219_7428 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t), (quals2))); FStar_Syntax_Syntax.sigrng = uu___219_7428.FStar_Syntax_Syntax.sigrng})))
end
| uu____7431 -> begin
(failwith "Impossible")
end)
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se1)
in (

let env2 = (

let uu____7434 = (FStar_ToSyntax_Env.qualify env1 id)
in (FStar_ToSyntax_Env.push_doc env1 uu____7434 d.FStar_Parser_AST.doc))
in ((env2), ((se1)::[])))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let uu____7444 = (typars_of_binders env binders)
in (match (uu____7444) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
(

let uu____7464 = (FStar_Util.for_some (fun uu___200_7465 -> (match (uu___200_7465) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| uu____7466 -> begin
false
end)) quals)
in (match (uu____7464) with
| true -> begin
FStar_Syntax_Syntax.teff
end
| uu____7467 -> begin
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

let uu____7472 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___201_7474 -> (match (uu___201_7474) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| uu____7475 -> begin
false
end))))
in (match (uu____7472) with
| true -> begin
quals
end
| uu____7477 -> begin
(match ((t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula)) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____7479 -> begin
quals
end)
end))
in (

let qlid = (FStar_ToSyntax_Env.qualify env id)
in (

let se = (

let uu____7482 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Effect))
in (match (uu____7482) with
| true -> begin
(

let uu____7484 = (

let uu____7488 = (

let uu____7489 = (unparen t)
in uu____7489.FStar_Parser_AST.tm)
in (match (uu____7488) with
| FStar_Parser_AST.Construct (head1, args) -> begin
(

let uu____7501 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____7517))::args_rev -> begin
(

let uu____7524 = (

let uu____7525 = (unparen last_arg)
in uu____7525.FStar_Parser_AST.tm)
in (match (uu____7524) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____7540 -> begin
(([]), (args))
end))
end
| uu____7545 -> begin
(([]), (args))
end)
in (match (uu____7501) with
| (cattributes, args1) -> begin
(

let uu____7566 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head1), (args1)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (uu____7566)))
end))
end
| uu____7572 -> begin
((t), ([]))
end))
in (match (uu____7484) with
| (t1, cattributes) -> begin
(

let c = (desugar_comp t1.FStar_Parser_AST.range env' t1)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let c1 = (FStar_Syntax_Subst.close_comp typars1 c)
in (

let uu____7583 = (

let uu____7584 = (

let uu____7593 = (FStar_All.pipe_right quals1 (FStar_List.filter (fun uu___202_7597 -> (match (uu___202_7597) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| uu____7598 -> begin
true
end))))
in ((qlid), ([]), (typars1), (c1), (uu____7593), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c1)))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (uu____7584))
in {FStar_Syntax_Syntax.sigel = uu____7583; FStar_Syntax_Syntax.sigrng = rng}))))
end))
end
| uu____7602 -> begin
(

let t1 = (desugar_typ env' t)
in (mk_typ_abbrev qlid [] typars k t1 ((qlid)::[]) quals1 rng))
end))
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se)
in (

let env2 = (FStar_ToSyntax_Env.push_doc env1 qlid d.FStar_Parser_AST.doc)
in ((env2), ((se)::[])))))))))
end))
end
| (FStar_Parser_AST.TyconRecord (uu____7607))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let uu____7620 = (tycon_record_as_variant trec)
in (match (uu____7620) with
| (t, fs) -> begin
(

let uu____7630 = (

let uu____7632 = (

let uu____7633 = (

let uu____7638 = (

let uu____7640 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.ids_of_lid uu____7640))
in ((uu____7638), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____7633))
in (uu____7632)::quals)
in (desugar_tycon env d uu____7630 ((t)::[])))
end)))
end
| (uu____7643)::uu____7644 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals1 et tc -> (

let uu____7731 = et
in (match (uu____7731) with
| (env1, tcs1) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (uu____7845) -> begin
(

let trec = tc
in (

let uu____7858 = (tycon_record_as_variant trec)
in (match (uu____7858) with
| (t, fs) -> begin
(

let uu____7889 = (

let uu____7891 = (

let uu____7892 = (

let uu____7897 = (

let uu____7899 = (FStar_ToSyntax_Env.current_module env1)
in (FStar_Ident.ids_of_lid uu____7899))
in ((uu____7897), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____7892))
in (uu____7891)::quals1)
in (collect_tcs uu____7889 ((env1), (tcs1)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let uu____7945 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____7945) with
| (env2, uu____7976, se, tconstr) -> begin
((env2), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals1))))::tcs1))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let uu____8054 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____8054) with
| (env2, uu____8085, se, tconstr) -> begin
((env2), ((FStar_Util.Inr (((se), (binders), (t), (quals1))))::tcs1))
end))
end
| uu____8149 -> begin
(failwith "Unrecognized mutual type definition")
end)
end)))
in (

let uu____8173 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (uu____8173) with
| (env1, tcs1) -> begin
(

let tcs2 = (FStar_List.rev tcs1)
in (

let docs_tps_sigelts = (FStar_All.pipe_right tcs2 (FStar_List.collect (fun uu___204_8423 -> (match (uu___204_8423) with
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, uu____8459, uu____8460, uu____8461); FStar_Syntax_Syntax.sigrng = uu____8462}, binders, t, quals1) -> begin
(

let t1 = (

let uu____8495 = (typars_of_binders env1 binders)
in (match (uu____8495) with
| (env2, tpars1) -> begin
(

let uu____8512 = (push_tparams env2 tpars1)
in (match (uu____8512) with
| (env_tps, tpars2) -> begin
(

let t1 = (desugar_typ env_tps t)
in (

let tpars3 = (FStar_Syntax_Subst.close_binders tpars2)
in (FStar_Syntax_Subst.close tpars3 t1)))
end))
end))
in (

let uu____8531 = (

let uu____8542 = (mk_typ_abbrev id uvs tpars k t1 ((id)::[]) quals1 rng)
in ((((id), (d.FStar_Parser_AST.doc))), ([]), (uu____8542)))
in (uu____8531)::[]))
end
| FStar_Util.Inl ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals1, uu____8579, tags); FStar_Syntax_Syntax.sigrng = uu____8581}, constrs, tconstr, quals1) -> begin
(

let mk_tot = (fun t -> (

let tot1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot1), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)))
in (

let tycon = ((tname), (tpars), (k))
in (

let uu____8634 = (push_tparams env1 tpars)
in (match (uu____8634) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun uu____8673 -> (match (uu____8673) with
| (x, uu____8681) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let tot_tconstr = (mk_tot tconstr)
in (

let uu____8686 = (

let uu____8701 = (FStar_All.pipe_right constrs (FStar_List.map (fun uu____8753 -> (match (uu____8753) with
| (id, topt, doc1, of_notation) -> begin
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
| uu____8783 -> begin
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

let uu____8786 = (close env_tps t)
in (desugar_term env_tps uu____8786))
in (

let name = (FStar_ToSyntax_Env.qualify env1 id)
in (

let quals2 = (FStar_All.pipe_right tags (FStar_List.collect (fun uu___203_8792 -> (match (uu___203_8792) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| uu____8799 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (

let uu____8805 = (

let uu____8816 = (

let uu____8817 = (

let uu____8818 = (

let uu____8828 = (

let uu____8831 = (

let uu____8834 = (FStar_All.pipe_right t1 FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total uu____8834))
in (FStar_Syntax_Util.arrow data_tpars uu____8831))
in ((name), (univs), (uu____8828), (tname), (ntps), (quals2), (mutuals1)))
in FStar_Syntax_Syntax.Sig_datacon (uu____8818))
in {FStar_Syntax_Syntax.sigel = uu____8817; FStar_Syntax_Syntax.sigrng = rng})
in ((((name), (doc1))), (tps), (uu____8816)))
in ((name), (uu____8805))))))))
end))))
in (FStar_All.pipe_left FStar_List.split uu____8701))
in (match (uu____8686) with
| (constrNames, constrs1) -> begin
(((((tname), (d.FStar_Parser_AST.doc))), ([]), ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs), (tpars), (k), (mutuals1), (constrNames), (tags))); FStar_Syntax_Syntax.sigrng = rng})))::constrs1
end))))
end))))
end
| uu____8959 -> begin
(failwith "impossible")
end))))
in (

let name_docs = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____9024 -> (match (uu____9024) with
| (name_doc, uu____9039, uu____9040) -> begin
name_doc
end))))
in (

let sigelts = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____9079 -> (match (uu____9079) with
| (uu____9090, uu____9091, se) -> begin
se
end))))
in (

let uu____9107 = (

let uu____9111 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals uu____9111 rng))
in (match (uu____9107) with
| (bundle, abbrevs) -> begin
(

let env2 = (FStar_ToSyntax_Env.push_sigelt env0 bundle)
in (

let env3 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2 abbrevs)
in (

let data_ops = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.collect (fun uu____9145 -> (match (uu____9145) with
| (uu____9157, tps, se) -> begin
(mk_data_projector_names quals env3 ((tps), (se)))
end))))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, uu____9189, tps, k, uu____9192, constrs, quals1) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals1)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::quals1
end
| uu____9207 -> begin
quals1
end)
in (mk_data_discriminators quals2 env3 tname tps k constrs))
end
| uu____9208 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env4 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env3 ops)
in (

let env5 = (FStar_List.fold_left (fun acc uu____9217 -> (match (uu____9217) with
| (lid, doc1) -> begin
(FStar_ToSyntax_Env.push_doc env4 lid doc1)
end)) env4 name_docs)
in ((env5), ((FStar_List.append ((bundle)::[]) (FStar_List.append abbrevs ops)))))))))))
end))))))
end)))))
end
| [] -> begin
(failwith "impossible")
end)))))))))))


let desugar_binders : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (

let uu____9239 = (FStar_List.fold_left (fun uu____9246 b -> (match (uu____9246) with
| (env1, binders1) -> begin
(

let uu____9258 = (desugar_binder env1 b)
in (match (uu____9258) with
| (Some (a), k) -> begin
(

let uu____9268 = (as_binder env1 b.FStar_Parser_AST.aqual ((Some (a)), (k)))
in (match (uu____9268) with
| (binder, env2) -> begin
((env2), ((binder)::binders1))
end))
end
| uu____9278 -> begin
(Prims.raise (FStar_Errors.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) binders)
in (match (uu____9239) with
| (env1, binders1) -> begin
((env1), ((FStar_List.rev binders1)))
end)))


let rec desugar_effect : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_typ eff_decls -> (

let env0 = env
in (

let monad_env = (FStar_ToSyntax_Env.enter_monad_scope env eff_name)
in (

let uu____9356 = (desugar_binders monad_env eff_binders)
in (match (uu____9356) with
| (env1, binders) -> begin
(

let eff_t = (desugar_term env1 eff_typ)
in (

let for_free = (

let uu____9369 = (

let uu____9370 = (

let uu____9374 = (FStar_Syntax_Util.arrow_formals eff_t)
in (Prims.fst uu____9374))
in (FStar_List.length uu____9370))
in (uu____9369 = (Prims.parse_int "1")))
in (

let mandatory_members = (

let rr_members = ("repr")::("return")::("bind")::[]
in (match (for_free) with
| true -> begin
rr_members
end
| uu____9397 -> begin
(FStar_List.append rr_members (("return_wp")::("bind_wp")::("if_then_else")::("ite_wp")::("stronger")::("close_wp")::("assert_p")::("assume_p")::("null_wp")::("trivial")::[]))
end))
in (

let name_of_eff_decl = (fun decl -> (match (decl.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____9402, ((FStar_Parser_AST.TyconAbbrev (name, uu____9404, uu____9405, uu____9406), uu____9407))::[]) -> begin
(FStar_Ident.text_of_id name)
end
| uu____9424 -> begin
(failwith "Malformed effect member declaration.")
end))
in (

let uu____9425 = (FStar_List.partition (fun decl -> (

let uu____9431 = (name_of_eff_decl decl)
in (FStar_List.mem uu____9431 mandatory_members))) eff_decls)
in (match (uu____9425) with
| (mandatory_members_decls, actions) -> begin
(

let uu____9441 = (FStar_All.pipe_right mandatory_members_decls (FStar_List.fold_left (fun uu____9452 decl -> (match (uu____9452) with
| (env2, out) -> begin
(

let uu____9464 = (desugar_decl env2 decl)
in (match (uu____9464) with
| (env3, ses) -> begin
(

let uu____9472 = (

let uu____9474 = (FStar_List.hd ses)
in (uu____9474)::out)
in ((env3), (uu____9472)))
end))
end)) ((env1), ([]))))
in (match (uu____9441) with
| (env2, decls) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let actions_docs = (FStar_All.pipe_right actions (FStar_List.map (fun d1 -> (match (d1.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____9502, ((FStar_Parser_AST.TyconAbbrev (name, params, uu____9505, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (uu____9506, ((def, uu____9508))::((cps_type, uu____9510))::[]); FStar_Parser_AST.range = uu____9511; FStar_Parser_AST.level = uu____9512}), doc1))::[]) when (not (for_free)) -> begin
(

let uu____9539 = (desugar_binders env2 params)
in (match (uu____9539) with
| (env3, params1) -> begin
(

let params2 = (FStar_Syntax_Subst.close_binders params1)
in (

let uu____9551 = (

let uu____9552 = (FStar_ToSyntax_Env.qualify env3 name)
in (

let uu____9553 = (

let uu____9554 = (desugar_term env3 def)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 params2) uu____9554))
in (

let uu____9557 = (

let uu____9558 = (desugar_typ env3 cps_type)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 params2) uu____9558))
in {FStar_Syntax_Syntax.action_name = uu____9552; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = params2; FStar_Syntax_Syntax.action_defn = uu____9553; FStar_Syntax_Syntax.action_typ = uu____9557})))
in ((uu____9551), (doc1))))
end))
end
| FStar_Parser_AST.Tycon (uu____9562, ((FStar_Parser_AST.TyconAbbrev (name, params, uu____9565, defn), doc1))::[]) when for_free -> begin
(

let uu____9584 = (desugar_binders env2 params)
in (match (uu____9584) with
| (env3, params1) -> begin
(

let params2 = (FStar_Syntax_Subst.close_binders params1)
in (

let uu____9596 = (

let uu____9597 = (FStar_ToSyntax_Env.qualify env3 name)
in (

let uu____9598 = (

let uu____9599 = (desugar_term env3 defn)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 params2) uu____9599))
in {FStar_Syntax_Syntax.action_name = uu____9597; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = params2; FStar_Syntax_Syntax.action_defn = uu____9598; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
in ((uu____9596), (doc1))))
end))
end
| uu____9603 -> begin
(Prims.raise (FStar_Errors.Error ((("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples)."), (d1.FStar_Parser_AST.drange)))))
end))))
in (

let actions1 = (FStar_List.map Prims.fst actions_docs)
in (

let eff_t1 = (FStar_Syntax_Subst.close binders1 eff_t)
in (

let lookup = (fun s -> (

let l = (FStar_ToSyntax_Env.qualify env2 (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange))))
in (

let uu____9622 = (

let uu____9623 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_definition env2) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders1) uu____9623))
in (([]), (uu____9622)))))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (Some (mname))) quals)
in (

let se = (match (for_free) with
| true -> begin
(

let dummy_tscheme = (

let uu____9635 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (([]), (uu____9635)))
in (

let uu____9645 = (

let uu____9646 = (

let uu____9647 = (

let uu____9648 = (lookup "repr")
in (Prims.snd uu____9648))
in (

let uu____9653 = (lookup "return")
in (

let uu____9654 = (lookup "bind")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = uu____9647; FStar_Syntax_Syntax.return_repr = uu____9653; FStar_Syntax_Syntax.bind_repr = uu____9654; FStar_Syntax_Syntax.actions = actions1})))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____9646))
in {FStar_Syntax_Syntax.sigel = uu____9645; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange}))
end
| uu____9655 -> begin
(

let rr = (FStar_Util.for_some (fun uu___205_9657 -> (match (uu___205_9657) with
| (FStar_Syntax_Syntax.Reifiable) | (FStar_Syntax_Syntax.Reflectable (_)) -> begin
true
end
| uu____9659 -> begin
false
end)) qualifiers)
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (

let uu____9665 = (

let uu____9666 = (

let uu____9667 = (lookup "return_wp")
in (

let uu____9668 = (lookup "bind_wp")
in (

let uu____9669 = (lookup "if_then_else")
in (

let uu____9670 = (lookup "ite_wp")
in (

let uu____9671 = (lookup "stronger")
in (

let uu____9672 = (lookup "close_wp")
in (

let uu____9673 = (lookup "assert_p")
in (

let uu____9674 = (lookup "assume_p")
in (

let uu____9675 = (lookup "null_wp")
in (

let uu____9676 = (lookup "trivial")
in (

let uu____9677 = (match (rr) with
| true -> begin
(

let uu____9678 = (lookup "repr")
in (FStar_All.pipe_left Prims.snd uu____9678))
end
| uu____9686 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let uu____9687 = (match (rr) with
| true -> begin
(lookup "return")
end
| uu____9688 -> begin
un_ts
end)
in (

let uu____9689 = (match (rr) with
| true -> begin
(lookup "bind")
end
| uu____9690 -> begin
un_ts
end)
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = uu____9667; FStar_Syntax_Syntax.bind_wp = uu____9668; FStar_Syntax_Syntax.if_then_else = uu____9669; FStar_Syntax_Syntax.ite_wp = uu____9670; FStar_Syntax_Syntax.stronger = uu____9671; FStar_Syntax_Syntax.close_wp = uu____9672; FStar_Syntax_Syntax.assert_p = uu____9673; FStar_Syntax_Syntax.assume_p = uu____9674; FStar_Syntax_Syntax.null_wp = uu____9675; FStar_Syntax_Syntax.trivial = uu____9676; FStar_Syntax_Syntax.repr = uu____9677; FStar_Syntax_Syntax.return_repr = uu____9687; FStar_Syntax_Syntax.bind_repr = uu____9689; FStar_Syntax_Syntax.actions = actions1})))))))))))))
in FStar_Syntax_Syntax.Sig_new_effect (uu____9666))
in {FStar_Syntax_Syntax.sigel = uu____9665; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange})))
end)
in (

let env3 = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env4 = (FStar_ToSyntax_Env.push_doc env3 mname d.FStar_Parser_AST.doc)
in (

let env5 = (FStar_All.pipe_right actions_docs (FStar_List.fold_left (fun env5 uu____9702 -> (match (uu____9702) with
| (a, doc1) -> begin
(

let env6 = (

let uu____9711 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env5 uu____9711))
in (FStar_ToSyntax_Env.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1))
end)) env4))
in (

let env6 = (

let uu____9713 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____9713) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange}
in (FStar_ToSyntax_Env.push_sigelt env5 refl_decl)))
end
| uu____9718 -> begin
env5
end))
in (

let env7 = (FStar_ToSyntax_Env.push_doc env6 mname d.FStar_Parser_AST.doc)
in ((env7), ((se)::[])))))))))))))))
end))
end))))))
end)))))
and desugar_redefine_effect : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  (FStar_Ident.lident Prims.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier)  ->  FStar_Parser_AST.qualifier Prims.list  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d trans_qual1 quals eff_name eff_binders defn -> (

let env0 = env
in (

let env1 = (FStar_ToSyntax_Env.enter_monad_scope env eff_name)
in (

let uu____9737 = (desugar_binders env1 eff_binders)
in (match (uu____9737) with
| (env2, binders) -> begin
(

let uu____9748 = (

let uu____9758 = (head_and_args defn)
in (match (uu____9758) with
| (head1, args) -> begin
(

let lid = (match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
l
end
| uu____9783 -> begin
(

let uu____9784 = (

let uu____9785 = (

let uu____9788 = (

let uu____9789 = (

let uu____9790 = (FStar_Parser_AST.term_to_string head1)
in (Prims.strcat uu____9790 " not found"))
in (Prims.strcat "Effect " uu____9789))
in ((uu____9788), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____9785))
in (Prims.raise uu____9784))
end)
in (

let ed = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_effect_defn env2) lid)
in (

let uu____9792 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____9808))::args_rev -> begin
(

let uu____9815 = (

let uu____9816 = (unparen last_arg)
in uu____9816.FStar_Parser_AST.tm)
in (match (uu____9815) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____9831 -> begin
(([]), (args))
end))
end
| uu____9836 -> begin
(([]), (args))
end)
in (match (uu____9792) with
| (cattributes, args1) -> begin
(

let uu____9863 = (desugar_args env2 args1)
in (

let uu____9868 = (desugar_attributes env2 cattributes)
in ((lid), (ed), (uu____9863), (uu____9868))))
end))))
end))
in (match (uu____9748) with
| (ed_lid, ed, args, cattributes) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let sub1 = (fun uu____9902 -> (match (uu____9902) with
| (uu____9909, x) -> begin
(

let uu____9913 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (uu____9913) with
| (edb, x1) -> begin
((match (((FStar_List.length args) <> (FStar_List.length edb))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end
| uu____9931 -> begin
()
end);
(

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (

let uu____9933 = (

let uu____9934 = (FStar_Syntax_Subst.subst s x1)
in (FStar_Syntax_Subst.close binders1 uu____9934))
in (([]), (uu____9933))));
)
end))
end))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let ed1 = (

let uu____9938 = (

let uu____9940 = (trans_qual1 (Some (mname)))
in (FStar_List.map uu____9940 quals))
in (

let uu____9943 = (

let uu____9944 = (sub1 (([]), (ed.FStar_Syntax_Syntax.signature)))
in (Prims.snd uu____9944))
in (

let uu____9950 = (sub1 ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____9951 = (sub1 ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____9952 = (sub1 ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____9953 = (sub1 ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____9954 = (sub1 ed.FStar_Syntax_Syntax.stronger)
in (

let uu____9955 = (sub1 ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____9956 = (sub1 ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____9957 = (sub1 ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____9958 = (sub1 ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____9959 = (sub1 ed.FStar_Syntax_Syntax.trivial)
in (

let uu____9960 = (

let uu____9961 = (sub1 (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd uu____9961))
in (

let uu____9967 = (sub1 ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____9968 = (sub1 ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____9969 = (FStar_List.map (fun action -> (

let uu____9972 = (FStar_ToSyntax_Env.qualify env2 action.FStar_Syntax_Syntax.action_unqualified_name)
in (

let uu____9973 = (

let uu____9974 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd uu____9974))
in (

let uu____9980 = (

let uu____9981 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd uu____9981))
in {FStar_Syntax_Syntax.action_name = uu____9972; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = action.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____9973; FStar_Syntax_Syntax.action_typ = uu____9980})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = uu____9938; FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = uu____9943; FStar_Syntax_Syntax.ret_wp = uu____9950; FStar_Syntax_Syntax.bind_wp = uu____9951; FStar_Syntax_Syntax.if_then_else = uu____9952; FStar_Syntax_Syntax.ite_wp = uu____9953; FStar_Syntax_Syntax.stronger = uu____9954; FStar_Syntax_Syntax.close_wp = uu____9955; FStar_Syntax_Syntax.assert_p = uu____9956; FStar_Syntax_Syntax.assume_p = uu____9957; FStar_Syntax_Syntax.null_wp = uu____9958; FStar_Syntax_Syntax.trivial = uu____9959; FStar_Syntax_Syntax.repr = uu____9960; FStar_Syntax_Syntax.return_repr = uu____9967; FStar_Syntax_Syntax.bind_repr = uu____9968; FStar_Syntax_Syntax.actions = uu____9969}))))))))))))))))
in (

let se = (

let for_free = (

let uu____9989 = (

let uu____9990 = (

let uu____9994 = (FStar_Syntax_Util.arrow_formals ed1.FStar_Syntax_Syntax.signature)
in (Prims.fst uu____9994))
in (FStar_List.length uu____9990))
in (uu____9989 = (Prims.parse_int "1")))
in {FStar_Syntax_Syntax.sigel = (match (for_free) with
| true -> begin
FStar_Syntax_Syntax.Sig_new_effect_for_free (ed1)
end
| uu____10012 -> begin
FStar_Syntax_Syntax.Sig_new_effect (ed1)
end); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange})
in (

let monad_env = env2
in (

let env3 = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env4 = (FStar_ToSyntax_Env.push_doc env3 ed_lid d.FStar_Parser_AST.doc)
in (

let env5 = (FStar_All.pipe_right ed1.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun env5 a -> (

let doc1 = (FStar_ToSyntax_Env.try_lookup_doc env5 a.FStar_Syntax_Syntax.action_name)
in (

let env6 = (

let uu____10023 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env5 uu____10023))
in (FStar_ToSyntax_Env.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1)))) env4))
in (

let env6 = (

let uu____10025 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____10025) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange}
in (FStar_ToSyntax_Env.push_sigelt env5 refl_decl)))
end
| uu____10031 -> begin
env5
end))
in (

let env7 = (FStar_ToSyntax_Env.push_doc env6 mname d.FStar_Parser_AST.doc)
in ((env7), ((se)::[])))))))))))))
end))
end)))))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let trans_qual1 = (trans_qual d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_pragma ((trans_pragma p)); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange}
in ((match ((p = FStar_Parser_AST.LightOff)) with
| true -> begin
(FStar_Options.set_ml_ish ())
end
| uu____10049 -> begin
()
end);
((env), ((se)::[]));
))
end
| FStar_Parser_AST.Fsdoc (uu____10051) -> begin
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

let uu____10063 = (FStar_ToSyntax_Env.push_module_abbrev env x l)
in ((uu____10063), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, tcs) -> begin
(

let quals = (match (is_effect) with
| true -> begin
(FStar_Parser_AST.Effect_qual)::d.FStar_Parser_AST.quals
end
| uu____10078 -> begin
d.FStar_Parser_AST.quals
end)
in (

let tcs1 = (FStar_List.map (fun uu____10084 -> (match (uu____10084) with
| (x, uu____10089) -> begin
x
end)) tcs)
in (

let uu____10092 = (FStar_List.map (trans_qual1 None) quals)
in (desugar_tycon env d uu____10092 tcs1))))
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
| ((p, uu____10131))::[] -> begin
(

let uu____10136 = (is_app_pattern p)
in (not (uu____10136)))
end
| uu____10137 -> begin
false
end))
in (match ((not (expand_toplevel_pattern))) with
| true -> begin
(

let as_inner_let = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let ds_lets = (desugar_term_maybe_top true env as_inner_let)
in (

let uu____10148 = (

let uu____10149 = (FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets)
in uu____10149.FStar_Syntax_Syntax.n)
in (match (uu____10148) with
| FStar_Syntax_Syntax.Tm_let (lbs, uu____10155) -> begin
(

let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals1 = (match (quals) with
| (uu____10175)::uu____10176 -> begin
(FStar_List.map (trans_qual1 None) quals)
end
| uu____10178 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun uu___206_10182 -> (match (uu___206_10182) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (uu____10184); FStar_Syntax_Syntax.lbunivs = uu____10185; FStar_Syntax_Syntax.lbtyp = uu____10186; FStar_Syntax_Syntax.lbeff = uu____10187; FStar_Syntax_Syntax.lbdef = uu____10188} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____10195; FStar_Syntax_Syntax.lbtyp = uu____10196; FStar_Syntax_Syntax.lbeff = uu____10197; FStar_Syntax_Syntax.lbdef = uu____10198} -> begin
(FStar_ToSyntax_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals2 = (

let uu____10210 = (FStar_All.pipe_right lets (FStar_Util.for_some (fun uu____10216 -> (match (uu____10216) with
| (uu____10219, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end))))
in (match (uu____10210) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals1
end
| uu____10222 -> begin
quals1
end))
in (

let lbs1 = (

let uu____10227 = (FStar_All.pipe_right quals2 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____10227) with
| true -> begin
(

let uu____10232 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu___220_10239 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let uu___221_10240 = fv
in {FStar_Syntax_Syntax.fv_name = uu___221_10240.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = uu___221_10240.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = uu___220_10239.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___220_10239.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___220_10239.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___220_10239.FStar_Syntax_Syntax.lbdef})))))
in (((Prims.fst lbs)), (uu____10232)))
end
| uu____10246 -> begin
lbs
end))
in (

let names = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (

let s = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((lbs1), (names), (quals2), (attrs1))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange}
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env s)
in (

let env2 = (FStar_List.fold_left (fun env2 id -> (FStar_ToSyntax_Env.push_doc env2 id d.FStar_Parser_AST.doc)) env1 names)
in ((env2), ((s)::[]))))))))))
end
| uu____10268 -> begin
(failwith "Desugaring a let did not produce a let")
end))))
end
| uu____10271 -> begin
(

let uu____10272 = (match (lets) with
| ((pat, body))::[] -> begin
((pat), (body))
end
| uu____10283 -> begin
(failwith "expand_toplevel_pattern should only allow single definition lets")
end)
in (match (uu____10272) with
| (pat, body) -> begin
(

let fresh_toplevel_name = (FStar_Ident.gen FStar_Range.dummyRange)
in (

let fresh_pat = (

let var_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((fresh_toplevel_name), (None)))) FStar_Range.dummyRange)
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, ty) -> begin
(

let uu___222_10299 = pat1
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed (((var_pat), (ty))); FStar_Parser_AST.prange = uu___222_10299.FStar_Parser_AST.prange})
end
| uu____10300 -> begin
var_pat
end))
in (

let main_let = (desugar_decl env (

let uu___223_10304 = d
in {FStar_Parser_AST.d = FStar_Parser_AST.TopLevelLet (((isrec), ((((fresh_pat), (body)))::[]))); FStar_Parser_AST.drange = uu___223_10304.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___223_10304.FStar_Parser_AST.doc; FStar_Parser_AST.quals = (FStar_Parser_AST.Private)::d.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = uu___223_10304.FStar_Parser_AST.attrs}))
in (

let build_projection = (fun uu____10323 id -> (match (uu____10323) with
| (env1, ses) -> begin
(

let main = (

let uu____10336 = (

let uu____10337 = (FStar_Ident.lid_of_ids ((fresh_toplevel_name)::[]))
in FStar_Parser_AST.Var (uu____10337))
in (FStar_Parser_AST.mk_term uu____10336 FStar_Range.dummyRange FStar_Parser_AST.Expr))
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

let uu____10365 = (desugar_decl env1 id_decl)
in (match (uu____10365) with
| (env2, ses') -> begin
((env2), ((FStar_List.append ses ses')))
end))))))))
end))
in (

let bvs = (

let uu____10376 = (gather_pattern_bound_vars pat)
in (FStar_All.pipe_right uu____10376 FStar_Util.set_elements))
in (FStar_List.fold_left build_projection main_let bvs))))))
end))
end)))))
end
| FStar_Parser_AST.Main (t) -> begin
(

let e = (desugar_term env t)
in (

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_main (e); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange}
in ((env), ((se)::[]))))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let f = (desugar_formula env t)
in (

let lid = (FStar_ToSyntax_Env.qualify env id)
in (

let env1 = (FStar_ToSyntax_Env.push_doc env lid d.FStar_Parser_AST.doc)
in ((env1), (({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((lid), (f), ((FStar_Syntax_Syntax.Assumption)::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange})::[])))))
end
| FStar_Parser_AST.Val (id, t) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let t1 = (

let uu____10398 = (close_fun env t)
in (desugar_term env uu____10398))
in (

let quals1 = (match ((env.FStar_ToSyntax_Env.iface && env.FStar_ToSyntax_Env.admitted_iface)) with
| true -> begin
(FStar_Parser_AST.Assumption)::quals
end
| uu____10402 -> begin
quals
end)
in (

let lid = (FStar_ToSyntax_Env.qualify env id)
in (

let se = (

let uu____10405 = (

let uu____10406 = (

let uu____10412 = (FStar_List.map (trans_qual1 None) quals1)
in ((lid), ([]), (t1), (uu____10412)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____10406))
in {FStar_Syntax_Syntax.sigel = uu____10405; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange})
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se)
in (

let env2 = (FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc)
in ((env2), ((se)::[])))))))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(

let uu____10421 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (match (uu____10421) with
| (t, uu____10429) -> begin
(

let l = (FStar_ToSyntax_Env.qualify env id)
in (

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Syntax_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((FStar_Syntax_Const.exn_lid)::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange}
in (

let se' = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((l)::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange}
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se')
in (

let env2 = (FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc)
in (

let data_ops = (mk_data_projector_names [] env2 (([]), (se)))
in (

let discs = (mk_data_discriminators [] env2 FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (

let env3 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2 (FStar_List.append discs data_ops))
in ((env3), ((FStar_List.append ((se')::discs) data_ops)))))))))))
end))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(

let t = (desugar_term env term)
in (

let t1 = (

let uu____10457 = (

let uu____10461 = (FStar_Syntax_Syntax.null_binder t)
in (uu____10461)::[])
in (

let uu____10462 = (

let uu____10465 = (

let uu____10466 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (Prims.fst uu____10466))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____10465))
in (FStar_Syntax_Util.arrow uu____10457 uu____10462)))
in (

let l = (FStar_ToSyntax_Env.qualify env id)
in (

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t1), (FStar_Syntax_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((FStar_Syntax_Const.exn_lid)::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange}
in (

let se' = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((l)::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange}
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se')
in (

let env2 = (FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc)
in (

let data_ops = (mk_data_projector_names [] env2 (([]), (se)))
in (

let discs = (mk_data_discriminators [] env2 FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (

let env3 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2 (FStar_List.append discs data_ops))
in ((env3), ((FStar_List.append ((se')::discs) data_ops)))))))))))))
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

let uu____10513 = (FStar_ToSyntax_Env.try_lookup_effect_name env l1)
in (match (uu____10513) with
| None -> begin
(

let uu____10515 = (

let uu____10516 = (

let uu____10519 = (

let uu____10520 = (

let uu____10521 = (FStar_Syntax_Print.lid_to_string l1)
in (Prims.strcat uu____10521 " not found"))
in (Prims.strcat "Effect name " uu____10520))
in ((uu____10519), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____10516))
in (Prims.raise uu____10515))
end
| Some (l2) -> begin
l2
end)))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let uu____10525 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(

let uu____10547 = (

let uu____10552 = (

let uu____10556 = (desugar_term env t)
in (([]), (uu____10556)))
in Some (uu____10552))
in ((uu____10547), (None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(

let uu____10574 = (

let uu____10579 = (

let uu____10583 = (desugar_term env wp)
in (([]), (uu____10583)))
in Some (uu____10579))
in (

let uu____10588 = (

let uu____10593 = (

let uu____10597 = (desugar_term env t)
in (([]), (uu____10597)))
in Some (uu____10593))
in ((uu____10574), (uu____10588))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(

let uu____10611 = (

let uu____10616 = (

let uu____10620 = (desugar_term env t)
in (([]), (uu____10620)))
in Some (uu____10616))
in ((None), (uu____10611)))
end)
in (match (uu____10525) with
| (lift_wp, lift) -> begin
(

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect ({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange}
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun uu____10671 d -> (match (uu____10671) with
| (env1, sigelts) -> begin
(

let uu____10683 = (desugar_decl env1 d)
in (match (uu____10683) with
| (env2, se) -> begin
((env2), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))


let open_prims_all : (FStar_Parser_AST.decoration Prims.list  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]


let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env1 = (match (((curmod), (m))) with
| (None, uu____10725) -> begin
env
end
| (Some ({FStar_Syntax_Syntax.name = prev_lid; FStar_Syntax_Syntax.declarations = uu____10728; FStar_Syntax_Syntax.exports = uu____10729; FStar_Syntax_Syntax.is_interface = uu____10730}), FStar_Parser_AST.Module (current_lid, uu____10732)) when ((FStar_Ident.lid_equals prev_lid current_lid) && (FStar_Options.interactive ())) -> begin
env
end
| (Some (prev_mod), uu____10737) -> begin
(FStar_ToSyntax_Env.finish_module_or_interface env prev_mod)
end)
in (

let uu____10739 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(

let uu____10759 = (FStar_ToSyntax_Env.prepare_module_or_interface true admitted env1 mname)
in ((uu____10759), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(

let uu____10769 = (FStar_ToSyntax_Env.prepare_module_or_interface false false env1 mname)
in ((uu____10769), (mname), (decls), (false)))
end)
in (match (uu____10739) with
| ((env2, pop_when_done), mname, decls, intf) -> begin
(

let uu____10787 = (desugar_decls env2 decls)
in (match (uu____10787) with
| (env3, sigelts) -> begin
(

let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in ((env3), (modul), (pop_when_done)))
end))
end))))


let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (

let m1 = (

let uu____10812 = ((FStar_Options.interactive ()) && (

let uu____10813 = (

let uu____10814 = (

let uu____10815 = (FStar_Options.file_list ())
in (FStar_List.hd uu____10815))
in (FStar_Util.get_file_extension uu____10814))
in (uu____10813 = "fsti")))
in (match (uu____10812) with
| true -> begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface (((mname), (decls), (true)))
end
| FStar_Parser_AST.Interface (mname, uu____10823, uu____10824) -> begin
(failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end
| uu____10827 -> begin
m
end))
in (

let uu____10828 = (desugar_modul_common curmod env m1)
in (match (uu____10828) with
| (x, y, pop_when_done) -> begin
((match (pop_when_done) with
| true -> begin
(

let uu____10838 = (FStar_ToSyntax_Env.pop ())
in ())
end
| uu____10839 -> begin
()
end);
((x), (y));
)
end))))


let desugar_modul : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun env m -> (

let uu____10850 = (desugar_modul_common None env m)
in (match (uu____10850) with
| (env1, modul, pop_when_done) -> begin
(

let env2 = (FStar_ToSyntax_Env.finish_module_or_interface env1 modul)
in ((

let uu____10861 = (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____10861) with
| true -> begin
(

let uu____10862 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" uu____10862))
end
| uu____10863 -> begin
()
end));
(

let uu____10864 = (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface modul.FStar_Syntax_Syntax.name env2)
end
| uu____10865 -> begin
env2
end)
in ((uu____10864), (modul)));
))
end)))


let desugar_file : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (

let uu____10875 = (FStar_List.fold_left (fun uu____10882 m -> (match (uu____10882) with
| (env1, mods) -> begin
(

let uu____10894 = (desugar_modul env1 m)
in (match (uu____10894) with
| (env2, m1) -> begin
((env2), ((m1)::mods))
end))
end)) ((env), ([])) f)
in (match (uu____10875) with
| (env1, mods) -> begin
((env1), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_ToSyntax_Env.env  ->  FStar_ToSyntax_Env.env = (fun m en -> (

let uu____10918 = (FStar_ToSyntax_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (uu____10918) with
| (en1, pop_when_done) -> begin
(

let en2 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt (

let uu___224_10924 = en1
in {FStar_ToSyntax_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_ToSyntax_Env.curmonad = uu___224_10924.FStar_ToSyntax_Env.curmonad; FStar_ToSyntax_Env.modules = uu___224_10924.FStar_ToSyntax_Env.modules; FStar_ToSyntax_Env.scope_mods = uu___224_10924.FStar_ToSyntax_Env.scope_mods; FStar_ToSyntax_Env.exported_ids = uu___224_10924.FStar_ToSyntax_Env.exported_ids; FStar_ToSyntax_Env.trans_exported_ids = uu___224_10924.FStar_ToSyntax_Env.trans_exported_ids; FStar_ToSyntax_Env.includes = uu___224_10924.FStar_ToSyntax_Env.includes; FStar_ToSyntax_Env.sigaccum = uu___224_10924.FStar_ToSyntax_Env.sigaccum; FStar_ToSyntax_Env.sigmap = uu___224_10924.FStar_ToSyntax_Env.sigmap; FStar_ToSyntax_Env.iface = uu___224_10924.FStar_ToSyntax_Env.iface; FStar_ToSyntax_Env.admitted_iface = uu___224_10924.FStar_ToSyntax_Env.admitted_iface; FStar_ToSyntax_Env.expect_typ = uu___224_10924.FStar_ToSyntax_Env.expect_typ; FStar_ToSyntax_Env.docs = uu___224_10924.FStar_ToSyntax_Env.docs}) m.FStar_Syntax_Syntax.exports)
in (

let env = (FStar_ToSyntax_Env.finish_module_or_interface en2 m)
in (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name env)
end
| uu____10926 -> begin
env
end)))
end)))




